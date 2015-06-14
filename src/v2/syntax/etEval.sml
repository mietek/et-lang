signature etEVAL =
sig
  structure AbsSyn     : etABSTRACTSYNTAX
  structure Env        : etENVIRONMENT

  val toHeadNormalForm : Env.Env -> AbsSyn.etTerm -> AbsSyn.etTerm
  val toNormalForm     : Env.Env -> AbsSyn.etTerm -> AbsSyn.etTerm
end

functor etEvalFun (structure AbsSyn : etABSTRACTSYNTAX
                   structure Env    : etENVIRONMENT
                   sharing AbsSyn = Env.AbsSyn) : etEVAL =
struct

structure AbsSyn     = AbsSyn
structure Env        = Env

fun liftBound level st (t as AbsSyn.BoundVar j) =
      if j>=st then AbsSyn.BoundVar (j+level) else t
  | liftBound level st (AbsSyn.App (t1,t2)) =
      AbsSyn.App (liftBound level st t1,liftBound level st t2)
  | liftBound level st (AbsSyn.Abs (n,t)) =
      AbsSyn.Abs (n,liftBound level (st+1) t)
  | liftBound level st (AbsSyn.Cons (a,b,c,d,e,f,lt)) =
      AbsSyn.Cons (a,b,c,d,e,f,map (liftBound level st) lt)
  | liftBound level st (AbsSyn.Coit (a,b,c,lt)) =
      AbsSyn.Coit (a,b,c,map (liftBound level st) lt)
  | liftBound level st (AbsSyn.Corec (a,b,c,lt)) =
      AbsSyn.Corec (a,b,c,map (liftBound level st) lt)
  | liftBound _     _   t        = t

fun appBound level ap (t as AbsSyn.BoundVar i) =
      if level=i then liftBound i 0 ap else
	if level<i then AbsSyn.BoundVar (i-1) else t
  | appBound level ap (AbsSyn.App (t1,t2)) =
      AbsSyn.App (appBound level ap t1,appBound level ap t2)
  | appBound level ap (AbsSyn.Abs (n,t)) =
      AbsSyn.Abs (n,(appBound (level+1) ap t))
  | appBound level ap (AbsSyn.Cons (a,b,c,d,e,f,lt)) =
      AbsSyn.Cons (a,b,c,d,e,f,map (appBound level ap) lt)
  | appBound level ap (AbsSyn.Coit (a,b,c,lt)) =
      AbsSyn.Coit (a,b,c,map (appBound level ap) lt)
  | appBound level ap (AbsSyn.Corec (a,b,c,lt)) =
      AbsSyn.Corec (a,b,c,map (appBound level ap) lt)
  | appBound _     _   t              = t

fun isFreeIn level (AbsSyn.BoundVar j) = level = j
  | isFreeIn level (AbsSyn.App (t1,t2)) =
      (isFreeIn level t1) orelse (isFreeIn level t2)
  | isFreeIn level (AbsSyn.Abs (_,t)) = isFreeIn (level+1) t
  | isFreeIn level (AbsSyn.Cons (a,b,c,d,e,f,lt)) =
      List.exists (isFreeIn level) lt
  | isFreeIn level (AbsSyn.Coit (a,b,c,lt)) =
      List.exists (isFreeIn level) lt
  | isFreeIn level (AbsSyn.Corec (a,b,c,lt)) =
      List.exists (isFreeIn level) lt
  | isFreeIn _      t        = false

datatype eq = EQyes | EQno | EQmaybe;

fun testEq env boundLevel (AbsSyn.BoundVar i) (AbsSyn.BoundVar j) =
  if i=j then EQyes else
      if i<boundLevel orelse j<boundLevel
	  then EQno else EQmaybe
  | testEq env boundLevel (AbsSyn.BoundVar i) _ =
	      if i<boundLevel then EQno else EQmaybe
  | testEq env boundLevel _ (AbsSyn.BoundVar j) =
	      if j<boundLevel then EQno else EQmaybe
  | testEq env boundLevel (AbsSyn.Abs (_,t1)) (AbsSyn.Abs (_,t2)) =
      testEq env (boundLevel+1) t1 t2
  | testEq env boundLevel (AbsSyn.App (t11,t12)) (AbsSyn.App (t21,t22)) =
    testEqL env boundLevel ([t11,t12]) ([t21,t22])
  | testEq env boundLevel (AbsSyn.Cons (_,id1,n1,_,_,_,tl1))
           (AbsSyn.Cons (_,id2,n2,_,_,_,tl2)) =
	   if id1=id2 andalso n1=n2 then testEqL env boundLevel tl1 tl2
	     else EQno
  | testEq env boundLevel (AbsSyn.Iter (_,id1,_)) (AbsSyn.Iter (_,id2,_)) =
	       if id1=id2 then EQyes else EQno
  | testEq env boundLevel (AbsSyn.Rec (_,id1,_)) (AbsSyn.Rec (_,id2,_)) =
	       if id1=id2 then EQyes else EQno
  | testEq env boundLevel (AbsSyn.Iter (_,id1,_)) (AbsSyn.Rec (_,id2,_)) =
	       if id1=id2 then
		   let
		       val (_,_,cl) = Env.getTypeDefFromNumber env id1
		   in
		       if List.all
			   (fn (AbsSyn.Cons (_,_,_,_,t1,t2,_),_) => t1=t2
			    | _  => true) cl then EQyes
		       else EQno
		   end
	       else EQno
  | testEq env boundLevel (AbsSyn.Rec (_,id1,_)) (AbsSyn.Iter (_,id2,_)) =
	       if id1=id2 then
		   let
		       val (_,_,cl) = Env.getTypeDefFromNumber env id1
		   in
		       if List.all
			   (fn (AbsSyn.Cons (_,_,_,_,t1,t2,_),_) => t1=t2
			    | _  => true) cl then EQyes
		       else EQno
		   end
	       else EQno
  | testEq env boundLevel (AbsSyn.Des (_,id1,n1,_,_))
		   (AbsSyn.Des (_,id2,n2,_,_)) =
	       if id1=id2 andalso n1=n2 then EQyes else EQno
  | testEq env boundLevel (AbsSyn.Coit (_,id1,_,tl1))
		   (AbsSyn.Coit (_,id2,_,tl2)) =
	   if id1=id2 then testEqL env boundLevel tl1 tl2 else EQno
  | testEq env boundLevel (AbsSyn.Corec (_,id1,_,tl1))
	              (AbsSyn.Corec (_,id2,_,tl2))=
	   if id1=id2 then testEqL env boundLevel tl1 tl2 else EQno
  | testEq env boundLevel (AbsSyn.Coit (_,id1,_,tl1))
		   (AbsSyn.Corec (_,id2,_,tl2)) =
	   if id1=id2 then
	       let
		   val (_,_,dl) = Env.getCoTypeDefFromNumber env id1
	       in
		   if List.all (fn (AbsSyn.Des (_,_,_,t1,t2),_) => t1=t2
                       | _  => true) dl
		       then testEqL env boundLevel tl1 tl2
		   else EQno
	       end
	   else EQno
  | testEq env boundLevel (AbsSyn.Corec (_,id1,_,tl1))
		   (AbsSyn.Coit (_,id2,_,tl2)) =
	   if id1=id2 then
	       let
		   val (_,_,dl) = Env.getCoTypeDefFromNumber env id1
	       in
		   if List.all (fn (AbsSyn.Des (_,_,_,t1,t2),_) => t1=t2
                       | _  => true) dl
		       then testEqL env boundLevel tl1 tl2
		   else EQno
	       end
	   else EQno
  | testEq _ _ _ _ = EQno
and testEqL env boundLevel nil     nil         = EQyes
  | testEqL env boundLevel (h1::tl1) (h2::tl2) =
       (case testEq env boundLevel h1 h2 of
	  EQyes =>  testEqL env boundLevel tl1 tl2
	| EQno  => EQno
	| EQmaybe => (fn EQno => EQno | _ => EQmaybe)
	               (testEqL env boundLevel tl1 tl2))
  | testEqL _ _ _ _                 = EQno

val izero  = IntInf.fromInt 0;
val ijeden = IntInf.fromInt 1;
fun ifOnlyNat (AbsSyn.Cons ("Suc",40,1,_,_,_,[tl])) =
      (fn (a,b) => (a,IntInf.+ (b,ijeden))) (ifOnlyNat tl)
  | ifOnlyNat (AbsSyn.Cons ("0",40,2,_,_,_,[])) =
      (true,izero)
  | ifOnlyNat _ = (false,izero)

fun mkNumber n = if IntInf.> (n,izero) then
AbsSyn.Cons ("Suc",40,1,1, AbsSyn.Abs("u1",
              AbsSyn.Abs ("v1", AbsSyn.Abs ("v2", AbsSyn.App
              (AbsSyn.BoundVar 1, AbsSyn.App (AbsSyn.App (AbsSyn.App
              (AbsSyn.Iter ("_NATit",40,2),AbsSyn.BoundVar
              2),AbsSyn.BoundVar 1), AbsSyn.BoundVar 0))))),
              AbsSyn.Abs ("u1", AbsSyn.Abs ("v1", AbsSyn.Abs ("v2",
              AbsSyn.App (AbsSyn.BoundVar 1, AbsSyn.Cons (",",2,1,2,
              AbsSyn.Abs ("u1", AbsSyn.Abs ("u2", AbsSyn.Abs ("v1",
              AbsSyn.App (AbsSyn.App (AbsSyn.BoundVar
              0,AbsSyn.BoundVar 2),AbsSyn.BoundVar 1)))), AbsSyn.Abs
              ("u1", AbsSyn.Abs ("u2", AbsSyn.Abs ("v1", AbsSyn.App
              (AbsSyn.App (AbsSyn.BoundVar 0,AbsSyn.BoundVar
              2),AbsSyn.BoundVar 1)))), [AbsSyn.BoundVar 2, AbsSyn.App
              (AbsSyn.App (AbsSyn.App (AbsSyn.Rec
              ("_NATrec",40,2),AbsSyn.BoundVar 2), AbsSyn.BoundVar
              1),AbsSyn.BoundVar 0)]))))),[mkNumber (IntInf.- (n,ijeden))])
    else AbsSyn.Cons ("0",40,2,0,AbsSyn.Abs ("v1",AbsSyn.Abs
              ("v2",AbsSyn.BoundVar 0)), AbsSyn.Abs ("v1",AbsSyn.Abs
              ("v2",AbsSyn.BoundVar 0)),[])


fun toHeadNormalForm env (AbsSyn.Var n) =
      toHeadNormalForm env ((fn (a,b) => a) (Env.getTermFromNumber env n))
(*  | toHeadNormalForm env
        (tt as AbsSyn.Abs (_,AbsSyn.App(t,AbsSyn.BoundVar 0))) =
			  if isFreeIn 0 t then tt
			  else toHeadNormalForm env (liftBound ~1 0 t) *)
  | toHeadNormalForm env (AbsSyn.App (AbsSyn.App(AbsSyn.Var 25,t1),t2)) =
      let
	val (ifNum1,BigNum1) = ifOnlyNat t1
	val (ifNum2,BigNum2) = ifOnlyNat t2
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.+ (BigNum1,BigNum2))
	else (
      let
	val (ifNum1,BigNum1) = ifOnlyNat (toNormalForm env t1)
	val (ifNum2,BigNum2) = ifOnlyNat (toNormalForm env t2)
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.+ (BigNum1,BigNum2))
	else
          toHeadNormalForm env (AbsSyn.App (AbsSyn.App(
	    (fn (a,b) => a) (Env.getTermFromNumber env 25),t1),t2))
      end)
      end
  | toHeadNormalForm env (AbsSyn.App (AbsSyn.App(AbsSyn.Var 26,t1),t2)) =
      let
	val (ifNum1,BigNum1) = ifOnlyNat (toNormalForm env t1)
	val (ifNum2,BigNum2) = ifOnlyNat (toNormalForm env t2)
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.* (BigNum1,BigNum2))
	else
          toHeadNormalForm env (AbsSyn.App (AbsSyn.App(
	    (fn (a,b) => a) (Env.getTermFromNumber env 26),t1),t2))
      end
  | toHeadNormalForm env (AbsSyn.App (t1,t2)) =
     (case toHeadNormalForm env t1
	of
	  AbsSyn.Cons ("=",b,c,d,e,f,[t]) =>
	  let
	    val t1 = toNormalForm env t
	    val t2 = toNormalForm env t2
	  in
	    case testEq env 0 t1 t2 of
	      EQyes     => AbsSyn.Var 13
	      | EQno    => AbsSyn.Var 14
	      | EQmaybe => AbsSyn.Cons ("=",b,c,d,e,f,[t1,t2])
	  end
         | AbsSyn.Cons (a,b,c,d,e,f,args) =>
	  toHeadNormalForm env (AbsSyn.Cons (a,b,c,d,e,f,args@[t2]))
         | AbsSyn.Abs (_,t1)           =>
	  toHeadNormalForm env (appBound 0 t2 t1)
         | (t as AbsSyn.Iter (_,n,_))  =>
	    (fn (tt as AbsSyn.Cons (_,nn,_,_,t,_,args)) =>
               if n=nn then
                   toHeadNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) t args)
               else AbsSyn.App (t,tt)
	     | tt => AbsSyn.App (t,tt)) (toHeadNormalForm env t2)
         | (t as AbsSyn.Rec (_,n,_))  =>
	    (fn (tt as AbsSyn.Cons (_,nn,_,_,_,t,args)) =>
               if n=nn then
                   toHeadNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) t args)
               else AbsSyn.App (t,tt)
	     | tt => AbsSyn.App (t,tt)) (toHeadNormalForm env t2)
         | AbsSyn.Coit (a,b,c,args) =>
	  toHeadNormalForm env (AbsSyn.Coit (a,b,c,args@[t2]))
         | AbsSyn.Corec (a,b,c,args) =>
	  toHeadNormalForm env (AbsSyn.Corec (a,b,c,args@[t2]))
         | (t as AbsSyn.Des (_,n,_,ti,tr))  =>
	    (fn (tt as AbsSyn.Coit (_,nn,_,args)) =>
               if n=nn then
                   toHeadNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) ti args)
               else AbsSyn.App (t,tt)
	      | (tt as AbsSyn.Corec (_,nn,_,args)) =>
		   if n=nn then
		       toHeadNormalForm env
		       (List.foldl (fn (a,b) => AbsSyn.App (b,a)) tr args)
		   else AbsSyn.App (t,tt)
	      | tt => AbsSyn.App (t,tt)) (toHeadNormalForm env t2)
         | t                           => AbsSyn.App (t,t2))
  | toHeadNormalForm _ t = t
and toNormalForm env (AbsSyn.Var n) =
      toNormalForm env ((fn (a,b) => a) (Env.getTermFromNumber env n))
(*  | toNormalForm env
        (tt as AbsSyn.Abs (s,ttt as AbsSyn.App(t,AbsSyn.BoundVar 0))) =
			  if isFreeIn 0 t then
			       AbsSyn.Abs (s, toNormalForm env ttt)
			  else toNormalForm env (liftBound ~1 0 t)*)
  | toNormalForm env (AbsSyn.App (AbsSyn.App(AbsSyn.Var 25,t1),t2)) =
      let
	val (ifNum1,BigNum1) = ifOnlyNat t1
	val (ifNum2,BigNum2) = ifOnlyNat t2
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.+ (BigNum1,BigNum2))
	  else (
      let
	val nf1 = toNormalForm env t1
	val nf2 = toNormalForm env t2
	val (ifNum1,BigNum1) = ifOnlyNat nf1
	val (ifNum2,BigNum2) = ifOnlyNat nf2
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.+ (BigNum1,BigNum2))
	else
          toNormalForm env (AbsSyn.App (AbsSyn.App(
	    (fn (a,b) => a) (Env.getTermFromNumber env 25),nf1),nf2))
      end)
      end
  | toNormalForm env (AbsSyn.App (AbsSyn.App(AbsSyn.Var 26,t1),t2)) =
      let
	val nf1 = toNormalForm env t1
	val nf2 = toNormalForm env t2
	val (ifNum1,BigNum1) = ifOnlyNat nf1
	val (ifNum2,BigNum2) = ifOnlyNat nf2
      in
	if ifNum1 andalso ifNum2 then
	  mkNumber (IntInf.* (BigNum1,BigNum2))
	else
          toNormalForm env (AbsSyn.App (AbsSyn.App(
	    (fn (a,b) => a) (Env.getTermFromNumber env 26),nf1),nf2))
      end
  | toNormalForm env (AbsSyn.App (t1,t2)) =
     (case toNormalForm env t1
	of
	  AbsSyn.Cons ("=",b,c,d,e,f,[t]) =>
	    let
	      val t1 = toNormalForm env t
	      val t2 = toNormalForm env t2
	    in
	      case testEq env 0 t1 t2 of
		EQyes     => AbsSyn.Var 13
	      | EQno    => AbsSyn.Var 14
	      | EQmaybe => AbsSyn.Cons ("=",b,c,d,e,f,[t1,t2])
	    end
	| AbsSyn.Cons (a,b,c,d,e,f,args) =>
	    toNormalForm env (AbsSyn.Cons (a,b,c,d,e,f,args@[t2]))
	| AbsSyn.Abs (_,t1)           =>
	    toNormalForm env (appBound 0 t2 t1)
	| (t as AbsSyn.Iter (_,n,_))  =>
	    (fn (tt as AbsSyn.Cons (_,nn,_,_,t,_,args)) =>
               if n=nn then
                   toNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) t args)
               else AbsSyn.App (t,tt)
	     | tt => AbsSyn.App (t,tt)) (toNormalForm env t2)
	| (t as AbsSyn.Rec (_,n,_))  =>
	    (fn (tt as AbsSyn.Cons (_,nn,_,_,_,t,args)) =>
               if n=nn then
                   toNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) t args)
               else AbsSyn.App (t,tt)
	     | tt => AbsSyn.App (t,tt)) (toNormalForm env t2)
        | AbsSyn.Coit (a,b,c,args) =>
	  toNormalForm env (AbsSyn.Coit (a,b,c,args@[t2]))
        | AbsSyn.Corec (a,b,c,args) =>
	  toNormalForm env (AbsSyn.Corec (a,b,c,args@[t2]))
	| (t as AbsSyn.Des (_,n,_,ti,tr))  =>
	    (fn (tt as AbsSyn.Coit (_,nn,_,args)) =>
               if n=nn then
                   toNormalForm env
                   (List.foldl (fn (a,b) => AbsSyn.App (b,a)) ti args)
               else AbsSyn.App (t,tt)
	     | (tt as AbsSyn.Corec (_,nn,_,args)) =>
		   if n=nn then
		       toNormalForm env
		       (List.foldl (fn (a,b) => AbsSyn.App (b,a)) tr args)
		   else AbsSyn.App (t,tt)
	      | tt => AbsSyn.App (t,tt)) (toNormalForm env t2)
	| t                           => AbsSyn.App (t,toNormalForm env t2))
(*  | toNormalForm env (AbsSyn.Abs     (n,AbsSyn.App(t,AbsSyn.BoundVar 0))) =
	toNormalForm env t*)
  | toNormalForm env (AbsSyn.Abs     (n,t)) =
	AbsSyn.Abs (n,toNormalForm env t)
  | toNormalForm env (AbsSyn.Cons (a,b,c,d,e,f,args)) =
        (AbsSyn.Cons (a,b,c,d,e,f,map (toNormalForm env) args))
  | toNormalForm env (AbsSyn.Coit (a,b,c,args)) =
        (AbsSyn.Coit (a,b,c,map (toNormalForm env) args))
  | toNormalForm env (AbsSyn.Corec (a,b,c,args)) =
        (AbsSyn.Corec (a,b,c,map (toNormalForm env) args))
  | toNormalForm _ t = t
end

structure etEval = etEvalFun(structure AbsSyn = etAbstractSyntax
			     structure Env    = etEnvironment)
