signature etENVIRONMENT =
sig
  type Env

  structure AbsSyn : etABSTRACTSYNTAX

  exception NotFoundInEnv

  val emptyEnv : Env

  val libEnv : Env

  val maxTermVarEnv     : Env -> AbsSyn.TermNumberId
  val maxTypeVarEnv     : Env -> AbsSyn.TypeNumberId

  val addTermToEnv : Env -> string * AbsSyn.etTerm * AbsSyn.etType
                         -> Env

  val addTermToEnvWithNumber : Env -> string * AbsSyn.etTerm * AbsSyn.etType
                               -> (Env * AbsSyn.TermNumberId)

  val addTypeToEnv : Env -> string -> Env

  val getTermFromNumber : Env -> AbsSyn.TermNumberId
                              -> AbsSyn.etTerm * AbsSyn.etType
  val getTermFromName   : Env -> string ->
                            AbsSyn.TermNumberId * AbsSyn.etTerm * AbsSyn.etType
  val getTermFromLib    : Env -> string ->
                            AbsSyn.TermNumberId * AbsSyn.etTerm * AbsSyn.etType
  val getTermNameFromNumber : Env -> AbsSyn.TermNumberId -> string

  val appFunToEnv : Env ->
    ((string * AbsSyn.TermNumberId * AbsSyn.etTerm * AbsSyn.etType) ->
     (string * AbsSyn.TermNumberId * AbsSyn.etTerm * AbsSyn.etType)) -> Env

  val getTypeFromName   : Env -> string -> AbsSyn.TypeNumberId

  val getTypeFromLib    : Env -> string -> AbsSyn.TypeNumberId

  val getTypeNameFromNumber : Env -> AbsSyn.TypeNumberId -> string

  val getTypeList : Env -> string list

  val getTypeDef : Env -> string ->
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list))

  val getTypeDefFromNumber : Env -> AbsSyn.TypeNumberId ->
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list))

  val getCoTypeDef : Env -> string ->
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list))

  val getCoTypeDefFromNumber : Env -> AbsSyn.TypeNumberId ->
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list))

  val GarbageCollector : Env -> Env
end


functor etEnvironmentFun (structure AbsSyn : etABSTRACTSYNTAX):etENVIRONMENT=
struct
  type Env =
         (string * AbsSyn.TermNumberId * AbsSyn.etTerm * AbsSyn.etType) list *
	  (string * AbsSyn.TypeNumberId) list

  structure AbsSyn = AbsSyn

  exception NotFoundInEnv

  val emptyEnv = (nil,[("->",1)])

  val libEnv = let
	val typeList =  [("NAT",40),("BOOL",38),("UNIT",36),("{}",34),
			 ("+",6),("*",2),("->",1)]
	local
	    open AbsSyn in
	val envList = [
    ("sub",28,
     Abs ("n",Abs ("m",App (App (App (Var 21,BoundVar 0),Var 27),BoundVar 1))),
     TypeApp
       (1,[TypeApp (40,[]),TypeApp (1,[TypeApp (40,[]),TypeApp (40,[])])])),
    ("pred",27,
     Abs
       ("n",
        App
          (App (App (Var 22,BoundVar 0),Var 7),
           Cons
             ("0",40,2,0,Abs ("v1",Abs ("v2",BoundVar 0)),
              Abs ("v1",Abs ("v2",BoundVar 0)),[]))),
     TypeApp (1,[TypeApp (40,[]),TypeApp (40,[])])),
           ("mult",26,Abs("n",Abs("m",App
             (App (App (Var 21,BoundVar 1),
			  App (Var 25,BoundVar 0)),
              Cons
                ("0",40,2,0,Abs ("v1",Abs
					("v2",BoundVar 0)),
                 Abs ("v1",Abs ("v2",BoundVar 0)),[])))),
     TypeApp
       (1,[TypeApp (40,[]),TypeApp (1,[TypeApp (40,[]),
					     TypeApp (40,[])])])),
	   ("add",25,Abs ("n",App (App (Var 21,
	       BoundVar 0),Var 23)),
	    TypeApp
       (1,[TypeApp (40,[]),TypeApp (1,[TypeApp (40,[]),
					TypeApp (40,[])])])),
	   ("0",24, Cons ("0",40,2,0,Abs ("v1",Abs
	      ("v2",BoundVar 0)), Abs ("v1",Abs
	      ("v2",BoundVar 0)),[]),TypeApp (40,[])),
	      ("Suc",23,Cons ("Suc",40,1,1, Abs("u1",
	      Abs ("v1", Abs ("v2", App
	      (BoundVar 1, App (App (App
	      (Iter ("_NATit",40,2),BoundVar
	      2),BoundVar 1), BoundVar 0))))),
	      Abs ("u1", Abs ("v1", Abs ("v2",
	      App (BoundVar 1, Cons (",",2,1,2,
	      Abs ("u1", Abs ("u2", Abs ("v1",
	      App (App (BoundVar
	      0,BoundVar 2),BoundVar 1)))), Abs
	      ("u1", Abs ("u2", Abs ("v1", App
	      (App (BoundVar 0,BoundVar
	      2),BoundVar 1)))), [BoundVar 2, App
	      (App (App (Rec
	      ("_NATrec",40,2),BoundVar 2), BoundVar
	      1),BoundVar 0)]))))),[]), TypeApp
	      (1,[TypeApp (40,[]),TypeApp (40,[])])),
	      ("_NATrec",22,Rec ("_NATrec",40,2),
	      TypeApp (1, [TypeApp (40,[]),
	      TypeApp (1, [TypeApp (1,[TypeApp
	      (2,[TypeApp (40,[]),TypeVar
	      41]),TypeVar 41]), TypeApp
	      (1,[TypeVar 41,TypeVar 41])])])),
	      ("_NATit",21,Iter ("_NATit",40,2), TypeApp
	      (1, [TypeApp (40,[]), TypeApp (1,
	      [TypeApp (1,[TypeVar 41,TypeVar
	      41]), TypeApp (1,[TypeVar
	      41,TypeVar 41])])])),
	   ("=",15,Cons ("=",38,3,2,Abs ("v1",
	    Abs ("v2",Var 14)),Abs ("v1",
	    Abs ("v2",Var 14)),[]),
            TypeApp (1,[TypeVar 39,
			       TypeApp (1,[TypeVar 39
						  ,TypeApp (38,[])])])),
	   ("False",14,Cons ("False",38,2,0,Abs ("v1",
	    Abs ("v2",BoundVar 0)),Abs ("v1",
	    Abs ("v2",BoundVar 0)),[]),
            TypeApp (38,[])),
           ("True",13,Cons ("True",38,1,0,Abs ("v1",
             Abs ("v2",BoundVar 1)),Abs ("v1",
             Abs ("v2",BoundVar 1)),[]),
             TypeApp (38,[])),
           ("IF",12,Iter ("IF",38,2),TypeApp (1,
            [TypeApp (38,[]), TypeApp (1,[TypeVar 39,
             TypeApp (1,[TypeVar 39,TypeVar 39])])])),
           ("IFrec",16,Rec ("IFrec",38,2),TypeApp (1,
            [TypeApp (38,[]), TypeApp (1,[TypeVar 39,
             TypeApp (1,[TypeVar 39,TypeVar 39])])])),
           ("()",11,Cons ("()",36,1,0,Abs ("v1",
	    BoundVar 0),Abs ("v1",
	    BoundVar 0),[]),TypeApp (36,[])),
           ("case1",10,Iter ("case1",36,1),TypeApp (1,[
            TypeApp (36,[]),TypeApp (1,[TypeVar 37,
            TypeVar 37])])),
           ("case1rec",17,Rec ("case1rec",36,1),TypeApp (1,[
            TypeApp (36,[]),TypeApp (1,[TypeVar 37,
            TypeVar 37])])),
           ("case0",9,Iter ("case0",34,0),TypeApp (1,[
            TypeApp (34,[]),TypeVar 35])),
           ("case0rec",18,Rec ("case0rec",34,0),TypeApp (1,[
            TypeApp (34,[]),TypeVar 35])),
           ("snd",8,Abs ("p",App (App (Var 1,
	    BoundVar 0),Abs ("a",
	    Abs ("b",BoundVar 0)))),
             TypeApp (1,[TypeApp (2,[TypeVar 31,
            TypeVar 33]),TypeVar 33])),
           ("fst",7,Abs ("p",App (App (Var 1,
            BoundVar 0),Abs ("a",Abs ("b",
            BoundVar 1)))),TypeApp (1,[TypeApp (2,[
            TypeVar 23,TypeVar 22]),TypeVar 23])),
            ("Inr",5,Cons ("Inr",6,2,1,
	     Abs ("u1",Abs ("v1",
             Abs ("v2",App (BoundVar 0,
             BoundVar 2)))),Abs ("u1",Abs ("v1",
             Abs ("v2",App (BoundVar 0,
             BoundVar 2)))),[]),
             TypeApp (1,[TypeVar 8,TypeApp (6,
             [TypeVar 7,TypeVar 8])])),
            ("Inl",4,Cons ("Inl",6,1,1,Abs ("u1",
              Abs ("v1",Abs ("v2",App (
              BoundVar 1,BoundVar 2)))),Abs ("u1",
              Abs ("v1",Abs ("v2",App (
              BoundVar 1,BoundVar 2)))),[]),
              TypeApp (1,[TypeVar 7,TypeApp (6,
	      [TypeVar 7,TypeVar 8])])),
	    ("when",3,Iter ("when",6,2),TypeApp (1,
              [TypeApp (6,[TypeVar 7,TypeVar 8]),
              TypeApp (1,[TypeApp (1,[TypeVar 7,
	      TypeVar 9]),TypeApp (1,[TypeApp
	      (1,[TypeVar 8,TypeVar 9]),TypeVar 9])])])),
	    ("whenrec",20,Rec ("whenrec",6,2),TypeApp (1,
              [TypeApp (6,[TypeVar 7,TypeVar 8]),
              TypeApp (1,[TypeApp (1,[TypeVar 7,
	      TypeVar 9]),TypeApp (1,[TypeApp
	      (1,[TypeVar 8,TypeVar 9]),TypeVar 9])])])),
	    (",",2,Cons (",",2,1,2,Abs ("u1",Abs ("u2",
	      Abs ("v1",App (App (BoundVar 0,
              BoundVar 2),BoundVar 1)))),Abs
				("u1",Abs ("u2",
	      Abs ("v1",App (App (BoundVar 0,
              BoundVar 2),BoundVar 1)))),[]),
             TypeApp (1,[TypeVar 3,TypeApp (1,
	     [TypeVar 4,TypeApp (2,[TypeVar 3,
						  TypeVar 4])])])),
	    ("split",1,Iter ("split",2,1),TypeApp (1,
             [TypeApp (2,[TypeVar 3,TypeVar 4]),
              TypeApp (1,[TypeApp (1,[TypeVar 3,
	      TypeApp (1,[TypeVar 4,TypeVar 5])]),
              TypeVar 5])])),
	    ("splitrec",19,Rec ("splitrec",2,1),TypeApp (1,
             [TypeApp (2,[TypeVar 3,TypeVar 4]),
              TypeApp (1,[TypeApp (1,[TypeVar 3,
	      TypeApp (1,[TypeVar 4,TypeVar 5])]),
              TypeVar 5])]))] end
	       in
		 (envList,typeList)
	       end

  fun maxTermVarEnv (((_,n,_,_)::_),_) = n
    | maxTermVarEnv  _                 = 0

  fun maxTypeVarEnv (tenv,tp) =
   Int.max(List.foldl (fn ((_,_,_,typ),n) => Int.max(AbsSyn.maxTypeVar typ,n))
	              0 tenv,
           List.foldl (fn ((_,num),n) => Int.max(num,n)) 0 tp)

  fun addTermToEnv (env as (tenv,tp)) (name,term,typ) =
    ((name,
      1+Int.max (maxTermVarEnv env,AbsSyn.maxTermVar term),term,typ)::tenv,
     tp)

  fun addTermToEnvWithNumber (env as (tenv,tp)) (name,term,typ) =
    let
      val n =  1+Int.max (maxTermVarEnv env,AbsSyn.maxTermVar term)
    in
      (((name,n,term,typ)::tenv,tp),n)
    end

  fun addTypeToEnv (env as (tenv,tp)) name = (tenv,
					      (name,1+maxTypeVarEnv env)::tp)

  fun getTermFromNumber (env,_) n = (fn (SOME (_,_,term,typ)) => (term,typ)
                                      | NONE => raise NotFoundInEnv)
                                    (List.find (fn (_,i,_,_) => i=n) env)

  fun getTermFromName (env,_) s = (fn (SOME (_,i,term,typ)) => (i,term,typ)
			            | NONE => raise NotFoundInEnv)
                                  (List.find (fn (n,_,_,_) => s=n) env)

  fun getTermFromLib (env,_) s = (fn (SOME (_,i,term,typ)) => (i,term,typ)
			            | NONE => raise NotFoundInEnv)
                                  (List.find (fn (n,_,_,_) => s=n) (rev env))

  fun getTermNameFromNumber (env,_) n =
    let
      val name = (fn (SOME (s,_,_,_)) => s | NONE => raise NotFoundInEnv)
                 (List.find (fn (_,i,_,_) => i=n) env)
      val prevId = (fn (SOME (_,id,_,_)) => id | NONE => n)
                   (List.find (fn (nam,_,_,_) => nam=name) env)
    in
      if prevId > n then name^"[hidden]" else name
    end

  fun appFunToEnv (env,tp) f = (map f env,tp)

  fun getTypeFromName (_,tp) s = (fn (SOME (_,i)) => i
			            | NONE => raise NotFoundInEnv)
                                  (List.find (fn (n,_) => s=n) tp)
  fun getTypeFromLib (_,tp) s = (fn (SOME (_,i)) => i
			            | NONE => raise NotFoundInEnv)
                                  (List.find (fn (n,_) => s=n) (rev tp))
  fun getTypeNameFromNumber (_,env) n =
    let
      val name = (fn (SOME (s,_)) => s | NONE => raise NotFoundInEnv)
                 (List.find (fn (_,i) => i=n) env)
      val prevId = (fn (SOME (_,id)) => id | NONE => n)
                   (List.find (fn (nam,_) => nam=name) env)
    in
      if prevId > n then name^"[hidden]" else name
    end

  fun uniq (h::t) = h::(List.filter (fn x => x<>h) (uniq t))
    | uniq nil    = nil

  fun getTypeList (_,tenv) = uniq (List.mapPartial
				   (fn (a,_) => if String.sub(a,0)= #"'"
						    then NONE
						else SOME a) tenv)

  fun getTypeDef (e as (env,tenv)) s =
    let
      val typeNumber = getTypeFromName e s
      val iter =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Iter (_,n,_),_) => n=typeNumber
		     |  _                          => false) env)
      val recc =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Rec (_,n,_),_) => n=typeNumber
		     |  _                          => false) env)
      val numCons = (fn (AbsSyn.Iter (_,_,n),_) => n | _ => 0) iter
      val getCons = fn consnum =>
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Cons (_,tn,cn,_,_,_,_),_) =>
		        tn=typeNumber andalso cn=consnum
		     |  _                          => false) env)
    in
	(iter,recc,map getCons (List.tabulate (numCons,fn x =>x+1)))
    end

  fun getTypeDefFromNumber (e as (env,tenv)) typeNumber =
    let
      val iter =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Iter (_,n,_),_) => n=typeNumber
		     |  _                          => false) env)
      val recc =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Rec (_,n,_),_) => n=typeNumber
		     |  _                          => false) env)
      val numCons = (fn (AbsSyn.Iter (_,_,n),_) => n | _ => 0) iter
      val getCons = fn consnum =>
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Cons (_,tn,cn,_,_,_,_),_) =>
		        tn=typeNumber andalso cn=consnum
		     |  _                          => false) env)
    in
	(iter,recc,map getCons (List.tabulate (numCons,fn x =>x+1)))
    end

  fun getCoTypeDef (e as (env,tenv)) s =
    let
      val typeNumber = getTypeFromName e s
      val coiter =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Coit (_,n,_,_),_) => n=typeNumber
		     |  _                          => false) env)
      val corec =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Corec (_,n,_,_),_) => n=typeNumber
		     |  _                          => false) env)
      val numDes = (fn (AbsSyn.Coit (_,_,n,_),_) => n | _ => 0) coiter
      val getDes = fn desnum =>
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Des (_,tn,cn,_,_),_) =>
		        tn=typeNumber andalso cn=desnum
		     |  _                          => false) env)
    in
	(coiter,corec,map getDes (List.tabulate (numDes,fn x =>x+1)))
    end

  fun getCoTypeDefFromNumber (e as (env,tenv)) typeNumber =
    let
      val coiter =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Coit (_,n,_,_),_) => n=typeNumber
		     |  _                          => false) env)
      val corec =
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Corec (_,n,_,_),_) => n=typeNumber
		     |  _                          => false) env)
      val numDes = (fn (AbsSyn.Coit (_,_,n,_),_) => n | _ => 0) coiter
      val getDes = fn desnum =>
	(fn (SOME (_,_,t,tt)) => (t,tt) | NONE => raise NotFoundInEnv)
	(List.find (fn (_,_,AbsSyn.Des (_,tn,cn,_,_),_) =>
		        tn=typeNumber andalso cn=desnum
		     |  _                          => false) env)
    in
	(coiter,corec,map getDes (List.tabulate (numDes,fn x =>x+1)))
    end

  fun Gc l ((w as (s,_,term,_))::tl,t) =
      if List.find (fn a => a = s) l = NONE
	  then Gc l (w::tl,t)
      else Gc l (tl,t)
    | Gc _ (nil ,t) = (nil,t)

  fun GarbageCollector env = Gc [] env
end

structure etEnvironment = etEnvironmentFun
                            (structure AbsSyn = etAbstractSyntax)
