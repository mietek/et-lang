signature etPRETTYPRINT =
sig
  structure AbsSyn : etABSTRACTSYNTAX
  structure Env : etENVIRONMENT
  structure Eval : etEVAL

  val typeToString : Env.Env -> AbsSyn.etType -> int -> string
  val termToString : Env.Env -> AbsSyn.etTerm -> int -> string
  val termWithTypeToString : Env.Env -> (AbsSyn.etTerm * AbsSyn.etType)
                             -> int -> string
  val valToString  : Env.Env -> (string * AbsSyn.etTerm * AbsSyn.etType)
                             -> int -> string
  val valNoTermToString  : Env.Env -> (string * AbsSyn.etTerm * AbsSyn.etType)
                             -> int -> string
  val dataToString  : Env.Env -> 
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list)) -> int -> string

  val codataToString  : Env.Env -> 
    ((AbsSyn.etTerm * AbsSyn.etType)*(AbsSyn.etTerm * AbsSyn.etType)*
     ((AbsSyn.etTerm * AbsSyn.etType) list)) -> int -> string
end

functor etPrettyPrintFun (structure AbsSyn : etABSTRACTSYNTAX
                          structure Env  : etENVIRONMENT
                          structure Eval : etEVAL
                          structure PrettyPrint : PRETTYPRINT
                            sharing AbsSyn = Env.AbsSyn
                            sharing AbsSyn = Eval.AbsSyn
                            sharing Env    = Eval.Env) : etPRETTYPRINT =
struct

structure AbsSyn = AbsSyn
structure Env    = Env
structure Eval   = Eval

type ppstream = PrettyPrint.ppstream

fun joinAbs l (AbsSyn.Abs (s,t)) = joinAbs (l@[s]) t
  | joinAbs l  t                 = (l,t)

fun joinApp (AbsSyn.App (t1,t2)) = (joinApp t1)@[t2]
  | joinApp t                    = [t]

fun getNewName env bound num = 
  let
    val  newName ="'" ^ (str (chr (97+ num)))
  in
   (Env.getTypeFromName env newName;
    getNewName env bound (num+1))
   handle Env.NotFoundInEnv =>
    (case  (List.find (fn (_,n) => n=newName) bound)
       of NONE   => newName
       |  SOME _ => getNewName env bound (num+1))
  end

fun getTypeName env bound i = (Env.getTypeNameFromNumber env i,bound)
                              handle Env.NotFoundInEnv =>
                                case (List.find (fn (n,_) => n=i) bound)
                                  of NONE => 
                                    let
                                      val newName = getNewName env bound 0
                                    in
                                        (newName,(i,newName)::bound)
                                    end
                                  | SOME (_,name) => (name,bound)
                                  
fun pType env bound pps (AbsSyn.TypeVar i) =
  let
    val (typeName,bound) = getTypeName env bound i
  in
    PrettyPrint.add_string pps typeName;
    bound
  end
  | pType env bound pps (AbsSyn.TypeApp (i,typelist)) =
  let
    val ifTypeApp =  (fn (AbsSyn.TypeApp (_,h::tl)) => true | _ => false) 
    val (typeName,bound) = getTypeName env bound i
  in
    if Char.isAlpha(String.sub(typeName,0)) then
     (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
      PrettyPrint.add_string pps typeName;
      let
        val bound = List.foldl (fn (s,boundd) => 
               (PrettyPrint.add_break pps (1,0);
                if (ifTypeApp s) then PrettyPrint.add_string pps "(" else ();
                let val boundd = pType env boundd pps s in
                if (ifTypeApp s) then PrettyPrint.add_string pps ")" else ();
                boundd
                end))
                bound typelist;
      in
        PrettyPrint.end_block pps;
        bound
      end)
    else
        (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
        let
         val bound = if length typelist >=1 then
            let
              val firstType = List.nth (typelist,0)
              val _ = if (ifTypeApp firstType) then 
                PrettyPrint.add_string pps "(" else ()
              val bound = pType env bound pps firstType
              val _ = if (ifTypeApp firstType) then 
                    PrettyPrint.add_string pps ")" else ()
              val _ = PrettyPrint.add_break pps (1,0)
            in
              bound
            end
          else bound
          val _ = PrettyPrint.add_string pps typeName
          val bound = 
            if length typelist >=1 then
              let
                val allButFirstTypes = List.drop(typelist,1)
                val ifArrows = typeName = "->" 
                               andalso ((fn (AbsSyn.TypeApp (j,_)::_) => i=j
                                         | _ => false) allButFirstTypes)
                val bound = List.foldl (fn (s,boundd) => 
                (PrettyPrint.add_break pps (1,0);
                if (ifTypeApp s) andalso (not ifArrows)
                  then PrettyPrint.add_string pps "(" else ();
                let val boundd = pType env boundd pps s in
                if (ifTypeApp s) andalso (not ifArrows)
                  then PrettyPrint.add_string pps ")" else ();
                boundd
                end))
                bound allButFirstTypes
              in
                bound
              end
          else bound
        in
          PrettyPrint.end_block pps;
          bound
        end)
  end

fun pTerm env bound pps (AbsSyn.Var i) = 
    let
	val name =  (Env.getTermNameFromNumber env i)
	val s = if List.exists (fn a => a=name) bound 
		    then name^"[env]" else name
    in
      PrettyPrint.add_string pps s
    end
  | pTerm env bound pps (AbsSyn.BoundVar i) = 
    let
	val name = List.nth (bound,i)
	val noflam = (List.length (List.filter (fn a => a=name)
				   (List.take (bound,i))));
	val s = if noflam>0 then name^"["^(Int.toString noflam)^"]"  else name
    in
      PrettyPrint.add_string pps s
    end
  | pTerm env bound pps (t as AbsSyn.App (t1,t2)) =
      let
          val ifCons = (fn (AbsSyn.Cons _) => true
                         | _ => false)
          val tlist = joinApp t1
          val ifApp =  (fn (AbsSyn.App _) => true
                         | (AbsSyn.Cons (_,_,_,_,_,_,h::tl)) => true
                         | (AbsSyn.Coit (_,_,_,h::tl)) => true
                         | (AbsSyn.Corec (_,_,_,h::tl)) => true
                         | _ => false) 
          val ifAbsOrApp =  (fn (AbsSyn.App _) => true 
                              | (AbsSyn.Abs _) => true 
                              | (AbsSyn.Cons (_,_,_,_,_,_,h::tl)) => true
                              | (AbsSyn.Coit (_,_,_,h::tl)) => true
                              | (AbsSyn.Corec (_,_,_,h::tl)) => true
                              |  _             => false)
      in
        if (length tlist>1) andalso (ifCons ((fn (AbsSyn.Var i) => 
                              (fn (a,b) => a) (Env.getTermFromNumber env i)
                               | a => a) (hd tlist) ))
          then pTerm env bound pps (Eval.toHeadNormalForm env t)
        else
          (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
          List.foldl (fn (s,_) => 
             (if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
              pTerm env bound pps s;
              if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ();
              PrettyPrint.add_break pps (1,0)))
             () tlist;
          if (ifApp t2) then PrettyPrint.add_string pps "(" else ();
          pTerm env bound pps t2;
          if (ifApp t2) then PrettyPrint.add_string pps ")" else ();
          PrettyPrint.end_block pps)
      end
  | pTerm env bound pps (AbsSyn.Abs (s,t)) =
       let
           val (strarg,t) = joinAbs [s] t
       in
          PrettyPrint.begin_block pps PrettyPrint.CONSISTENT 2;
          PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 1;
          PrettyPrint.add_string pps "fn";
          List.foldl (fn (s,_) => (PrettyPrint.add_break pps (1,0);
                                   PrettyPrint.add_string pps s))
                     () strarg;
          PrettyPrint.end_block pps;
          PrettyPrint.add_break pps (1,0);
          PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
          PrettyPrint.add_string pps "=>";
          PrettyPrint.add_break pps (1,1);
          pTerm env ((rev strarg)@bound) pps t;
          PrettyPrint.end_block pps;
          PrettyPrint.end_block pps
       end
  | pTerm env bound pps (t as AbsSyn.Cons ("Suc",40,1,1,_,_,tl)) = 
      let
          val ifAbsOrApp =  (fn (AbsSyn.App _) => true 
                              | (AbsSyn.Abs _) => true 
                              | (AbsSyn.Cons _) => true
                              | (AbsSyn.Iter _) => true
                              | (AbsSyn.Des _) => true
                              | (AbsSyn.Coit _) => true
                              | (AbsSyn.Corec _) => true
                              |  _             => false)
          val izero  = IntInf.fromInt 0;
          val ijeden = IntInf.fromInt 1;
          fun ifOnlyNat (AbsSyn.Cons ("Suc",40,1,_,_,_,[tl])) = 
                         (fn (a,b) => (a,IntInf.+ (b,ijeden))) (ifOnlyNat tl)
            | ifOnlyNat (AbsSyn.Cons ("0",40,2,_,_,_,[])) = 
                         (true,izero) 
            | ifOnlyNat _ = (false,izero) 
          val (ifNum,BigNum) = ifOnlyNat t 
      in
        if ifNum then
          PrettyPrint.add_string pps (IntInf.toString BigNum)
        else(
        PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
        PrettyPrint.add_string pps "Suc";
        List.foldl (fn (s,_) => 
          (PrettyPrint.add_break pps (1,0);
           if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
             pTerm env bound pps s;
             if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ()))
        () tl;
        PrettyPrint.end_block pps)
      end
  | pTerm env bound pps (t as AbsSyn.Cons (s,_,_,_,_,_,tl)) = 
      let
          val ifAbsOrApp =  (fn (AbsSyn.App _) => true 
                              | (AbsSyn.Abs _) => true 
                              | (AbsSyn.Cons (_,_,_,_,_,_,h::tl)) => true
                              | (AbsSyn.Coit (_,_,_,h::tl)) => true
                              | (AbsSyn.Corec (_,_,_,h::tl)) => true
                              |  _             => false)
      in
        PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
        if Char.isAlpha(String.sub(s,0)) orelse (length tl <2) then
        (PrettyPrint.add_string pps s;
        List.foldl (fn (s,_) => 
          (PrettyPrint.add_break pps (1,0);
           if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
             pTerm env bound pps s;
             if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ()))
        () tl)
        else
        (pTerm env bound pps (hd tl);
         PrettyPrint.add_break pps (1,0);
         PrettyPrint.add_string pps s;
         List.foldl (fn (s,_) => 
          (PrettyPrint.add_break pps (1,0);
           if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
             pTerm env bound pps s;
             if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ()))
         () (List.drop (tl,1)));
        PrettyPrint.end_block pps
      end
  | pTerm env bound pps (AbsSyn.Iter (s,_,_)) = PrettyPrint.add_string pps s
  | pTerm env bound pps (AbsSyn.Rec  (s,_,_)) = PrettyPrint.add_string pps s
  | pTerm env bound pps (AbsSyn.Des  (s,_,_,_,_)) = 
      PrettyPrint.add_string pps s
  | pTerm env bound pps (t as AbsSyn.Coit (s,_,_,tl)) = 
      let
          val ifAbsOrApp =  (fn (AbsSyn.App _) => true 
                              | (AbsSyn.Abs _) => true 
                              | (AbsSyn.Cons (_,_,_,_,_,_,h::tl)) => true
                              | (AbsSyn.Coit (_,_,_,h::tl)) => true
                              | (AbsSyn.Corec (_,_,_,h::tl)) => true
                              |  _             => false)
      in
        PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
        PrettyPrint.add_string pps s;
        List.foldl (fn (s,_) => 
          (PrettyPrint.add_break pps (1,0);
           if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
             pTerm env bound pps s;
             if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ()))
        () tl;
        PrettyPrint.end_block pps
      end
  | pTerm env bound pps (t as AbsSyn.Corec (s,_,_,tl)) = 
      let
          val ifAbsOrApp =  (fn (AbsSyn.App _) => true 
                              | (AbsSyn.Abs _) => true 
                              | (AbsSyn.Cons (_,_,_,_,_,_,h::tl)) => true
                              | (AbsSyn.Coit (_,_,_,h::tl)) => true
                              | (AbsSyn.Corec (_,_,_,h::tl)) => true
                              |  _             => false)
      in
        PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 2;
        PrettyPrint.add_string pps s;
        List.foldl (fn (s,_) => 
          (PrettyPrint.add_break pps (1,0);
           if (ifAbsOrApp s) then PrettyPrint.add_string pps "(" else ();
             pTerm env bound pps s;
             if (ifAbsOrApp s) then PrettyPrint.add_string pps ")" else ()))
        () tl;
        PrettyPrint.end_block pps
      end

fun pTermWithType env pps (term,type_) =
      (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
       pTerm env [] pps term;
       PrettyPrint.add_break pps (1,0);
       PrettyPrint.add_string pps ":";
       PrettyPrint.add_break pps (1,0);
       pType env [] pps type_;
       PrettyPrint.end_block pps)

fun printType env pps type_ = (pType env [] pps type_;
                              PrettyPrint.flush_ppstream pps)

fun printTerm env pps term = (pTerm env [] pps term;
                              PrettyPrint.flush_ppstream pps)

fun printTermWithType env pps tt = (pTermWithType env pps tt;
                                    PrettyPrint.flush_ppstream pps)

fun printVal env pps (name,term,type_) =
      (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
       PrettyPrint.add_string pps "val";
       PrettyPrint.add_break pps (1,0);
       PrettyPrint.add_string pps name;
       PrettyPrint.add_break pps (1,0);
       PrettyPrint.add_string pps "=";
       PrettyPrint.add_break pps (1,2);
       pTermWithType env pps (term,type_);
       PrettyPrint.end_block pps;
       PrettyPrint.flush_ppstream pps)

fun printValNoTerm env pps (name,term,type_) =
      (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
       PrettyPrint.add_string pps "val";
       PrettyPrint.add_break pps (1,0);
       PrettyPrint.add_string pps name;
       PrettyPrint.add_break pps (1,0);
       PrettyPrint.add_string pps ":";
       PrettyPrint.add_break pps (1,2);
       pType env [] pps type_;
       PrettyPrint.end_block pps;
       PrettyPrint.flush_ppstream pps)

fun printData env pps (iter,recc,cl) =
    let
        val itName = (fn (AbsSyn.Iter (n,_,_),_) => n | _=>"") iter
        val rcName = (fn (AbsSyn.Rec (n,_,_),_) => n | _=>"") recc
        val typebound =
      (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
       foldl (fn ((AbsSyn.Cons (name,_,_,_,t1,t2,_),typ),tb) =>
              (let
                   val tb = 
               (PrettyPrint.add_string pps "con";
               PrettyPrint.add_break pps (1,0);
               PrettyPrint.add_string pps name;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps ":";
               PrettyPrint.add_break pps (1,2);
               pType env tb pps typ)
               in
               PrettyPrint.add_newline pps;tb
               end)
               | _ => []) [] cl)
      val typebound = (
       (fn (AbsSyn.Iter (name,_,_),typ) =>
          (let val tb =
           (PrettyPrint.add_string pps "iter";
           PrettyPrint.add_break pps (1,0);
           PrettyPrint.add_string pps name;
           PrettyPrint.add_break pps (1,2);
           PrettyPrint.add_string pps ":";
           PrettyPrint.add_break pps (1,2);
           pType env typebound pps typ)
           in
               PrettyPrint.add_newline pps;tb
           end)
           | _ => typebound) iter )
    in
      foldl (fn ((AbsSyn.Cons (name,a,b,narg,t,c,[]),typ),_) =>
              let
                val (arglist,listnames) = ListPair.unzip
                  (List.tabulate (narg,fn n => 
                                 (AbsSyn.BoundVar (n),
                                  "u"^(Int.toString (n+1)))))
                val ittocons = AbsSyn.App 
               ((fn (a,_) =>a) iter,AbsSyn.Cons (name,a,b,narg,t,c,arglist))
              in
               PrettyPrint.add_string pps "comp";
               PrettyPrint.add_break pps (1,0);
               pTerm env listnames pps ittocons;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps "=";
               PrettyPrint.add_break pps (1,2);
               pTerm env listnames pps (Eval.toNormalForm env ittocons);
               PrettyPrint.add_newline pps
              end
               | _ => ()) () cl;
      if List.all (fn (AbsSyn.Cons (_,_,_,_,t1,t2,_),_) => t1=t2
                       | _  => true) cl then 
          (PrettyPrint.add_string pps ("rec "^rcName^" = "^itName);
           PrettyPrint.add_newline pps)
      else(
       (fn (AbsSyn.Rec (name,_,_),typ) =>
          (PrettyPrint.add_string pps "rec ";
           PrettyPrint.add_break pps (1,0);
           PrettyPrint.add_string pps name;
           PrettyPrint.add_break pps (1,2);
           PrettyPrint.add_string pps ":";
           PrettyPrint.add_break pps (1,2);
           pType env typebound pps typ;
           PrettyPrint.add_newline pps)
           | _ => ()) recc;
       foldl (fn ((AbsSyn.Cons (name,a,b,narg,c,t,[]),typ),_) =>
              (let
                val (arglist,listnames) = ListPair.unzip
                  (List.tabulate (narg,fn n => 
                                 (AbsSyn.BoundVar (n),
                                  "u"^(Int.toString (n+1)))))
                val ittocons = AbsSyn.App 
               ((fn (a,_) =>a) recc,AbsSyn.Cons (name,a,b,narg,c,t,arglist))
              in
               PrettyPrint.add_string pps "comp";
               PrettyPrint.add_break pps (1,0);
               pTerm env listnames pps ittocons;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps "=";
               PrettyPrint.add_break pps (1,2);
               pTerm env listnames pps (Eval.toNormalForm env ittocons);
               PrettyPrint.add_newline pps
              end)
              | _ => ()) () cl);
       PrettyPrint.end_block pps;
       PrettyPrint.flush_ppstream pps
    end

fun printCoData env pps (coit,corec,dl) =
      (let val numDes = (fn (AbsSyn.Coit (_,_,n,_),_) =>n | _ => 0) coit;
           val mkCoit = fn l => (fn (AbsSyn.Coit (a,b,n,_),_) => 
                                  AbsSyn.Coit (a,b,n,l)
                                  | (AbsSyn.Corec (a,b,n,_),_) =>
                                  AbsSyn.Corec (a,b,n,l)
                                  | (c,_) => c);
           val coitName =  (fn (AbsSyn.Coit (a,_,_,_),_) => a | _ => "") coit
           val corcName =  (fn (AbsSyn.Corec (a,_,_,_),_) => a | _ => "") corec
	   val typebound =
       (PrettyPrint.begin_block pps PrettyPrint.INCONSISTENT 0;
       foldl (fn ((AbsSyn.Des (name,_,_,t1,t2),typ),tb) =>
	      let val tb =
              (PrettyPrint.add_string pps "des";
               PrettyPrint.add_break pps (1,0);
               PrettyPrint.add_string pps name;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps ":";
               PrettyPrint.add_break pps (1,2);
               pType env tb pps typ)
	      in
               PrettyPrint.add_newline pps;tb
	      end
               | _ => []) [] dl)
       val typebound = 
       (fn (AbsSyn.Coit (name,_,_,_),typ) =>
	  let val tb =
          (PrettyPrint.add_string pps "coiter";
           PrettyPrint.add_break pps (1,0);
           PrettyPrint.add_string pps name;
           PrettyPrint.add_break pps (1,2);
           PrettyPrint.add_string pps ":";
           PrettyPrint.add_break pps (1,2);
           pType env typebound pps typ)
	  in
           PrettyPrint.add_newline pps;tb
	   end
           | _ => typebound) coit;
       in
       foldl (fn ((d as AbsSyn.Des (name,a,b,t,c),typ),_) =>
              let
                val (arglist,listnames) = (ListPair.unzip
                  ((List.tabulate (numDes,fn n => 
                                 (AbsSyn.BoundVar (n),
                                  "v"^(Int.toString (n+1)))))@
                   [(AbsSyn.BoundVar numDes,"u")]))
                val destocoit = AbsSyn.App 
               (d,mkCoit arglist coit)
              in
               PrettyPrint.add_string pps "comp";
               PrettyPrint.add_break pps (1,0);
               pTerm env listnames pps destocoit;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps "=";
               PrettyPrint.add_break pps (1,2);
               pTerm env listnames pps (Eval.toNormalForm env destocoit);
               (*  (List.foldl (fn (a,b)=> AbsSyn.App (b,a)) t arglist));*)
               PrettyPrint.add_newline pps
              end
               | _ => ()) () dl;
      if List.all (fn (AbsSyn.Des (_,_,_,t1,t2),_) => t1=t2
                       | _  => true) dl then 
          (PrettyPrint.add_string pps ("corec "^corcName^" = "^coitName);
           PrettyPrint.add_newline pps)
      else(
       (fn (AbsSyn.Corec (name,_,_,_),typ) =>
          (PrettyPrint.add_string pps "corec";
           PrettyPrint.add_break pps (1,0);
           PrettyPrint.add_string pps name;
           PrettyPrint.add_break pps (1,2);
           PrettyPrint.add_string pps ":";
           PrettyPrint.add_break pps (1,2);
           pType env typebound pps typ;
           PrettyPrint.add_newline pps)
           | _ => ()) corec;
       foldl (fn ((d as AbsSyn.Des (name,a,b,t,c),typ),_) =>
              let
                val (arglist,listnames) = (ListPair.unzip
                  ((List.tabulate (numDes,fn n => 
                                 (AbsSyn.BoundVar (n),
                                  "v"^(Int.toString (n+1)))))@
                   [(AbsSyn.BoundVar numDes,"u")]))
                val destocoit = AbsSyn.App 
               (d,mkCoit arglist corec)
              in
               PrettyPrint.add_string pps "comp";
               PrettyPrint.add_break pps (1,0);
               pTerm env listnames pps destocoit;
               PrettyPrint.add_break pps (1,2);
               PrettyPrint.add_string pps "=";
               PrettyPrint.add_break pps (1,2);
               pTerm env listnames pps (Eval.toNormalForm env destocoit);
               PrettyPrint.add_newline pps
              end
               | _ => ()) () dl);
       PrettyPrint.end_block pps;
       PrettyPrint.flush_ppstream pps
       end)


fun ppToString i f arg = PrettyPrint.pp_to_string i f arg;

fun typeToString env type_ i = ppToString i (printType env) type_
fun termToString env term i  = ppToString i (printTerm env) term
fun termWithTypeToString env tt i = ppToString i (printTermWithType env) tt
fun valToString  env v i = ppToString i (printVal env) v
fun valNoTermToString  env v i = ppToString i (printValNoTerm env) v
fun dataToString  env d i = ppToString i (printData env) d
fun codataToString  env d i = ppToString i (printCoData env) d
end

structure etPrettyPrint = etPrettyPrintFun 
                         (structure AbsSyn = etAbstractSyntax
                          structure Env = etEnvironment
                          structure Eval = etEval
                          structure PrettyPrint =  Compiler.PrettyPrint)


