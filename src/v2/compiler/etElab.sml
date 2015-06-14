signature etELAB =
sig
  structure AbsSyn     : etABSTRACTSYNTAX
  structure FromParser : etFROMPARSER
  structure Env        : etENVIRONMENT
  structure Unifier    : etUNIFIER

  exception ElabError of string * FromParser.LRPos
  val W : Env.Env -> FromParser.etTerm
    -> Unifier.Substitution * AbsSyn.etTerm * AbsSyn.etType
end

functor etElabFun (structure AbsSyn     : etABSTRACTSYNTAX
		   structure FromParser : etFROMPARSER
		   structure Env        : etENVIRONMENT
		   structure Unifier    : etUNIFIER
		     sharing AbsSyn = Unifier.AbsSyn
		     sharing AbsSyn = Env.AbsSyn
		     sharing Env = Unifier.Env) : etELAB =
struct

structure AbsSyn     = AbsSyn
structure FromParser = FromParser
structure Env        = Env
structure Unifier    = Unifier

exception ElabError of string * FromParser.LRPos

type boundEnv = (string * bool) list

val emptyBEnv = nil

fun addToBEnv benv s = (s,false) ::benv

fun addToBEnvLet benv s = (s,true) ::benv

fun getLevelBEnv benv s = List.foldr (fn ((a,_),b) => if a=s then 0
                                                  else if b> ~1 then b+1
                                                       else ~1) ~1 benv
fun isFromLet benv s =
  if not ((SOME (s,false)) = List.find (fn (a,_) => a=s) benv)
    then true else false

fun dropBEnv (h::tl) = tl
  | dropBEnv  nil    = nil

type localTypeEnv = AbsSyn.TypeNumberId list

val emptyTLEnv = nil

fun addToTLEnv (AbsSyn.TypeVar i) tlenv = i::tlenv
  | addToTLEnv  _                 tlenv = tlenv

fun addListToTLEnv l tlenv =
      (List.mapPartial (fn (AbsSyn.TypeVar i) => SOME i
                         |  _                 => NONE  ) l) @ tlenv

fun isInTLEnv (AbsSyn.TypeVar i) tlenv = List.exists (fn j => i=j) tlenv
  | isInTLEnv  _                 _     = false

val izero = IntInf.fromInt 0;
val ijeden = IntInf.fromInt 1;

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

local
  fun w (env,benv,tlenv,FromParser.Ident (name,pos),m) =
    let
      val (id,_,typ)= Env.getTermFromName env name
                      handle Env.NotFoundInEnv => raise
                       ElabError ("unbound identifier: "^name,pos)
      val toretype = if not (isFromLet benv name) then []
                     else List.filter (fn t => not (isInTLEnv t tlenv))
                                 (AbsSyn.allTypeVarIn typ)
      val lentoretype = length toretype
      val sub = Unifier.addLtoS  Unifier.SId
                  (ListPair.zip
                   (toretype,List.tabulate (lentoretype,
                                            fn x => AbsSyn.TypeVar (x+m+1))))
      val boundLevel = getLevelBEnv benv name
      val newTerm = if boundLevel = ~1 then AbsSyn.Var id
                    else AbsSyn.BoundVar boundLevel
    in
      (Unifier.SId,newTerm,Unifier.appS sub typ,m+lentoretype)
    end
  | w (env,benv,tlenv,FromParser.App ((e1,e2),pos),m) =
    let
      val (s1,term1,type1,m1)=w(env,benv,tlenv,e1,m)
      val (s2,term2,type2,m2)=w(Unifier.appStoEnv s1 env,benv,tlenv,e2,m1)
      val s3=Unifier.unify [(Unifier.appS (Unifier.addStoS s2 s1) type1,
                             AbsSyn.TypeApp (Env.getTypeFromName env "->",
                                             [type2,AbsSyn.TypeVar (m2+1)]))]
             handle Unifier.Fail => raise
                      ElabError ("type error",pos)
                  | Env.NotFoundInEnv => raise
                      ElabError ("type \"->\" is undefined",pos)
      val sub = Unifier.addStoS (Unifier.addStoS s1 s2) s3
    in
      (sub,
       AbsSyn.App (term1,term2),
       Unifier.appS sub (AbsSyn.TypeVar (m2+1)),m2+1)
    end
  | w (env,benv,tlenv,FromParser.Fn ((s::tl,e),pos),m) =
    let
      val (name,_) = s
      val (sub,term,typ,m1)=
        w (Env.addTermToEnv env
           (name,AbsSyn.Var (1+Env.maxTermVarEnv env),AbsSyn.TypeVar(m+1)),
           addToBEnv benv name,addToTLEnv (AbsSyn.TypeVar(m+1)) tlenv,
           FromParser.Fn ((tl,e),pos),m+1)
    in
      (sub,AbsSyn.Abs (name,term),
       Unifier.appS sub (AbsSyn.TypeApp (Env.getTypeFromName env "->",
                                         [AbsSyn.TypeVar (m+1),typ])),m1)
    end
  | w (env,benv,tlenv,FromParser.Fn ((nil,e),pos),m) = w(env,benv,tlenv,e,m)
  | w (env,benv,tlenv,FromParser.Let
         (((FromParser.Val (((lname,_),lterm),_))::l,e),pos),m) =
    let
      val (s1,term1,type1,m1)=w(env,benv,tlenv,lterm,m)
(*      val varInType1 = AbsSyn.allTypeVarIn type1
      val varInLet = List.mapPartial
            (fn t => if isInTLEnv t tlenv
                       then SOME t else NONE) varInType1
      val varLSub = Unifier.addLtoS Unifier.SId
          (map (fn (AbsSyn.TypeVar i) =>
                (print (Int.toString i);(AbsSyn.TypeVar i,AbsSyn.TypeVar (~i)))
                 |  t                 =>  (t,t)) varInLet)*)
      val (s2,term2,type2,m2) =
          w(Unifier.appStoEnv s1 (Env.addTermToEnv env
             (lname,term1,type1)),
             addToBEnvLet benv lname,tlenv,
             FromParser.Let  ((l,e),pos),m1)
    in
      (Unifier.addStoS s1 s2,AbsSyn.App (AbsSyn.Abs (lname,term2),term1),
       type2,m2)
    end
  | w (env,benv,tlenv,FromParser.Let ((nil,e),pos),m) =
      w(env,benv,tlenv,e,m)
  | w (env,benv,tlenv,FromParser.Number (n,pos),m) =
      (Unifier.SId,mkNumber n,AbsSyn.TypeApp (40,[]),m)
in
  fun W env e =
    let
      val (s,term,typ,_)=w(env,emptyBEnv,emptyTLEnv,e,Env.maxTypeVarEnv env)
    in
      (s,term,typ)
    end
end

end

structure etElab =etElabFun (structure AbsSyn     = etAbstractSyntax
                             structure FromParser = etFromParser
                             structure Env        = etEnvironment
                             structure Unifier    = etUnifier)
