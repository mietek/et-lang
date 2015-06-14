signature etUNIFIER =
sig
  structure AbsSyn : etABSTRACTSYNTAX

  structure Env : etENVIRONMENT

  datatype DisPair =
    DPair of AbsSyn.etType * AbsSyn.etType | Pi

  type Substitution

  exception Fail

  val SId       : Substitution
  val addS      : Substitution -> AbsSyn.etType * AbsSyn.etType -> Substitution
  val addLtoS   : Substitution ->
                    (AbsSyn.etType * AbsSyn.etType) list -> Substitution
  val addStoS   : Substitution -> Substitution -> Substitution
  val appS      : Substitution -> AbsSyn.etType -> AbsSyn.etType
  val appStoEnv : Substitution -> Env.Env -> Env.Env

  val unify     : (AbsSyn.etType * AbsSyn.etType) list -> Substitution
end

functor etUnifierFun (structure AbsSyn : etABSTRACTSYNTAX
                      structure Env : etENVIRONMENT
                        sharing AbsSyn = Env.AbsSyn):etUNIFIER =
struct

structure AbsSyn = AbsSyn

structure Env = Env

datatype DisPair  = Pi | DPair of AbsSyn.etType * AbsSyn.etType

type Substitution = (AbsSyn.etType * AbsSyn.etType) list

val SId = nil

local
  fun app ((v,e)::tl) t = if t=v then e else app tl t
    | app  nil        t = t
in
  fun appS sub (tv as AbsSyn.TypeVar i) = app sub tv
    | appS sub (AbsSyn.TypeApp (i,lt))  = AbsSyn.TypeApp (i,map (appS sub) lt)
end

fun addS    sub (p as (v,e)) = let
                                 val s = map (fn (a,b) => (a,appS [p] b)) sub
                               in
                                 (v,appS s e)::s
                               end
fun addLtoS sub l = List.foldr (fn (a,b) => addS b a) sub l
fun addStoS sub l = List.foldr (fn (a,b) => addS b a) sub l

exception Fail;

local
  fun D (z as (AbsSyn.TypeVar i1,AbsSyn.TypeVar i2)) =
        if i1=i2 then Pi else DPair z
    | D (z as (AbsSyn.TypeApp (i1,lt1),AbsSyn.TypeApp (i2,lt2))) =
        if (i1=i2) andalso (length lt1 = length lt2) then
          D' (ListPair.zip (lt1,lt2))
        else DPair z
    | D p                                                 = DPair p
  and D' [t as (t1,t2)]          = D t
    | D' ((t as (t1,t2))::tail)  = let val d = (D t)
                                   in
                                     if d = Pi then D'(tail) else d
                                   end
    | D' []                      = Pi

  fun U S (l as ((e,e')::t)) =
    let
      val se  = appS S e
      val se' = appS S e'
    in
      if se = se' then U S t
      else let
             val (u,v)=(fn DPair a => a
                        | Pi => raise etTools.InternalError "Error in unifier")
                       (D (se,se'))
           in
             if AbsSyn.notTypeVarIn u v then  U (addS S (u,v)) l
             else
               if AbsSyn.notTypeVarIn v u then U (addS S (v,u)) l
               else raise Fail
           end
    end
    | U S nil                 = S
in
  fun unify el =U SId el
end

fun appStoEnv subs env  = Env.appFunToEnv env
                           (fn (a,b,c,t) => (a,b,c,appS subs t))
end

structure etUnifier = etUnifierFun (structure AbsSyn = etAbstractSyntax
                                    structure Env = etEnvironment)
