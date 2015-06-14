signature etABSTRACTSYNTAX =
sig
  type TypeNumberId = int
  type TermNumberId = int

  datatype etType =
    TypeVar of TypeNumberId
  | TypeApp of TypeNumberId * etType list

  datatype etTerm =
    Var of TermNumberId
  | BoundVar of int
  | App of etTerm * etTerm
  | Abs of string * etTerm
  | Cons of string * TypeNumberId * int * int * etTerm * etTerm * (etTerm list)
  | Iter of string * TypeNumberId * int
  | Rec  of string * TypeNumberId * int
  | Des  of string * TypeNumberId * int * etTerm * etTerm
  | Coit of string * TypeNumberId * int * (etTerm list)
  | Corec of string * TypeNumberId * int * (etTerm list)

val maxTypeVar  : etType -> int
val maxTypeVarL : etType list -> int
val maxTermVar  : etTerm -> int
val maxTermVarL : etTerm list -> int

val allTypeVarIn  : etType -> etType list
val notTypeVarIn  : etType -> etType -> bool
val notTypeVarInL : etType -> etType list -> bool
end

structure etAbstractSyntax : etABSTRACTSYNTAX =
struct
  type TypeNumberId = int
  type TermNumberId = int

  datatype etType =
    TypeVar of TypeNumberId
  | TypeApp of TypeNumberId * etType list

  datatype etTerm =
    Var of TermNumberId
  | BoundVar of int
  | App of etTerm * etTerm
  | Abs of string * etTerm
  | Cons of string * TypeNumberId * int * int * etTerm * etTerm * (etTerm list)
  | Iter of string * TypeNumberId * int
  | Rec  of string * TypeNumberId * int
  | Des  of string * TypeNumberId * int * etTerm * etTerm
  | Coit of string * TypeNumberId * int * (etTerm list)
  | Corec of string * TypeNumberId * int * (etTerm list)

fun maxTypeVar (TypeVar i)      = i
  | maxTypeVar (TypeApp (i,lt)) = Int.max (i,maxTypeVarL lt)
and maxTypeVarL tl = foldl (fn (a,b) => Int.max (maxTypeVar a,b)) 0 tl

fun maxTermVar (Var i)       = i
  | maxTermVar (BoundVar i)  = 0
  | maxTermVar (App (t1,t2)) = Int.max (maxTermVar t1,maxTermVar t2)
  | maxTermVar (Abs (_,t))   = maxTermVar t
  | maxTermVar (Cons (_,_,_,_,t1,t2,tl)) = maxTermVarL (tl@[t1,t2])
  | maxTermVar (Iter _)      = 0
  | maxTermVar (Rec _)      = 0
  | maxTermVar (Des (_,_,_,t1,t2)) = maxTermVarL ([t1,t2])
  | maxTermVar (Coit (_,_,_,tl))   = maxTermVarL tl
  | maxTermVar (Corec (_,_,_,tl))   = maxTermVarL tl
and maxTermVarL tl = foldl (fn (a,b) => Int.max (maxTermVar a,b)) 0 tl

local
  fun alltv (t as (TypeVar _)) = [t]
    | alltv (TypeApp (_,lt))   = List.concat (map alltv lt)

  fun uniq (h::t) = h::(List.filter (fn x => x<>h) t)
    | uniq nil    = nil
in
  fun allTypeVarIn t = uniq (alltv t)
end

fun notTypeVarIn (TypeVar i)        (TypeVar j)     = i<>j
  | notTypeVarIn (tv1 as TypeVar _) (TypeApp (_,tl))=
      notTypeVarInL tv1 tl
  | notTypeVarIn  _                  _              = false
and notTypeVarInL (tv1 as TypeVar _) tl =
      List.all (fn x => notTypeVarIn tv1 x) tl
  | notTypeVarInL  _                 _  = false
end
