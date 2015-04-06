
(*********************************************************************)
(*                                                                   *)
(*         TYLAM.SML  - THE DEFINITION OF TYPED LAMBDA TERMS         *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports: none                                                     *)
(* Exports: datatype term and typex and tyvar and constr and tycon   *)
(*                                                                   *)
(*********************************************************************)

datatype term   = Parameter   of int                |
                  Constructor of constr             |
                  Iterator    of tycon ref          |
                  Recursor    of tycon ref          |
                  Lambda      of term               |
                  Application of term * term        |
                  True                              |
                  False                             |
                  Conditional of term * term * term |
                  Equality    of term * term        |
                  Pair        of term * term        |
                  Fst                               |
                  Snd                               |
                  Inl                               |
                  Inr                               |
                  Unit                              |
                  When                              |
                  Case0                             |
                  Case1

     and typex  = Tyvar       of tyvar ref              |
                  Tycon       of tycon ref * typex list |
                  Tyfun       of typex * typex          |
                  Tybool                                |
                  Typair      of typex * typex          |
                  Tyun        of typex * typex          |
                  Absurd                                |
                  Tyunit

     and tyvar  = None                 |
                  Some        of typex |
                  Label       of int

     and constr = Constr      of { name    : string,
                                   coty    : bool,
                                   ty      : typex,
                                   trai    : term,
                                   trar    : term
                                 } ref

     and tycon  = Type        of { name    : string,
                                   induc   : bool,
                                   coty    : bool,
                                   varlist : tyvar ref list,
                                   typiter : typex,
                                   typrec  : typex,
                                   conlist : constr list
                                 } |
                  Marker;

(* end of TYLAM.SML **************************************************)

