
(*********************************************************************)
(*                                                                   *)
(*             EVAL.SML  - THE EVALUATOR OF LAMBDA TERMS             *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from ARITHME.SML:                                              *)
(*       pred     = fn: int -> int                                   *)
(*       succ     = fn: int -> int                                   *)
(*    from LAMTERM.SML:                                              *)
(*       nest     = fn: int -> term -> term                          *)
(*       occvar   = fn: term -> bool                                 *)
(*       freevar  = fn: term -> bool                                 *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and constr and tycon                          *)
(* Exports:                                                          *)
(*       eval     = fn: term -> term                                 *)
(*                                                                   *)
(*********************************************************************)

local
   fun beta level (Parameter n) rand =
          if n = level
             then nest level rand
             else Parameter (if n > level then pred n else n)
     | beta level (Lambda rator) rand =
          Lambda (beta (succ level) rator rand)
     | beta level (Application (t1 , t2)) rand =
          Application (beta level t1 rand , beta level t2 rand)
     | beta level (Conditional (t1,t2,t3)) rand = Conditional
          (beta level t1 rand,beta level t2 rand,beta level t3 rand)
     | beta level (Equality (t1,t2)) rand =
          Equality (beta level t1 rand , beta level t2 rand)
     | beta level (Pair (t1,t2)) rand =
          Pair (beta level t1 rand , beta level t2 rand)
     | beta _ rator _ = rator;

   fun eta (0 , t as Application (t' , Parameter 0)) =
          if occvar t' then Lambda t else nest (~1) t'
     | eta (0 , t) = Lambda t;

   val cut = iter (fn x::xs => xs);

   datatype eliminator = It | Rec | Co of term * term;

   fun lazy _ (It::_) false (t as Constructor
          (Constr (ref {trai=tr,coty=false,...}))) = (1 , tr)
     | lazy _ (Rec::_) false (t as Constructor
          (Constr (ref {trar=tr,coty=false,...}))) = (1 , tr)
     | lazy _ (Co (ti,tr) ::_) false
         (t as Iterator (ref (Type {coty=true,...}))) = (1 , ti)
     | lazy _ (Co (ti,tr) ::_) false
         (t as Recursor (ref (Type {coty=true,...}))) = (1 , tr)
     | lazy _ (It::_) false Unit = (1 , Lambda (Parameter 0))
     | lazy _ (It::_) false Inl = (1 , Lambda (Lambda (Lambda
         (Application (Parameter 1 , Parameter 2)))))
     | lazy _ (It::_) false Inr = (1 , Lambda (Lambda (Lambda
         (Application (Parameter 0 , Parameter 2)))))
     | lazy false nil false (Lambda t) =
          (0 , eta (lazy false nil false t))
     | lazy false nil false (Pair (t1,t2)) =
          (0 ,  Pair (#2 (lazy false nil false t1),
                          #2 (lazy false nil false t2)))
     | lazy redex trans sel (Application (rator , rand)) =
          let
             val (trac , rator') = lazy true trans false rator;
          in
             case rator' of
                Lambda trm =>
                   let
                      val (trac' , trm) = lazy redex (cut trans trac)
                                               sel (beta 0 trm rand);
                   in
                      (trac + trac' , trm)
                   end |
                Iterator (ref (Type {coty=false,...})) =>
                   let
                      val (trac' , rand') =
                        lazy false (It::trans) sel rand;
                   in
                      if trac' > 0
                         then (trac + trac' - 1 , rand')
                         else (trac , Application (rator' , rand'))
                   end |
                Recursor (ref (Type {coty=false,...})) =>
                   let
                      val (trac' , rand') =
                        lazy false (Rec::trans) sel rand;
                   in
                      if trac' > 0
                         then (trac + trac' - 1 , rand')
                         else (trac , Application (rator' , rand'))
                   end |
                Constructor (Constr
                  (ref {trai=ti,trar=tr,coty=true,...})) =>
                   let
                      val (trac' , rand') =
                        lazy false (Co (ti,tr) :: trans) sel rand;
                   in
                      if trac' > 0
                         then (trac + trac' - 1 , rand')
                         else (trac , Application (rator' , rand'))
                   end |
                Case1 =>
                   let
                      val (trac' , rand') =
                        lazy false (It::trans) sel rand;
                   in
                      if trac' > 0
                         then (trac + trac' - 1 , rand')
                         else (trac , Application (rator' , rand'))
                   end |
                When =>
                   let
                      val (trac' , rand') =
                        lazy false (It::trans) sel rand;
                   in
                      if trac' > 0
                         then (trac + trac' - 1 , rand')
                         else (trac , Application (rator' , rand'))
                   end |
                Fst =>
                   let
                      val (0 , trm) = lazy false nil true rand;
                   in
                      case trm of
                         Pair (t , _) => lazy redex
                                   (cut trans trac) sel t |
                         _ => (trac , Application (Fst , trm))
                   end |
                Snd =>
                   let
                      val (0 , trm) = lazy false nil true rand;
                   in
                      case trm of
                         Pair (_ , t) => lazy redex
                                   (cut trans trac) sel t |
                         _ => (trac , Application (Snd , trm))
                   end |
                _ => (trac , Application
                        (rator', #2 (lazy false nil false rand)))
          end
     | lazy redex trans sel (Conditional (t1,t2,t3)) =
          let
             val (0 , t1') = lazy false nil false t1;
          in
             case t1' of
               True  => lazy redex trans sel t2 |
               False => lazy redex trans sel t3 |
                   _ => (0 , Conditional
                           (t1' , #2 (lazy false nil false t2),
                                  #2 (lazy false nil false t3)
                           ))
          end
     | lazy false nil false (Equality (t1,t2)) =
          let
             val (0 , t1') = lazy false nil false t1;
             val (0 , t2') = lazy false nil false t2;
          in
             if t1' = t2'
                then (0 , True)
                else if freevar t1' orelse freevar t2'
                        then (0 , Equality (t1',t2'))
                        else (0 , False)
          end
     | lazy _ _ _ t = (0 , t);
in
   val eval = #2 o (lazy false nil false)
end;

(* end of EVAL.SML ***************************************************)

