   
(*********************************************************************)
(*                                                                   *)
(*    MONAMON.SML - THE MONOTONICITY / ANTIMONOTONICITY FUNCTIONS    *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from GENITER.SML:                                              *)
(*       splitconty = fn: typex -> typex list                        *)
(*       substy     = fn: typex -> (typex -> bool) -> typex -> typex *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar                           *)
(*    from TYPEX.SML:                                                *)
(*       derefer    = fn: typex -> typex                             *)
(*    from UNIFY.SML:                                                *)
(*       occurs     = fn: tyvar ref -> typex -> unit                 *)
(*       con Infinite_type  = - : exn                                *)
(* Exports:                                                          *)
(*       con Bad_occurrence = - : exn                                *)
(*       mon        = fn: bool -> tyvar ref -> typex -> bool -> term *)
(*                                                                   *)
(*********************************************************************)

exception Bad_occurrence;

fun mon posocc var t elim =
  (occurs var t ; Lambda (Lambda (Parameter 0)))
  handle Infinite_type =>
  (case derefer t of
     Tyvar (ref None) =>
       if posocc
         then Lambda (Parameter 0)
         else raise Bad_occurrence |
     Tyfun (t1 , t2) =>
       Lambda (Lambda (Lambda
         (Application
            (Application (mon posocc var t2 elim , Parameter 2),
             Application                                   
               (Parameter 1,
                Application
                  (Application (mon (not posocc) var t1 elim,
                                Parameter 2),
                   Parameter 0
                  )
               )
            )
         ))) |
     Tycon (t as ref (Type{conlist=cl,varlist=vl,coty=ct,...}),para) =>
       let                                              
         fun save_var ((v as ref tv) :: vs) vs' =
               ( v := None ; save_var vs (vs' @ [tv]) )
           | save_var nil vs' = vs';
          fun restore_var (v :: vs) (tv :: vs') =
               ( v := tv ; restore_var vs vs' )
           | restore_var nil nil = ();
                                 
         val V2  = Tyvar (ref None);
         val vl' = save_var vl nil;
         val t' =
          if ct 
           then Lambda (Lambda (Application 
           (revfold
             (fn (c as Constr (ref {ty=conty,...}) , trm) =>
                let 
                  val Tyfun (_,p) = conty;
                in
                  Application
                    (trm,
                     Lambda
                      ((fn x =>
                        if elim
                          then 
                            Application 
                              (Application
                                 (let
                                    val t' = substy 
                                      (fn ty =>
                                         case ty of
                                           Tycon (t',_) => t = t' |
                                                      _ => false)
                                      (Tyvar var) p;
                                    val tt =
                                      (restore_var vl
                                           (map (fn x => Some x) para);
                                       mon posocc var t' elim);
                                  in 
                                    app (fn v =>v := None) vl;
                                    tt               
                                  end,
                                  Inr
                                 ),
                               x
                              )
                          else x
                       )
                       (Application
                          (Application
                             (let
                                val t' = substy 
                                  (fn ty => case ty of
                                              Tycon (t',_) => t = t' |
                                                         _ => false)
                                  V2 p;
                                val tt = (restore_var vl 
                                           (map (fn x => Some x) para);
                                          mon posocc var t' elim);
                              in 
                                app (fn v => v := None) vl;
                                tt
                              end,
                              Parameter 2
                             ),
                           Application
                             (Constructor c,
                              Parameter 0
                             )
                          )
                       )
                      )
                    )
                end
             )
             cl ((if elim then Recursor else Iterator) t),
            Parameter 0
           )))
           else Lambda (Lambda
           (revfold
             (fn (c as Constr (ref {ty=conty,...}) , trm) =>
                Application
                  (trm,
                   let
                     val conpara = splitconty conty;
                     val paranum = length conpara;
                   in                             
                     iter (fn trm => Lambda trm)
                          (#2
                            (revfold
                              (fn (p , (j,trm)) =>
                                (pred j,
                                 Application
                                   (trm,
                                    Application
                                      (Application
                                         (let
                                           val t' = substy 
                                             (fn ty => case ty of
                                                Tycon (t',_) => t = t'|
                                                           _ => false)
                                             V2 p;
                                           val tt =
                                            (restore_var vl 
                                             (map (fn x=>Some x) para);
                                             mon posocc var t' elim);
                                          in 
                                           app (fn v => v := None) vl;
                                           tt
                                          end,
                                          Parameter (paranum + 1)
                                         ),            
                                       if elim 
                                        then Application
                                         (Application
                                            (let
                                           val t' = substy 
                                             (fn ty => case ty of
                                                Tycon (t',_) => t = t'|
                                                           _ => false)
                                             (Tyvar var) p;
                                           val tt =
                                            (restore_var vl 
                                             (map (fn x=>Some x) para);
                                             mon posocc var t' elim);
                                          in 
                                           app (fn v => v := None) vl;
                                           tt
                                          end,
                                             Snd
                                            ),
                                          Parameter j
                                         )
                                       else Parameter j
                                      )
                                   )
                                )
                              )
                              conpara
                              (paranum - 1 , Constructor c)
                            )
                          )
                          paranum
                   end
                  )
             )
             cl
             ( Application 
                 ((if elim then Recursor else Iterator) t,
                  Parameter 0
                 )
             )
         ));
       in
         restore_var vl vl' ; t'
       end |
     Typair (t1 , t2) =>
       Lambda (Lambda
         (Pair
            (Application
               (Application (mon posocc var t1 elim, Parameter 1),
                Application (Fst , Parameter 0)
               ),
             Application
               (Application (mon posocc var t2 elim, Parameter 1),
                Application (Snd , Parameter 0)
               )
            )
         )) |
     Tyun (t1 , t2) =>
       Lambda (Lambda
         (Application
            (Application
               (Application (When , Parameter 0),
                Lambda
                  (Application
                     (Inl,
                      Application
                        (Application
                           (mon posocc var t1 elim,
                            Parameter 2
                           ),
                         Parameter 0
                        )
                     )
                  )
               ),
             Lambda
               (Application
                  (Inr,
                   Application
                     (Application
                        (mon posocc var t2 elim,
                         Parameter 2
                        ),
                      Parameter 0
                     )
                  )
               )
            )
         ))
 ); (* mon *)
                                     
(* end of MONAMON.SML ************************************************)

