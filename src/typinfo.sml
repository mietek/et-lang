
(*********************************************************************)
(*                                                                   *)
(*               TYPINFO.SML - INFORMATION ABOUT TYPES               *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LAMTERM.SML:                                              *)
(*       nest     = fn: int -> term -> term                          *)
(*       printerm = fn: int -> term -> unit                          *)
(*       z        = ? : int                                          *)
(*    from LISTING.SML:                                              *)
(*       out      = fn: string -> unit                               *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and constr and tycon      *)
(*    from TYPEX.SML:                                                *)
(*       numtyvar = fn: typex -> unit                                *)
(*       eratyvar = fn: typex -> unit                                *)
(*       a        = ? : int                                          *)
(*       printy   = fn: typex -> unit                                *)
(* Exports:                                                          *)
(*       typinfo  = fn: tycon ref -> unit                            *)
(*                                                                   *)
(*********************************************************************)
         
fun typinfo ( ref (Type {name=id,induc=ic,coty=ct,varlist=vl,
                         typiter=ti,typrec=tr,conlist=cl}) ) =
   let
      val conum  = length cl;                                        
      val varnum = revfold (fn (tr,k) => (tr := Label k;succ k)) vl 0; 
      val costr  = if ct then "co" else "";

      fun info elim =                         
         let
            val eliminator =
              costr ^ (if elim then "rec  " else "iter ");
            val elimname = if ct then (if elim then "cr" else "ci")
                                 else (if elim then "rec" else "it");
            fun f (n , Lambda trm) = f (succ n , trm)
              | f x = x;
            val prinpar = iter 
                           (fn k => ( out (" " ^ chr (z-k)) ; succ k )) 
         in
            out ( eliminator ^ "_" ^ id ^ elimname ^ " : " );
            printy (if elim then tr else ti) ; out "\n";
            if ct
            then
            app (fn Constr (ref {name=str,trai=tri,trar=trr,...}) =>
                  let
                    val (lamnum , trm') =
                      f (0 , if elim then trr else tri);
                    val etan = conum+1-lamnum;
                    val trm = if etan >= 0
                      then recur (fn n => fn t => Application
                                    (t , Parameter (etan-n-1)))
                                 (nest etan trm') etan
                      else iter (fn t => Lambda t) trm' (~etan);
                  in
                    out ( "comp   " ^ str ^ " ");
                    out ("(_" ^ id ^ elimname);
                    prinpar 0 (conum+1);
                    out ") = ";
                    printerm (conum+1) trm; out "\n"
                  end
                ) cl
            else
            app ( fn Constr (ref {name=str,trai=tri,trar=trr,...}) =>
                   let
                      val (lamnum , trm) =
                        f (0 , if elim then trr else tri);
                      val argnum = max (lamnum - conum , 0);
                   in
                      out ( "comp _" ^ id ^ elimname ^ " " );
                      if argnum > 0
                         then (out ("("^str);
                               prinpar 0 argnum;
                               out ")")
                         else out str;
                      out " = " ; printerm argnum
                        (iter (fn t => Lambda t) trm (lamnum-argnum));
                      out "\n"
                   end
              ) cl
         end;
   in                        
      numtyvar ti varnum;
      out ( costr ^ "datatype " ^ id );    
      iter (fn k => ( out ( " '" ^ chr (a+k) ) ; succ k )) 0 varnum;
      out "\n";          
      app ( fn Constr (ref {name=str,ty=t,...}) =>
                ( out ( (if ct then "des    " else  "con  ") ^ str ^
                        " : " ) ; printy t ; out "\n" )
          ) cl;
      info false;
      if ic then info true
            else out (costr ^ "rec  _" ^ id ^
                      (if ct then "cr" else "rec") ^ " = _" ^ id ^
                      (if ct then "ci" else "it") ^ "\n");
      eratyvar ti
   end; (* typinfo *)

(* end of TYPINFO.SML ************************************************)

