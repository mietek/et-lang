
(*********************************************************************)
(*                                                                   *)
(*        ENVIRON.SML - COMMON DEFINITIONS FOR AN ENVIRONMENT        *)
(*                                                                   *)
(*    Programmed in Standard ML by Tomasz Wierzbicki, 1992, 1993.    *)
(*                                                                   *)
(*                                                                   *)
(* Imports:                                                          *)
(*    from LAMTERM.SML:                                              *)
(*       nest     = fn: int -> term -> term                          *)
(*    from TYLAM.SML:                                                *)
(*       datatype term and typex and tyvar and constr and tycon      *)
(*    from TYPINFO.SML:                                              *)
(*       typinfo  = fn: tycon ref -> unit                            *)
(* Exports:                                                          *)
(*       con Undef_constr    = - : exn                               *)
(*       con Undef_type      = - : exn                               *)
(*       con Unbound_value   = - : exn                               *)
(*       abstype environment with                                    *)
(*          emptyenv   = - : environment                             *)
(*          find_param = fn: string -> environment -> term           *)
(*          find_con   = fn: string -> environment -> constr         *)
(*          find_ty    = fn: string -> environment -> tycon ref      *)
(*          ins_param  = fn: string -> environment -> environment    *)
(*          del_val    = fn: string -> environment -> environment    *)
(*          repl_val   = fn: string -> term -> environment ->        *)
(*                           environment                             *)
(*          repl_ty    = fn: tycon ref -> environment -> environment *)
(*          show_env   = fn: environment -> string -> environment    *)
(*                                                                   *)
(*********************************************************************)

exception Undef_constr and Undef_type and Unbound_value;

local
   datatype parameter = Formal | BoundVal of term;

   val hidden = "[hidden]";
   val sh = size hidden;
   fun ishidden str =
      let
         val len = size str;
      in
         len > 8 andalso substring (str , len-sh , sh) = hidden
      end;
in
   abstype
      environment = E of (string * parameter) list * tycon ref list
   with
      val emptyenv = E (nil,nil);

      fun find_param str ( E (bv , _) ) =
         let
            fun f n ((id , Formal) :: bv) =
                   if id = str
                      then Parameter n
                      else f (succ n) bv
              | f n ( (id , BoundVal trm) :: bv ) =
                   if id = str
                      then nest n trm
                      else f n bv
              | f _ nil = raise Unbound_value;
         in
            f 0 bv
         end;

      fun find_con str ( E (_ , ts) ) =
         let
            exception Not_found;

            fun f ( ( con as Constr (ref {name=id,...}) ) :: cons ) =
                   if id = str
                      then con
                      else f cons
              | f nil = raise Not_found;

            fun g ( ref (Type {conlist=cons,...}) :: ts ) =
                   ( f cons handle Not_found => g ts )
              | g nil = raise Undef_constr;
         in
            g ts
         end;

      fun find_ty str ( E (_ , ts) ) =
         let
            fun f ( ( t as ref (Type {name=id,...}) ) :: ts ) =
                   if id = str
                      then t
                      else f ts
              | f nil = raise Undef_type;
         in
            f ts
         end;

      fun ins_param str (E (bv , ts)) = E ((str , Formal) :: bv , ts);

      local
         fun f acc str ( (x as (id,_)) :: rest ) =
                if id = str
                   then acc @ rest
                   else f (acc @ [x]) str rest
           | f acc _ nil = acc;
      in
         fun del_val str ( E (bv , ts) ) = E ( f nil str bv , ts );
         fun repl_val str trm ( E (bv , ts) ) =
            E ( f [ (str , BoundVal trm) ] str bv , ts );
      end;

      fun repl_ty (newt as ref (Type {name=str,conlist=ncl,...}))
         ( env as E (bv , ts) ) =
         let
            fun hide str = if ishidden str then str else str ^ hidden;
         in
            (case find_ty str env of
                tr as ref (Type { name    = id,
                                  induc   = ic,
                                  coty    = cty,
                                  varlist = vl,
                                  typiter = tyi,
                                  typrec  = tyr,
                                  conlist = cl
                                }) =>
                   tr := Type { name    = hide id,
                                induc   = ic,
                                coty    = cty,
                                varlist = vl,
                                typiter = tyi,
                                typrec  = tyr,
                                conlist = cl
                              }) handle Undef_type => ();
            app (fn Constr (ref {name=str,...}) =>
                              (case find_con str env of
                                 Constr (cr as ref {name = id,
                                                    coty = ct,
                                                    ty   = t,
                                                    trai = tri,
                                                    trar = trr
                                                   }) => cr :=
                                      { name = hide id,
                                        coty = ct,
                                        ty   = t,
                                        trai = tri,
                                        trar = trr
                                      })
                                 handle Undef_constr => ()
                ) ncl;
            E (bv , newt :: ts)
         end;

      fun show_env ( env as E (bv , ts) ) str =
         ( if str = ""
              then ( out "Types:" ;
                     if ts = nil
                        then out "  -"
                        else revapp
                                (fn ref (Type {name=id,...}) =>
                                    if ishidden id
                                       then ()
                                       else out (" " ^ id)
                                ) ts;
                     out "\nValues:" ;
                     if bv = nil
                        then out "  -"
                        else revapp ( fn (id,_) => out (" " ^ id) ) bv;
                     out "\n"
                   )
              else ( typinfo ( find_ty str env ) handle Undef_type =>
                        out "There's no such type\n"
                   );
          env
        );
   end
end;

(* end of ENVIRON.SML ************************************************)

