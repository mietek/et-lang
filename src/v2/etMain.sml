signature ET =
sig

type Env

val env : Env

val fromStdIn  : Env -> Env
val fromString : Env -> string -> Env
val fromFile   : Env -> string -> Env
end

functor etFun (structure Parser : etPARSER
	       structure Elab   : etELAB
	       structure Env    : etENVIRONMENT
	       structure PP     : etPRETTYPRINT
	       structure Eval   : etEVAL
		 sharing Elab.Env         = Env
		 sharing Eval.Env         = Env
		 sharing Elab.Unifier.Env = Env
		 sharing PP.Env           = Env
		 sharing Elab.AbsSyn      = PP.AbsSyn
		 sharing Elab.AbsSyn      = Eval.AbsSyn
		 sharing Elab.AbsSyn      = Env.AbsSyn
		 sharing Elab.FromParser  = Parser.FromParser) :>ET =
struct

type Env = Env.Env

structure AbsSyn = Env.AbsSyn

exception Error of string

val screenSize = 75

val env = Env.libEnv;

fun printError s lrpos = 
  let
    val leftPos   = Parser.FromParser.getLeftPos  ((),lrpos)
    val rightPos  = Parser.FromParser.getRightPos ((),lrpos)
    val filename  = Parser.FromParser.Position.getFile rightPos
    val leftLine  = Parser.FromParser.Position.getLine leftPos
    val rightLine = Parser.FromParser.Position.getLine rightPos
    val posStr    = filename ^ ":" ^ (Int.toString leftLine) ^ "." ^
      (Int.toString (1+Parser.FromParser.Position.getColumn leftPos)) ^ "-" ^
      (Int.toString rightLine) ^ "." ^
      (Int.toString (1+Parser.FromParser.Position.getColumn rightPos))
      ^ " Error: " ^ s ^"\n"
    val lines = 
      if leftLine=rightLine then
        (Parser.FromParser.Position.getTextLine rightPos) ^ "\n"
      else
        (Parser.FromParser.Position.getTextLine leftPos) ^ "...\n"
         ^ (Parser.FromParser.Position.getTextLine rightPos) ^"\n"
  in
    print (posStr ^ lines)
  end

fun elabType env (Parser.FromParser.TypeVar (s,lrpos)) = (
      AbsSyn.TypeVar (Env.getTypeFromName env s) 
      handle Env.NotFoundInEnv => 
	raise Elab.ElabError ("unbound type identifier: "^s,lrpos))
  | elabType env (Parser.FromParser.TypeApp (((s,lrpos),tl),_)) = 
      AbsSyn.TypeApp (Env.getTypeFromName env s,map (elabType env) tl) 
      handle Env.NotFoundInEnv => 
	raise Elab.ElabError ("unbound type identifier: "^s,lrpos)

fun subType t n (tt as AbsSyn.TypeApp (s,tl)) = 
      if t=tt then n else AbsSyn.TypeApp (s,map (subType t n) tl)
  | subType _ _  t                            = t


fun mkApp t f 0 = t
  | mkApp t f n = AbsSyn.App(mkApp t f (n-1),f n)

fun mkAbs t f 0 = t
  | mkAbs t f n = AbsSyn.Abs(f n,mkAbs t f (n-1))

fun mon i env t (tt as (AbsSyn.TypeVar _)) =
      if t = tt then AbsSyn.Abs ("z",AbsSyn.BoundVar 0)
      else AbsSyn.Abs ("z",AbsSyn.Abs ("y",AbsSyn.BoundVar 0))
  | mon i env t (AbsSyn.TypeApp (1,[t1,t2])) =
      AbsSyn.Abs ("z",AbsSyn.Abs ("y",
       AbsSyn.Abs ("x"^(Int.toString i),
                  AbsSyn.App(AbsSyn.App(mon (i+1) env t t2,AbsSyn.BoundVar 2),
				  AbsSyn.App(AbsSyn.BoundVar 1,
				    AbsSyn.App (AbsSyn.App(amon (i+1) env t t1,
							   AbsSyn.BoundVar 2)
						, AbsSyn.BoundVar 0))))))
  | mon i env t (AbsSyn.TypeApp (6,[t1,t2])) =
      AbsSyn.Abs ("z",AbsSyn.Abs ("y",
         AbsSyn.App(
         AbsSyn.App(AbsSyn.App(AbsSyn.Var 3,AbsSyn.BoundVar 0),
         AbsSyn.Abs("m1",AbsSyn.App(AbsSyn.Var 4,
                                    AbsSyn.App(AbsSyn.App(mon i env t t1,
                                                          AbsSyn.BoundVar 2),
                                               AbsSyn.BoundVar 0)))),
         AbsSyn.Abs("m2",AbsSyn.App(AbsSyn.Var 5,
                                    AbsSyn.App(AbsSyn.App(mon i env t t2,
                                                          AbsSyn.BoundVar 2),
                                               AbsSyn.BoundVar 0))))))
  | mon i  env t tt = AbsSyn.Abs ("z",AbsSyn.Abs ("y",AbsSyn.BoundVar 0))
and amon i env t (tt as (AbsSyn.TypeVar _)) =
      if t = tt then 
       raise 
        Error "Error: all occurrences of type being defined must be positive."
      else AbsSyn.Abs ("z",AbsSyn.Abs ("y",AbsSyn.BoundVar 1))
  | amon i env t (AbsSyn.TypeApp (1,[t1,t2])) =
     AbsSyn.Abs ("z",AbsSyn.Abs ("y",
      AbsSyn.Abs ("x"^(Int.toString i),
                AbsSyn.App(AbsSyn.App(amon (i+1) env t t2,AbsSyn.BoundVar 2),
				  AbsSyn.App(AbsSyn.BoundVar 1,
				    AbsSyn.App (AbsSyn.App(mon (i+1) env t t1,
							   AbsSyn.BoundVar 2)
						, AbsSyn.BoundVar 0))))))
  | amon i env t (AbsSyn.TypeApp (6,[t1,t2])) =
      AbsSyn.Abs ("z",AbsSyn.Abs ("y",
         AbsSyn.App(
         AbsSyn.App(AbsSyn.App(AbsSyn.Var 3,AbsSyn.BoundVar 0),
         AbsSyn.Abs("m1",AbsSyn.App(AbsSyn.Var 4,
                                    AbsSyn.App(AbsSyn.App(amon i env t t1,
                                                          AbsSyn.BoundVar 2),
                                               AbsSyn.BoundVar 0)))),
         AbsSyn.Abs("m2",AbsSyn.App(AbsSyn.Var 5,
                                    AbsSyn.App(AbsSyn.App(amon i env t t2,
                                                          AbsSyn.BoundVar 2),
                                               AbsSyn.BoundVar 0))))))
  | amon i env t tt = AbsSyn.Abs ("z",AbsSyn.Abs ("y",AbsSyn.BoundVar 0))

fun mkTypeAppFromList n m (h1::h2::tl) = 
      AbsSyn.TypeApp (n,[h1,mkTypeAppFromList n m (h2::tl)])
  | mkTypeAppFromList n m ([h1]) = h1
  | mkTypeAppFromList n m nil    = AbsSyn.TypeVar m


local
  fun apptoel u v mon 0 t = AbsSyn.App (mon,AbsSyn.Abs ("z",t))
    | apptoel u v mon i t = apptoel u v mon (i-1) 
                               (AbsSyn.App (t,AbsSyn.BoundVar (i)))

  fun apptoelrec u v mon 0 t = AbsSyn.App (mon,
       AbsSyn.Abs ("z",AbsSyn.App 
		   (AbsSyn.App (AbsSyn.Var 2,AbsSyn.BoundVar 0),t)))
    | apptoelrec u v mon i t = apptoelrec u v mon (i-1) 
                               (AbsSyn.App (t,AbsSyn.BoundVar (i)))

  fun app t (h::tl) = app (AbsSyn.App (t,h)) tl
    | app t nil     = t

  fun addvabs t 0 = t
    | addvabs t v = addvabs (AbsSyn.Abs ("v"^(Int.toString v),t)) (v-1)

  fun adduabs t 0 = t
    | adduabs t u = adduabs (AbsSyn.Abs ("u"^(Int.toString u),t)) (u-1)
in
  fun mkIter u v elim mon  i =
    let
      val l = map 
	(fn n => AbsSyn.App 
	 ((apptoel u v (mon n) v (AbsSyn.App (elim,AbsSyn.BoundVar 0))),
	  AbsSyn.BoundVar (v+u-n)))
	(List.tabulate (u,fn n => n+1))
      val f = app (AbsSyn.BoundVar (v-i)) l
    in
      adduabs (addvabs f v) u
    end

  fun mkRec u v elim mon  i =
    let
      val l = map 
	(fn n => AbsSyn.App 
	 ((apptoelrec u v (mon n) v (AbsSyn.App (elim,AbsSyn.BoundVar 0))),
	  AbsSyn.BoundVar (v+u-n)))
	(List.tabulate (u,fn n => n+1))
      val f = app (AbsSyn.BoundVar (v-i)) l
    in
      adduabs (addvabs f v) u
    end
end

local
  fun apptoin mon 0 t = AbsSyn.App (mon,t)
    | apptoin mon i t = apptoin mon (i-1) (AbsSyn.App (t,AbsSyn.BoundVar (i)))

  fun apptoinr mon 0 t = AbsSyn.App (mon,
        AbsSyn.Abs("z",AbsSyn.App(AbsSyn.App (AbsSyn.App(
              AbsSyn.Var 3,AbsSyn.BoundVar 0),
	      AbsSyn.Abs("x",AbsSyn.BoundVar 0)),t)))
    | apptoinr mon i t = apptoinr mon (i-1) 
        (AbsSyn.App (t,AbsSyn.BoundVar (i+1)))

  fun addvabs t 0 = t
    | addvabs t v = addvabs (AbsSyn.Abs ("v"^(Int.toString v),t)) (v-1)
in
  fun mkCoit v intro mon  i =
    let
      val l = AbsSyn.App (apptoin mon v intro,
	  AbsSyn.App (AbsSyn.BoundVar (v+1-i),AbsSyn.BoundVar 0))
    in
      addvabs (AbsSyn.Abs ("u",l)) v
    end

  fun mkCorec v intro mon  i =
    let
      val l = AbsSyn.App (apptoinr mon v intro,
	  AbsSyn.App (AbsSyn.BoundVar (v+1-i),AbsSyn.BoundVar 0))
    in
      addvabs (AbsSyn.Abs ("u",l)) v
    end
end


fun loop env lexer pos = 
  let
    val (result,lexer,pos) = Parser.parse lexer pos
  in
    (case result of
      Parser.FromParser.LexerError (s,lrpos) => (printError s lrpos;
						 (env,false))
    | Parser.FromParser.ParserError(s,lrpos) => (printError s lrpos;
						 (env,false))
    | Parser.FromParser.Eof   _ => (env,true)
    | Parser.FromParser.Empty _ => loop env lexer pos
    | Parser.FromParser.Command ((c,arg),lrpos) =>
       (case c of
          "use" => (fromFile env (let val l = String.size arg in
                                    String.substring(arg,1,l-2) end),false)
        | "show" => if arg = "" then 
	             (print ((foldl (fn (s,ss) => ss^" "^s) 
			     "" (Env.getTypeList env))^"\n")  ;(env,false))
		    else 
		     (( (print ((PP.dataToString env 
			      (Env.getTypeDef env arg) screenSize))
		      handle _ => print ((PP.codataToString env 
			(Env.getCoTypeDef env arg) screenSize)))
	              handle _ => raise Error 
		        ("Error: type is undefined: "^arg));(env,false))
        |   _    => raise Error ("Error: wrong command: "^c))
    | Parser.FromParser.Norm (t,_) =>
	let
	  val (sub,term,type_) = Elab.W env t
	in
	  print ((PP.termWithTypeToString env (Eval.toNormalForm env 
		  term,type_) screenSize) ^ "\n");
	  loop env lexer pos
	end
    | Parser.FromParser.Term (t,_) =>
	let
	  val (sub,term,type_) = Elab.W env t
	  val v = ("it",Eval.toHeadNormalForm env term,type_)
	  val env = Env.addTermToEnv env v
	in
	  print ((PP.valToString env v screenSize) ^ "\n");
	  loop env lexer pos
	end
    | Parser.FromParser.ValBind (Parser.FromParser.Val (((str,_),t),_),_) =>
	let
	  val (sub,term,type_) = Elab.W env t
	  val v = (str,Eval.toHeadNormalForm env term,type_)
	  val env = Env.addTermToEnv env v
	in
	  print ((PP.valNoTermToString env v screenSize) ^ "\n");
	  loop env lexer pos
	end
    | Parser.FromParser.DatatypeDef (((typename,_),arglist,conslist),lrpos) =>
	(let
	  val env = Env.addTypeToEnv env typename
	  val numType = Env.getTypeFromName env typename
	  val envloc = List.foldl (fn ((n,_),b) => Env.addTypeToEnv b n)
	                  env arglist
	  val numArg = map (fn (n,_) => Env.getTypeFromName envloc n)
	                  arglist
	  val dataType = 
	    AbsSyn.TypeApp (numType,map (fn n => AbsSyn.TypeVar n) numArg)
	  val cons = 
	    map (fn ((cname,_),ctypel) => 
		 (cname,map (elabType envloc) ctypel)) conslist
	  val appNumber = Env.getTypeFromName env "->"
	  val newTypeVar = AbsSyn.TypeVar (1+ (Env.maxTypeVarEnv envloc))
	  val consNum = length cons
	  val (env,iterNum) = Env.addTermToEnvWithNumber env 
	    ("_"^typename^"it",
	     AbsSyn.Iter ("_"^typename^"it",numType,consNum),
	     mkTypeAppFromList appNumber  appNumber
          (dataType::(map (fn (_,tl) => mkTypeAppFromList appNumber appNumber
		  ((map (subType dataType newTypeVar) tl)@[newTypeVar])) cons)
	     @[newTypeVar]))
	  val (env,recNum) = Env.addTermToEnvWithNumber env 
	    ("_"^typename^"rec",
	     AbsSyn.Rec ("_"^typename^"rec",numType,consNum),
	     mkTypeAppFromList appNumber appNumber
            (dataType::(map (fn (_,tl) => mkTypeAppFromList appNumber appNumber
		  ((map (subType dataType 
			 (AbsSyn.TypeApp (2,[dataType,newTypeVar]))) tl)
		    @[newTypeVar])) cons)
	     @[newTypeVar]))
	  val newTypeVar = AbsSyn.TypeVar (Env.maxTypeVarEnv env)
	  val (env,_) = List.foldl 
		 (fn ((name,tl),(e,n)) => 
		  (Env.addTermToEnv e (name,
		     AbsSyn.Cons (name,numType,n,length tl,
                        Eval.toNormalForm e
 		       (mkIter (length tl) consNum (AbsSyn.Var iterNum) 
        		       (fn i => mon 1 env newTypeVar (List.nth (
                                map (subType dataType newTypeVar) tl,i-1))) n),
                        Eval.toNormalForm e
 		       (mkRec (length tl) consNum (AbsSyn.Var recNum) 
        		       (fn i => mon 1 env newTypeVar (List.nth (
                                map (subType dataType newTypeVar) tl,i-1))) n),
				       []),
		   mkTypeAppFromList appNumber appNumber (tl@[dataType])),n+1))
		 (env,1) cons
	in
	  print ((PP.dataToString env (Env.getTypeDef env typename) 
		  screenSize));
	  loop env lexer pos
	end
        handle Match => raise 
           Elab.ElabError("creation of monocity function is impossible"
			  ,lrpos))
    | Parser.FromParser.CodatatypeDef (((typename,_),arglist,destlist),lrpos)=>
	let
	  val env = Env.addTypeToEnv env typename
	  val numType = Env.getTypeFromName env typename
	  val envloc = List.foldl (fn ((n,_),b) => Env.addTypeToEnv b n)
	                  env arglist
	  val numArg = map (fn (n,_) => Env.getTypeFromName envloc n)
	                  arglist
	  val dataType = 
	    AbsSyn.TypeApp (numType,map (fn n => AbsSyn.TypeVar n) numArg)
	  val dest = 
	    map (fn ((dname,_),dtypel) => 
		 (dname,map (elabType envloc) dtypel)) destlist
	  val appNumber = Env.getTypeFromName env "->"
	  val sumNumber = Env.getTypeFromName env "+"
	  val absurdNumber = Env.getTypeFromName env "{}"
	  val newTypeVar = AbsSyn.TypeVar (1+ (Env.maxTypeVarEnv envloc))
	  val destNum = length dest
	  val (env,coiterNum) = Env.addTermToEnvWithNumber env 
	    ("_"^typename^"ci",
	     AbsSyn.Coit ("_"^typename^"ci",numType,destNum,[]),
	     mkTypeAppFromList appNumber appNumber
	     ((map (fn (_,tl) => 
		    AbsSyn.TypeApp (appNumber,[newTypeVar,
		      mkTypeAppFromList sumNumber absurdNumber
		      (map (subType dataType newTypeVar) tl)])) dest)
	      @[newTypeVar,dataType]))
	  val (env,corecNum) = Env.addTermToEnvWithNumber env 
	    ("_"^typename^"cr",
	     AbsSyn.Corec ("_"^typename^"cr",numType,destNum,[]),
	     mkTypeAppFromList appNumber appNumber
	     ((map (fn (_,tl) => 
		    AbsSyn.TypeApp (appNumber,[newTypeVar,
		      mkTypeAppFromList sumNumber absurdNumber
		      (map (subType dataType 
			    (AbsSyn.TypeApp(6,[dataType,newTypeVar]))) tl)]))
	       dest)
	      @[newTypeVar,dataType]))
	  val newTypeVar = AbsSyn.TypeVar (Env.maxTypeVarEnv env)
	  val (env,_) = List.foldl 
		 (fn ((name,tl),(e,n)) => 
		  (Env.addTermToEnv e (name,
		     AbsSyn.Des (name,numType,n,
                        Eval.toNormalForm e
 		       (mkCoit destNum (AbsSyn.Var coiterNum)
			(mon 1 env newTypeVar (mkTypeAppFromList 
					    sumNumber absurdNumber
		      (map (subType dataType newTypeVar) tl))) n),
                        Eval.toNormalForm e
 		       (mkCorec destNum (AbsSyn.Var corecNum)
			(mon 1 env newTypeVar (mkTypeAppFromList 
					    sumNumber absurdNumber
		      (map (subType dataType newTypeVar) tl))) n)
				 ),AbsSyn.TypeApp 
		   (appNumber,[dataType,
			       mkTypeAppFromList sumNumber absurdNumber tl]))
		                             ,n+1))
		 (env,1) dest
	in
	  print ((PP.codataToString env (Env.getCoTypeDef env typename) 
		  screenSize));
	  loop env lexer pos
	end
        handle Match => raise 
	    Elab.ElabError("creation of monocity function is impossible"
			   ,lrpos))
  end
  handle Elab.ElabError (s,lrpos) =>( printError s lrpos;(env,false))
       | Error s                  =>(print (s^"\n");(env,false))
and fromFile env s=
  let
    val _=SMLofNJ.Internals.GC.messages false;
    val str = TextIO.openIn s
    val lexer = 
      Parser.makeLexer 
        (fn _ => let val s = TextIO.inputLine str
		 in 
		     TextIO.output(TextIO.stdOut,s);
		     TextIO.flushOut TextIO.stdOut;
		     s
		 end)
        (fn p => ((TextIO.output(TextIO.stdOut,if p then "= " else "+ "));
	          TextIO.flushOut TextIO.stdOut))
    val (env,_) = loop env lexer (Parser.FromParser.Position.startPosFile s)
  in
    (print "\n";env)
  end
  handle IO.Io _  => (print ("Error reading file : " ^ s ^"\n");env)

fun fromStdIn env =
  let
    val _=SMLofNJ.Internals.GC.messages false;
    val lexer = 
      Parser.makeLexer 
        (fn _ => TextIO.inputLine TextIO.stdIn)
        (fn p => ((TextIO.output(TextIO.stdOut,if p then "= " else "+ "));
	          TextIO.flushOut TextIO.stdOut))
    val (env,exit) = loop env lexer Parser.FromParser.Position.startPos
  in
    if exit then env else fromStdIn env
  end

fun fromString env s=
  let
    val _=SMLofNJ.Internals.GC.messages false;
    val lexer = 
      Parser.makeLexer 
        (fn _ => s ^ "\nexit;")
        (fn p => ((TextIO.output(TextIO.stdOut,if p then "= " else "+ "));
	          TextIO.flushOut TextIO.stdOut))
    val (env,_) = loop env lexer Parser.FromParser.Position.startPos
  in
    env
  end

end

structure et = etFun(structure Parser = etParser
		     structure Elab   = etElab
		     structure Eval   = etEval
		     structure Env    = etEnvironment
		     structure PP     = etPrettyPrint)
