signature etPARSER =
sig
structure FromParser : etFROMPARSER

type LexerType

val makeLexer : (int -> string) -> (bool -> unit) -> LexerType
val parse : LexerType -> FromParser.Position.Position -> 
   (FromParser.etDeclaration * LexerType * FromParser.Position.Position)
end

functor etParserFun (structure FromParser : etFROMPARSER) : etPARSER =
struct
structure FromParser = FromParser

structure etLrVals=etLrValsFun(
  structure Token = LrParser.Token
  structure FromParser = FromParser)

structure etLex=etLexFun(structure Tokens   = etLrVals.Tokens
                         structure LexPosition = FromParser.Position)

structure etYacc=JoinWithArg
    (structure ParserData=etLrVals.ParserData
     structure Lex = etLex
     structure LrParser = LrParser)

val dummyEof = etLrVals.Tokens.Eof
              (FromParser.Position.startPos,FromParser.Position.startPos)

val dummySemicolon = etLrVals.Tokens.Semicolon
              (FromParser.Position.startPos,FromParser.Position.startPos)

exception etParseError of string * FromParser.LRPos

val currPos = ref FromParser.Position.startPos

val duringParsing  = ref true

val invoke = fn lexstream =>
    let 
        val errorInParsing = fn (s,lPos,rPos) => 
                        raise etParseError (s,FromParser.mkLRPos lPos rPos)
    in
      etYacc.parse(0,lexstream,errorInParsing,())
    end;

type LexerType = (etYacc.svalue,etYacc.pos) LrParser.Token.token
                     LrParser.Stream.stream

fun makeLexer inputFun outputFun = etYacc.makeLexer
    (fn i => (outputFun (!duringParsing);
              inputFun i))
    (currPos,duringParsing);

fun parse lexer pos = 
    let
        val _ = currPos:=pos;
        val _ = duringParsing:=false;
        val (nextToken,nextlexer)=etYacc.Stream.get lexer
    in
        if etYacc.sameToken(nextToken,dummyEof) then 
            (FromParser.mkTermWithPos FromParser.Eof () pos pos,lexer,pos)
        else 
	    let
		val (result,lexer) = invoke lexer
		val (nextToken,lexer)=etYacc.Stream.get lexer
	    in
		if etYacc.sameToken(nextToken,dummySemicolon) then
		    (result,lexer,!currPos)
		else
		    raise etParseError 
			("syntax error, Semicolon expected",
			 FromParser.mkLRPos (!currPos) (!currPos))
	    end
    end
    handle etParseError (s,lrpos) => 
	    (FromParser.ParserError ("syntax error",lrpos),lexer,!currPos) 
	 |  etLex.UserDeclarations.LexError (s,lpos,rpos) => 
	    (FromParser.LexerError 
	     ("unrecognized character: "^s,
	      FromParser.mkLRPos (lpos) (rpos)),lexer,!currPos)
end

structure etParser = etParserFun(structure FromParser=etFromParser)
