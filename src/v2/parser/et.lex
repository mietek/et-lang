(* this is lexfile for et *)
type pos = LexPosition.Position
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type arg = LexPosition.Position ref * bool ref

type lexresult = (svalue,LexPosition.Position) token
fun eof (currPos,_) = Tokens.Eof (!currPos,!currPos)

exception LexError of string * LexPosition.Position * LexPosition.Position

fun whitesp yytext currPos duringParsing lex =
    let
	val cPos = !currPos
	val nPos =LexPosition.addText cPos yytext
    in
	(currPos:=nPos;lex (currPos,duringParsing) ())
    end

fun newline yytext currPos duringParsing lex =
    let
	val cPos = !currPos
	val nPos =LexPosition.newLine cPos
    in
	(currPos:=nPos;lex (currPos,duringParsing) ())
    end

fun makeToken token yytext currPos duringParsing=
    let
	val cPos = !currPos
	val nPos =LexPosition.addText cPos yytext
    in
	(duringParsing:=true;currPos:=nPos;token (cPos,nPos))
    end

fun makeValToken token value yytext currPos duringParsing=
    let
	val cPos = !currPos
	val nPos =LexPosition.addText cPos yytext
    in
	(duringParsing:=true;currPos:=nPos;token (value, cPos, nPos))
    end

fun makeError yytext currPos _=
    let
	val cPos = !currPos
	val nPos =LexPosition.addText cPos yytext
    in
	(currPos:=nPos;raise LexError (yytext,cPos,nPos))
    end
%%
%header (functor etLexFun(structure Tokens:et_TOKENS
			   structure LexPosition:etLEXPOSITION));

%arg (currPos:LexPosition.Position ref,duringParsing:bool ref);

WhiteSpaces  = [\ \t\013\012]+;
NewLine      = \n;
Digit        = [0-9];
LowerCase    = [a-z];
UpperCase    = [A-Z];
Letter       = {UpperCase} | {LowerCase};
Alphanum     = ({Letter} | {Digit} | [_'])*;
DatatypeCons = {Letter} {Alphanum};
LowerIdent   = {LowerCase} {Alphanum};
UpperIdent   = {UpperCase} {Alphanum};
Iterator     = _ {DatatypeCons} "it";
Recursor     = _ {DatatypeCons} "rec";
Coiterator   = _ {DatatypeCons} "ci";
Corecursor   = _ {DatatypeCons} "cr";
TypeVar      = ' {Alphanum};
%%
{WhiteSpaces} => (whitesp yytext currPos duringParsing lex);
{NewLine}     => (newline yytext currPos duringParsing lex);
"fn"          => (makeToken Tokens.Fn yytext currPos duringParsing);
"val"         => (makeToken Tokens.Val yytext currPos duringParsing);
"let"         => (makeToken Tokens.Let yytext currPos duringParsing);
"in"          => (makeToken Tokens.In yytext currPos duringParsing);
"end"         => (makeToken Tokens.End yytext currPos duringParsing);
"datatype"    => (makeToken Tokens.Datatype yytext currPos duringParsing);
"from"        => (makeToken Tokens.From yytext currPos duringParsing);
"codatatype"  => (makeToken Tokens.Codatatype yytext currPos duringParsing);
"to"          => (makeToken Tokens.To yytext currPos duringParsing);
\(            => (makeToken Tokens.LeftParen yytext currPos duringParsing);
\)            => (makeToken Tokens.RightParen yytext currPos duringParsing);
"=>"          => (makeToken Tokens.DArrow yytext currPos duringParsing);
,             => (makeToken Tokens.Colon yytext currPos duringParsing);
\=            => (makeToken Tokens.Equals yytext currPos duringParsing);
\;            => (makeToken Tokens.Semicolon yytext currPos duringParsing);
\|            => (makeToken Tokens.Bar yytext currPos duringParsing);
&             => (makeToken Tokens.Ampersand yytext currPos duringParsing);
\*            => (makeToken Tokens.Star yytext currPos duringParsing);
\+            => (makeToken Tokens.Plus yytext currPos duringParsing);
"->"          => (makeToken Tokens.Arrow yytext currPos duringParsing);
"if"          => (makeToken Tokens.If yytext currPos duringParsing);
"then"        => (makeToken Tokens.Then yytext currPos duringParsing);
"else"        => (makeToken Tokens.Else yytext currPos duringParsing);
"use"         => (makeToken Tokens.Use yytext currPos duringParsing);
"exit"        => (makeToken Tokens.Exit yytext currPos duringParsing);
"show"        => (makeToken Tokens.Show yytext currPos duringParsing);
"norm"        => (makeToken Tokens.Norm yytext currPos duringParsing);
{Digit}+      => (makeValToken Tokens.Number
		  ((fn SOME a => a | NONE => IntInf.fromInt 0)
		   (IntInf.fromString yytext))
		  yytext currPos duringParsing);
"()"          => (makeToken Tokens.LRParen yytext currPos duringParsing);
"{}"          => (makeToken Tokens.LRBrace yytext currPos duringParsing);
\"[^"]*\"     => (makeValToken Tokens.Str yytext yytext currPos duringParsing);
"(*"(((([^*]\))*)|([^\)]*))*)"*)" =>
                 (whitesp yytext currPos duringParsing lex);
{UpperIdent}  => (makeValToken Tokens.UpperIdent yytext yytext
		  currPos duringParsing);
{LowerIdent}  => (makeValToken Tokens.LowerIdent yytext yytext
		  currPos duringParsing);
{TypeVar}     => (makeValToken Tokens.TypeVar yytext yytext
		  currPos duringParsing);
{Iterator}    => (makeValToken Tokens.Iterator yytext yytext
		  currPos duringParsing);
{Recursor}    => (makeValToken Tokens.Recursor yytext yytext
		  currPos duringParsing);
{Coiterator}  => (makeValToken Tokens.Coiterator yytext yytext
		  currPos duringParsing);
{Corecursor}  => (makeValToken Tokens.Corecursor yytext yytext
		  currPos duringParsing);
.             => (makeError yytext currPos duringParsing);
