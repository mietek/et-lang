signature etFROMPARSER=
sig
  structure Position : etLEXPOSITION 
 
  type LRPos 

  type String = string * LRPos

  datatype etTerm =
      Let of (etValBinding list * etTerm) * LRPos
    | Fn of (String list * etTerm )  * LRPos
    | Ident of string  * LRPos
    | App of (etTerm * etTerm) * LRPos
    | Number of (IntInf.int) * LRPos
  and etValBinding =
      Val of (String * etTerm) * LRPos

  datatype etType = 
      TypeVar of string * LRPos
    | TypeApp of (String * etType list) * LRPos

  datatype etDeclaration =
      LexerError of string * LRPos
    | ParserError of string * LRPos
    | Eof of unit * LRPos
    | Command of (string * string) * LRPos
    | Norm of (etTerm) * LRPos
    | Empty of unit * LRPos
    | Term of etTerm * LRPos
    | ValBind of etValBinding * LRPos
    | DatatypeDef 
          of (String * (String list) * (String * etType list) list) * LRPos
    | CodatatypeDef
	  of (String * (String list) * (String * etType list) list) * LRPos

  val mkLRPos       : Position.Position -> Position.Position -> LRPos
  val mkTermWithPos : ('a * LRPos -> 'b ) -> 'a -> Position.Position 
                        -> Position.Position -> 'b
  val getTerm       : 'a * LRPos -> 'a
  val getLeftPos    : 'a * LRPos -> Position.Position
  val getRightPos   : 'a * LRPos -> Position.Position
end

functor etFromParserFun (structure Position:etLEXPOSITION) : etFROMPARSER = 
struct
  structure Position = Position

  type LRPos = (Position.Position * Position.Position)

  type String = string * LRPos

  datatype etTerm =
      Let of (etValBinding list * etTerm) * LRPos
    | Fn of (String list * etTerm )  * LRPos
    | Ident of string  * LRPos
    | App of (etTerm * etTerm) * LRPos
    | Number of (IntInf.int) * LRPos
  and etValBinding =
      Val of (String * etTerm) * LRPos

  datatype etType = 
      TypeVar of string * LRPos
    | TypeApp of (String * etType list) * LRPos

  datatype etDeclaration =
      LexerError of string * LRPos
    | ParserError of string * LRPos
    | Eof of unit * LRPos
    | Command of (string * string) * LRPos
    | Norm of (etTerm) * LRPos
    | Empty of unit * LRPos
    | Term of etTerm * LRPos
    | ValBind of etValBinding * LRPos
    | DatatypeDef 
          of (String * (String list) * (String * etType list) list) * LRPos
    | CodatatypeDef
	  of (String * (String list) * (String * etType list) list) * LRPos

  fun mkLRPos lpos rpos = (lpos,rpos)
  fun mkTermWithPos cons t lpos rpos = cons (t,mkLRPos lpos rpos)
  fun getTerm (t,(lpos,rpos)) = t
  fun getLeftPos (t,(lpos,rpos)) = lpos
  fun getRightPos (t,(lpos,rpos)) = rpos
end

structure etFromParser = etFromParserFun(structure Position=etLexPosition)
