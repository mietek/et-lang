signature etLEXPOSITION =
    sig
	type Position 
	val startPos : Position
	val startPosFile : string -> Position
	val newLine : Position -> Position
	val addText : Position -> string -> Position
	val getFile : Position -> string
	val getLine : Position -> int
	val getColumn : Position -> int
	val getTextLine : Position -> string
    end;

structure etLexPosition : etLEXPOSITION =
    struct
	type Position = {file: string,line: int,column: int,textline:string}
	    
	val startPos = {file="",line=1,column=0,textline=""}
	fun startPosFile name = {file=name,line=1,column=0,textline=""}
	fun newLine (p:Position) = {file=(#file p),line=(#line p +1),
				    column=0,textline=""}
	fun addText (p:Position) text = {file=(#file p),line=(#line p),
					 column=(#column p)+String.size(text),
					 textline=(#textline p) ^ text}
	fun getFile (p:Position) = (#file p)
	fun getLine (p:Position) = (#line p)
	fun getColumn (p:Position) = (#column p)
	fun getTextLine (p:Position) = (#textline p)
    end;
    
