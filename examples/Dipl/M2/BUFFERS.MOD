IMPLEMENTATION MODULE Buffers;

FROM Lib IMPORT IncAddr;
FROM Str IMPORT Copy;
FROM FIO IMPORT File, EOF, IOresult, ChopOff, IOcheck, Separators;
FROM FIO IMPORT RdChar, WrChar, Seek, GetPos, Create, Open, Close;
IMPORT IO;

CONST
	NULL=0C;
	TAB=11C;
	MaxHandles=10;
VAR
 	inputOriginal,outOriginal:File;
 	lastChar:CHAR;
 	valid:BOOLEAN;
 	stack:ARRAY [1..MaxHandles] OF
 		RECORD
 			handle:File;
 			posReached:LONGCARD;
 			lineReached:CARDINAL;
 			linePosition:LONGCARD;
 		END;
 	top:[0..MaxHandles];

PROCEDURE ReadChar(VAR ch:CHAR);
BEGIN
	INC(position);
	IF NOT valid THEN
		lastChar:=RdChar(input);
		IF reached<position THEN
			reached:=position;
			IF lastChar=CHR(10) THEN
				INC(reachedLine);
				linePos:=position
			END
		END;
		IF EOF THEN
			lastChar:=IO.RdChar();
			WrChar(input,lastChar)
		END
	ELSE
		valid:=FALSE
	END;
	ch:=lastChar
END ReadChar;

PROCEDURE Rewind(newPos:LONGCARD);
BEGIN
	IF (position=newPos+1) AND (lastChar#0C) AND NOT valid THEN
		valid:=TRUE
	ELSE
		valid:=FALSE;
		lastChar:=0C;
		Seek(input,newPos)
	END;
	position:=newPos
END Rewind;

PROCEDURE FlushOut;
VAR
	count,last:LONGCARD;
BEGIN
	IF output=outOriginal THEN
		last:=GetPos(output);
		Seek(output,0);
		FOR count:=1 TO last DO
			IO.WrChar(RdChar(output))
		END
	END
END FlushOut;

PROCEDURE ReadWord(VAR wd:ARRAY OF CHAR; VAR first,rest:CharSet);
VAR
	i:CARDINAL;
	ch:CHAR;
BEGIN
	ReadChar(ch);
	i:=0;
	IF ch IN first THEN
		wd[0]:=ch;
		REPEAT
			ReadChar(ch);
			INC(i);
			wd[i]:=ch
		UNTIL NOT(ch IN rest) OR (i=HIGH(wd));
		IF ch IN rest THEN
			REPEAT
				ReadChar(ch)
			UNTIL NOT(ch IN rest)
		END
	END;
	wd[i]:=NULL;
	Rewind(position-1)
END ReadWord;

PROCEDURE WriteChars(a:ADDRESS);
TYPE
	CharPtr=POINTER TO CHAR;
BEGIN
	WHILE CharPtr(a)^#NULL DO
		WrChar(output,CharPtr(a)^);
		IncAddr(a,1)
	END
END WriteChars;

PROCEDURE ReportError;
VAR
	ch:CHAR;
	i:CARDINAL;
BEGIN
   IO.WrStr('Line ');
   IO.WrCard(reachedLine,0);
   IO.WrLn;
   Seek(input,linePos);
   REPEAT
      ch:=RdChar(input);
      IF ch=TAB THEN
      	ch:=' '
      END;
      IO.WrChar(ch)
   UNTIL (ch=CHR(13)) OR EOF;
   IO.WrLn;
   FOR i:=2 TO CARDINAL(reached-linePos) DO
      IO.WrChar(' ')
   END;
   IO.WrChar('^');
   Rewind(position)
END ReportError;

PROCEDURE OpenInput(filename:ARRAY OF CHAR):BOOLEAN;
VAR
	handle:CARDINAL;
	unique:ARRAY [0..7] OF CHAR;
BEGIN
	IF filename[0]=0C THEN
		Copy(unique,'input  .buf');
      unique[5]:=CHR(ORD('0') + top DIV 10);
      unique[6]:=CHR(ORD('0') + top MOD 10);
		handle:=Create(unique);
	ELSE
		handle:=Open(filename)
	END;
	IF IOresult()=0 THEN
		INC(top);
		WITH stack[top] DO
			handle:=input;
			posReached:=reached;
			lineReached:=reachedLine;
			linePosition:=linePos
		END;
		Seek(input,position);
		input:=handle;
		position:=0;
		linePos:=0;
		reached:=0;
		reachedLine:=1;
		valid:=FALSE
	END;
	RETURN IOresult()=0
END OpenInput;

PROCEDURE CloseInput;
BEGIN
	Close(input);
	WITH stack[top] DO
		input:=handle;
		reached:=posReached;
		reachedLine:=lineReached;
		linePos:=linePosition
	END;
	DEC(top);
	position:=GetPos(input);
	valid:=FALSE
END CloseInput;

BEGIN
   ChopOff:=FALSE;
   IOcheck:=FALSE;
   top:=0;
   output:=Create("output.buf");
   outOriginal:=output
END Buffers.
