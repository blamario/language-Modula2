IMPLEMENTATION MODULE Parser;

FROM Memory IMPORT ALLOCATE, AddMarker;
FROM Lib IMPORT IncAddr;
IMPORT Str;
FROM FIO IMPORT File, Open, IOresult, Close;
FROM Buffers IMPORT ReadChar, ReadWord, Rewind, CharSet;
FROM Buffers IMPORT position, OpenInput, CloseInput, ReportError;

FROM Machine IMPORT EmptyClosure, tempDef, wPackage, link, HandlePackage, Reduce;
FROM Machine IMPORT Join, AddEnv, AddValuedEnv, Root, Copy, result;
FROM Machine IMPORT ChangeDefinition, NewLayer, StartLayer, PopLayer;
FROM Machine IMPORT MakeDef, MakePrimitive, MakeString, MakePacked, ExtractPacked;
FROM Machine IMPORT MarkString, MarkClosure;

FROM Library IMPORT wChar, wString,	wCharSet, wNumber, wError, errorCodes;
FROM Library IMPORT wType, wStruct, wFile, wUndefined, wDescription;

FROM Names IMPORT FindWord, DefEntry, AddPrimWord, DefineWord, wMeaning;
FROM Names IMPORT NewDictionary, OldDictionary;

FROM Grammars IMPORT wSequence, wLexSequence, wValSequence, wLexValSequence;
FROM Grammars IMPORT wEndSeq, wChoice, wOption;
FROM Grammars IMPORT wDummy, wFail, wDone, wRaise, wDiscard, wGrammar, wNext;
FROM Grammars IMPORT wSpaceChars, wSpaces, wComment, wFrameGrammar, wCustomGrammar;
FROM Grammars IMPORT wCharGrammar, wCharSetGrammar, wStrGrammar, wNumGrammar;
FROM Grammars IMPORT wIdentifier, wIdentGrammar, wFirst, wTail;
FROM Grammars IMPORT wStructGrammar;
FROM Grammars IMPORT Failure, Confirmation;

FROM ParseLow IMPORT ParsePrimitive, buildTree;
FROM ParseLow IMPORT ParseSequencePrimitive, ParseEndSequence, ParseChoice, ParseOption;

CONST
	MaxStrLength=200;
	all=CharSet{0C..377C};

TYPE
	CharPtr=POINTER TO CHAR;
	string=ARRAY [0..MaxStrLength] OF CHAR;

VAR
	firstSet,tailSet:CharSet;
	originalFirst,originalTail:closure;
	strPtr:POINTER TO string;

PROCEDURE pSpaces;
VAR
	prevPos:LONGCARD;
	spaces:POINTER TO CharSet;
	str:ARRAY [0..1] OF CHAR;
BEGIN
	StartLayer;
	ChangeDefinition(wCharSet,HandlePackage);
	Reduce(wSpaceChars^);
	PopLayer;
	ExtractPacked(result,spaces);
	IF Root(wComment^)=wFail THEN
		ReadWord(str,spaces^,spaces^)
	ELSE
		REPEAT
			ReadWord(str,spaces^,spaces^);
			prevPos:=position;
			StartLayer;
			ChangeDefinition(wGrammar,wComment^);
			ParsePrimitive;
			PopLayer;
		UNTIL Root(result)=wFail;
		Rewind(prevPos)
	END;
	result:=Confirmation
END pSpaces;

PROCEDURE ParseLexValSequence;
BEGIN
	ParseSequencePrimitive(TRUE)
END ParseLexValSequence;

PROCEDURE ParseLexSequence;
BEGIN
	ParseSequencePrimitive(FALSE)
END ParseLexSequence;

PROCEDURE ParseValSequence;
BEGIN
	Reduce(wSpaces^);
	ParseSequencePrimitive(TRUE)
END ParseValSequence;

PROCEDURE ParseSequence;
BEGIN
	Reduce(wSpaces^);
	ParseSequencePrimitive(FALSE)
END ParseSequence;

PROCEDURE ParseTheLetter;
VAR
	chExpect,chRead:CHAR;
BEGIN
	ExtractPacked(wPackage^,chExpect);
	ReadChar(chRead);
	IF chRead=chExpect THEN
		IF buildTree THEN
			MakePacked(result,wChar,chRead)
		ELSE
			result:=Confirmation
		END
	ELSE
		result:=Failure
	END
END ParseTheLetter;

VAR
	strRest:CharPtr;

PROCEDURE ParseTheString;
VAR
	ch:CHAR;
	strExpect:CharPtr;
BEGIN
	ExtractPacked(wPackage^,strExpect);
	strRest:=strExpect;
	LOOP
		IF strRest^=0C THEN
			EXIT
		END;
		ReadChar(ch);
		IF strRest^#ch THEN
			EXIT
		END;
		IncAddr(strRest,1)
	END;
	IF strRest^=0C THEN
		IF buildTree THEN
			MakeString(result,wString,strExpect)
		ELSE
			result:=Confirmation
		END
	ELSE
		result:=Failure
	END
END ParseTheString;

PROCEDURE ParseTheCharSet;
VAR
	ch:CHAR;
	s:POINTER TO CharSet;
BEGIN
	ExtractPacked(wPackage^,s);
	ReadChar(ch);
	IF ch IN s^ THEN
		IF buildTree THEN
			MakePacked(result,wChar,ch)
		ELSE
			result:=Confirmation
		END
	ELSE
		result:=Failure
	END
END ParseTheCharSet;

PROCEDURE ParseNumber;
VAR
	ch:CHAR;
	minus:BOOLEAN;
	x:CARDINAL;
BEGIN
	ReadChar(ch);
	IF ch='-' THEN
		minus:=TRUE;
		ReadChar(ch)
	ELSE
		minus:=FALSE;
		IF ch='+' THEN
			ReadChar(ch)
		END
	END;
	x:=0;
	IF ch IN CharSet{'0'..'9'} THEN
		REPEAT
			IF x <= (MAX(INTEGER)-ORD(ch)+ORD('0')) DIV 10 THEN
				x:=10*x+ORD(ch)-ORD('0')
			END;
			ReadChar(ch)
		UNTIL NOT (ch IN CharSet{'0'..'9'});
		Rewind(position-1);
 		IF minus THEN
  			MakePacked(result,wNumber,-INTEGER(x))
  		ELSE
			MakePacked(result,wNumber,x)
		END
  	ELSE
		result:=Failure
  	END
END ParseNumber;

PROCEDURE ParseChar;
VAR
	delimiter,chRead:CHAR;
BEGIN
	ReadChar(delimiter);
	IF delimiter="'" THEN
		ReadChar(chRead);
		ReadChar(delimiter);
		IF delimiter="'" THEN
			MakePacked(result,wChar,chRead)
		ELSE
			result:=Failure
		END
	ELSE
		result:=Failure
	END
END ParseChar;

PROCEDURE ParseCharSET;
VAR
	ch,second,i:CHAR;
	s:CharSet;
	complement:BOOLEAN;
BEGIN
	ReadChar(ch);
	IF ch='{' THEN
		s:=CharSet{};
		ReadChar(ch);
		IF ch='~' THEN
			complement:=TRUE;
		ELSE
			complement:=FALSE;
			Rewind(position-1)
		END;
		LOOP
			pSpaces;
			ReadChar(ch);
			IF ch='}' THEN
				EXIT
			ELSIF ch='\' THEN
				ReadChar(ch);
			END;
			pSpaces;
			ReadChar(second);
			IF second='-' THEN
				pSpaces;
				ReadChar(second);
				IF second<ch THEN
					ch:=0C;
					EXIT
				END;
				FOR i:=ch TO second DO
					INCL(s,i)
				END;
				ReadChar(second)
			ELSE
				INCL(s,ch)
			END;
			IF second#',' THEN
				IF second#'}' THEN
					ch:=0C
				END;
				EXIT
			END
		END;
		IF ch#0C THEN
			IF buildTree THEN
				IF complement THEN
					s:=all-s;
				END;
				MakePacked(result,wCharSet,s)
			ELSE
				result:=Confirmation
			END;
			RETURN
		END
	END;
	result:=Failure
END ParseCharSET;

PROCEDURE ParseIdentifier;
VAR
	first,tail:POINTER TO CharSet;
	wd:link;
	str:string;
BEGIN
	IF (wFirst^=originalFirst) AND (wTail^=originalTail) THEN
		ReadWord(str,firstSet,tailSet)
	ELSE
		ChangeDefinition(wCharSet,HandlePackage);
		Reduce(wFirst^);
		ExtractPacked(result,first);
		Reduce(wTail^);
		ExtractPacked(result,tail);
		ReadWord(str,first^,tail^)
	END;
	IF str[0]=0C THEN
		result:=Failure
	ELSE
		wd:=FindWord(str);
		IF wd=NIL THEN
			ALLOCATE(strPtr,Str.Length(str)+1);
			Str.Copy(strPtr^,str);
			MakeDef(result,wIdentifier);
			DefineWord(wd,strPtr^,result);
			AddEnv(wd^,wDescription,DefEntry(wd));
			strPtr:=NIL
		END;
		NewLayer(DefEntry(wd));
		result:=wMeaning^
	END
END ParseIdentifier;
	
PROCEDURE ParseString;
VAR
	ch,between:CHAR;
	str:string;
	length:CARDINAL;
BEGIN
	ReadChar(between);
	IF (between="'") OR (between='"') THEN
		length:=0;
		ReadChar(ch);
		WHILE (ch#between) AND (ch#CHR(13)) AND (length<MaxStrLength) DO
			str[length]:=ch;
			INC(length);
			ReadChar(ch)
		END;
		IF ch=between THEN
			str[length]:=0C;
			ALLOCATE(strPtr,length+1);
			Str.Copy(strPtr^,str);
			MakeString(result,wString,strPtr);
			strPtr:=NIL;
			RETURN
	  	END
  	END;
	result:=Failure
END ParseString;

PROCEDURE ParseCustom;
VAR
	wprop:closure;
BEGIN
	ParseIdentifier;
	IF Root(result)#wFail THEN
		wprop:=DefEntry(Root(result));
		ChangeDefinition(wFrameGrammar,wStructGrammar^);
		NewLayer(wprop);
		ChangeDefinition(wType,result);
		Reduce(wFrameGrammar^)
	END
END ParseCustom;

PROCEDURE Parse;
VAR
	saveFirstSet,saveTailSet:CharSet;
BEGIN
	StartLayer;
	LinkPrimitive(wSpaces,pSpaces);
	LinkPrimitive(wSequence,ParseSequence);
	LinkPrimitive(wLexSequence,ParseLexSequence);
	LinkPrimitive(wValSequence,ParseValSequence);
	LinkPrimitive(wLexValSequence,ParseLexValSequence);
	LinkPrimitive(wEndSeq,ParseEndSequence);
	LinkPrimitive(wChoice,ParseChoice);
	LinkPrimitive(wOption,ParseOption);
	LinkPrimitive(wChar,ParseTheLetter);
	LinkPrimitive(wString,ParseTheString);

	originalFirst:=wFirst^;
	originalTail:=wTail^;
	Reduce(wFirst^);
	saveFirstSet:=firstSet;
	ExtractPacked(result,firstSet);
	IF Root(result)#wCharSet THEN
		originalFirst:=NIL
	END;
	Reduce(wTail^);
	saveTailSet:=tailSet;
	ExtractPacked(result,tailSet);
	IF Root(result)#wCharSet THEN
		originalTail:=NIL
	END;
	LinkPrimitive(wCharSet,ParseTheCharSet);

	LinkPrimitive(wNumGrammar,ParseNumber);
	LinkPrimitive(wCharGrammar,ParseChar);
	LinkPrimitive(wStrGrammar,ParseString);
	LinkPrimitive(wCharSetGrammar,ParseCharSET);
	LinkPrimitive(wIdentGrammar,ParseIdentifier);
	LinkPrimitive(wCustomGrammar,ParseCustom);
	ChangeDefinition(wFrameGrammar,Failure);
	pSpaces;
	ParsePrimitive;
	PopLayer;
	originalFirst:=EmptyClosure;
	originalTail:=EmptyClosure;
	IF Root(result)=wFail THEN
		ReportError;
		MakePacked(result,wError,SyntaxError)
	ELSE
		ChangeDefinition(wStruct,result);
		Reduce(result)
	END;
END Parse;

PROCEDURE pParse;
VAR
	filename:POINTER TO string;
	newFile:BOOLEAN;
BEGIN
	Reduce(wFile^);
	newFile:=(Root(result)=wString);
	IF newFile THEN
		ExtractPacked(result,filename);
		IF NOT OpenInput(filename^) THEN
			MakePacked(result,wError,IOError);
			RETURN
		END;
		LinkDef(wFile,wUndefined)
	END;
	NewDictionary;
	Parse;
	OldDictionary;
	IF newFile THEN
		CloseInput
	END
END pParse;

PROCEDURE MarkInternals;
BEGIN
	MarkString(strPtr);
	MarkClosure(originalFirst);
	MarkClosure(originalTail)
END MarkInternals;

BEGIN
	strPtr:=NIL;
	originalFirst:=EmptyClosure;
	originalTail:=EmptyClosure;
	AddMarker(MarkInternals);
	AddPrimWord(wParse,'Parse',pParse)
END Parser.


