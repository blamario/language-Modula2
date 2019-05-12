IMPLEMENTATION MODULE Decoder;

FROM SYSTEM IMPORT TSIZE;
FROM Lib IMPORT IncAddr;
FROM Memory IMPORT ALLOCATE, AddMarker, MarkNeeded;
FROM FIO IMPORT File, Create, Close, Seek, GetPos, WrChar, WrStr, WrLn, WrInt, WrLngHex, IOresult;
FROM Buffers IMPORT output, FlushOut, WriteChars, CharPtr, CharSet;

FROM Machine IMPORT EmptyClosure, link, HandlePackage, Reduce, Envelope, Root, result;
FROM Machine IMPORT wPackage, tempDef, MakePrimitive, MakeDef, MakePacked, ExtractPacked;
FROM Machine IMPORT SaveDefinition, NewLayer, StartLayer, PopLayer, Equal;
FROM Machine IMPORT Copy, RemoveEnv, MarkLink, Join;

FROM Library IMPORT wChar, wCharSet, wString, wNumber, wError, errorCodes;
FROM Library IMPORT wStruct, wProperty, wValue, wFile, wDescription;
FROM Library IMPORT wAddProp, wAddValProp;

FROM Grammars IMPORT wSequence, wLexSequence, wValSequence, wLexValSequence;
FROM Grammars IMPORT wEndSeq, wChoice, wOption;
FROM Grammars IMPORT wDummy, wFail, wDone, wDiscard, wRaise, wGrammar, wNext;
FROM Grammars IMPORT wSeparator, wFrameGrammar, wCustomGrammar;
FROM Grammars IMPORT wFirst, wTail, wIdentGrammar, wIdentifier, wCharSetGrammar;
FROM Grammars IMPORT wCharGrammar, wStrGrammar, wNumGrammar, wErrorGrammar, wPackageGrammar;
FROM Grammars IMPORT Failure, Confirmation, HoldDummy;

FROM Names IMPORT DefName, DefEntry, wName, wMeaning;
FROM Names IMPORT AddPrimWord;

TYPE
	PassPtr=POINTER TO PassPoint;
	PassPoint=RECORD
		grammar,statement:closure;
		next:PassPtr
	END;

VAR
	wStatement:link;
	oldChar, oldString, oldNumber, oldError, oldRoute:closure;
	separated:BOOLEAN;
	path:PassPtr;

PROCEDURE PopPath;
BEGIN
	path:=path^.next
END PopPath;

PROCEDURE PathClosed():BOOLEAN;
VAR
	follow:PassPtr;
BEGIN
	follow:=path;
	WHILE (follow#NIL) AND
			((follow^.grammar#wGrammar^) OR (follow^.statement#wStatement^)) DO
		follow:=follow^.next
	END;
	IF follow=NIL THEN
		NEW(follow);
		follow^.grammar:=wGrammar^;
		follow^.statement:=wStatement^;
		follow^.next:=path;
		path:=follow;
		RETURN FALSE
	ELSE
		RETURN TRUE
	END
END PathClosed;

PROCEDURE PhraseTheLetter;
VAR
	chExpect,chIs:CHAR;
BEGIN
	ExtractPacked(wPackage^,chExpect);
	IF wStatement^#EmptyClosure THEN
		SaveDefinition(wChar);
		wChar^:=HandlePackage;
		Reduce(wStatement^);
		ExtractPacked(result,chIs);
		IF chExpect#chIs THEN
			result:=Failure;
			RETURN
		END
	END;
	WrChar(output,chExpect);
	result:=Confirmation
END PhraseTheLetter;

PROCEDURE PhraseTheString;
VAR
	str:CharPtr;
BEGIN
	IF wStatement^#EmptyClosure THEN
		SaveDefinition(wString);
		wString^:=HandlePackage;
		Reduce(wStatement^);
		IF NOT Equal(wPackage^,result) THEN
			result:=Failure;
			RETURN
		END
	END;
	ExtractPacked(wPackage^,str);
	WriteChars(str);
	result:=Confirmation
END PhraseTheString;

PROCEDURE PhraseTheCharSet;
VAR
	s:POINTER TO CharSet;
	ch:CHAR;
BEGIN
	SaveDefinition(wChar);
	wChar^:=HandlePackage;
	Reduce(wStatement^);
	IF Root(result)=wChar THEN
		ExtractPacked(result,ch);
		ExtractPacked(wPackage^,s);
		IF ch IN s^ THEN
			WrChar(output,ch);
			result:=Confirmation
		ELSE
			result:=Failure
		END
	ELSE
		result:=Failure
	END
END PhraseTheCharSet;

PROCEDURE PhraseChoice;
BEGIN
	Reduce(wGrammar^);
	IF Root(result)=wFail THEN
		Reduce(wNext^)
	END
END PhraseChoice;

PROCEDURE PhraseOption;
BEGIN
	Reduce(wGrammar^);
	IF Root(result)=wFail THEN
		result:=HoldDummy
	END
END PhraseOption;

PROCEDURE PhraseSeqPrimitive(separate:BOOLEAN);
VAR
	down:closure;
	downPtr:link;
	oldPos:LONGCARD;
BEGIN
	downPtr:=Root(wProperty^);
	oldPos:=GetPos(output);
	SaveDefinition(wStatement);
	StartLayer;
	SaveDefinition(wStatement);
	IF downPtr#wDiscard THEN
		IF (downPtr#wRaise) THEN
			StartLayer;
			SaveDefinition(downPtr);
			downPtr^:=EmptyClosure;
			NewLayer(wStatement^);
			down:=downPtr^;
			PopLayer;
			IF down=EmptyClosure THEN
				result:=Failure;
				PopLayer;
				RETURN
			END;
			wStatement^:=down
		END
	ELSE
		wStatement^:=EmptyClosure
	END;
	IF PathClosed() THEN
		result:=Failure;
		RETURN
	END;
	separated:=FALSE;
	Reduce(wGrammar^);
	PopPath;
	PopLayer;
	IF Root(result)#wFail THEN
(*
		IF (Root(wProperty^)=wRaise) AND (Root(result)=wDone) THEN
			MakeDef(tempDef,wDummy);
			Join(tempDef,wStatement^);
			wStatement^:=tempDef
		END;
*)
		IF separate AND (GetPos(output)>oldPos) AND NOT separated THEN
			StartLayer;
			SaveDefinition(wChar);
			SaveDefinition(wString);
			SaveDefinition(wStatement);
			MakePrimitive(wChar^,PhraseTheLetter);
			MakePrimitive(wString^,PhraseTheString);
			wStatement^:=EmptyClosure;
			Reduce(wSeparator^);
			PopLayer;
			separated:=TRUE
		END;
		Reduce(wNext^);
		IF Root(result)=wFail THEN
			Seek(output,oldPos)
		END
	END	
END PhraseSeqPrimitive;

PROCEDURE PhraseSequence;
BEGIN
	PhraseSeqPrimitive(TRUE)
END PhraseSequence;

PROCEDURE PhraseLexSequence;
BEGIN
	PhraseSeqPrimitive(FALSE)
END PhraseLexSequence;

PROCEDURE PhraseEndSequence;
BEGIN
	IF (Root(wStruct^)=wDummy) OR (Root(wStatement^)=Root(wStruct^)) THEN
		result:=Confirmation
	ELSE
		result:=Failure
	END
END PhraseEndSequence;

PROCEDURE PhraseNumber;
VAR
	num:INTEGER;
BEGIN
	IF Root(wStatement^)#wNumber THEN
		result:=Failure;
		RETURN
	END;
	SaveDefinition(wNumber);
	wNumber^:=HandlePackage;
	Reduce(wStatement^);
	ExtractPacked(result,num);
	WrInt(output,num,0);
	result:=Confirmation
END PhraseNumber;

PROCEDURE PhrasePackage;
VAR
	contents:LONGCARD;
BEGIN
	WrChar(output,'[');
	ExtractPacked(wStatement^,contents);
	WrLngHex(output,contents,0);
	WrChar(output,']')
END PhrasePackage;

PROCEDURE PhraseChar;
VAR
	ch:CHAR;
BEGIN
	IF Root(wStatement^)#wChar THEN
		result:=Failure;
		RETURN
	END;
	SaveDefinition(wChar);
	wChar^:=HandlePackage;
	Reduce(wStatement^);
	ExtractPacked(result,ch);
	WrChar(output, "'");
	WrChar(output,ch);
	WrChar(output, "'");
END PhraseChar;

PROCEDURE PhraseCharSET;
VAR
	s:SET OF CHAR;
	ch:CHAR;
	first:BOOLEAN;
BEGIN
	IF Root(wStatement^)=wCharSet THEN
		SaveDefinition(wCharSet);
		wCharSet^:=HandlePackage;
		Reduce(wStatement^);
		ExtractPacked(result,s);
		ch:=MIN(CHAR);
		WrChar(output,'{');
		first:=TRUE;
		LOOP
			IF ch IN s THEN
				IF first THEN
					first:=FALSE
				ELSE
					WrChar(output,',')
				END;
				IF (ch=' ') OR (ch='}') OR (ch='{') OR (ch='\') THEN
					WrChar(output,'\')
				END;
				WrChar(output,ch);
				INC(ch);
				IF ch IN s THEN
					REPEAT
						INC(ch)
					UNTIL NOT (ch IN s);
					DEC(ch);
					WrChar(output,'-');
					IF (ch=' ') OR (ch='}') OR (ch='{') OR (ch='\') THEN
						WrChar(output,'\')
					END;
					WrChar(output,ch);
					INC(ch)
				END
			ELSIF ch<MAX(CHAR) THEN
				INC(ch)
			ELSE
				EXIT
			END
		END;
		WrChar(output,'}')
	ELSE
		result:=Failure
	END
END PhraseCharSET;

PROCEDURE PhraseIdent;
VAR
	string:POINTER TO CHAR;
	s:POINTER TO SET OF CHAR;
BEGIN
	IF Root(wStatement^)=wIdentifier THEN
		NewLayer(wStatement^);
		SaveDefinition(wString);
		wString^:=HandlePackage;
		Reduce(wDescription^);
		ExtractPacked(result,string)
	ELSE
		string:=DefName(Root(wStatement^))
	END;
	SaveDefinition(wCharSet);
	wCharSet^:=HandlePackage;
	Reduce(wFirst^);
	ExtractPacked(result,s);
	IF string^ IN s^ THEN
		Reduce(wTail^);
		ExtractPacked(result,s);
		REPEAT
			WrChar(output,string^);
			IncAddr(string,1)
		UNTIL NOT (string^ IN s^) OR (string^=0C);
		IF string^=0C THEN
			result:=Confirmation;
			RETURN
		END
	END;
	result:=Failure
END PhraseIdent;
	
PROCEDURE PhraseString;
VAR
	string:ADDRESS;
BEGIN
	IF Root(wStatement^)#wString THEN
		result:=Failure;
		RETURN
	END;
	SaveDefinition(wString);
	wString^:=HandlePackage;
	Reduce(wStatement^);
	ExtractPacked(result,string);
	WrChar(output,'"');
	WriteChars(string);
	WrChar(output,'"');
	result:=Confirmation
END PhraseString;
	
PROCEDURE PhraseError;
VAR
	err:errorCodes;
BEGIN
	IF Root(wStatement^)#wError THEN
		result:=Failure;
		RETURN
	END;
	SaveDefinition(wError);
	wString^:=HandlePackage;
	Reduce(wStatement^);
	ExtractPacked(result,err);
	CASE err OF
		NotLogicalType:WrStr(output,'Not the logical type!')
		|NotNumberType:WrStr(output,'Not the number type!')
		|NotStringType:WrStr(output,'Not the string type!')
		|IOError:WrStr(output,'(R) Tape loading error!')
		|SyntaxError:WrStr(output,'Syntax error!')
		|NotFound:WrStr(output,'Undefined word meaning!')
	END;
	WrLn(output);
	result:=Confirmation
END PhraseError;

PROCEDURE PhraseCustom;
FORWARD;

PROCEDURE PhraseStd;
VAR
	oldPos:LONGCARD;
BEGIN
	oldPos:=GetPos(output);
	SaveDefinition(wStatement);
	WriteChars(DefName(Root(wStatement^)));
(*
	IF Root(wFrameGrammar^)#wFail THEN
		StartLayer;
		SaveDefinition(wGrammar);
		wGrammar^:=wFrameGrammar^;
		PhraseGrammar;
		PopLayer;
		IF Root(result)#wFail THEN
			RETURN
		END
	END;
*)
	Envelope(result,wStatement^,wAddProp,wAddValProp,wDone,wProperty,wValue,wStruct);
	WrChar(output,'(');
	LOOP
		IF Root(result)=wDone THEN
			EXIT
		END;
		StartLayer;
		NewLayer(result);
		WriteChars(DefName(Root(wProperty^)));
		IF Root(result)=wAddValProp THEN
			WrChar(output,':')
		END;
		WrChar(output,'=');
		wStatement^:=wValue^;
		PhraseCustom;
		IF Root(result)=wFail THEN
			PopLayer;
			EXIT
		END;
		result:=wStruct^;
		PopLayer;
		IF Root(result)#wDone THEN
			WrChar(output,',')
		END
	END;
	IF Root(result)=wFail THEN
		Seek(output,oldPos)
	ELSE
		WrChar(output,')')
	END
END PhraseStd;

PROCEDURE PhraseCustom;
VAR
	prop:closure;
BEGIN
	SaveDefinition(wCustomGrammar);
	MakePrimitive(wCustomGrammar^,PhraseStd);
	SaveDefinition(wFrameGrammar);
	wFrameGrammar^:=Failure;
	prop:=DefEntry(Root(wStatement^));
	StartLayer;
	NewLayer(prop);
	result:=wCustomGrammar^;
	PopLayer;
	SaveDefinition(wGrammar);
	wGrammar^:=result;
	Reduce(result)
END PhraseCustom;

PROCEDURE PhraseGrammar;
BEGIN
	SaveDefinition(wSequence);
	MakePrimitive(wSequence^,PhraseSequence);
	SaveDefinition(wValSequence);
	MakePrimitive(wValSequence^,PhraseSequence);
	SaveDefinition(wLexSequence);
	MakePrimitive(wLexSequence^,PhraseSequence);
	SaveDefinition(wLexValSequence);
	MakePrimitive(wLexValSequence^,PhraseSequence);
	SaveDefinition(wEndSeq);
	MakePrimitive(wEndSeq^,PhraseEndSequence);
	SaveDefinition(wChoice);
	MakePrimitive(wChoice^,PhraseChoice);
	SaveDefinition(wOption);
	MakePrimitive(wOption^,PhraseOption);
	SaveDefinition(wChar);
	MakePrimitive(wChar^,PhraseTheLetter);
	SaveDefinition(wString);
	MakePrimitive(wString^,PhraseTheString);
	SaveDefinition(wCharSet);
	MakePrimitive(wCharSet^,PhraseTheCharSet);
	SaveDefinition(wPackageGrammar);
	MakePrimitive(wPackageGrammar^,PhrasePackage);
	SaveDefinition(wCharGrammar);
	MakePrimitive(wCharGrammar^,PhraseChar);
	SaveDefinition(wCharSetGrammar);
	MakePrimitive(wCharSetGrammar^,PhraseCharSET);
	SaveDefinition(wIdentGrammar);
	MakePrimitive(wIdentGrammar^,PhraseIdent);
	SaveDefinition(wStrGrammar);
	MakePrimitive(wStrGrammar^,PhraseString);
	SaveDefinition(wNumGrammar);
	MakePrimitive(wNumGrammar^,PhraseNumber);
	SaveDefinition(wErrorGrammar);
	MakePrimitive(wErrorGrammar^,PhraseError);
	SaveDefinition(wCustomGrammar);
	MakePrimitive(wCustomGrammar^,PhraseCustom);
	SaveDefinition(wStatement);
	wStatement^:=wStruct^;
	
	Reduce(wGrammar^);
	path:=NIL
END PhraseGrammar;

PROCEDURE WriteGrammar;
CONST
	FormalLength=1000;
VAR
	filename:POINTER TO ARRAY [0..FormalLength] OF CHAR;
	oldHandle:File;
BEGIN
	Reduce(wFile^);
	oldHandle:=output;
	IF Root(result)=wString THEN
		ExtractPacked(result,filename);
		IF filename^[0]#0C THEN
			output:=Create(filename^);
			IF IOresult()#0 THEN
				MakePacked(result,wError,IOError);
				output:=oldHandle;
				RETURN
			END
		END
	END;
	Seek(output,0);
	PhraseGrammar;
	IF Root(result)#wFail THEN
		FlushOut
	END;
	IF output#oldHandle THEN
		Close(output);
		output:=oldHandle
	END
END WriteGrammar;

PROCEDURE Write;
BEGIN
	SaveDefinition(wGrammar);
	MakePrimitive(wGrammar^,PhraseCustom);
	WriteGrammar
END Write;

PROCEDURE MarkPath;
VAR
	follow:PassPtr;
	fresh:BOOLEAN;
BEGIN
	MarkLink(wStatement);
	follow:=path;
	WHILE follow#NIL DO
		MarkNeeded(follow,TSIZE(PassPoint),fresh);
		follow:=follow^.next
	END
END MarkPath;

BEGIN
	path:=NIL;
	NEW(wStatement);
	wStatement^:=EmptyClosure;
	AddMarker(MarkPath);
	AddPrimWord(wWrite,'Write',Write);
	AddPrimWord(wWriteGrammar,'WriteGrammar',WriteGrammar)
END Decoder.
