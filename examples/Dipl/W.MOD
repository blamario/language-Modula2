MODULE W;

FROM IO IMPORT WrStr, WrLn, WrCard, EndOfRd, RdChar;
IMPORT IO;
FROM Machine IMPORT link, Root, result;
FROM Machine IMPORT Reduce, StartLayer, PopLayer, SaveDefinition;
FROM Machine IMPORT MakeDef, MakePacked, MakeString, ExtractPacked;
FROM Library IMPORT wStruct, wFile, wAncestor;
FROM Library IMPORT wString, wError, errorCodes, wTrue, wUndefined;
FROM Names IMPORT AddAtom, AddPrimWord, NewDictionary, OldDictionary;
FROM Buffers IMPORT ReportError, OpenInput, CloseInput;
FROM Parser IMPORT Parse;
FROM Decoder IMPORT wWrite;
FROM Grammars IMPORT wGrammar, wFail, wSentence;
(* FROM Graph IMPORT SetVideoMode, InitGraph; *)
IMPORT PMD;

VAR
	wInterpret,wQuit,wLoad:link;
	level:CARDINAL;

(*# data(stack_size => 0FF00H) *)
	
PROCEDURE pInterpret;
VAR
	ch,empty:CHAR;
BEGIN
	empty:=0C;
	INC(level);
	LOOP
		MakeString(wFile^,wString,ADR(empty));
		WrLn;
		WrStr('Reduce[');
		WrCard(level,0);
		WrStr(']>');
		Reduce(wLoad^);
		WHILE NOT EndOfRd(FALSE) DO
			ch:=RdChar()
		END;
		IF Root(result)=wQuit THEN
			MakeDef(result,wTrue);
			EXIT
		ELSE
			StartLayer;
			SaveDefinition(wStruct);
			wStruct^:=result;
			Reduce(wWrite^);
			IF Root(result)=wFail THEN
				WrStr('Output error!')
			END;
			PopLayer
		END
	END;
	DEC(level)
END pInterpret;

PROCEDURE pLoad;
VAR
	filename:ARRAY [0..30] OF CHAR;
	newFile:BOOLEAN;
	ch:CHAR;
BEGIN
	Reduce(wFile^);
	newFile:=(Root(result)=wString);
	IF newFile THEN
		ExtractPacked(result,filename);
		IF NOT OpenInput(filename) THEN
			MakePacked(result,wError,IOError);
			RETURN
		END;
      SaveDefinition(wFile);
      MakeDef(wFile^,wUndefined)
	END;
	NewDictionary;
	StartLayer;
	SaveDefinition(wGrammar);
	wGrammar^:=wSentence^;
	Parse;
	PopLayer;
	SaveDefinition(wAncestor);
	wAncestor^:=result;
	Reduce(result);
	OldDictionary;
	IF newFile THEN
		CloseInput
	END
END pLoad;

BEGIN
	level:=0;
	AddAtom(wQuit,'Quit');
	AddPrimWord(wInterpret, 'Interpret', pInterpret);
	AddPrimWord(wLoad, 'Load', pLoad);
(*	InitGraph;
	IF NOT SetVideoMode(7) THEN
		WrStr('Prebacivanje u tekst mod nije uspelo!')
	END;
*)
	pInterpret
END W.
