IMPLEMENTATION MODULE Names;

FROM SYSTEM IMPORT TSIZE;
FROM Lib IMPORT AddAddr, SubAddr, HashString;
FROM IO IMPORT WrStrAdj, WrLn;
FROM Str IMPORT Caps;
FROM Memory IMPORT ALLOCATE, MarkNeeded, AddMarker, DropMarker;
FROM Machine IMPORT link, closure, parent, tempDef;
FROM Machine IMPORT EmptyClosure, MarkClosure, MarkString;
FROM Machine IMPORT wType, Build, HandlePackage, HandleParent, SaveDefinition;
FROM Machine IMPORT AddEnv, RemoveEnv, MakeDef, MakePrimitive, MakeString;
CONST
	FormalMaximum=10000;
	MaxEntries=64;
	LastEntry=MaxEntries-1;
TYPE
	wordPtr=POINTER TO wordType;
	wordType=RECORD
					next:wordPtr;
					def:closure;
					name:POINTER TO ARRAY [0..FormalMaximum] OF CHAR;
					entry:closure;
				END;
	dictionary=POINTER TO dictRec;
	dictRec= RECORD
					info:ARRAY [0..LastEntry] OF wordPtr;
					next:dictionary
				 END;
VAR
	i:CARDINAL;
	top:dictionary;
	UndefinedMeaning:closure;
	
PROCEDURE DefWord(l:link):wordPtr;
BEGIN
	RETURN wordPtr(SubAddr(l,TSIZE(wordPtr)))
END DefWord;

PROCEDURE vList;
CONST
	WordsInRow=3;
	MaxLength=25;
VAR
	follow:wordPtr;
	i,counter:CARDINAL;
BEGIN
	counter:=1;
	FOR i:=0 TO LastEntry DO
		follow:=top^.info[i];
		WHILE follow#NIL DO
			DEC(counter);
			IF counter=0 THEN
				counter:=WordsInRow;
				WrLn
			END;
			WrStrAdj(follow^.name^,-MaxLength);
			follow:=follow^.next
		END
	END;
	WrLn
END vList;

PROCEDURE NewDictionary;
VAR
	d:dictionary;
	i:CARDINAL;
BEGIN
	NEW(d);
	FOR i:=0 TO LastEntry DO
		d^.info[i]:=top^.info[i]
	END;
	d^.next:=top;
	top:=d
END NewDictionary;

PROCEDURE OldDictionary;
BEGIN
	top:=top^.next
END OldDictionary;

PROCEDURE DefineWord(VAR worDef:link; wordName:ARRAY OF CHAR;
								wordMeaning:closure);
VAR
	newWord:wordPtr;
	hash:CARDINAL;
BEGIN
	hash:=HashString(wordName,MaxEntries);
	NEW(newWord);
	WITH newWord^ DO
		next:=top^.info[hash];
		top^.info[hash]:=newWord;
		name:=ADR(wordName);
		def:=EmptyClosure;
		entry:=EmptyClosure;
		worDef:=ADR(def);
		MakeDef(entry,wEntry);
		MakeDef(def,worDef);
		AddEnv(entry,wMeaning,def);
		MakeString(def,wString,name);
		AddEnv(entry,wName,def);
		def:=wordMeaning
	END
END DefineWord;

(*
PROCEDURE UndefineWord(l:link);
VAR
	hash:CARDINAL;
BEGIN
	hash:=HashString(DefWord(l)^.name^,MaxEntries);
	top^.info[hash]:=top^.info[hash]^.next
END UndefineWord;

PROCEDURE MoveWord(l:link; fromVoc, toVoc:dictionary);
VAR
	hash:CARDINAL;
	follow:POINTER TO wordPtr;
	wd:wordPtr;
BEGIN
	wd:=DefWord(l);
	hash:=HashString(wd^.name^,MaxEntries);
	IF fromVoc#EmptyDict THEN
		follow:=ADR(fromVoc^.info[hash]);
		WHILE (follow^#wd) AND (follow^#NIL) DO
			follow:=ADR(follow^^.next)
		END;
		IF follow^=wd THEN
			follow^:=follow^^.next
		END
	END;
	wd^.next:=toVoc^.info[hash];
	toVoc^.info[hash]:=wd
END MoveWord;

PROCEDURE Forget(dp:link):BOOLEAN;
VAR
	follow,target:wordPtr;
BEGIN
	target:=wordPtr(dp);
	follow:=lastWord;
	WHILE (follow#NIL) AND (follow#target) DO
		follow:=follow^.next
	END;
	IF follow=NIL THEN
		RETURN FALSE
	ELSE
		lastWord:=follow^.next;
		RETURN TRUE
	END
END Forget;
*)

PROCEDURE AddPrimWord(VAR worDef:link; wordName:ARRAY OF CHAR;
								handler:handlerType);
BEGIN
	MakePrimitive(tempDef,handler);
	DefineWord(worDef,wordName,tempDef);
	tempDef:=EmptyClosure
END AddPrimWord;

PROCEDURE AddArgument(VAR worDef:link; wordName:ARRAY OF CHAR);
BEGIN
	DefineWord(worDef,wordName,UndefinedMeaning)
END AddArgument;

PROCEDURE AddAtom(VAR worDef:link; wordName:ARRAY OF CHAR);
BEGIN
	AddPrimWord(worDef,wordName,Build);
	MakeDef(tempDef,worDef);
	AddEnv(worDef^,wType,tempDef);
	tempDef:=EmptyClosure
END AddAtom;
	
PROCEDURE MarkWords;
VAR
	i:[0..LastEntry];
	wdCurrent:wordPtr;
	dictFollow:dictionary;
	fresh:BOOLEAN;
BEGIN
	MarkClosure(UndefinedMeaning);
	dictFollow:=top;
	WHILE dictFollow#NIL DO
		MarkNeeded(dictFollow,TSIZE(dictRec),fresh);
		dictFollow:=dictFollow^.next
	END;
	FOR i:=0 TO LastEntry DO
		wdCurrent:=top^.info[i];
		WHILE wdCurrent#NIL DO
			MarkNeeded(wdCurrent,TSIZE(wordType),fresh);
			WITH wdCurrent^ DO
				MarkString(name);
				MarkClosure(def);
				MarkClosure(entry);
				wdCurrent:=next
			END
		END
	END
END MarkWords;

PROCEDURE FindWord(wd:ARRAY OF CHAR):link;
VAR
	follow:wordPtr;
	letter:CARDINAL;
BEGIN
	follow:=top^.info[HashString(wd,MaxEntries)];
	WHILE follow#NIL DO
		IF follow^.name^[0]=wd[0] THEN
			letter:=1;
			WITH follow^ DO
				WHILE (wd[letter]=name^[letter]) AND (name^[letter]#0C) DO
					INC(letter)
				END;
				IF wd[letter]=name^[letter] THEN
					RETURN ADR(def)
				END;
			END
		END;
		follow:=follow^.next
	END;
	RETURN NIL
END FindWord;

(*# call( o_a_copy => on ) *)

PROCEDURE FindWordNoCase(wd:ARRAY OF CHAR):link;
VAR
	follow:wordPtr;
	letter:CARDINAL;
BEGIN
	Caps(wd);
	follow:=top^.info[HashString(wd,MaxEntries)];
	WHILE follow#NIL DO
		IF CAP(follow^.name^[0])=wd[0] THEN
			letter:=1;
			WITH follow^ DO
				WHILE (wd[letter]=CAP(name^[letter])) AND (name^[letter]#0C) DO
					INC(letter)
				END;
				IF wd[letter]=name^[letter] THEN
					RETURN ADR(def)
				END;
			END
		END;
		follow:=follow^.next
	END;
	RETURN NIL
END FindWordNoCase;

PROCEDURE DefName(dp:link):ADDRESS;
TYPE
	AddrPtr=POINTER TO ADDRESS;
BEGIN
	RETURN AddrPtr(AddAddr(dp,TSIZE(closure)))^
END DefName;

PROCEDURE DefEntry(dp:link):closure;
BEGIN
	RETURN link(AddAddr(dp, TSIZE(closure) + TSIZE(ADDRESS)))^
END DefEntry;

PROCEDURE SetDefEntry(dp:link;newEntry:closure);
VAR
	entry:link;
BEGIN
	entry:=link(AddAddr(dp, TSIZE(closure) + TSIZE(ADDRESS)));
	SaveDefinition(entry);
	entry^:=newEntry
END SetDefEntry;

VAR
	name:closure;		(* unmarked temporary, used only during initialisation *)

BEGIN
	AddMarker( MarkWords );
	NEW(top);
	top^.next:=NIL;
	FOR i:=0 TO LastEntry DO
		top^.info[i]:=NIL
	END;

	AddArgument(wEntry, 'Entry');
	tempDef:=DefEntry(wEntry);
	RemoveEnv(tempDef,wMeaning);
	RemoveEnv(tempDef,wName);

	DefineWord(wParent, 'Parent', HandleParent);
	tempDef:=DefEntry(wParent);
	RemoveEnv(tempDef,wMeaning);
	RemoveEnv(tempDef,wName);

	AddAtom(wUndefined, 'Undefined');
	tempDef:=DefEntry(wUndefined);
	RemoveEnv(tempDef,wMeaning);
	RemoveEnv(tempDef,wName);
	MakeDef(UndefinedMeaning,wUndefined);
	parent:= UndefinedMeaning;

	AddArgument(wMeaning,'Meaning');
	tempDef:=DefEntry(wMeaning);
	RemoveEnv(tempDef,wName);

	AddArgument(wName,'Name');

	DefineWord(wString,'STRING',HandlePackage);

	MakeString(name,wString,DefName(wName));
	tempDef:=DefEntry(wName);
	AddEnv(tempDef,wName,name);

	MakeString(name,wString,DefName(wMeaning));
	tempDef:=DefEntry(wMeaning);
	AddEnv(tempDef,wName,name);

	MakeString(name,wString,DefName(wUndefined));
	tempDef:=DefEntry(wUndefined);
	AddEnv(tempDef,wName,name);
	MakeDef(name,wUndefined);
	AddEnv(tempDef,wMeaning,name);

	MakeString(name,wString,DefName(wParent));
	tempDef:=DefEntry(wParent);
	AddEnv(tempDef,wName,name);
	MakeDef(name,wParent);
	AddEnv(tempDef,wMeaning,name);

	MakeString(name,wString,DefName(wEntry));
	tempDef:=DefEntry(wEntry);
	AddEnv(tempDef,wName,name);
	MakeDef(name,wEntry);
	AddEnv(tempDef,wMeaning,name);
	wEntry^:=UndefinedMeaning;

	tempDef:=EmptyClosure
END Names.

