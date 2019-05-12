IMPLEMENTATION MODULE Grammars;

(*# call(o_a_copy=>off, o_a_size=>off) *)

FROM Memory IMPORT AddMarker;

FROM Machine IMPORT EmptyClosure, link, HandlePackage, tempDef, AddEnv;
FROM Machine IMPORT MakeDef, MakePrimitive, MakeString, MakePacked;
FROM Machine IMPORT closure, handlerType, Build, MarkClosure;

FROM Library IMPORT wChar, wCharSet, wString, wNumber, wError, wVain;
FROM Library IMPORT wAddProp, wAddValProp, wJoin, wQuote, wCopy, wFind, wDummy;
FROM Library IMPORT wType, wStruct, wProperty, wValue, wDescription;

FROM Names IMPORT DefineWord, AddArgument, AddAtom, DefEntry, wName;

TYPE CharSet=SET OF CHAR;

PROCEDURE ChrDef(ch:CHAR):closure;
VAR
	result:closure;
BEGIN
	MakePacked(result,wChar,ch);
	RETURN result
END ChrDef;

PROCEDURE StrDef(str:ARRAY OF CHAR):closure;
VAR
	result:closure;
BEGIN
	MakeString(result,wString,ADR(str));
	RETURN result
END StrDef;

PROCEDURE Prim(h:handlerType):closure;
VAR
	result:closure;
BEGIN
	MakePrimitive(result,h);
	RETURN result
END Prim;

PROCEDURE Def(root:link):closure;
VAR
	result:closure;
BEGIN
	MakeDef(result,root);
	RETURN result
END Def;

PROCEDURE Obj(str:closure; prop:link; value:closure):closure;
BEGIN
	AddEnv(str,prop,value);
	RETURN str
END Obj;

PROCEDURE Seq(pp:link; g,n:closure):closure;
BEGIN
	RETURN Obj(Obj(Obj(Def(wSequence),
		wProperty,Def(pp)),
		wGrammar,g),
		wNext,n)
END Seq;

PROCEDURE ValSeq(pp:link; g,n:closure):closure;
BEGIN
	RETURN Obj(Obj(Obj(Def(wValSequence),
		wProperty,Def(pp)),
		wGrammar,g),
		wNext,n)
END ValSeq;

PROCEDURE EndSeq(root:link):closure;
BEGIN
	RETURN Obj(Def(wEndSeq), wStruct, Def(root))
END EndSeq;

PROCEDURE Option(g:closure):closure;
BEGIN
	RETURN Obj(Def(wOption), wGrammar, g)
END Option;

PROCEDURE Choose(g,n:closure):closure;
BEGIN
	RETURN Obj(Obj(Def(wChoice),
		wGrammar,g),
		wNext,n)
END Choose;

PROCEDURE MarkFailure;
BEGIN
	MarkClosure(Failure);
	MarkClosure(Confirmation);
	MarkClosure(HoldDummy)
END MarkFailure;

VAR
	entry:closure;	(* unmarked temporary, used only during initialisation *)

BEGIN
	AddAtom(wFail, 'Fail');
	MakeDef(Failure,wFail);
	AddAtom(wDone, 'Done');
	MakeDef(Confirmation,wDone);
	MakeDef(HoldDummy,wDummy);
	AddMarker(MarkFailure);

	AddAtom(wDiscard, 'Discard');
	AddAtom(wRaise, 'Raise');
	AddArgument(wGrammar, 'Grammar');
	AddArgument(wNext, 'Next');
	DefineWord(wSeparator, 'Separator', HandlePackage);
	
	MakePacked(tempDef,wCharSet,CharSet{'A'..'Z','a'..'z'});
	DefineWord(wFirst, 'First', tempDef);
	MakePacked(tempDef,wCharSet,CharSet{'0'..'9','A'..'Z','a'..'z'});
	DefineWord(wTail, 'Tail', tempDef);

	DefineWord(wFrameGrammar, 'FrameGrammar', Failure);
	AddAtom(wCustomGrammar, 'CustomGrammar');
	AddAtom(wPackageGrammar, 'PackageGrammar');
	AddAtom(wNumGrammar, 'NumGrammar');
	AddAtom(wCharSetGrammar, 'CharSetGrammar');
	AddAtom(wCharGrammar, 'CharGrammar');
	AddAtom(wErrorGrammar, 'ErrorGrammar');
	AddAtom(wStrGrammar, 'StrGrammar');
	AddAtom(wIdentGrammar, 'IdentGrammar');
	DefineWord(wIdentifier, 'Identifier', HandlePackage);
	DefineWord(wSpaceChars, 'SpaceChars', EmptyClosure);
	MakePacked(wSpaceChars^,wCharSet,CharSet{' ',15C,12C,11C}); (* space,LF,CR,TAB *)
	AddAtom(wSpaces, 'Spaces');
	DefineWord(wComment, 'Comment', Failure);

	MakeDef(tempDef,wVain);
	DefineWord(wSequence, 'Seq', tempDef);
	DefineWord(wLexSequence, 'LexSeq', tempDef);
	DefineWord(wValSequence, 'ValSeq', tempDef);
	DefineWord(wLexValSequence, 'LexValSeq', tempDef);
	DefineWord(wEndSeq, 'EndSeq', tempDef);
	DefineWord(wChoice, 'Choice', tempDef);
	DefineWord(wOption, 'Option', tempDef);
	
	MakeDef(tempDef,wCharGrammar);
	entry:=DefEntry(wChar);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	MakeDef(tempDef,wCharSetGrammar);
	entry:=DefEntry(wCharSet);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	MakeDef(tempDef,wNumGrammar);
	entry:=DefEntry(wNumber);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	MakeDef(tempDef,wStrGrammar);
	entry:=DefEntry(wString);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	MakeDef(tempDef,wErrorGrammar);
	entry:=DefEntry(wError);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	MakeDef(tempDef,wIdentGrammar);
	entry:=DefEntry(wIdentifier);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	entry:=DefEntry(wPacked);
	MakeDef(tempDef,wPackageGrammar);
	AddEnv(entry,wCustomGrammar,tempDef);
	
	DefineWord(wSentence, 'Sentence', EmptyClosure);
	DefineWord(wEnvGrammar, 'EnvGrammar', EmptyClosure);

	wEnvGrammar^:=
		Seq(wProperty,Def(wIdentGrammar),
		Seq(wRaise, Choose(
			Seq(wDiscard, ChrDef('='),
			EndSeq(wAddProp)),

			Seq(wDiscard, StrDef(':='),
			EndSeq(wAddValProp))),
		ValSeq(wValue, Def(wSentence),
		ValSeq(wStruct,
			Option(
				Seq(wDiscard, ChrDef(','),
				Seq(wRaise, Def(wEnvGrammar),
				EndSeq(wDummy)))),
		EndSeq(wDummy)))));

(* StructGrammar::= Join(Struct=IdentGrammar '(' Description:=[EnvGrammar] ')'). *)
	DefineWord(wStructGrammar, 'StructGrammar',
		Seq(wStruct,Obj(Def(wCopy),wProperty,Def(wType)),
		Seq(wDiscard, ChrDef('('),
		Seq(wRaise,
			Option(
				ValSeq(wDescription, Def(wEnvGrammar),
				EndSeq(wJoin))),
		Seq(wDiscard, ChrDef(')'),
		EndSeq(wQuote))))));

(* Sentence::= Custom|Char|CharSet|String|Number. *)
	wSentence^:=
		Choose(Def(wCustomGrammar),
		Choose(Def(wCharGrammar),
		Choose(Def(wStrGrammar),
		Choose(Def(wCharSetGrammar),
		Def(wNumGrammar)))));
	
	tempDef:=EmptyClosure
END Grammars.

(*
EnvGrammar::= Property:=IdentGrammar() Raise=('=' :AddProperty() | ":=" :AddValuedProperty())
		Value:=Sentence(), Struct:=[',' Raise=EnvGrammar() :Dummy()]: Dummy().
StructGrammar::= Property:=IdentGrammar() '(' Raise=[Description:=EnvGrammar() :Join()] ')' :Quote().
Sentence::= Number()|Char()|String()|CharSET()|StructGrammar()|CommonGrammar().
InputGrammar::= Struct:=Sentence() :Struct().
*)
