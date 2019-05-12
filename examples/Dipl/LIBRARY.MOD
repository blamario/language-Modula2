IMPLEMENTATION MODULE Library;
FROM Machine IMPORT closure, link, EmptyClosure, result;
FROM Machine IMPORT Reduce, NewLayer, SaveDefinition, StartLayer, PopLayer, debug;
FROM Machine IMPORT AddEnv, AddValuedEnv, RemoveEnv, Copy, Join, Equal, Root;
FROM Machine IMPORT MakeDef, MakePrimitive, MakePacked, ExtractPacked;
FROM Machine IMPORT tempDef, HandlePackage, Build, wPackage;
FROM Machine IMPORT Build, BuildReduced;
FROM Names IMPORT DefineWord, AddArgument, AddPrimWord, AddAtom;
FROM Names IMPORT wName, wMeaning;
FROM Names IMPORT DefEntry, SetDefEntry, FindWord, vList;
FROM Memory IMPORT Collect;

CONST
	FormalLength=1000;

PROCEDURE pGetProp;
VAR
	r:link;
BEGIN
	r:=Root(wProperty^);
	NewLayer(wStruct^);
	result:=r^
END pGetProp;

PROCEDURE pAddProp;
BEGIN
	IF Root(wStruct^)=wError THEN
		result:=wStruct^
	ELSIF Root(wProperty^)=wError THEN
		result:=wProperty^
	ELSIF Root(wValue^)=wError THEN
		result:=wValue^
	ELSE
		Copy(wStruct^,result);
		AddEnv(result,Root(wProperty^),wValue^)
	END
END pAddProp;

PROCEDURE pAddValProp;
BEGIN
	IF Root(wStruct^)=wError THEN
		result:=wStruct^
	ELSIF Root(wProperty^)=wError THEN
		result:=wProperty^
	ELSIF Root(wValue^)=wError THEN
		result:=wValue^
	ELSE
		Copy(wStruct^,result);
		AddValuedEnv(result,Root(wProperty^),wValue^)
	END
END pAddValProp;

PROCEDURE pRemProp;
BEGIN
	Copy(wStruct^,result);
	RemoveEnv(result,Root(wProperty^))
END pRemProp;

PROCEDURE pJoin;
BEGIN
	IF Root(wStruct^)=wError THEN
		result:=wStruct^
	ELSIF Root(wDescription^)=wError THEN
		result:=wDescription^
	ELSE
		Copy(wStruct^,result);
		Join(result,wDescription^)
	END
END pJoin;

PROCEDURE pCopy;
BEGIN
	result:=Root(wProperty^)^
END pCopy;

PROCEDURE pQuote;
BEGIN
	result:=wStruct^
END pQuote;

PROCEDURE pVain;
BEGIN
	result:=wAncestor^
END pVain;

PROCEDURE pGetType;
BEGIN
	MakeDef(result,Root(wStruct^))
END pGetType;

PROCEDURE pIsOfClass;
BEGIN
	IF Root(wStruct^)=Root(wType^) THEN
		MakeDef(result,wTrue)
	ELSE
		MakeDef(result,wFalse)
	END
END pIsOfClass;

PROCEDURE pEqual;
BEGIN
	IF Equal(wArg1^,wArg2^) THEN
		MakeDef(result,wTrue)
	ELSE
		MakeDef(result,wFalse)
	END
END pEqual;

PROCEDURE pNot;
VAR
	l:BOOLEAN;
BEGIN
	IF Root(wArg1^)=wTrue THEN
		MakeDef(result,wFalse)
	ELSIF Root(wTest^)=wFalse THEN
		MakeDef(result,wTrue)
	ELSE
		MakePacked(result,wError,NotLogicalType)
	END
END pNot;

PROCEDURE pAnd;
VAR
	l:BOOLEAN;
BEGIN
	IF Root(wArg1^)=wTrue THEN
		Reduce(wArg2^)
	ELSIF Root(wTest^)=wFalse THEN
		MakeDef(result,wFalse)
	ELSE
		MakePacked(result,wError,NotLogicalType)
	END
END pAnd;

PROCEDURE pOr;
VAR
	l:BOOLEAN;
BEGIN
	IF Root(wArg1^)=wFalse THEN
		Reduce(wArg2^)
	ELSIF Root(wTest^)=wTrue THEN
		MakeDef(result,wTrue)
	ELSE
		MakePacked(result,wError,NotLogicalType)
	END
END pOr;

PROCEDURE pIf;
VAR
	l:BOOLEAN;
BEGIN
	Reduce(wTest^);
	IF Root(result)=wTrue THEN
		Reduce(wYes^)
	ELSIF Root(wTest^)=wFalse THEN
		Reduce(wNo^)
	ELSE
		MakePacked(result,wError,NotLogicalType)
	END
END pIf;

PROCEDURE ExtractNumbers(VAR x,y:INTEGER):BOOLEAN;
BEGIN
	Reduce(wArg1^);
	IF Root(result)#wNumber THEN
		IF Root(result)#wError THEN
			MakePacked(result,wError,NotNumberType)
		END;
		RETURN FALSE
	END;
	ExtractPacked(result,x);
	
	Reduce(wArg2^);
	IF Root(result)#wNumber THEN
		IF Root(result)#wError THEN
			MakePacked(result,wError,NotNumberType)
		END;
		RETURN FALSE
	END;
	ExtractPacked(result,y);
	RETURN TRUE
END ExtractNumbers;

PROCEDURE pAdd;
VAR
	x,y:INTEGER;
BEGIN
	IF ExtractNumbers(x,y) THEN
		MakePacked(result,wNumber,x+y)
	END
END pAdd;

PROCEDURE pSub;
VAR
	x,y:INTEGER;
BEGIN
	IF ExtractNumbers(x,y) THEN
		MakePacked(result,wNumber,x-y)
	END
END pSub;

PROCEDURE pMul;
VAR
	x,y:INTEGER;
BEGIN
	IF ExtractNumbers(x,y) THEN
		MakePacked(result,wNumber,x*y)
	END
END pMul;

PROCEDURE pDiv;
VAR
	x,y:INTEGER;
BEGIN
	IF ExtractNumbers(x,y) THEN
		MakePacked(result,wNumber,x DIV y)
	END
END pDiv;

PROCEDURE pFind;
VAR
	s:POINTER TO ARRAY [0..FormalLength] OF CHAR;
	l:link;
BEGIN
	Reduce(wName^);
	IF Root(result)#wString THEN
		IF Root(result)#wError THEN
			MakePacked(result,wError,NotStringType)
		END;
		RETURN
	END;
	ExtractPacked(result,s);
	l:=FindWord(s^);
	IF l=NIL THEN
		MakePacked(result,wError,NotFound)
	ELSE
		NewLayer(DefEntry(l));
		result:=wMeaning^
	END
END pFind;

PROCEDURE pAssociate;
VAR
	entry:closure;
BEGIN
	Copy(DefEntry(Root(wName^)),tempDef);
	AddEnv(tempDef,Root(wProperty^),wValue^);
	SetDefEntry(Root(wName^),tempDef);
	tempDef:=EmptyClosure;
	Reduce(wStruct^)
END pAssociate;

PROCEDURE pWordEntry;
BEGIN
	result:=DefEntry(Root(wStruct^))
END pWordEntry;

PROCEDURE pDebug;
BEGIN
	debug:=TRUE;
	Reduce(wStruct^);
	debug:=FALSE
END pDebug;

PROCEDURE pCollect;
BEGIN
	Collect;
	Reduce(wStruct^)
END pCollect;

PROCEDURE pAbort;
BEGIN
	HALT
END pAbort;

PROCEDURE pVList;
BEGIN
	vList;
	MakeDef(result,wTrue)
END pVList;

BEGIN
	DefineWord(wChar, 'CHAR', HandlePackage);
	DefineWord(wError, 'ERROR', HandlePackage);
	DefineWord(wNumber, 'NUMBER', HandlePackage);
	DefineWord(wCharSet, 'CharSET', HandlePackage);

	AddArgument(wPackage, 'Package');
	DefineWord(wPacked, 'Packed', HandlePackage);

	AddArgument(wCar, 'Car');
	AddArgument(wCdr, 'Cdr');
	AddAtom(wNil, 'Nil');

	AddPrimWord(wCons, 'Cons', Build);
	MakeDef(tempDef,wCons);
	AddEnv(wCons^,wType,tempDef);
	MakeDef(tempDef,wCar);
	AddValuedEnv(wCons^,wCar,tempDef);
	MakeDef(tempDef,wCdr);
	AddValuedEnv(wCons^,wCdr,tempDef);
	tempDef:=EmptyClosure;

	AddPrimWord(wJoin, 'Join', pJoin);
	AddPrimWord(wGetType, 'GetType', pGetType);
	AddPrimWord(wGetProp, 'PropertyValue', pGetProp);
	AddPrimWord(wAddValProp, 'AddValuedProperty', pAddValProp);
	AddPrimWord(wAddProp, 'AddProperty', pAddProp);
	AddPrimWord(wRemProp, 'RemoveProperty', pRemProp);
	AddPrimWord(wCopy, 'Copy', pCopy);
	AddPrimWord(wIsOfClass, 'IsOfClass', pIsOfClass);
	AddPrimWord(wEqual, 'Equal', pEqual);
	AddPrimWord(wQuote, 'Quote', pQuote);
	AddPrimWord(wBuild, 'Build', Build);
	AddPrimWord(wBuild, 'BuildReduced', BuildReduced);
	AddPrimWord(wVain, 'Vain', pVain);

	AddArgument(wDescription, 'Description');
	AddArgument(wStruct, 'Struct');
	AddArgument(wProperty, 'Property');
	AddArgument(wValue, 'Value');
	AddArgument(wType, 'Type');
	AddArgument(wAncestor, 'Ancestor');
	
	AddAtom(wDummy, 'Dummy');
	AddAtom(wTrue, 'True');
	AddAtom(wFalse, 'False');
	AddPrimWord(wAnd, 'And', pAnd);
	AddPrimWord(wOr, 'Or', pOr);
	AddPrimWord(wNot, 'Not', pNot);
	AddPrimWord(wIf, 'If', pIf);
	AddArgument(wTest, 'Test');
	AddArgument(wYes, 'Yes');
	AddArgument(wNo, 'No');
	AddArgument(wArg1, 'Arg1');
	AddArgument(wArg2, 'Arg2');
	AddArgument(wFile, 'File');

	AddPrimWord(wAdd, 'Add', pAdd);
	AddPrimWord(wSub, 'Sub', pSub);
	AddPrimWord(wMul, 'Mul', pMul);
	AddPrimWord(wDiv, 'Div', pDiv);
	
	AddPrimWord(wFind, 'Find', pFind);
	AddPrimWord(wWordEntry, 'WordEntry', pWordEntry);
	AddPrimWord(wAssociate, 'Associate', pAssociate);
	
	AddPrimWord(wDebug, 'Debug', pDebug);
	AddPrimWord(wCollect, 'Collect', pCollect);
	AddPrimWord(wAbort, 'Abort', pAbort);
	AddPrimWord(wVList, 'VList', pVList)
END Library.

