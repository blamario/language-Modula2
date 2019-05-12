IMPLEMENTATION MODULE ParseLow;

FROM SYSTEM IMPORT TSIZE;
FROM Buffers IMPORT Rewind, position;
FROM Memory IMPORT ALLOCATE, AddMarker, DropMarker, MarkNeeded;
FROM Machine IMPORT MarkLink, MarkClosure, tempDef, EmptyClosure;
FROM Machine IMPORT closure, result, MakeDef, Reduce;
FROM Machine IMPORT Root, AddEnv, AddValuedEnv, Join, Copy;
FROM Library IMPORT wProperty, wStruct;
FROM Grammars IMPORT wDummy, wFail, wRaise, wDiscard, wGrammar, wNext;
FROM Grammars IMPORT Failure, HoldDummy;

TYPE
	RestPtr=POINTER TO RestRec;
	RestRec=RECORD
				grammar:closure;
				next:RestPtr
			  END;
	ParsedPtr=POINTER TO ParsedRec;
	ParsedRec=RECORD
					CASE leaf:BOOLEAN OF
						FALSE:
							property:closure;
							valued:BOOLEAN
						|TRUE:
							result:closure
					END;
					next:ParsedPtr
				 END;
	StackPtr=POINTER TO StackRec;
	StackRec=RECORD
					restRec:RestRec;
					prevLink:ParsedPtr;
					pos:LONGCARD;
(*					layer:CARDINAL; *)
					next:StackPtr
				END;
VAR
	current:closure;
	parsed,parsedNew,linked:ParsedPtr;
	rest,restNew:RestPtr;
	stack,stackNew:StackPtr;
(*	layers:CARDINAL; *)

PROCEDURE MarkRest(list:RestPtr);
VAR
	fresh:BOOLEAN;
BEGIN
	WHILE list#NIL DO
		MarkNeeded(list,TSIZE(RestRec),fresh);
		IF NOT fresh THEN
			RETURN
		END;
		MarkClosure(list^.grammar);
		list:=list^.next
	END
END MarkRest;

PROCEDURE MarkParsed(list:ParsedPtr);
VAR
	fresh:BOOLEAN;
BEGIN
	WHILE list#NIL DO
		MarkNeeded(list,TSIZE(ParsedRec),fresh);
		IF NOT fresh THEN
			RETURN
		END;
		IF list^.leaf THEN
			MarkClosure(list^.result)
		ELSE
			MarkClosure(list^.property)
		END;
		list:=list^.next
	END
END MarkParsed;

PROCEDURE MarkAll;
VAR
	s:StackPtr;
	fresh:BOOLEAN;
BEGIN
	s:=stack;
	fresh:=TRUE;
	WHILE fresh AND (s#NIL) DO
		MarkNeeded(s,TSIZE(StackRec),fresh);
		MarkRest(s^.restRec.next);
		MarkParsed(s^.prevLink);
		s:=s^.next
	END;
	MarkClosure(current);
	MarkRest(rest);
	MarkParsed(parsed)
END MarkAll;

PROCEDURE MarkLinked;
BEGIN
	MarkParsed(linked)
END MarkLinked;

PROCEDURE LinkParsed;
VAR
	swap:ParsedPtr;
BEGIN
	linked:=NIL;
	AddMarker(MarkLinked);
	WHILE parsed#NIL DO
		IF parsed^.leaf THEN
			swap:=parsed^.next;
			parsed^.next:=linked;
			linked:=parsed;
			parsed:=swap;
		ELSE
         IF Root(parsed^.property)#wDiscard THEN
         	IF Root(parsed^.property)=wRaise THEN
         		IF Root(linked^.result)#wDummy THEN
						IF linked^.leaf THEN
							Copy(linked^.result,tempDef);
							linked^.next^.leaf:=FALSE
						ELSE
							tempDef:=linked^.result
						END;
						Join(tempDef,linked^.next^.result);
						linked^.next^.result:=tempDef
					END
				ELSE
					IF linked^.next^.leaf THEN
						tempDef:=linked^.next^.result;
						Copy(tempDef,linked^.next^.result);
						linked^.next^.leaf:=FALSE
					END;
					IF parsed^.valued THEN
						AddValuedEnv(linked^.next^.result,Root(parsed^.property),linked^.result)
					ELSE
						AddEnv(linked^.next^.result,Root(parsed^.property),linked^.result)
					END
				END
			END;
			linked:=linked^.next;
			parsed:=parsed^.next
		END
	END;
	tempDef:=EmptyClosure;
	IF linked^.next=NIL THEN
		result:=linked^.result
	ELSE
		result:=Failure
	END;
	DropMarker
END LinkParsed;
				
PROCEDURE ParsePrimitive;
VAR
	prevPos:LONGCARD;
BEGIN
	NEW(stackNew);
	WITH stackNew^ DO
(*		layer:=layers; *)
		restRec.next:=rest;
		restRec.grammar:=NIL;
		prevLink:=parsed;
		pos:=MAX(LONGCARD);
		next:=stack
	END;
	stack:=stackNew;
(*	layers:=0; *)
	NEW(rest);
	WITH rest^ DO
		grammar:=wGrammar^;
		next:=NIL
	END;
	parsed:=NIL;
	REPEAT
		REPEAT
			buildTree:=TRUE;
			current:=rest^.grammar;
			rest:=rest^.next;
			Reduce(current);
			IF Root(result)=wFail THEN
				rest:=NIL
			ELSIF (parsed#NIL) AND NOT parsed^.leaf AND
					((Root(parsed^.property)=wDiscard) OR
					(Root(parsed^.property)=wRaise) AND (Root(result)=wDummy)) THEN
				parsed:=parsed^.next
			ELSE
				NEW(parsedNew);
				parsedNew^.leaf:=TRUE;
				parsedNew^.result:=result;
				parsedNew^.next:=parsed;
				parsed:=parsedNew
			END
		UNTIL rest=NIL;
		IF Root(result)#wFail THEN
			WHILE stack^.pos#MAX(LONGCARD) DO
				stack:=stack^.next
			END;
			LinkParsed;
(*			WHILE layers>0 DO
				PopLayer;
				DEC(layers)
			END *)
		END;
		prevPos:=stack^.pos;
		IF prevPos#MAX(LONGCARD) THEN
			Rewind(prevPos)
		END;
		rest:=ADR(stack^.restRec);
		parsed:=stack^.prevLink;
(*		WHILE layers>stack^.layer DO
			PopLayer;
			DEC(layers)
		END;
		layers:=stack^.layer; *)
		stack:=stack^.next;
	UNTIL prevPos=MAX(LONGCARD);
	rest:=rest^.next;
	current:=NIL
END ParsePrimitive;

PROCEDURE ParseSequencePrimitive(valuedProperty:BOOLEAN);
VAR
	buildOld:BOOLEAN;
BEGIN
	NEW(restNew);
	restNew^.grammar:=wNext^;
	restNew^.next:=rest;
	rest:=restNew;
	buildOld:=buildTree;
	IF Root(wProperty^)=wDiscard THEN
		buildTree:=FALSE
	END;
	NEW(parsedNew);
	WITH parsedNew^ DO
		leaf:=FALSE;
		property:=wProperty^;
		valued:=valuedProperty;
		next:=parsed;
	END;
	parsed:=parsedNew;
	Reduce(wGrammar^);
	buildTree:=buildOld
END ParseSequencePrimitive;

PROCEDURE ParseEndSequence;
BEGIN
	result:=wStruct^
END ParseEndSequence;

PROCEDURE ParseChoice;
BEGIN
	NEW(stackNew);
	WITH stackNew^ DO
(*		StartLayer;
		INC(layers);
		layer:=layers; *)
		pos:=position;
		prevLink:=parsed;
		next:=stack;
		stack:=stackNew;
		restRec.grammar:=wNext^;
		restRec.next:=rest
	END;
	Reduce(wGrammar^)
END ParseChoice;

PROCEDURE ParseOption;
BEGIN
	NEW(stackNew);
	WITH stackNew^ DO
(*		StartLayer;
		INC(layers);
		layer:=layers; *)
		pos:=position;
		prevLink:=parsed;
		next:=stack;
		stack:=stackNew;
		restRec.grammar:=wGrammar^;
		restRec.next:=rest
	END;
	result:=HoldDummy
END ParseOption;

BEGIN
	rest:=NIL;
	stack:=NIL;
	parsed:=NIL;
	current:=NIL;
	AddMarker(MarkAll)
END ParseLow.

