IMPLEMENTATION MODULE Machine;
FROM SYSTEM IMPORT ADDRESS, WORD, BYTE, ADR, TSIZE, Registers;
FROM Lib IMPORT IncAddr, Move, WordMove, WordFill, Compare, Intr;
FROM Memory IMPORT ALLOCATE, MarkNeeded, AddMarker, DropMarker;
FROM IO IMPORT WrStr, WrChar, WrCharRep, WrInt, WrHex, WrLn, RdKey;
CONST
	MaxStack=8000;
	MaxLayers=8000;
	indention=3;
	FillValue=700H;
	TextScreen=0B000H;
TYPE
(*
	envList=POINTER TO environment;
	closure=POINTER TO clRec;
   flag=(defined, primitive, packed, string, length);
   clRec=RECORD
            CASE kind:flag OF
               defined:
                  root:link
               ELSE
                  handler:handlerType
            END;
            env,valEnv:envList
         END;
	environment=RECORD
						name:link;
						newDef:closure;
						next:envList
					END;
*)
	stackItem=	RECORD
						name:wdPtr;
						oldDef:closure
					END;
VAR
	stack:ARRAY[1..MaxStack] OF stackItem;
	layers:ARRAY[1..MaxLayers] OF [0..MaxStack];
	sp:[0..MaxStack];
	topLayer,breakLayer:[0..MaxLayers];
	runScreen:ARRAY [0..25*80-1] OF WORD;
	runCurPos:CARDINAL;

PROCEDURE StartLayer;
BEGIN
	INC(topLayer);
	layers[topLayer]:=sp
END StartLayer;

PROCEDURE SaveDefinition(name:link);
BEGIN
	INC(sp);
	stack[sp].name:=wdPtr(name);
	stack[sp].oldDef:=name^
END SaveDefinition;

PROCEDURE NewLayer(d:closure);
VAR
	swap:closure;
	i:CARDINAL;
	layer:envList;
BEGIN
	IF (d^.kind<packed) & (d^.env=NIL) & (d^.valEnv=NIL) THEN
		RETURN
	END;
	IF d^.kind>primitive THEN
		INC(sp);
		stack[sp].name:=wdPtr(ADR(parent));
		stack[sp].oldDef:=parent;
		parent:=d;
		INC(sp);
		stack[sp].name:=wdPtr(wPackage);
		stack[sp].oldDef:=wPackage^;
		wPackage^:=d
	ELSE
		IF d^.valEnv=NIL THEN
			layer:=d^.env
		ELSE
			i:=sp;
			layer:=d^.valEnv;
			WHILE layer#NIL DO
				INC(sp);
				WITH stack[sp] DO
					name:=layer^.name;
					oldDef:=layer^.newDef;
					Reduce(oldDef);
					oldDef:=result
				END;
				layer:=layer^.next
			END;
			layer:=d^.env;
			WHILE i<sp DO
				INC(i);
	 			WITH stack[i] DO
					swap:=oldDef;
					oldDef:=link(name)^;
					link(name)^:=swap
				END
			END
		END;
		INC(sp);
		stack[sp].name:=wdPtr(ADR(parent));
		stack[sp].oldDef:=parent;
		parent:=d;
		WHILE layer#NIL DO
			INC(sp);
			WITH stack[sp] DO
				name:=layer^.name;
				oldDef:=link(name)^;
				link(name)^:=layer^.newDef
			END;
			layer:=layer^.next
		END
	END
END NewLayer;
		
PROCEDURE PopLayer;
BEGIN
(*	limit:=layers[topLayer]; *)
	WHILE sp>layers[topLayer] DO
		link(stack[sp].name)^:=stack[sp].oldDef;
		DEC(sp)
	END;
	DEC(topLayer)
END PopLayer;

PROCEDURE Keep(name:link);
VAR
	s:CARDINAL;
BEGIN
	s:=sp;
	WHILE (s>layers[topLayer]) AND (link(stack[s].name)#name) DO
		DEC(s)
	END;
	IF s>layers[topLayer] THEN
		stack[s]:=stack[sp];
		DEC(sp)
	END
END Keep;

PROCEDURE ShowDef(d:closure);
FORWARD;

PROCEDURE Reduce(def:closure);
BEGIN
	StartLayer;
	WHILE def^.kind#primitive DO
		IF debug OR (topLayer<=breakLayer) THEN
			ShowDef(def)
		END;
		NewLayer(def);
		def:=link(def^.root)^
	END;
	IF (def^.env#NIL) OR (def^.valEnv#NIL) THEN
		NewLayer(def)
	END;
	def^.handler;
	PopLayer
END Reduce;

PROCEDURE DummyHandler;
BEGIN
	result:=wPackage^
END DummyHandler;

PROCEDURE EmptyHandler;
END EmptyHandler;

PROCEDURE ParentHandler;
BEGIN
	result:=parent
END ParentHandler;

PROCEDURE Root(def:closure):link;
BEGIN
	RETURN link(def^.root)
END Root;

PROCEDURE EnvCopy(source:envList; VAR dest:envList);
VAR
	current:POINTER TO envList;
BEGIN
	dest:=NIL;
	current:=ADR(dest);
	WHILE source#NIL DO
		NEW(current^);
		current^^:=source^;
		current:=ADR(current^^.next);
		source:=source^.next
	END
END EnvCopy;

PROCEDURE Copy(source:closure; VAR dest:closure);
BEGIN
	NEW(dest);
	IF source^.kind>primitive THEN
		dest^:=source^
	ELSE
		dest^.root:=source^.root;
		dest^.kind:=source^.kind;
		dest^.valEnv:=NIL;
		EnvCopy(source^.env,dest^.env);
		EnvCopy(source^.valEnv,dest^.valEnv)
	END
END Copy;

PROCEDURE JoinEnv(VAR union:envList; add:envList);
VAR
	newEnv:envList;
	current:POINTER TO envList;
BEGIN
	current:=ADR(union);
	WHILE add#NIL DO
		WHILE (current^#NIL) AND (Seg(add^.name^) > Seg(current^^.name^)) DO
			current:=ADR(current^^.next)
		END;
		IF (current^#NIL) AND (add^.name=current^^.name) THEN
			current^^.newDef:=add^.newDef
		ELSE
			NEW(newEnv);
			newEnv^:=add^;
			newEnv^.next:=current^;
			current^:=newEnv
		END;
		add:=add^.next
	END
END JoinEnv;
	
PROCEDURE Join(VAR def:closure; description:closure);
BEGIN
	IF (def^.kind<=primitive) AND (description^.kind<=primitive) THEN
		JoinEnv(def^.env,description^.env);
		JoinEnv(def^.valEnv,description^.valEnv)
	ELSIF (def^.kind=defined) AND (def^.env=NIL) AND (def^.valEnv=NIL) THEN
		def^.kind:=description^.kind;
		EnvCopy(description^.env,def^.env);
		EnvCopy(description^.valEnv,def^.valEnv)
	END
END Join;

PROCEDURE Build;
VAR
	follow,valFollow:envList;
	current:POINTER TO envList;
BEGIN
	IF (parent^.kind<packed) & (parent^.valEnv#NIL) THEN
		NEW(result);
		result^:=wType^^;
		follow:=result^.env;
		valFollow:=parent^.valEnv;
		IF link(valFollow^.name)=wType THEN
			valFollow:=valFollow^.next
		END;
		current:=ADR(result^.env);
		WHILE valFollow#NIL DO
			WHILE (follow#NIL) & (Seg(follow^.name^) < Seg(valFollow^.name^)) DO
				current^:=NIL;
				NEW(current^);
				current^^.name:=follow^.name;
				current^^.newDef:=follow^.newDef;
				current:=ADR(current^^.next);
				follow:=follow^.next
			END;
			IF (follow#NIL) & (follow^.name = valFollow^.name) THEN
				follow:=follow^.next
			END;
			current^:=NIL;
			NEW(current^);
			current^^.name:=valFollow^.name;
			current^^.newDef:=link(valFollow^.name)^;
			current:=ADR(current^^.next);
			valFollow:=valFollow^.next
		END;
		WHILE follow#NIL DO
			current^:=NIL;
			NEW(current^);
			current^^.name:=follow^.name;
			current^^.newDef:=follow^.newDef;
			current:=ADR(current^^.next);
			follow:=follow^.next
		END;
		current^:=NIL
	ELSE
		result:=wType^
	END
END Build;

PROCEDURE BuildMixed;
VAR
	e:envList;
	dest:POINTER TO envList;
BEGIN
	result:=parent;
	IF (result^.kind<packed) & (result^.valEnv#NIL) THEN
		NEW(result);
		result^:=parent^;
		WITH result^ DO
			dest:=ADR(env);
			REPEAT
				NEW(e);
				e^.name:=valEnv^.name;
				e^.newDef:=link(e^.name)^;
				WHILE (dest^#NIL) & (Seg(e^.name^) > Seg(dest^^.name^)) DO
					dest:=ADR(dest^^.next)
				END;
				e^.next:=dest^;
				dest^:=e;
				valEnv:=valEnv^.next
			UNTIL valEnv=NIL
		END
	END
END BuildMixed;

PROCEDURE BuildReduced;
VAR
	follow:envList;
	i:CARDINAL;
BEGIN
	follow:=parent^.env;
	WHILE follow#NIL DO
		link(stack[sp].name)^:=stack[sp].oldDef;
		DEC(sp);
		follow:=follow^.next
	END;
	SaveDefinition(ADR(parent));
	Copy(parent,parent);
	follow:=parent^.env;
	WHILE follow#NIL DO
		Reduce(follow^.newDef);
		follow^.newDef:=result;
		follow:=follow^.next
	END;
	follow:=parent^.valEnv;
	WHILE follow#NIL DO
		Reduce(link(follow^.name)^);
		follow^.newDef:=result;
		follow:=follow^.next
	END;
	result:=parent;
	JoinEnv(result^.env,result^.valEnv);
	result^.valEnv:=NIL
END BuildReduced;

PROCEDURE MakeDef(VAR def:closure; defRoot:link);
BEGIN
	NEW(def);
	WITH def^ DO
		kind:=defined;
		env:=NIL;
		valEnv:=NIL;
		root:=wdPtr(defRoot)
	END
END MakeDef;

PROCEDURE MakePrimitive(VAR def:closure; defHandler:handlerType);
BEGIN
	NEW(def);
	WITH def^ DO
		kind:=primitive;
		env:=NIL;
		valEnv:=NIL;
		handler:=defHandler
	END
END MakePrimitive;

PROCEDURE MakePacked(VAR d:closure; root:link; x:ARRAY OF BYTE);
BEGIN
	NEW(d);
	d^.root:=wdPtr(root);
	d^.kind:=packed;
	IF HIGH(x)>3 THEN
		ALLOCATE(d^.env,HIGH(x)+1);
		d^.kind:=length;
		Move(ADR(x),d^.env,HIGH(x)+1);
		d^.valEnv:=envList(HIGH(x)+1)
	ELSE
		d^.valEnv:=NIL;
		d^.env:=NIL;
		Move(ADR(x),ADR(d^.env),HIGH(x)+1)
	END
END MakePacked;

PROCEDURE MakeString(VAR d:closure; root:link; a:ADDRESS);
BEGIN
	NEW(d);
	d^.kind:=string;
	d^.root:=wdPtr(root);
	d^.env:=envList(a);
	d^.valEnv:=NIL
END MakeString;

PROCEDURE AddEnv(VAR d:closure; prop:link; newValue:closure);
VAR
	newProp:envList;
	current:POINTER TO envList;
BEGIN
	IF (prop=NIL) OR (d^.kind>primitive) THEN
		RETURN
	END;
	current:=ADR(d^.env);
	WHILE (current^#NIL) AND (Seg(current^^.name^) < Seg(prop^)) DO
		current:=ADR(current^^.next)
	END;
	IF (current^#NIL) AND (link(current^^.name)=prop) THEN
		current^^.newDef:=newValue
	ELSE
		NEW(newProp);
		WITH newProp^ DO
			name:=wdPtr(prop);
			newDef:=newValue;
			next:=current^
		END;
		current^:=newProp
	END
END AddEnv;

PROCEDURE AddValuedEnv(VAR d:closure; prop:link; newValue:closure);
VAR
	newProp:envList;
	current:POINTER TO envList;
BEGIN
	IF (prop=NIL) OR (d^.kind>primitive) THEN
		RETURN
	END;
	current:=ADR(d^.valEnv);
	WHILE (current^#NIL) AND (Seg(current^^.name^) < Seg(prop^)) DO
		current:=ADR(current^^.next)
	END;
	IF (current^#NIL) AND (link(current^^.name)=prop) THEN
		current^^.newDef:=newValue
	ELSE
		NEW(newProp);
		WITH newProp^ DO
			name:=wdPtr(prop);
			newDef:=newValue;
			next:=current^
		END;
		current^:=newProp
	END
END AddValuedEnv;

PROCEDURE RemoveEnv(VAR d:closure; prop:link);
VAR
	current:POINTER TO envList;
BEGIN
	IF (prop=NIL) OR (d^.kind>primitive) THEN
		RETURN
	END;
	current:=ADR(d^.env);
	WHILE (current^#NIL) AND (link(current^^.name)#prop) DO
		current:=ADR(current^^.next)
	END;
	IF current^#NIL THEN
		current^:=current^^.next
	END;
	current:=ADR(d^.valEnv);
	WHILE (current^#NIL) AND (link(current^^.name)#prop) DO
		current:=ADR(current^^.next)
	END;
	IF current^#NIL THEN
		current^:=current^^.next
	END
END RemoveEnv;

PROCEDURE EnvEqual(e1,e2:envList):BOOLEAN;
BEGIN
	WHILE e1#NIL DO
		IF (e2#NIL) AND (e1^.name=e2^.name) AND (e1^.newDef=e2^.newDef) THEN
			e1:=e1^.next;
			e2:=e2^.next
		ELSE
			RETURN FALSE
		END
	END;
	RETURN e2=NIL
END EnvEqual;
	
TYPE
	CharPtr=POINTER TO CHAR;

PROCEDURE SameStrings(s1,s2:ADDRESS):BOOLEAN;
BEGIN
   WHILE (s1^=s2^) AND (CharPtr(s1)^#0C) DO
      IncAddr(s1,1);
      IncAddr(s2,1)
   END;
   RETURN s1^=s2^
END SameStrings;

PROCEDURE Equal(d1,d2:closure):BOOLEAN;
BEGIN
	IF (d1=d2) OR (d1^=d2^) THEN
		RETURN TRUE
	END;
	IF (d1^.root#d2^.root) OR (d1^.kind#d2^.kind) THEN
		RETURN FALSE
	END;
	CASE d1^.kind OF
		|packed:RETURN FALSE
		|string:RETURN SameStrings(d1^.env,d2^.env)
		|length:RETURN (d1^.valEnv=d2^.valEnv) AND
				(CARDINAL(d1^.valEnv)=Compare(d1^.env,d2^.env,CARDINAL(d1^.valEnv)))
	ELSE
		RETURN EnvEqual(d1^.env,d2^.env) AND EnvEqual(d1^.valEnv,d2^.valEnv)
	END
END Equal;
		
PROCEDURE ExtractPacked(package:closure; VAR x:ARRAY OF BYTE);
BEGIN
	IF HIGH(x)<4 THEN
		Move(ADR(package^.env),ADR(x),HIGH(x)+1)
	ELSE
		Move(package^.env,ADR(x),HIGH(x)+1)
	END
END ExtractPacked;

PROCEDURE Envelope(VAR def:closure; struct:closure;
						cons,valCons,listEnd,prop,value,next:link);
	PROCEDURE EnvToList(env:envList;cons:link);
	BEGIN
		IF env#NIL THEN
			EnvToList(env^.next,cons);
			tempDef:=def;
			MakeDef(def,cons);
			AddEnv(def,next,tempDef);
			MakeDef(tempDef,link(env^.name));
			AddEnv(def,prop,tempDef);
			AddEnv(def,value,env^.newDef)
		END
	END EnvToList;
BEGIN
	MakeDef(def,listEnd);
	IF struct^.kind>primitive THEN
		tempDef:=def;
		MakeDef(def,cons);
		AddEnv(def,next,tempDef);
		MakeDef(tempDef,wPackage);
		AddEnv(def,prop,tempDef);
		NEW(tempDef);
		tempDef^:=struct^;
		tempDef^.root:=wdPtr(wPacked);
		AddEnv(def,value,tempDef)
	ELSE
		EnvToList(struct^.env,cons);
		EnvToList(struct^.valEnv,valCons)
	END;
	tempDef:=EmptyClosure
END Envelope;

	
PROCEDURE MarkEnvironment(VAR env:envList);
VAR
	fresh:BOOLEAN;
	ep:POINTER TO envList;
BEGIN
	fresh:=TRUE;
	ep:=ADR(env);
	WHILE (ep^#NIL) AND fresh DO
		MarkNeeded(ep^, TSIZE(environment), fresh);
		MarkClosure(ep^^.newDef);
		ep:=ADR(ep^^.next)
	END
END MarkEnvironment;

PROCEDURE MarkString(VAR str:ADDRESS);
VAR
	length:CARDINAL;
	fresh:BOOLEAN;
	follow:CharPtr;
BEGIN
	IF str#NIL THEN
		length:=1;
		follow:=CharPtr(str);
		WHILE follow^#0C DO
			INC(length);
			IncAddr(follow,1)
		END;
		MarkNeeded(str,length,fresh)
	END
END MarkString;

PROCEDURE MarkClosure(VAR def:closure);
VAR
	fresh:BOOLEAN;
BEGIN
	IF def=NIL THEN
		RETURN
	END;
	MarkNeeded(def,TSIZE(clRec),fresh);
	IF fresh THEN
		CASE def^.kind OF
			defined:
				MarkLink(link(def^.root));
				MarkEnvironment(def^.env);
				MarkEnvironment(def^.valEnv)
			|primitive:
				MarkEnvironment(def^.env);
				MarkEnvironment(def^.valEnv)
			|string:
				MarkLink(link(def^.root));
				MarkString(def^.env)
			|length:
				MarkLink(link(def^.root));
				MarkNeeded(def^.env,CARDINAL(def^.valEnv),fresh)
		END
	END
END MarkClosure;

PROCEDURE MarkLink(VAR l:link);
VAR
	fresh:BOOLEAN;
BEGIN
	MarkNeeded(l,TSIZE(closure),fresh);
	IF fresh THEN
		MarkClosure(l^)
	END
END MarkLink;

PROCEDURE MarkStack;
VAR
	i:CARDINAL;
BEGIN
	FOR i:=sp TO 1 BY -1 DO
		MarkLink(link(stack[i].name));
		MarkClosure(stack[i].oldDef)
	END
END MarkStack;

PROCEDURE MarkTemporaries;
BEGIN
	MarkClosure(tempDef);
	MarkClosure(result);
	MarkClosure(EmptyClosure);
	MarkClosure(HandlePackage);
	MarkClosure(HandleParent);
	MarkLink(wPackage);
	MarkClosure(parent)
END MarkTemporaries;

PROCEDURE CursorPos():CARDINAL;
VAR
	r:Registers;
BEGIN
	r.AH:=3;
	r.BH:=0;
	Intr(r,10H);
	RETURN r.DX
END CursorPos;

PROCEDURE PlaceCursor(pos:CARDINAL);
VAR
	r:Registers;
BEGIN
	r.AH:=2;
	r.BH:=0;
	r.DX:=pos;
	Intr(r,10H)
END PlaceCursor;

PROCEDURE SaveScreen(VAR scr:ARRAY OF WORD);
BEGIN
	WordMove([TextScreen:0], ADR(scr), 25*80)
END SaveScreen;

PROCEDURE RestoreScreen(VAR scr:ARRAY OF WORD);
BEGIN
	WordMove(ADR(scr), [TextScreen:0], 25*80)
END RestoreScreen;

PROCEDURE ClearScreen;
BEGIN
	WordFill([TextScreen:0], 50*80, FillValue);
	PlaceCursor(0)
END ClearScreen;

PROCEDURE WriteDef(d:closure; indent:CARDINAL);
VAR
	follow:CharPtr;
	
	PROCEDURE WriteEnv(e:envList; indent:CARDINAL; colon:BOOLEAN);
	BEGIN
		WHILE e#NIL DO
			WrLn;
			WrCharRep(' ',indent);
			WrStr(e^.name^.name^);
			IF colon THEN
				WrChar(':')
			END;
			WrChar('=');
			WriteDef(e^.newDef, indent);
			e:=e^.next
		END
	END WriteEnv;
BEGIN
	CASE d^.kind OF
		|defined:
			WrStr(d^.root^.name^);
			WrChar('(');
			IF d^.valEnv#NIL THEN
				WriteEnv(d^.valEnv, indent+indention, TRUE);
				WrLn
			END;
			WriteEnv(d^.env, indent+indention, FALSE);
			WrChar(')')
		|string:
			WrChar('[');
			WrStr(d^.root^.name^);
			WrChar(']');
			WrChar('"');
			follow:=CharPtr(d^.env);
			WHILE follow^#0C DO
				WrChar(follow^);
				IncAddr(follow,1)
			END;
			WrChar('"')
		|primitive:
			WrStr('PRIMITIVE[');
			WrHex(Seg(d^.env),0);
			WrChar(':');
			WrHex(Ofs(d^.env),0);
			WrChar(']')
		|packed:
			WrChar('[');
			WrStr(d^.root^.name^);
			WrChar(']');
			WrInt(INTEGER(d^.env),0);
			IF CHAR(d^.env) >= ' ' THEN
				WrStr(" - '");
				WrChar(CHAR(d^.env));
				WrChar("'")
			END
		|length:
			WrChar('[');
			WrStr(d^.root^.name^);
			WrChar(']');
			WrHex(Seg(d^.valEnv),5)
	END
END WriteDef;

PROCEDURE ShowDef(d:closure);
VAR
	ch:CHAR;
BEGIN
	debug:=TRUE;
	breakLayer:=0;
	runCurPos:=CursorPos();
	SaveScreen(runScreen);
	ClearScreen;
	WriteDef(d,0);
	LOOP
		ch:=RdKey();
		CASE ch OF
(*			|'w','W':
				Info(debugWin,winfo);
				SetWrap(NOT winfo.WrapOn);
				Clear;
				WriteDef(d,0)
*)
		   |' ':
	   		EXIT
	   	|'p','P':
	   		debug:=FALSE;
	   		breakLayer:=topLayer;
	   		RestoreScreen(runScreen);
	   		EXIT
	   	|'/':
	   		RestoreScreen(runScreen);
	   		ch:=RdKey();
	   		ClearScreen;
	   		WriteDef(d,0)
	   	|'g','G':
	   		debug:=FALSE;
	   		EXIT
	   	|'q','Q':
	   		ch:=RdKey();
	   		IF ch='!' THEN
	   			HALT
	   		END
	   END
	END;
	RestoreScreen(runScreen);
	PlaceCursor(runCurPos)
END ShowDef;

BEGIN
	sp:=0;
	topLayer:=1;
	breakLayer:=0;
	MakePrimitive(EmptyClosure,EmptyHandler);
	MakePrimitive(HandlePackage,DummyHandler);
	MakePrimitive(HandleParent,ParentHandler);
	tempDef:=EmptyClosure;
	result:=EmptyClosure;
	parent:=NIL;
	AddMarker(MarkStack);
	AddMarker(MarkTemporaries);
	debug:=FALSE
END Machine.




