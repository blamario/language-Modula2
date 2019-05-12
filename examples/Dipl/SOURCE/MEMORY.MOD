IMPLEMENTATION MODULE Memory;
FROM Lib IMPORT AddAddr, DecAddr, IncAddr, SubAddr, Dos;
FROM SYSTEM IMPORT ADDRESS, BYTE, TSIZE, Registers;
FROM IO IMPORT WrStr, WrLn;
CONST
	MaxMarkers=200;
	MinParagraph=400H;
	MaxParagraph=0A000H;
	MinBitMap=MinParagraph DIV 16;
	MaxBitMap=MaxParagraph DIV 16;
	MaxBlockSize=1025;
VAR
	markers:ARRAY [1..MaxMarkers] OF PROC;
	lastMarker:[0..MaxMarkers];
	bitMap:ARRAY [MinBitMap..MaxBitMap] OF BITSET;
	HeapTop,HeapBottom:CARDINAL;
	sizes:ARRAY [0..MaxBlockSize+1] OF
		RECORD
			paragraph:CARDINAL;
			previous,next:[0..MaxBlockSize+1]
		END;
	largestBlock:[0..MaxBlockSize];
	block1,length1:CARDINAL;

PROCEDURE FatalError(text:ARRAY OF CHAR);
BEGIN
	WrLn;
	WrStr('Greska u garbage collector modulu!');
	WrLn;
	WrStr(text);
	HALT
END FatalError;

PROCEDURE AddMarker(m:PROC);
BEGIN
	IF lastMarker<MaxMarkers THEN
		INC(lastMarker);
		markers[lastMarker]:=m
	ELSE
		FatalError('Prekoracen maximalan broj markera potrebnih celija u HEAPu!')
	END
END AddMarker;

PROCEDURE DropMarker;
BEGIN
	IF lastMarker>0 THEN
		DEC(lastMarker)
	ELSE
		FatalError('Malo previse brisanja markera potrebnih celija u HEAPu.')
	END
END DropMarker;

PROCEDURE MarkNeeded(VAR addr:ADDRESS; length:CARDINAL; VAR discovery:BOOLEAN);
VAR
	paragraph:CARDINAL;
BEGIN
	paragraph:=Seg(addr^);
	IF Ofs(addr^)#0 THEN
		paragraph:=paragraph + Ofs(addr^) DIV 16;
		length:=length + Ofs(addr^) MOD 16
	END;
	length:=(length+15) DIV 16;
	IF paragraph>=HeapBottom THEN
		discovery:=FALSE;
		IF paragraph>HeapTop THEN
			RETURN
		END;
		REPEAT
			IF NOT (paragraph MOD 16 IN bitMap[paragraph DIV 16]) THEN
				discovery:=TRUE;
				INCL(bitMap[paragraph DIV 16],paragraph MOD 16)
			END;
			INC(paragraph);
			DEC(length)
		UNTIL length=0
	ELSE
		discovery:=TRUE
	END
END MarkNeeded;

(*#check(index => off) *)
(*#check(range => off) *)
(*#check(overflow => off) *)
(*#check(stack => off) *)
(*#check(guard => off) *)
(*#check(nil_ptr => off) *)

PROCEDURE Collect;
VAR
	i,blockSize,previous:CARDINAL;
BEGIN
	FOR i:=HeapBottom DIV 16 TO HeapTop DIV 16 DO
		bitMap[i]:=BITSET(0)
	END;
	FOR i:=1 TO lastMarker DO
		markers[i]
	END;
	largestBlock:=0;
	FOR i:=1 TO MaxBlockSize DO
		sizes[i].paragraph:=0
	END;
	EXCL(bitMap[HeapBottom DIV 16],HeapBottom MOD 16);
	INCL(bitMap[(HeapBottom+1) DIV 16],(HeapBottom+1) MOD 16);
	i:=HeapTop-1;
	LOOP
		WHILE i MOD 16 IN bitMap[i DIV 16] DO
			DEC(i)
		END;
		IF i=HeapBottom THEN
			EXIT
		END;
		blockSize:=0;
		REPEAT
			INC(blockSize);
			DEC(i);
		UNTIL i MOD 16 IN bitMap[i DIV 16];
		IF blockSize>largestBlock THEN
			IF blockSize>MaxBlockSize THEN
				INC(i,blockSize-MaxBlockSize);
				blockSize:=MaxBlockSize
			END;
			largestBlock:=blockSize
		END;
		[i+1:0]^:=sizes[blockSize].paragraph;
		sizes[blockSize].paragraph:=i+1
	END;
	IF largestBlock=0 THEN
		FatalError( 'Heap je definitivno prepunjen. Zaboravi na taj algoritam!' )
	END;
	previous:=0;
	FOR blockSize:=1 TO largestBlock DO
		IF sizes[blockSize].paragraph#0 THEN
			sizes[blockSize].previous:=previous;
			sizes[previous].next:=blockSize;
			previous:=blockSize
		END
	END;
	sizes[largestBlock].next:=MaxBlockSize+1;
	length1:=0
END Collect;

PROCEDURE ALLOCATE(VAR ptr:ADDRESS; length:CARDINAL);
VAR
	original:CARDINAL;
BEGIN
	IF length<=16 THEN
		IF sizes[1].paragraph#0 THEN
			ptr:=[sizes[1].paragraph:0];
			sizes[1].paragraph:=ptr^;
			IF sizes[1].paragraph=0 THEN
				sizes[0].next:=sizes[1].next;
				sizes[sizes[1].next].previous:=0
			END
		ELSE
			IF length1=0 THEN
				length1:=sizes[0].next;
				IF length1>MaxBlockSize THEN
					Collect;
					ALLOCATE(ptr,length);
					RETURN
				END;
				block1:=sizes[length1].paragraph;
				sizes[length1].paragraph:=[block1:0]^;
				IF sizes[length1].paragraph=0 THEN
					sizes[0].next:=sizes[length1].next;
					sizes[sizes[length1].next].previous:=0
				END
			END;
			ptr:=[block1:0];
			INC(block1);
			DEC(length1)
		END
	ELSE
		length:=(length+15) DIV 16;
		original:=length;
		IF sizes[length].paragraph=0 THEN
			length:=0;
			REPEAT
				length:=sizes[length].next
			UNTIL length>=original;
			IF length>MaxBlockSize THEN
				Collect;
				IF original>largestBlock THEN
					FatalError( 'Heap je definitivno prepunjen. Zaboravi na taj algoritam!' )
				END;
				ALLOCATE(ptr,original*16);
				RETURN
			END
		END;
		WITH sizes[length] DO
			IF length#original THEN
				[paragraph+original:0]^:=sizes[length-original].paragraph;
				sizes[length-original].paragraph:=paragraph+original;
				IF [paragraph+original:0]^=WORD(0) THEN
					sizes[previous].next:=length-original;
					sizes[length-original].previous:=previous;
					previous:=length-original;
					sizes[length-original].next:=length
				END
			END;
			ptr:=[paragraph:0];
			paragraph:=ptr^;
			IF paragraph=0 THEN
				sizes[previous].next:=next;
				sizes[next].previous:=previous
			END
		END
	END
END ALLOCATE;

VAR
	r:Registers;
	
BEGIN
	r.AH:=48H;
	r.BX:=0FFFFH;
	Dos(r);
	r.AH:=48H;
	Dos(r);
	HeapBottom:=r.AX;
	HeapTop:=r.AX+r.BX-1;
	lastMarker:=0;
	Collect
END Memory.


