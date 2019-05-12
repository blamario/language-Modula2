IMPLEMENTATION MODULE TextLines;

	(********************************************************)
	(*							*)
	(*  Drawing horizontal and vertical lines in text mode	*)
	(*							*)
	(*  Programmer:		P. Moylan			*)
	(*  Last edited:	25 November 1994		*)
	(*  Status:		Working				*)
	(*							*)
	(********************************************************)

FROM SYSTEM IMPORT
    (* type *)	BYTE;

FROM Windows IMPORT
    (* proc *)	ReadBack, SetCursor, WriteChar;

FROM LowLevel IMPORT
    (* proc *)	LSB, IORB, IANDB;

(************************************************************************)
(*			GLOBAL DECLARATIONS				*)
(************************************************************************)

TYPE
    (* On PC-compatible machines, line graphics can be done with	*)
    (* characters from the following range.				*)
    (*		│┤╡╢╖╕╣║╗╝╜╛┐└┴┬├─┼╞╟╚╔╩╦╠═╬╧╨╤╥╙╘╒╓╫╪┘┌		*)

    GraphicsCharRange = [CHR(179)..CHR(218)];

    (* Internally, we represent a graphics character by a 4-tuple	*)
    (* (N,E,S,W), where the components represent the north, east,	*)
    (* south, and west sides of the character.  Each component is	*)
    (* encoded as 0=nothing, 1=single, 2=double, 3=triple; and we pack	*)
    (* all four as an 8-bit quantity.  Of course there's no hardware	*)
    (* support for the triple-line case, but it simplifies the coding	*)
    (* if we pretend that there is.					*)

    PackedCode = BYTE;
    EncodingTable = ARRAY PackedCode OF CHAR;
    DecodingTable = ARRAY GraphicsCharRange OF PackedCode;

CONST
    (* The following table converts packed codes to characters.  The	*)
    (* packed code should be read as NNEESSWW.				*)

    CharTable = EncodingTable (

		(* Codes 00000000..00001111 *)
	' ','─','═','═','│','┐','╕','╕','║','╖','╗','╗','║','╖','╗','╗',
		(* Codes 00010000..00011111 *)
	'─','─','═','═','┌','┬','╤','╤','╓','╥','╦','╦','╓','╥','╦','╦',
		(* Codes 00100000..00101111 *)
	'═','═','═','═','╒','╤','╤','╤','╔','╦','╦','╦','╔','╦','╦','╦',
		(* Codes 00110000..00111111 *)
	'═','═','═','═','╒','╤','╤','╤','╔','╦','╦','╦','╔','╦','╦','╦',

		(* Codes 01000000..01001111 *)
	'│','┘','╛','╛','│','┤','╡','╡','║','╢','╣','╣','║','╢','╣','╣',
		(* Codes 01010000..01011111 *)
	'└','┴','╧','╧','├','┼','╪','╪','╟','╫','╬','╬','╟','╫','╬','╬',
		(* Codes 01100000..01101111 *)
	'╘','╧','╧','╧','╞','╪','╪','╪','╠','╬','╬','╬','╠','╬','╬','╬',
		(* Codes 01110000..01111111 *)
	'╘','╧','╧','╧','╞','╪','╪','╪','╠','╬','╬','╬','╠','╬','╬','╬',

		(* Codes 10000000..10001111 *)
	'║','╜','╝','╝','║','╢','╣','╣','║','╢','╣','╣','║','╢','╣','╣',
		(* Codes 10010000..10011111 *)
	'╙','╨','╩','╩','╟','╫','╬','╬','╟','╫','╬','╬','╟','╫','╬','╬',
		(* Codes 10100000..10101111 *)
	'╚','╩','╩','╩','╠','╬','╬','╬','╠','╬','╬','╬','╠','╬','╬','╬',
		(* Codes 10110000..10111111 *)
	'╚','╩','╩','╩','╠','╬','╬','╬','╠','╬','╬','╬','╠','╬','╬','╬',

		(* Codes 11000000..11001111 *)
	'║','╜','╝','╝','║','╢','╣','╣','║','╢','╣','╣','║','╢','╣','╣',
		(* Codes 11010000..11011111 *)
	'╙','╨','╩','╩','╟','╫','╬','╬','╟','╫','╬','╬','╟','╫','╬','╬',
		(* Codes 11100000..11101111 *)
	'╚','╩','╩','╩','╠','╬','╬','╬','╠','╬','╬','╬','╠','╬','╬','╬',
		(* Codes 11110000..11111111 *)
	'╚','╩','╩','╩','╠','╬','╬','╬','╠','╬','╬','╬','╠','╬','╬','╬');

    (* The following table converts characters to packed codes.	*)

    CodeTable = DecodingTable (
		    44H,45H,46H,89H,09H,06H,8AH,88H,	(* │┤╡╢╖╕╣║ *)
		    0AH,82H,81H,42H,05H,50H,51H,15H,	(* ╗╝╜╛┐└┴┬ *)
		    54H,11H,55H,64H,98H,0A0H,28H,0A2H,	(* ├─┼╞╟╚╔╩ *)
		    2AH,0A8H,22H,0AAH,62H,91H,26H,19H,	(* ╦╠═╬╧╨╤╥ *)
		    90H,60H,24H,18H,99H,66H,41H,14H);	(* ╙╘╒╓╫╪┘┌ *)

(************************************************************************)
(*		     DECODING OF GRAPHICS CHARACTERS			*)
(************************************************************************)

PROCEDURE Decode (char: CHAR): PackedCode;

    (* Converts a character to a PackedCode representation.	*)

    TYPE CharSet = SET OF CHAR;

    CONST GraphicsChars = CharSet
			{MIN(GraphicsCharRange)..MAX(GraphicsCharRange)};

    BEGIN
	IF char IN GraphicsChars THEN
	    RETURN CodeTable[char];
	ELSE
	    RETURN PackedCode(0);
	END (*IF*);
    END Decode;

(************************************************************************)
(*			 WRITING TO THE SCREEN				*)
(************************************************************************)

PROCEDURE PutChar (w: Window;  row, col: CARDINAL;
				N, E, S, W: LineType;  mask: PackedCode);

    (* Adds a new part of a line, described by (N,E,S,W), at location	*)
    (* (row,col) in window w.  The mask is applied to the graphics	*)
    (* character, if any, that is already present at that screen	*)
    (* location: we can selectively remove parts of that character.	*)

    VAR code: PackedCode;

    BEGIN
	(* Decode the existing character. *)

	code := IANDB (Decode(ReadBack (w, row, col)), mask);

	(* Encode and write the character for a combined code. *)

	code := IORB (code, LSB(BYTE(N),6) + LSB(BYTE(E),4)
				+ LSB(BYTE(S),2) + BYTE(W));
	SetCursor (w, row, col);
	WriteChar (w, CharTable[code]);

    END PutChar;

(************************************************************************)
(*		    THE EXTERNALLY CALLABLE PROCEDURES			*)
(************************************************************************)

PROCEDURE HLine (w: Window;  row, col1, col2: CARDINAL;  type: LineType);

    (* Draws a horizontal line from (row,col1) to (row,col2).	*)

    VAR j: CARDINAL;

    BEGIN
	IF col1 > col2 THEN
	    j := col1;  col1 := col2;  col2 := j;
	END (*IF*);
	PutChar (w, row, col1, none, type, none, none, 0CFH);
	FOR j := col1+1 TO col2-1 DO
	    PutChar (w, row, j, none, type, none, type, 0CCH);
	END (*FOR*);
	PutChar (w, row, col2, none, none, none, type, 0FCH);
    END HLine;

(************************************************************************)

PROCEDURE VLine (w: Window;  col, row1, row2: CARDINAL;  type: LineType);

    (* Draws a vertical line from (row1,col) to (row2,col).	*)

    VAR i: CARDINAL;

    BEGIN
	IF row1 > row2 THEN
	    i := row1;  row1 := row2;  row2 := i;
	END (*IF*);
	PutChar (w, row1, col, none, none, type, none, 0F3H);
	FOR i := row1+1 TO row2-1 DO
	    PutChar (w, i, col, type, none, type, none, 033H);
	END (*FOR*);
	PutChar (w, row2, col, type, none, none, none, 03FH);
    END VLine;

(************************************************************************)

PROCEDURE Box (w: Window;  top, left, width, height: CARDINAL;
							type: LineType);

    (* Draws a rectangular box whose top left corner is at (top,left)	*)
    (* and with the given width and height.				*)

    VAR i: CARDINAL;

    BEGIN
	(* Put in the corners. *)

	PutChar (w, top, left, none, type, type, none, 0C3H);
	PutChar (w, top, left+width, none, none, type, type, 0F0H);
	PutChar (w, top+height, left, type, type, none, none, 00FH);
	PutChar (w, top+height, left+width, type, none, none, type, 03CH);

	(* Now the sides. *)

	HLine (w, top, left, left+width, type);
	HLine (w, top+height, left, left+width, type);
	VLine (w, left, top, top+height, type);
	VLine (w, left+width, top, top+height, type);

    END Box;

(************************************************************************)

END TextLines.
