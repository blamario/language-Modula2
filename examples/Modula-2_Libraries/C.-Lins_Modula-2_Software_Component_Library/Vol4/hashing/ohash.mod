IMPLEMENTATION MODULE OHash;
(*==============================================================
    Version  : 2.0 16 Sep 1990 C. Lins
    Compiler : Generic pc Modula-2
    Component: Hash Table - Sequential Bounded Managed Iterator
              Collision resolution using double hashing

    REVISION HISTORY
    v1.00  22 Apr 1989  C. Lins:
        Initial Modula-2 implementation
    v1.01  30 Jun 1989  C. Lins:
        Removed separation of key and data.
    v1.02  21 Aug 1989  C. Lins:
        Added HashOf selector.
    v1.03  29 Aug 1989  C. Lins:
        Added HashOf selector.
    v1.04  03 Sep 1989  C. Lins:
        Copy hashing function to target hash table in Assign.
    v1.05  19 Sep 1989  C. Lins:
       Pass back result from hash table for key from searches
       instead of key parameter.

   v2.00  16 Sep 1990  C. Lins
     Created generic pc version
   (C) Copyright 1990 Charles A. Lins
==============================================================*)

FROM SCLStorage IMPORT
   (*--proc*) Allocate, Deallocate;

FROM Relations IMPORT
   (*--type*) Relation;

FROM HashTypes IMPORT
   (*--type*) Exceptions, Operations, ComponentID,
              FoundProc, NotFoundProc, UpdateProc, LoopProc,
              AccessProc, HashFunction, States, Key, Data;

FROM Items IMPORT
   (*--cons*) NullItem,
   (*--type*) Item, AssignProc, CompareProc, DisposeProc;

FROM ErrorHandling IMPORT
   (*--cons*) NullHandler,
   (*--type*) HandlerProc,
   (*--proc*) Raise;

FROM TypeManager IMPORT
   (*--cons*) NullType,
   (*--type*) TypeID,
   (*--proc*) AssignOf, CompareOf, DisposeOf;

   (*-------------------------*)

VAR   tableError : Exceptions;
VAR   handlers   : ARRAY Exceptions OF HandlerProc;

PROCEDURE TableError () : Exceptions               (*--out  *);
BEGIN
  RETURN tableError;
END TableError;
(*-------------------------*)

PROCEDURE SetHandler (    theError   : Exceptions  (*--in   *);
                          theHandler : HandlerProc (*--in   *));
BEGIN
  handlers[theError] := theHandler;
END SetHandler;
(*-------------------------*)

PROCEDURE GetHandler (    theError   : Exceptions  (*--in   *))
                                     : HandlerProc (*--out  *);
BEGIN
  RETURN handlers[theError];
END GetHandler;
(*-------------------------*)

PROCEDURE RaiseErrIn (    theRoutine : Operations  (*--in   *);
                          theError   : Exceptions  (*--in   *));
BEGIN
  tableError := theError;
  Raise(ComponentID + ModuleID, theRoutine, theError, handlers[theError]);
END RaiseErrIn;
(*-------------------------*)


TYPE  HashTable  = POINTER TO BoundedHashTable;
TYPE  TableEntry = RECORD
        state : States;
        key   : Key;
        data  : Data;
      END (*-- TableEntry --*);
TYPE  HashingTable = ARRAY [0..0] OF TableEntry;

TYPE  BoundedHashTable = RECORD
        keyID   : TypeID;
        dataID  : TypeID;
        h       : HashFunction;
        size    : CARDINAL;
        extent  : CARDINAL;
        table   : HashingTable;
      END (*-- BoundedHashTable --*);


PROCEDURE InitToEmpty (    theTable : HashTable (*--inout*));

VAR   index : CARDINAL;

BEGIN
  WITH theTable^ DO
    FOR index := 0 TO size-1 DO
      table[index].state := empty;
    END (*--for*);
  END (*--with*);
END InitToEmpty;
(*-------------------------*)

PROCEDURE FreeTableEntry (    theTable : HashTable  (*--in   *);
                              theEntry : TableEntry (*--inout*));

VAR   free : DisposeProc;  (*-- key/data disposal routine *)

BEGIN
  free := DisposeOf(theTable^.keyID);
  free(theEntry.key);
  free := DisposeOf(theTable^.dataID);
  free(theEntry.data);
END FreeTableEntry;
(*-------------------------*)

PROCEDURE Hash (    hashAddress: CARDINAL  (*--in   *);
                    tableSize  : CARDINAL  (*--in   *);
                VAR theBucket  : CARDINAL  (*--out  *);
                VAR increment  : CARDINAL  (*--out  *));
BEGIN
   theBucket   := hashAddress MOD tableSize;
   increment   := hashAddress DIV tableSize;
   IF (increment = 0) THEN
     increment := 1;
   END (*--if*);
END Hash;
(*-------------------------*)

(*
Search the given hash table for the given key returning the index
into the hash table where the key was found. Finding an empty
slot in the table causes the index to the last empty or deleted
slot encountered during the search.
*)

PROCEDURE Search   (    theTable   : HashTable     (*--in   *);
                        theKey     : Key           (*--in   *);
                    VAR theBucket  : CARDINAL      (*--out  *))
                                   : BOOLEAN       (*--out  *);

VAR  index     : CARDINAL;     (*-- loop index over table entries *)
     incr      : CARDINAL;     (*-- increment *)
     last      : CARDINAL;     (*-- last table entry to examine *)
     compare   : CompareProc;  (*-- key comparison routine *)
     comparison: Relation;     (*-- compare result *)

BEGIN
  theBucket := 0;
  WITH theTable^ DO
    compare := CompareOf(keyID);
    Hash(h(theKey), size, index, incr);
    last := (index + (size - 1) * incr) MOD size;
    WHILE (index # last) DO
      WITH table[index] DO
        CASE state OF
          empty:
            IF (theBucket = 0) THEN
              theBucket := index;
            END (*--if*);
            RETURN FALSE;
        | deleted:
            IF (theBucket = 0) THEN
              theBucket := index;
            END (*--if*);
        | used:
            comparison := compare(theKey, key);
            IF (comparison = equal) THEN
              theBucket := index;
              RETURN TRUE;
            ELSIF (comparison = greater) THEN
              theBucket := index;
              RETURN FALSE;
            END (*--if*);
        END (*--case*);
      END (*--with*);
      index := (index + incr) MOD size;
    END (*--while*);
  END (*--with*);
  RETURN FALSE;
END Search;
(*-------------------------*)

PROCEDURE AddTableEntry (    theTable : HashTable  (*--inout*);
                            theKey   : Key         (*--in   *);
                            theData  : Data        (*--in   *);
                            theProc  : Operations  (*--in   *));

VAR  index     : CARDINAL;     (*-- bucket where to insert *)
     incr      : CARDINAL;     (*-- increment value *)
     compare   : CompareProc;
     comparison: Relation;
     tempData  : Item;

BEGIN
  WITH theTable^ DO
   compare := CompareOf(keyID);
   Hash(h(theKey), size, index, incr);
   LOOP
     WITH table[index] DO
       IF (state = used) THEN
         comparison := compare(key, theKey);
         IF (comparison = equal) THEN
           RaiseErrIn(theProc, duplicatekey);
           EXIT (*--loop*);
         ELSIF (comparison = greater) THEN
           tempData := theKey;
           theKey   := key;
           key      := tempData;
           tempData := theData;
           theData  := data;
           data     := tempData;
         END (*--if*);
       ELSE
         (*-- empty or deleted --*)
         state := used;
         key   := theKey;
         data  := theData;
         INC(extent);
         EXIT (*--loop*);
       END (*--if*);
     END (*--with*);
     index := (index + incr) MOD size;
   END (*--loop*);
  END (*--with*);
END AddTableEntry;
(*-------------------------*)


PROCEDURE Create   (    keyTypeID  : TypeID        (*--in   *);
                        dataTypeID : TypeID        (*--in   *);
                        theSize    : CARDINAL      (*--in   *);
                        hashFunc   : HashFunction  (*--in   *))
                                   : HashTable     (*--out  *);

CONST baseSize  = SIZE(BoundedHashTable) - SIZE(HashingTable);
CONST entrySize = SIZE(TableEntry);

VAR   newTable : HashTable; (*--temporary for new hash table object *)

BEGIN
  tableError := noerr;
  Allocate(newTable, baseSize + theSize * entrySize);
  IF (newTable = NullTable) THEN
    RaiseErrIn(create, overflow);
  ELSE
    WITH newTable^ DO
      keyID  := keyTypeID;
      dataID := dataTypeID;
      extent := 0;
      size   := theSize;
      h      := hashFunc;
    END (*--with*);
    InitToEmpty(newTable);
  END (*--if*);
  RETURN newTable;
END Create;
(*-------------------------*)

PROCEDURE Destroy  (VAR theTable   : HashTable     (*--inout*));
CONST baseSize  = SIZE(BoundedHashTable) - SIZE(HashingTable);
CONST entrySize = SIZE(TableEntry);
BEGIN
  Clear(theTable);
  IF (tableError = noerr) THEN
    Deallocate(theTable, baseSize + theTable.size * entrySize);
  END (*--if*);
END Destroy;
(*-------------------------*)

PROCEDURE Clear        (    theTable   : HashTable     (*--inout*));

VAR   index : CARDINAL;

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(clear, undefined);
  ELSE
    WITH theTable^ DO
      FOR index := 0 TO size-1 DO
        IF (table[index].state = used) THEN
          FreeTableEntry(theTable, table[index]);
        END (*--if*);
      END (*--for*);
      extent := 0;
    END (*--with*);
    InitToEmpty(theTable);
  END (*--if*);
END Clear;
(*-------------------------*)

PROCEDURE Assign   (    theTable   : HashTable     (*--in   *);
                    VAR toTable    : HashTable     (*--inout*));

  PROCEDURE RecreateTarget () : BOOLEAN (*--out *);
  BEGIN
    IF (theTable = NullTable) THEN
      RaiseErrIn(assign, undefined);
    ELSIF (toTable = NullTable) THEN
      WITH theTable^ DO
        toTable := Create(keyID, dataID, size, h);
      END (*--with*);
    ELSIF (toTable = theTable) THEN
      RETURN FALSE;
    ELSIF (toTable^.size >= theTable^.extent) THEN
      Clear(toTable);
      WITH theTable^ DO
        toTable^.keyID  := keyID;
        toTable^.dataID := dataID;
        toTable^.h      := h;
      END (*--with*);
    ELSE
      RaiseErrIn(assign, overflow);
    END (*--if*);
    RETURN tableError = noerr;
  END RecreateTarget;

VAR  assignKey  : AssignProc; (*-- key assignment routine *)
     assignData : AssignProc; (*-- data assignment routine *)
     index      : CARDINAL;   (*-- loop index over table entries *)

BEGIN
  tableError := noerr;
  IF RecreateTarget() THEN
    WITH theTable^ DO
      assignKey  := AssignOf(keyID);
      assignData := AssignOf(dataID);
      FOR index := 0 TO size-1 DO
        WITH table[index] DO
          IF (state = used) THEN
            Insert(toTable, assignKey(key), assignData(data));
          END (*--if*);
        END (*--with*);
      END (*--for*);
    END (*--with*);
  END (*--if*);
END Assign;
(*-------------------------*)

PROCEDURE Insert   (    theTable   : HashTable     (*--inout*);
                        theKey     : Key           (*--in   *);
                        theData    : Data          (*--in   *));
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(insert, undefined);
  ELSIF (theTable^.extent >= theTable^.size) THEN
   RaiseErrIn(insert, overflow);
  ELSE
    AddTableEntry(theTable, theKey, theData, insert);
  END (*--if*);
END Insert;
(*-------------------------*)

PROCEDURE Remove   (    theTable   : HashTable     (*--inout*);
                        theKey     : Key           (*--in   *);
                        notFound   : NotFoundProc  (*--in   *));

VAR   index : CARDINAL;        (*-- bucket where key was found *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(remove, undefined);
  ELSIF Search(theTable, theKey, index) THEN
    WITH theTable^ DO
      FreeTableEntry(theTable, table[index]);
      table[index].state := deleted;
      DEC(extent);
    END (*--with*);
  ELSE
    notFound(theKey);
  END (*--if*);
END Remove;
(*-------------------------*)

PROCEDURE Update   (    theTable   : HashTable     (*--inout*);
                        theKey     : Key           (*--in   *);
                        theData    : Data          (*--in   *);
                        updateEntry: UpdateProc    (*--in   *));

VAR   index : CARDINAL;        (*-- bucket where key was found *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(remove, undefined);
  ELSIF Search(theTable, theKey, index) THEN
    updateEntry(theTable^.table[index].key, theTable^.table[index].data, theData);
  ELSIF (theTable^.extent >= theTable^.size) THEN
    RaiseErrIn(update, overflow);
  ELSE
    AddTableEntry(theTable, theKey, theData, update);
  END (*--if*);
END Update;
(*-------------------------*)


PROCEDURE IsDefined (    theTable  : HashTable     (*--in   *))
                                   : BOOLEAN       (*--out  *);
BEGIN
  RETURN (theTable # NullTable);
END IsDefined;
(*-------------------------*)

PROCEDURE IsEmpty  (    theTable   : HashTable     (*--in   *))
                                   : BOOLEAN       (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(isempty, undefined);
    RETURN TRUE;
  END (*--if*);
  RETURN theTable^.extent = 0;
END IsEmpty;
(*-------------------------*)

PROCEDURE KeyTypeOf (    theTable  : HashTable     (*--in   *))
                                   : TypeID        (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(typeof, undefined);
    RETURN NullType;
  END (*--if*);
  RETURN theTable^.keyID;
END KeyTypeOf;
(*-------------------------*)

PROCEDURE DataTypeOf(    theTable  : HashTable     (*--in   *))
                                   : TypeID        (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(typeof, undefined);
    RETURN NullType;
  END (*--if*);
  RETURN theTable^.dataID;
END DataTypeOf;
(*-------------------------*)

PROCEDURE HashOf    (    theTable  : HashTable     (*--in   *))
                                   : HashFunction  (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(hashof, undefined);
    RETURN VAL(HashFunction, NIL);
  END (*--if*);
  RETURN theTable^.h;
END HashOf;
(*-------------------------*)

PROCEDURE SizeOf    (    theTable  : HashTable     (*--in   *))
                                   : CARDINAL      (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(sizeof, undefined);
    RETURN 0;
  END (*--if*);
  RETURN theTable^.size;
END SizeOf;
(*-------------------------*)

PROCEDURE ExtentOf  (    theTable  : HashTable     (*--in   *))
                                   : CARDINAL      (*--out  *);
BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(extentof, undefined);
    RETURN 0;
  END (*--if*);
  RETURN theTable^.extent;
END ExtentOf;
(*-------------------------*)

PROCEDURE IsPresent(    theTable   : HashTable     (*--in   *);
                        theKey     : Key           (*--in   *);
                        found      : FoundProc     (*--in   *);
                        notFound   : NotFoundProc  (*--in   *));

VAR   index : CARDINAL;        (*-- bucket where item was found *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(ispresent, undefined);
  ELSIF Search(theTable, theKey, index) THEN
    found(theTable^.table[index].key, theTable^.table[index].data);
  ELSE
    notFound(theKey);
  END (*--if*);
END IsPresent;
(*-------------------------*)


PROCEDURE LoopOver (    theTable   : HashTable     (*--in   *);
                        process    : LoopProc      (*--in   *));

VAR   index : CARDINAL;        (*-- loop index over hashing table *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(loopover, undefined);
  ELSE
    WITH theTable^ DO
      FOR index := 0 TO size-1 DO
        WITH table[index] DO
          IF (state = used) & ~process(key, data) THEN
            RETURN;
          END (*--if*);
        END (*--with*);
      END (*--for*);
    END (*--with*);
  END (*--if*);
END LoopOver;
(*-------------------------*)

PROCEDURE Traverse (    theTable   : HashTable     (*--in   *);
                        process    : AccessProc    (*--in   *));

VAR   index : CARDINAL;        (*-- loop index over hashing table *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(traverse, undefined);
  ELSE
    WITH theTable^ DO
      FOR index := 0 TO size-1 DO
        WITH table[index] DO
          IF (state = used) THEN
            process(key, data);
          END (*--if*);
        END (*--with*);
      END (*--for*);
    END (*--with*);
  END (*--if*);
END Traverse;
(*-------------------------*)

PROCEDURE Iterate  (    theTable   : HashTable     (*--in   *);
                        process    : IterateProc   (*--in   *));

VAR   index : CARDINAL;        (*-- loop index over hashing table *)

BEGIN
  tableError := noerr;
  IF (theTable = NullTable) THEN
    RaiseErrIn(traverse, undefined);
  ELSE
    WITH theTable^ DO
      FOR index := 0 TO size-1 DO
        WITH table[index] DO
          CASE state OF
            used:
              process(index, state, key, data);
          | empty, deleted:
              process(index, state, NullItem, NullItem);
          END (*--case*);
        END (*--with*);
      END (*--for*);
    END (*--with*);
  END (*--if*);
END Iterate;
(*-------------------------*)


BEGIN
  FOR tableError := MIN(Exceptions) TO MAX(Exceptions) DO
    SetHandler(tableError, NullHandler);
  END (*--for*);
  SetHandler(noerr, NullHandler);
  tableError := noerr;
  NullTable := NIL;
END OHash.