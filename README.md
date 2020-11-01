language-Modula2 - Modula-2 parser, pretty-printer, and more
------------------------------------------------------------

This package provides a library and executable for parsing and processing the source code in programming language
Modula-2. The following functionality is presently available:

* Parsing with the grammars specified in the
  [Grammar](http://hackage.haskell.org/package/language-modula-2/docs/Language-Modula-2-Grammar.html) module.
* Constant folding with the
  [ConstantFolder](http://hackage.haskell.org/package/language-modula-2/docs/Language-Modula-2-ConstantFolder.html) module.
* Pretty-printing of a parsed AST with the
  [Pretty](http://hackage.haskell.org/package/language-modula-2/docs/Language-Modula-2-Pretty.html) module.

Much of this functionality is reused from the [`language-oberon`](http://hackage.haskell.org/package/language-oberon)
package, and more should be coming in due course.
