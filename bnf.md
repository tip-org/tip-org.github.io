% TIP BNF

This document contains the BNF of the [TIP](index.html) format, which is
an extension of [SMT-LIB](http://smt-lib.org) for expression inductive
problems. The grammar is written in
[BNFC](http://bnfc.digitalgrammars.com/) syntax. The format is also
decribed in [prose](format.html) with examples.

``` {.bnfc}
comment ";";
Start. Start ::= [Decl];

[].  [Decl] ::= "(" "check-sat" ")";
(:). [Decl] ::= "(" Decl ")"  [Decl];

DeclareDatatypes. Decl ::= "declare-datatypes" "(" [Symbol] ")" "(" [Datatype] ")";
DeclareSort.      Decl ::= "declare-sort" Symbol Integer;
DeclareConst.     Decl ::= "declare-const" ConstDecl;
DeclareConstPar.  Decl ::= "declare-const" "(" Par "(" ConstDecl ")" ")";
DeclareFun.       Decl ::= "declare-fun" FunDecl;
DeclareFunPar.    Decl ::= "declare-fun" "(" Par "(" FunDecl ")" ")";
DefineFun.        Decl ::= "define-fun" FunDef;
DefineFunPar.     Decl ::= "define-fun" "(" Par "(" FunDef ")" ")";
DefineFunRec.     Decl ::= "define-fun-rec" FunDef;
DefineFunRecPar.  Decl ::= "define-fun-rec" "(" Par "(" FunDef ")" ")";
DefineFunsRec.    Decl ::= "define-funs-rec" "(" [FunDec] ")" "(" [Expr] ")";
Assert.           Decl ::= Assertion Expr;
AssertPar.        Decl ::= Assertion "(" Par Expr ")";

AssertIt.  Assertion ::= "assert";
AssertNot. Assertion ::= "assert-not";

Par.         Par    ::= "par" "(" [Symbol] ")";

ConstDecl.   ConstDecl ::= Symbol Type;

FunDecl.     FunDecl ::= Symbol "(" [Type] ")" Type;

FunDef.      FunDef ::= Symbol "(" [Binding] ")" Type Expr;

ParFunDec.   FunDec ::= "(" Par InnerFunDec ")";
MonoFunDec.  FunDec ::= InnerFunDec;
InnerFunDec. InnerFunDec ::= "(" Symbol "(" [Binding] ")" Type ")";

Datatype.     Datatype ::= "(" Symbol [Constructor] ")";
Constructor.  Constructor ::= "(" Symbol [Binding] ")";

Binding. Binding ::= "(" Symbol Type ")";

LetDecl. LetDecl ::= "(" Symbol Expr ")";

TyVar.   Type ::= Symbol;
TyApp.   Type ::= "(" Symbol [Type] ")";
ArrowTy. Type ::= "(" "=>" [Type] ")";
IntTy.   Type ::= "Int";
BoolTy.  Type ::= "Bool";

Var.       Expr ::= Symbol;
As.        Expr ::= "(" "as" Expr Type ")";
App.       Expr ::= "(" Head [Expr] ")";
Match.     Expr ::= "(" "match" Expr [Case] ")";
Let.       Expr ::= "(" "let" "(" [LetDecl] ")" Expr ")";
Binder.    Expr ::= "(" Binder "(" [Binding] ")" Expr ")";
LitInt.    Expr ::= Integer;
LitNegInt. Expr ::= "-" Integer;
LitTrue.   Expr ::= "true";
LitFalse.  Expr ::= "false";

Lambda. Binder ::= "lambda";
Forall. Binder ::= "forall";
Exists. Binder ::= "exists";

Case.    Case ::= "(" "case" Pattern Expr ")";

Default.    Pattern ::= "default";
ConPat.     Pattern ::= "(" Symbol [Symbol] ")";
SimplePat.  Pattern ::= Symbol;

Const.      Head ::= Symbol;
At.         Head ::= "@";
IfThenElse. Head ::= "ite";
And.        Head ::= "and";
Or.         Head ::= "or";
Not.        Head ::= "not";
Implies.    Head ::= "=>";
Equal.      Head ::= "=";
Distinct.   Head ::= "distinct";
IntAdd.     Head ::= "+";
IntSub.     Head ::= "-";
IntMul.     Head ::= "*";
IntDiv.     Head ::= "div";
IntMod.     Head ::= "mod";
IntGt.      Head ::= ">";
IntGe.      Head ::= ">=";
IntLt.      Head ::= "<";
IntLe.      Head ::= "<=";

terminator LetDecl "";
terminator Case "";
terminator Expr "";
terminator Datatype "";
terminator Constructor "";
terminator Binding "";
terminator Symbol "";
terminator Type "";
terminator FunDecl "";
terminator FunDef "";
terminator FunDec "";

position token Symbol (letter|["~!@$%^&*_+=<>.?/"])(letter|digit|["~!@$%^&*_-+=<>.?/"])*;
```
