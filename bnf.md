% TIP BNF

This document contains the BNF of the [TIP](index.html) format,
which is an extension of [SMT-LIB](http://smt-lib.org)
for expression inductive problems.
The grammar is written in [BNFC](http://bnfc.digitalgrammars.com/) syntax.
The format is also decribed in [prose](format.html) with examples.

```{.bnfc}
comment ";";
Start. Start ::= [Decl];

[].  [Decl] ::= "(" "check-sat" ")";
(:). [Decl] ::= "(" Decl ")"  [Decl];

DeclareDatatypes. Decl ::= "declare-datatypes" "(" [Symbol] ")" "(" [Datatype] ")";
DeclareSort.      Decl ::= "declare-sort" Symbol Integer;
DeclareFun.       Decl ::= "declare-fun" FunDecl;
DefineFunsRec.    Decl ::= "define-funs-rec" "(" [FunDef] ")" "(" [Expr] ")";
MonoAssert.       Decl ::= Assertion Expr;
ParAssert.        Decl ::= Assertion "(" "par" "(" [Symbol] ")" Expr ")";

AssertIt.  Assertion ::= "assert";
AssertNot. Assertion ::= "assert-not";

ParFunDef.   FunDef ::= "(" "par" "(" [Symbol] ")" InnerFunDef ")";
MonoFunDef.  FunDef ::= InnerFunDef;
InnerFunDef. InnerFunDef ::= "(" Symbol "(" [Binding] ")" Type ")";

ParFunDecl.   FunDecl ::= "(" "par" "(" [Symbol] ")" "(" InnerFunDecl ")" ")";
MonoFunDecl.  FunDecl ::= InnerFunDecl;
InnerFunDecl. InnerFunDecl ::= Symbol "(" [Type] ")" Type;

Datatype.     Datatype ::= "(" Symbol [Constructor] ")";
Constructor.  Constructor ::= "(" Symbol [Binding] ")";

Binding. Binding ::= "(" Symbol Type ")";

LetDecl. LetDecl ::= "(" Binding Expr ")";

TyVar.   Type ::= Symbol;
TyApp.   Type ::= "(" Symbol [Type] ")";
ArrowTy. Type ::= "(" "=>" [Type] ")";
IntTy.   Type ::= "int";
BoolTy.  Type ::= "bool";

Var.      Expr ::= Symbol;
As.       Expr ::= "(" "as" Expr Type ")";
App.      Expr ::= "(" Head [Expr] ")";
Match.    Expr ::= "(" "match" Expr [Case] ")";
Let.      Expr ::= "(" "let" "(" [LetDecl] ")" Expr ")";
Binder.   Expr ::= "(" Binder "(" [Binding] ")" Expr ")";
LitInt.   Expr ::= Integer;
LitTrue.  Expr ::= "true";
LitFalse. Expr ::= "false";

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

position token Symbol (letter|["~!@$%^&*_-+=<>.?/"])(letter|digit|["~!@$%^&*_-+=<>.?/"])*;
```

