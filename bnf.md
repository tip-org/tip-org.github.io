% TIP BNF

This document contains the BNF of the [TIP](index.html) format, which is
an extension of [SMT-LIB](http://smt-lib.org) for expression inductive
problems. The grammar is written in
[BNFC](http://bnfc.digitalgrammars.com/) syntax. The format is also
decribed in [prose](format.html) with examples.

``` {.bnfc}
comment ";";
Start. Start ::= [Decl];

[].  [Decl] ::= ;
(:). [Decl] ::= "(" Decl ")"  [Decl];

DeclareDatatype.  Decl ::= "declare-datatype" AttrSymbol Datatype;
DeclareDatatypes. Decl ::= "declare-datatypes" "(" [DatatypeName] ")" "(" [Datatype] ")";
DeclareSort.      Decl ::= "declare-sort" AttrSymbol Integer;
DeclareConst.     Decl ::= "declare-const" AttrSymbol ConstType ;
DeclareFun.       Decl ::= "declare-fun" AttrSymbol FunType;
DefineFun.        Decl ::= "define-fun" FunDec Expr;
DefineFunRec.     Decl ::= "define-fun-rec" FunDec Expr;
DefineFunsRec.    Decl ::= "define-funs-rec" "(" [BracketedFunDec] ")" "(" [Expr] ")";
Formula.          Decl ::= Assertion [Attr] Expr;
FormulaPar.       Decl ::= Assertion [Attr] "(" Par Expr ")";

Assert. Assertion ::= "assert";
Prove.  Assertion ::= "prove";

Par.         Par    ::= "par" "(" [Symbol] ")";

ConstTypeMono. ConstType ::= Type;
ConstTypePoly. ConstType ::= "(" Par Type ")";

InnerFunType. InnerFunType ::= "(" [Type] ")" Type;
FunTypeMono.  FunType ::= InnerFunType;
FunTypePoly.  FunType ::= "(" Par "(" InnerFunType ")" ")";

InnerFunDec.  InnerFunDec ::= "(" [Binding] ")" Type;
FunDecMono.   FunDec ::= AttrSymbol InnerFunDec;
FunDecPoly.   FunDec ::= AttrSymbol "(" Par "(" InnerFunDec ")" ")";
BracketedFunDec. BracketedFunDec ::= "(" FunDec ")";

DatatypeName. DatatypeName ::= "(" AttrSymbol Integer ")";
InnerDatatype. InnerDatatype ::= "(" [Constructor] ")";
DatatypeMono. Datatype ::= InnerDatatype;
DatatypePoly. Datatype ::= "(" Par InnerDatatype ")";
Constructor.  Constructor ::= "(" AttrSymbol [Binding] ")";

Binding. Binding ::= "(" Symbol Type ")";

LetDecl. LetDecl ::= "(" Symbol Expr ")";

TyVar.   Type ::= Symbol;
TyApp.   Type ::= "(" Symbol [Type] ")";
ArrowTy. Type ::= "(" "=>" [Type] ")";
IntTy.   Type ::= "Int";
RealTy.  Type ::= "Real";
BoolTy.  Type ::= "Bool";

Var.       Expr ::= PolySymbol;
App.       Expr ::= "(" Head [Expr] ")";
Match.     Expr ::= "(" "match" Expr "(" [Case] ")" ")";
Let.       Expr ::= "(" "let" "(" [LetDecl] ")" Expr ")";
Binder.    Expr ::= "(" Binder "(" [Binding] ")" Expr ")";
Lit.       Expr ::= Lit;

LitInt.    Lit ::= Integer;
LitNegInt. Lit ::= "-" Integer;
LitTrue.   Lit ::= "true";
LitFalse.  Lit ::= "false";

Lambda. Binder ::= "lambda";
Forall. Binder ::= "forall";
Exists. Binder ::= "exists";

Case.    Case ::= "(" Pattern Expr ")";

Default.    Pattern ::= "_";
ConPat.     Pattern ::= "(" Symbol [Symbol] ")";
SimplePat.  Pattern ::= Symbol;
LitPat.     Pattern ::= Lit;

Const.      Head ::= PolySymbol;
At.         Head ::= "@";
IfThenElse. Head ::= "ite";
And.        Head ::= "and";
Or.         Head ::= "or";
Not.        Head ::= "not";
Implies.    Head ::= "=>";
Equal.      Head ::= "=";
Distinct.   Head ::= "distinct";
NumAdd.     Head ::= "+";
NumSub.     Head ::= "-";
NumMul.     Head ::= "*";
NumDiv.     Head ::= "/";
IntDiv.     Head ::= "div";
IntMod.     Head ::= "mod";
NumGt.      Head ::= ">";
NumGe.      Head ::= ">=";
NumLt.      Head ::= "<";
NumLe.      Head ::= "<=";
NumWiden.   Head ::= "to_real";

NoAs. PolySymbol ::= Symbol;
As.   PolySymbol ::= "(" "_" Symbol [Type] ")";

AttrSymbol. AttrSymbol ::= Symbol [Attr];
NoValue. Attr ::= Keyword;
Value.   Attr ::= Keyword Symbol;

terminator LetDecl "";
terminator Case "";
terminator Expr "";
terminator Datatype "";
terminator Constructor "";
terminator Binding "";
terminator Symbol "";
terminator Type "";
terminator FunDec "";
terminator BracketedFunDec "";
terminator Attr "";
terminator DatatypeName "";

Unquoted. Symbol ::= UnquotedSymbol;
Quoted.   Symbol ::= QuotedSymbol;

position token UnquotedSymbol (letter|["~!@$%^&*_+=<>.?/"])(letter|digit|["~!@$%^&*_-+=<>.?/"])*;
position token QuotedSymbol '|'((char - '|') | ('\\' char))*'|';
token Keyword ':'(letter|digit|["-"])*;
```
