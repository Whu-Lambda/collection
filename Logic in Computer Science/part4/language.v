Require Import Coq.Strings.String.
Require Import util.

Inductive aexp : Type :=
| ANum    : nat -> aexp
| AId     : id -> aexp
| APlus   : aexp -> aexp -> aexp
| AMult   : aexp -> aexp -> aexp.

Inductive bexp : Type :=
| BTrue   : bexp
| BFalse  : bexp
| BEq     : aexp -> aexp -> bexp
| BLe     : aexp -> aexp -> bexp
| BNot    : bexp -> bexp
| BAnd    : bexp -> bexp -> bexp.


Inductive command : Type :=
| CSkip   : command
| CAss    : id -> aexp -> command
| CSeq    : command -> command -> command
| CIf     : bexp  -> command -> command -> command
| CWhile  : bexp -> command -> command
| CCons   : id -> aexp -> command
| CLookup : id -> aexp -> command
| CMutat  : aexp -> aexp -> command
| CDispose: aexp -> command.



Definition W : id := Id "W".
Definition X : id := Id "X".
Definition Y : id := Id "Y".
Definition Z : id := Id "Z".
Definition M : id := Id "M".
Definition N : id := Id "N".


