Require Export Subst.
Require Export TSubstGeneral.

(* The term datatype includes both types and terms so that the variable binding is shared. *)
(* terms are commented with their respective binding *)

Inductive term : Type :=
| var : nat -> term

(* types *)

| cn_zero : term
| cn_unit : term
| cn_arrow : term -> term -> term
| cn_prod : term -> term -> term
| cn_all : (* cn => *) term -> term
| cn_exists : (* cn => *) term -> term
| cn_cont : term -> term

(* terms *)

| tm_star : term
| tm_fun : (* cn *) term -> (* cn *) term -> (* tm => tm => *) term -> term
| tm_app : term -> term -> term
| tm_pair : term -> term -> term
| tm_pi1 : term -> term
| tm_pi2 : term -> term
| tm_plam : (* cn => *) term -> term
| tm_papp : term -> (* cn *) term -> term
| tm_pack : (* cn *) term -> term -> (* cn => cn *) term -> term
| tm_unpack : term -> (* cn => tm => *) term -> term
| tm_lett : term -> (* tm => *) term -> term
| tm_abort : (* cn *) term -> term -> term
| tm_letcc : (* cn *) term -> (* tm => *) term  -> term
| tm_throw : term -> term -> term
| tm_cont : (* k *) term -> term

(* evaluation contexts *)
| k_hole : term

(* marker for compactness *)
| pat : term
.


(*  The following is part of the substitution framework *)

Fixpoint traverse (S:Type) (enter : S -> S) (resolve : S -> nat -> term) (s : S) (t : term) {struct t} : term :=
  (match t with
    | var i => resolve s i

    | cn_zero => cn_zero
    | cn_unit => cn_unit
    | cn_arrow t1 t2 => cn_arrow (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | cn_prod t1 t2 => cn_prod (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | cn_all t1 => cn_all (traverse S enter resolve (enter s) t1)
    | cn_exists t1 => cn_exists (traverse S enter resolve (enter s) t1)
    | cn_cont t => cn_cont (traverse S enter resolve s t)

    | tm_star => tm_star
    | tm_fun a b t2 => tm_fun (traverse S enter resolve s a) (traverse S enter resolve s b) (traverse S enter resolve (enter (enter s)) t2)
    | tm_app t1 t2 => tm_app (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | tm_pair t1 t2 => tm_pair (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | tm_pi1 t1 => tm_pi1 (traverse S enter resolve s t1)
    | tm_pi2 t1 => tm_pi2 (traverse S enter resolve s t1)
    | tm_plam t1 => tm_plam (traverse S enter resolve (enter s) t1)
    | tm_papp t1 t2 => tm_papp (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | tm_pack t1 t2 t3 => tm_pack (traverse S enter resolve s t1) (traverse S enter resolve s t2) (traverse S enter resolve (enter s) t3)
    | tm_unpack t1 t2 => tm_unpack (traverse S enter resolve s t1) (traverse S enter resolve (enter (enter s)) t2)
    | tm_lett t1 t2 => tm_lett (traverse S enter resolve s t1) (traverse S enter resolve (enter s) t2)
    | tm_abort tau e => tm_abort (traverse S enter resolve s tau) (traverse S enter resolve s e)
    | tm_letcc tau e => tm_letcc (traverse S enter resolve s tau) (traverse S enter resolve (enter s) e)
    | tm_throw t1 t2 => tm_throw (traverse S enter resolve s t1) (traverse S enter resolve s t2)
    | tm_cont k => tm_cont (traverse S enter resolve s k)

    | k_hole => k_hole

    | pat => pat
   end).



#[export] Instance termVar : HasVar term := {var := var}.
#[export] Instance termTraverse : HasTraverse term := {traverse := traverse}.

#[export] Instance termSubst : SubstType term.
Proof.
econstructor; replace Subst.traverse with traverse; auto.
prove_traverse_parametric term_ind.
prove_traverse_id term_ind.
prove_traverse_compose term_ind.
Qed.
Global Hint Resolve termSubst : subst.


Inductive classifier : Type :=
| cl_tm : (* cn *) term -> classifier
| cl_tp : classifier
| cl_skip : classifier
.

Definition context := list classifier.

(* This function substitutes the second input in for k_hole within the first input *)
(* This applies for both E[e] and composition of evaluation contexts E o E' *)

Fixpoint fill E efill : term := match E with
| var i => var i

| cn_zero => cn_zero
| cn_unit => cn_unit
| cn_arrow t1 t2 => cn_arrow (fill t1 efill) (fill t2 efill)
| cn_prod t1 t2 => cn_prod (fill t1 efill) (fill t2 efill)
| cn_all t1 => cn_all (fill t1 efill)
| cn_exists t1 => cn_exists (fill t1 efill)
| cn_cont t => cn_cont (fill t efill)

| tm_star => tm_star
| tm_fun a b t2 => tm_fun (fill a efill) (fill b efill) (fill t2 efill)
| tm_app t1 t2 => tm_app (fill t1 efill) (fill t2 efill)
| tm_pair t1 t2 => tm_pair (fill t1 efill) (fill t2 efill)
| tm_pi1 t1 => tm_pi1 (fill t1 efill)
| tm_pi2 t1 => tm_pi2 (fill t1 efill)
| tm_plam t1 => tm_plam (fill t1 efill)
| tm_papp t1 t2 => tm_papp (fill t1 efill) (fill t2 efill)
| tm_pack t1 t2 t3 => tm_pack (fill t1 efill) (fill t2 efill) (fill t3 efill)
| tm_unpack t1 t2 => tm_unpack (fill t1 efill) (fill t2 efill)
| tm_lett t1 t2 => tm_lett (fill t1 efill) (fill t2 efill)
| tm_abort tau e => tm_abort (fill tau efill) (fill e efill)
| tm_letcc tau e => tm_letcc (fill tau efill) (fill e efill)
| tm_throw t1 t2 => tm_throw (fill t1 efill) (fill t2 efill)
| tm_cont k => tm_cont k

| k_hole => efill

| pat => pat
end.

Declare Scope syntax.
Notation "E1 'o' E2" := (fill E1 E2)
  (at level 2, left associativity,
   format "E1  o  E2" ) : syntax.

Notation "E [ e ]" := (fill E e)
  (at level 2, e at level 200, left associativity,
   format "E [ e ]" ) : syntax.

Notation "e .[ t ]" := (subst (dot t (sh 0)) e) 
  (at level 2, t at level 200, left associativity,
   format "e .[ t ]" ) : syntax.

Notation "e .[ t , s ]" := (subst (dot t (dot s (sh 0))) e) 
  (at level 2, t at level 200, s at level 200, left associativity,
   format "e .[ t , s ]" ) : syntax.

(* functions that do not refer to themselves are defined in terms of recursive functions *)
Definition tm_lam A B f := tm_fun A B (subst (sh 1) f).

Open Scope syntax.