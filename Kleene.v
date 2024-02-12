Require Import SyntaX.
Require Import Rules.
Require Import Substitution.
Require Import Lia.
Require Import Sequence.

Inductive starn : nat -> term -> term -> Prop :=
| starn_refl {x}
    : starn 0 x x

| starn_step {x y z i}
    : tstep k_hole x y
      -> starn i y z
      -> starn (S i) x z.

Definition terminates (n : nat) (e : term) :=
  exists e',
    starn n e e' /\ is_val e'
.


Definition kleene (M : term) (M' : term) : Prop :=
  (exists n, terminates n M) <-> (exists n, terminates n M')
.

(* ------------------------------ Useful Lemmas ------------------------------------- *)

Lemma infinite_loop_doesn't_terminate {E tau v A B n} :
E ÷ tau ->
is_val v ->
terminates n E[tm_app (tm_fun A B (tm_app (var 0) (var 1))) v] -> False.
Proof.
intros HE Hval Hterm. elim Hterm; clear Hterm; intros v' Hterm; elim Hterm; clear Hterm; intros Hstarn Hval'.
assert (tstep k_hole (E[tm_app (tm_fun A B (tm_app (var 0) (var 1))) v]) (E[tm_app (tm_fun A B (tm_app (var 0) (var 1))) v])) as Hstep.
eapply stepECompose.
econstructor.
eauto.
simpl.
replace (tm_app (tm_fun A B (tm_app (var 0) (var 1))) v)
with ((tm_app (var 0) (var 1)).[tm_fun A B (tm_app (var 0) (var 1)), v]) at 2
by (simp_sub; rewrite project_dot; repeat rewrite project_zero; reflexivity).
eapply tstep_app3; eauto.
induction n.
inversion Hstarn; subst.
eapply val_isn't_step; eauto.
inversion Hstarn; subst.
assert (y = E[tm_app (tm_fun A B (tm_app (var 0) (var 1))) v]).
eapply deterministic; eauto.
subst. eauto.
Qed.