Require Import SyntaX.
Require Import Rules.
Require Import Substitution.
Require Import Kleene.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
Require Import Safety.

(* Definitions for pattern language *)

Inductive is_valf : term -> Prop :=
| Valf_pat : is_valf (pat)
| Valf_Fun {a b : term} (s1 : term) :
    is_valf (tm_fun a b s1)
| Valf_LamT (s1 : term) :
    is_valf (tm_plam s1)
| Valf_pair (s1 s2 : term) :
    is_valf s1 -> is_valf s2 -> is_valf (tm_pair s1 s2)
| Valf_Unit :
    is_valf tm_star
| Valf_pack {c e t} :
    is_valf e -> is_valf (tm_pack c e t)
| Valf_cont {E} :
    is_valf (tm_cont E)
.

Inductive stepf (A B f : term) : term -> term -> term -> Prop := 
| stepf_pat {E v2} :
    is_valf v2 ->
    stepf A B f E (tm_app pat v2) (E[f.[pat, v2]])

| stepf_app1 {E e1 e' e2}
    : stepf A B f (E o (tm_app k_hole e2)) e1 e'
      -> stepf A B f E (tm_app e1 e2) e'
| stepf_app2 {E v1 e2 e'}
    : is_valf v1
      -> stepf A B f (E o (tm_app v1 k_hole)) e2 e'
      -> stepf A B f E (tm_app v1 e2) e'
| stepf_app3 {E a b e1 v2}
    : is_valf v2
      -> stepf A B f E (tm_app (tm_fun a b e1) v2) (E[e1.[tm_fun a b e1,v2]])

| stepf_pair1 {E e1 e2 e'}
    : stepf A B f (E o (tm_pair k_hole e2)) e1 e'
      -> stepf A B f E (tm_pair e1 e2) e'

| stepf_pair2 {E v1 e2 e'}
    : is_valf v1
      -> stepf A B f (E o (tm_pair v1 k_hole)) e2 e'
      -> stepf A B f E (tm_pair v1 e2) e'

| stepf_pi11 {E e e'}
    : stepf A B f (E o (tm_pi1 k_hole)) e e'
      -> stepf A B f E (tm_pi1 e) e'

| stepf_pi12 {E v1 v2}
    : is_valf v1
      -> is_valf v2
      -> stepf A B f E (tm_pi1 (tm_pair v1 v2)) (E[v1])

| stepf_pi21 {E e e'}
    : stepf A B f (E o (tm_pi2 k_hole)) e e'
      -> stepf A B f E (tm_pi2 e) e'

| stepf_pi22 {E v1 v2}
    : is_valf v1
      -> is_valf v2
      -> stepf A B f E (tm_pi2 (tm_pair v1 v2)) (E[v2])

| stepf_papp1 {E e e' c}
    : stepf A B f (E o (tm_papp k_hole c)) e e'
      -> stepf A B f E (tm_papp e c) e'

| stepf_papp2 {E e c}
    : stepf A B f E (tm_papp (tm_plam e) c) (E[e.[c]])

| stepf_pack {E c e e' t}
    : stepf A B f (E o (tm_pack c k_hole t)) e e'
      -> stepf A B f E (tm_pack c e t) e'

| stepf_unpack1 {E e1 e2 e'}
    : stepf A B f (E o (tm_unpack k_hole e2)) e1 e'
      -> stepf A B f E (tm_unpack e1 e2) e'

| stepf_unpack2 {E c v t e}
    : is_valf v
      -> stepf A B f E (tm_unpack (tm_pack c v t) e) (E[e.[v,c]])

| stepf_lett1 {E e1 e2 e'}
    : stepf A B f (E o (tm_lett k_hole e2)) e1 e'
      -> stepf A B f E (tm_lett e1 e2) e'

| stepf_lett2 {E v1 e2}
    : is_valf v1
      -> stepf A B f E (tm_lett v1 e2) (E[e2.[v1]])

| stepf_abort {E e e' c}
    : stepf A B f (E o (tm_abort c k_hole)) e e'
      -> stepf A B f E (tm_abort c e) e'

| stepf_throw_1 {E e1 e2 e'}
    : stepf A B f (E o (tm_throw k_hole e2)) e1 e'
      -> stepf A B f E (tm_throw e1 e2) e'

| stepf_throw_2 {E e1 e2 e'}
    : is_valf e1
      -> stepf A B f (E o (tm_throw e1 k_hole)) e2 e'
      -> stepf A B f E (tm_throw e1 e2) e'

| stepf_throw {E v E'}
    : is_valf v
      -> stepf A B f E (tm_throw v (tm_cont E')) (E'[v])

| stepf_letcc {E tau e}
    : stepf A B f E (tm_letcc tau e) (E[e.[tm_cont E]])
.

Inductive starnf (A B f : term) : nat -> term -> term -> Prop :=
| starnf_refl {x}
    : starnf A B f 0 x x

| starnf_step {x y z i}
    : stepf A B f k_hole x y
      -> starnf A B f i y z
      -> starnf A B f (S i) x z
.

Fixpoint unroll i A B f := match i with
| 0 => tm_fun A B (tm_app (var 0) (var 1))
| S n => tm_lam A B (f.[unroll n A B f])
end.

Inductive Of (A B f : term) (n : nat) : term -> term -> Prop :=
| Of_var : forall i, Of A B f n (var i) (var i)

(* types *)

| Of_cn_zero : Of A B f n cn_zero cn_zero
| Of_cn_unit : Of A B f n cn_unit cn_unit
| Of_cn_arrow : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (cn_arrow a1 a2) (cn_arrow b1 b2)
| Of_cn_prod : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (cn_prod a1 a2) (cn_prod b1 b2)
| Of_cn_all : forall a b,
  Of A B f n a b ->
  Of A B f n (cn_all a) (cn_all b)
| Of_cn_exists : forall a b,
  Of A B f n a b ->
  Of A B f n (cn_exists a) (cn_exists b)
| Of_cn_cont : forall a b,
  Of A B f n a b ->
  Of A B f n (cn_cont a) (cn_cont b)

(* terms *)

| Of_tm_star : Of A B f n tm_star tm_star
| Of_tm_fun : forall a1 a2 a3 b1 b2 b3,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n a3 b3 ->
  Of A B f n (tm_fun a1 a2 a3) (tm_fun b1 b2 b3)
| Of_tm_app : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_app a1 a2) (tm_app b1 b2)
| Of_tm_pair : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_pair a1 a2) (tm_pair b1 b2)
| Of_tm_pi1 : forall a b,
  Of A B f n a b ->
  Of A B f n (tm_pi1 a) (tm_pi1 b)
| Of_tm_pi2 : forall a b,
  Of A B f n a b ->
  Of A B f n (tm_pi2 a) (tm_pi2 b)
| Of_tm_plam : forall a b,
  Of A B f n a b ->
  Of A B f n (tm_plam a) (tm_plam b)
| Of_tm_papp : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_papp a1 a2) (tm_papp b1 b2)
| Of_tm_pack : forall a1 a2 a3 b1 b2 b3,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n a3 b3 ->
  Of A B f n (tm_pack a1 a2 a3) (tm_pack b1 b2 b3)
| Of_tm_unpack : forall a1 a2 b1 b2,
  Of A B f n a1 b1 -> 
  Of A B f n a2 b2 ->
  Of A B f n (tm_unpack a1 a2) (tm_unpack b1 b2)
| Of_tm_lett : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_lett a1 a2) (tm_lett b1 b2)
| Of_tm_abort : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_abort a1 a2) (tm_abort b1 b2)
| Of_tm_letcc : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_letcc a1 a2) (tm_letcc b1 b2)
| Of_tm_throw : forall a1 a2 b1 b2,
  Of A B f n a1 b1 ->
  Of A B f n a2 b2 ->
  Of A B f n (tm_throw a1 a2) (tm_throw b1 b2)
| Of_tm_cont : forall a b,
  Of A B f n a b ->
  Of A B f n (tm_cont a) (tm_cont b)

(* evaluation contexts *)
| Of_k_hole : Of A B f n k_hole k_hole

(* patterns *)
| Of_pat_inf : Of A B f n (tm_fun A B f) pat
| Of_pat_fin : forall i, i >= n -> Of A B f n (unroll i A B f) pat
.

(* ------------------------------------------------------------------------------- *)

(* Substitution related content *)

Definition relPatSub (A B f : term) (n : nat) (s : @sub term) (sp : @sub term) : Prop :=
forall i, Of A B f n (project s i) (project sp i)
.

Lemma unroll_type {A B f i}:
  oft nil (tm_fun A B f) (cn_arrow A B) ->
  oft nil (unroll i A B f) (cn_arrow A B).
Proof.
intro Hf; inversion Hf; subst.
rewrite subst_nil_equal in H5; eauto.
rewrite subst_nil_equal in H5; eauto.
rewrite subst_nil_equal in H5; eauto.
induction i; simpl.
- econstructor; eauto.
  repeat (rewrite subst_nil_equal; eauto).
  eapply oft_app.
  2: { repeat econstructor. }
  rewrite subst_nil_equal; eauto.
  eapply oft_var'.
  econstructor; eauto.
  simp_sub; repeat(rewrite subst_nil_equal); eauto.
- eapply oft_lam; eauto.
  replace (subst (sh 1) B) with (B.[unroll i A B f]).
  eapply subst_oft; eauto.
  econstructor. econstructor. econstructor.
  simpl.
  econstructor. rewrite subst_id.
  replace (cl_tm A :: nil) with ((cl_tm A :: nil) ++ nil).
  replace (unroll i A B f) with (subst (sh (length (cl_tm A :: nil))) (unroll i A B f)).
  replace (cn_arrow A B) with (subst (sh (length (cl_tm A :: nil))) (cn_arrow A B)).
  eapply weaken_oft.
  eassumption.
  simp_sub; repeat(rewrite subst_nil_equal); eauto.
  erewrite subst_nil_equal_tm; eauto.
  eauto.
  simp_sub; repeat(rewrite subst_nil_equal); eauto.
Qed.


Lemma Of_under_sh {x y A B f c e p} :
oft nil (tm_fun A B f) (cn_arrow A B) ->
Of A B f c e p ->
Of A B f c (subst (under x (sh y)) e) (subst (under x (sh y)) p).
Proof.
intros Hnil HOf.
revert x y.
induction HOf; intros x y; try (simp_sub; econstructor; eauto).
- {
  assert (i < x \/ i >= x) as Hcase by lia.
  simp_sub.
  destruct Hcase.
  - repeat rewrite project_under_lt; eauto; econstructor.
  - repeat rewrite project_under_ge; eauto.
    simp_sub.
    econstructor.
  }
- erewrite subst_nil_equal_tm; eauto. simp_sub; econstructor.
- eapply unroll_type in Hnil. erewrite subst_nil_equal_tm; eauto. simp_sub; econstructor. eassumption.
Qed.

Lemma relPatSub_under {A B f c s sp n} :
oft nil (tm_fun A B f) (cn_arrow A B) ->
relPatSub A B f c s sp ->
relPatSub A B f c (under n s) (under n sp).
Proof.
unfold relPatSub.
intros Hnil HrelPatSub i.
assert (i < n \/ i >= n) as Hcase by lia.
destruct Hcase.
- repeat rewrite project_under_lt; eauto; econstructor.
- repeat rewrite project_under_ge; eauto.
  pose (@Of_under_sh 0 n A B f c (project s (i - n)) (project sp (i - n)) Hnil (HrelPatSub (i - n))) as Hans.
  unfold under in Hans.
  auto.
Qed.

Lemma Of_relPatSub {A B f c s sp e ep} :
oft nil (tm_fun A B f) (cn_arrow A B) ->
Of A B f c e ep ->
relPatSub A B f c s sp ->
Of A B f c (subst s e) (subst sp ep).
Proof.
intro Hnil.
generalize 0; intros n Hfit; revert s sp.
induction Hfit; intros s sp HrelPatSub; try (simp_sub; econstructor; eauto using relPatSub_under).
- erewrite subst_nil_equal_tm; eauto. simp_sub; econstructor.
- eapply unroll_type in Hnil. erewrite subst_nil_equal_tm; eauto. simp_sub; econstructor. eassumption.
Qed.

(* reflexivity of Of *)

Lemma Of_reflexivity_type {G t A B f c} :
ofc G t ->
Of A B f c t t.
Proof.
intros Ht. induction Ht; intros; econstructor; eauto.
Qed.

Lemma Of_reflexivity_k {tau k A B f c}:
k ÷ tau -> Of A B f c k k.
Proof.
intro Hk.
revert A B f c.
pose (Pe (G : context) e (tau:term) := (forall (A B f : term) (c : nat), Of A B f c e e)).
pose (Pk k (t : term) (t2:term) := forall (A B f : term) (c : nat), Of A B f c k k).
eapply (ofk_ind' Pe Pk); unfold Pe; unfold Pk; intros; simpl in *; eauto; econstructor; eauto using Of_reflexivity_type.
Qed.

Lemma Of_reflexivity_term {G e t A B f c}:
oft G e t -> Of A B f c e e.
Proof.
intro Hk.
revert A B f c.
pose (Pe (G : context) e (tau:term) := (forall (A B f : term) (c : nat), Of A B f c e e)).
pose (Pk k (t : term) (t2:term) := forall (A B f : term) (c : nat), Of A B f c k k).
eapply (oft_ind' Pe Pk); unfold Pe; unfold Pk; intros; simpl in *; eauto; try econstructor; eauto using Of_reflexivity_type.
Qed.

(* E[e] for Of *)

Lemma fill_in_type_hole {A B f c G tau tau' g} :
  ofc G tau -> Of A B f c tau tau' -> fill tau' g = tau'.
Proof.
intros Hofc Hfits. revert A B f c tau' g Hfits. 
induction Hofc; intros; inversion Hfits; subst; simpl; f_equal; eauto.
Qed.

Lemma fill_in_term_hole {A B f c G e tau e' g} :
  oft G e tau -> Of A B f c e e' -> fill e' g = e'.
Proof.
intros Hofe Hfits. revert A B f c e' g Hfits. 
induction Hofe; intros; inversion Hfits; subst; simpl; f_equal; eauto using fill_in_type_hole.
Qed.

Lemma Of_fill {tau tau' A B f c E E' e e'}:
ofk E tau tau' ->
Of A B f c E E' ->
Of A B f c e e' ->
Of A B f c (fill E e) (fill E' e').
Proof.
intros HE HEfit Hefit.
revert A B f c E' e e' HEfit Hefit.
induction HE; intros; inversion HEfit; subst; clear HEfit; eauto; simpl in *;
try (destruct i; simpl in *; discriminate);
econstructor; try (eauto; fail);
try (erewrite fill_in_term; eauto; erewrite fill_in_term_hole; eauto; fail);
try (erewrite fill_in_type; eauto; erewrite fill_in_type_hole; eauto; fail).
erewrite fill_in_type; eauto; rewrite (fill_in_type_hole H H4); eauto.
Qed.

(* ----------------------------------------------------------------------- *)

Lemma valf_val {A B f c v v'} :
is_valf v' ->
Of A B f c v v' ->
is_val v.
Proof.
intro H. revert A B f v.
induction H; intros A B f v; inversion 1; subst; try econstructor; eauto.
- induction i; simpl; econstructor.
Qed.

Lemma val_valf {v v' A B f c} :
is_val v ->
Of A B f c v v' ->
is_valf v'.
Proof.
intro H; revert v' A B f c.
induction H; intros.
- inversion H; subst; econstructor.
- inversion H; subst; econstructor.
- inversion H1; subst; econstructor; eauto.
- inversion H; subst; econstructor.
- inversion H0; subst; econstructor; eauto.
- inversion H; subst; econstructor.
Qed.

Lemma step_stepf  {A B f tau E a b E' a'} :
  oft nil (tm_fun A B f) (cn_arrow A B) ->
  (E ÷ tau) -> (oft nil a tau) ->
  tstep E a b ->
  Of A B f 0 E E' ->
  Of A B f 0 a a' ->
  (exists n, terminates n (E[a])) ->
  exists b', stepf A B f E' a' b' /\ Of A B f 0 b b'.
Proof.
intros Hf HE He Hstep HfitsE Hfitse Hterminates; revert tau E' a' HE He HfitsE Hfitse Hterminates; induction Hstep; intros.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(E[tm_app k_hole e2] ÷ (cn_arrow t1 tau)) as HE'.
  { eapply compose_cont. econstructor. econstructor. eassumption. eassumption. }
  assert(Of A B f 0 E[tm_app k_hole e2] E'[tm_app k_hole b2]) as Hfits.
  { eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption. }
  eelim (IHHstep _ _ b1 HE'); eauto.
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hof.
  exists b'. split.
  apply stepf_app1.
  eassumption. eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H6); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(E[tm_app v1 k_hole] ÷ t1) as HE'.
  eapply compose_cont. eapply ofk_app_2. eassumption. eassumption. econstructor. eassumption.
  assert(Of A B f 0 E[tm_app v1 k_hole] E'[tm_app b1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  elim (IHHstep _ _ b2 HE' H7 Hfits H4).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'.
  split; eauto.
  apply stepf_app2.
  eapply val_valf; eassumption.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H5); eauto.
- {inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H2.
  - subst. exists (E'[b4.[tm_fun b0 b3 b4, b2]]). split.
    eapply stepf_app3. eapply val_valf; eassumption.
    eapply Of_fill; eauto.
    eapply Of_relPatSub; eauto.
    unfold relPatSub; intro i.
    destruct i; simp_sub.
    destruct i; simp_sub.
    econstructor.
    - exists (E'[f.[pat, b2]]). subst. split.
    eapply stepf_pat. eapply val_valf; eassumption.
    eapply Of_fill; eauto.
    eapply Of_relPatSub; eauto.
    eapply Of_reflexivity_term.
    inversion Hf; eauto.
    unfold relPatSub; intro i.
    destruct i; simp_sub.
    destruct i; simp_sub.
    econstructor.
  - exists (E'[f.[pat, b2]]). subst.
    split.
    eapply stepf_pat. eapply val_valf; eassumption.
    eapply Of_fill; eauto.
    destruct i; simpl in *.
    inversion H0; subst; simp_sub.
    destruct Hterminates; destruct (infinite_loop_doesn't_terminate HE H H3).
    inversion H0; subst; simp_sub.
    eapply Of_relPatSub; eauto.
    eapply Of_reflexivity_term; inversion Hf; eauto.
    unfold relPatSub; intro i'.
    destruct i'; simp_sub.
    erewrite subst_nil_equal_tm; eauto using unroll_type; econstructor; lia.
    destruct i'; simp_sub.
    econstructor.
  }
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_pair k_hole e2] E'[tm_pair k_hole b2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E[tm_pair k_hole e2] ÷ t1) as HE'.
  eapply compose_cont. eapply ofk_pair_1. econstructor. eassumption. eassumption.
  elim (IHHstep _ _ b1 HE' H4 Hfits H1).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split.
  apply stepf_pair1.
  eassumption.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H6); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert (Of A B f 0 E[tm_pair v1 k_hole] E'[tm_pair b1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  assert (E[tm_pair v1 k_hole] ÷ t2) as HE'.
  eapply compose_cont. eapply ofk_pair_2. eassumption. eassumption. econstructor. eassumption.
  elim (IHHstep _ _ b2 HE' H7 Hfits H4).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_pair2.
  eapply val_valf; eassumption.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H5); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_pi1 k_hole] E'[tm_pi1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor.
  assert(E[tm_pi1 k_hole] ÷ (cn_prod tau t2)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption.
  elim (IHHstep _ _ b HE' H2 Hfits H0).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_pi11.
  eassumption.
  erewrite <- fill_associativity; eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H2; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b1]). split; eauto.
  eapply stepf_pi12; eapply val_valf.
  eapply H.
  eassumption.
  eapply H0.
  eassumption.
  eapply Of_fill; eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_pi2 k_hole] E'[tm_pi2 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor.
  assert(E[tm_pi2 k_hole] ÷ (cn_prod t1 tau)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption.
  elim (IHHstep _ _ b HE' H2 Hfits H0).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_pi21.
  eassumption.
  erewrite <- fill_associativity; eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H2; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b2]). split.
  eapply stepf_pi22; eapply val_valf.
  eapply H.
  eassumption.
  eapply H0.
  eassumption.
  eapply Of_fill; eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_papp k_hole c] E'[tm_papp k_hole b2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E[tm_papp k_hole c] ÷ (cn_all t)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim (IHHstep _ _ b1 HE' H4 Hfits H1).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_papp1.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_type H6); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H1; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b.[b2]]). split.
  eapply stepf_papp2.
  eapply Of_fill; eauto.
  eapply Of_relPatSub; eauto.
  intro i; destruct i; simp_sub; econstructor.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_pack c k_hole t] E'[tm_pack b1 k_hole b3]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor. eassumption.
  assert(E[tm_pack c k_hole t] ÷ (t.[c])) as HE'.
  eapply compose_cont. econstructor. eassumption. econstructor. eassumption. eassumption.
  elim (IHHstep _ _ b2 HE' H8 Hfits H4).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_pack.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_type H6); rewrite (fill_in_type H9); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst.
  assert(Of A B f 0 E[tm_unpack k_hole e2] E'[tm_unpack k_hole b2]) as Hfits.
  eapply Of_fill; eauto. repeat (econstructor; eauto).
  assert(E[tm_unpack k_hole e2] ÷ (cn_exists t)) as HE'.
  eapply compose_cont; eauto; repeat (econstructor; eauto).
  elim (IHHstep _ _ b1 HE' H2 Hfits H1).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_unpack1.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H5); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H2; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b2.[b3,b0]]). split; eauto.
  eapply stepf_unpack2.
  eapply val_valf; eassumption.
  eapply Of_fill; eauto.
  eapply Of_relPatSub; eauto.
  intro i; destruct i; simp_sub; destruct i; simp_sub; econstructor.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst; try (induction i; simpl in *; discriminate).
  assert(Of A B f 0 E[tm_lett k_hole e2] E'[tm_lett k_hole b2]) as Hfits.
  eapply Of_fill; eauto; repeat (econstructor; eauto).
  assert(E[tm_lett k_hole e2] ÷ t1) as HE'.
  eapply compose_cont; eauto; repeat (econstructor; eauto).
  elim (IHHstep _ _ b1 HE' H4 Hfits H1).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_lett1.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H6); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b2.[b1]]). split; eauto.
  eapply stepf_lett2.
  eapply val_valf; eassumption.
  eapply Of_fill; eauto.
  eapply Of_relPatSub; eauto.
  intro i; destruct i; simp_sub; econstructor.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst; try (induction i; simpl in *; discriminate).
  assert(Of A B f 0 E[tm_abort tau k_hole] E'[tm_abort b1 k_hole]) as Hfits.
  eapply Of_fill; eauto; repeat (econstructor; eauto).
  assert(E[tm_abort tau k_hole] ÷ cn_zero) as HE'.
  eapply compose_cont; eauto; repeat (econstructor; eauto).
  elim (IHHstep _ _ b2 HE' H6 Hfits H3).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_abort.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_type H4); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst; try (induction i; simpl in *; discriminate).
  assert(Of A B f 0 E[tm_throw k_hole e2] E'[tm_throw k_hole b2]) as Hfits.
  eapply Of_fill; eauto; repeat (econstructor; eauto).
  assert(E[tm_throw k_hole e2] ÷ tau0) as HE'.
  eapply compose_cont; eauto; repeat (econstructor; eauto).
  elim (IHHstep _ _ b1 HE' H4 Hfits H1).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_throw_1.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H6); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion He; subst; try (induction i; simpl in *; discriminate).
  assert(Of A B f 0 E[tm_throw e1 k_hole] E'[tm_throw b1 k_hole]) as Hfits.
  eapply Of_fill; eauto; repeat (econstructor; eauto).
  assert(E[tm_throw e1 k_hole] ÷ (cn_cont tau0)) as HE'.
  eapply compose_cont; eauto; eapply ofk_throw_2; eauto; repeat (econstructor; eauto).
  elim (IHHstep _ _ b2 HE' H7 Hfits H4).
  intros b' Hstepf; elim Hstepf; clear Hstepf; intros Hstepf Hfit.
  exists b'. split; eauto.
  apply stepf_throw_2.
  eapply val_valf; eassumption.
  eassumption.
  erewrite <- fill_associativity; simpl; rewrite (fill_in_term H5); eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  inversion H4; subst; try (induction i; simpl in *; discriminate).
  exists (b[b1]). split; eauto.
  apply stepf_throw.
  eapply val_valf; eassumption.
  inversion He; subst. inversion H8; subst.
  eapply Of_fill; eauto.
- inversion Hfitse; subst; try (induction i; simpl in *; discriminate).
  exists (E'[b2.[tm_cont E']]). split; eauto.
  eapply stepf_letcc.
  eapply Of_fill; eauto.
  eapply Of_relPatSub; eauto.
  intro i; destruct i; simp_sub; econstructor; eauto.
Qed.


Lemma Of_dec {A B f c e e'}: 
Of A B f (S c) e e' -> Of A B f c e e'.
Proof.
induction 1; econstructor; eauto.
lia.
Qed.

Lemma stepf_step {tau A B f c E' a' b' E a}:
(E ÷ tau) -> (oft nil a tau) -> oft nil (tm_fun A B f) (cn_arrow A B) ->
stepf A B f E' a' b' ->
Of A B f (S c) E E' ->
Of A B f (S c) a a' ->
exists b, tstep E a b /\ Of A B f c b b'.
Proof.
intros HE He Hf Hstep; revert c tau E a HE He; induction Hstep; intros.
- inversion H1; subst.
  inversion H5; subst.
  exists (E0[f.[tm_fun A B f,a2]]).
  split.
  eapply tstep_app3.
  eapply valf_val; eassumption.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption.
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; inversion Hf; eauto.
  intro i.
  destruct i; simp_sub.
  econstructor; eauto.
  destruct i; simp_sub.
  eapply Of_dec. eassumption.
  econstructor.

  destruct i; try lia.
  simpl.
  exists (E0[(f.[unroll i A B f]).[a2]]). split.
  eapply tstep_app4. eapply valf_val; eassumption.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption.
  replace (f.[unroll i A B f].[a2]) with (f.[unroll i A B f, a2]) by (simp_sub; rewrite (subst_nil_equal_tm (unroll_type Hf)); reflexivity).
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; inversion Hf; eauto.
  intro i'.
  destruct i'; simp_sub.
  econstructor; lia.
  destruct i'; simp_sub.
  eapply Of_dec. eassumption.
  econstructor.
- inversion H0; subst.
  inversion He; subst.
  assert (Of A B f (S c) E0[tm_app k_hole a2] E[tm_app k_hole e2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert (E0[tm_app k_hole a2] ÷ (cn_arrow t1 tau)) as HE'.
  eapply compose_cont. eapply ofk_app_1. econstructor. eassumption. eassumption.
  elim (IHHstep c _ _ a1 HE' H6 Hfits).
  intros b Hb. elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_app1; eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_app a1 k_hole] E[tm_app v1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  assert(E0[tm_app a1 k_hole] ÷ t1) as HE'.
  eapply compose_cont. eapply ofk_app_2. eassumption. eapply valf_val. eassumption. eassumption. econstructor. eassumption.
  elim(IHHstep c _ _ a2 HE' H9 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_app2.
  eapply valf_val. eassumption. eassumption.
  eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion H5; subst.
  inversion He; subst.
  exists (E0[a4.[tm_fun a0 a3 a4, a2]]). split.
  eapply tstep_app3.
  eapply valf_val. eassumption. eassumption.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption.
  eapply Of_relPatSub; eauto using Of_dec.
  intro i; destruct i; simp_sub; try econstructor; eauto using Of_dec; destruct i; simp_sub; eauto using Of_dec; econstructor.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_pair k_hole a2] E[tm_pair k_hole e2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E0[tm_pair k_hole a2] ÷ t1) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim(IHHstep c _ _ a1 HE' H6 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_pair1.
  eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_pair a1 k_hole] E[tm_pair v1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  assert(E0[tm_pair a1 k_hole] ÷ t2) as HE'.
  eapply compose_cont. eapply ofk_pair_2. eassumption. eapply valf_val. eassumption. eassumption. econstructor. eassumption.
  elim(IHHstep c _ _ a2 HE' H9 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_pair2.
  eapply valf_val.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
  eassumption.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_pi1 k_hole] E[tm_pi1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor.
  assert(E0[tm_pi1 k_hole] ÷ (cn_prod tau t2)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption.
  elim(IHHstep c _ _ a0 HE' H4 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_pi11.
  eassumption.
  eassumption.
  eassumption.
- inversion H2; subst.
  inversion H5; subst.
  econstructor. split.
  eapply tstep_pi12.
  eapply valf_val.
  eapply H.
  eassumption.
  eapply valf_val.
  eapply H0.
  eassumption.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption. eapply Of_dec. eassumption.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_pi2 k_hole] E[tm_pi2 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor.
  assert(E0[tm_pi2 k_hole] ÷ (cn_prod t1 tau)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption.
  elim(IHHstep c _ _ a0 HE' H4 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_pi21.
  eassumption.
  eassumption.
  eassumption.
- inversion H2; subst.
  inversion H5; subst.
  econstructor. split.
  eapply tstep_pi22.
  eapply valf_val.
  eapply H.
  eassumption.
  eapply valf_val.
  eapply H0.
  eassumption.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption. eapply Of_dec. eassumption.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c0) E0[tm_papp k_hole a2] E[tm_papp k_hole c]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E0[tm_papp k_hole a2] ÷ (cn_all t)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim(IHHstep c0 _ _ a1 HE' H6 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_papp1.
  eassumption.
  eassumption.
  eassumption.
- inversion H0; subst.
  inversion H4; subst.
  econstructor. split.
  eapply tstep_papp2.
  eapply Of_fill. eassumption. eapply Of_dec. eassumption.
  eapply Of_relPatSub; eauto using Of_dec.
  intro i; destruct i; simp_sub; eauto using Of_dec; destruct i; simp_sub; eauto using Of_dec; econstructor.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c0) E0[tm_pack a1 k_hole a3] E[tm_pack c k_hole t]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor. eassumption.
  assert(E0[tm_pack a1 k_hole a3] ÷ (a3.[a1])) as HE'.
  eapply compose_cont. econstructor; try eassumption. econstructor. eassumption.
  elim(IHHstep c0 _ _ a2 HE' H10 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_pack; eassumption.
  eassumption.
  eassumption.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_unpack k_hole a2] E[tm_unpack k_hole e2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E0[tm_unpack k_hole a2] ÷ (cn_exists t)) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption. eassumption.
  elim(IHHstep c _ _ a1 HE' H3 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_unpack1; eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion H5; subst.
  econstructor. split.
  eapply tstep_unpack2.
  eapply valf_val; eassumption.
  eapply Of_fill. eassumption. eapply Of_dec; eassumption.
  eapply Of_relPatSub; eauto using Of_dec.
  intro i; destruct i; simp_sub; eauto using Of_dec; destruct i; simp_sub; eauto using Of_dec; econstructor.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_lett k_hole a2] E[tm_lett k_hole e2]) as Hfits.
  eapply Of_fill; try eassumption. econstructor; try eassumption. econstructor.
  assert(E0[tm_lett k_hole a2] ÷ t1) as HE'.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim(IHHstep c _ _ a1 HE' H6 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_lett1; eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  econstructor. split.
  eapply tstep_lett2.
  eapply valf_val; eassumption.
  eapply Of_fill. eassumption. eapply Of_dec; eassumption.
  eapply Of_relPatSub; eauto using Of_dec.
  intro i; destruct i; simp_sub; eauto using Of_dec; destruct i; simp_sub; eauto using Of_dec; econstructor.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c0) E0[tm_abort tau k_hole] E[tm_abort c k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  assert(E0[tm_abort tau k_hole] ÷ cn_zero) as HE'.
  eapply compose_cont; try eassumption. econstructor; try eassumption. econstructor.
  elim(IHHstep c0 _ _ a2 HE' H8 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_abort; eassumption.
  eassumption.
  eassumption.
- inversion H0; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_throw k_hole a2] E[tm_throw k_hole e2]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. econstructor. eassumption.
  assert(E0[tm_throw k_hole a2] ÷ tau0) as HE'.
  eapply compose_cont; try eassumption. econstructor; try eassumption. econstructor.
  elim(IHHstep c _ _ a1 HE' H6 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_throw_1; eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion He; subst.
  assert(Of A B f (S c) E0[tm_throw a1 k_hole] E[tm_throw e1 k_hole]) as Hfits.
  eapply Of_fill. eassumption. eassumption. econstructor. eassumption. econstructor.
  assert(E0[tm_throw a1 k_hole] ÷ (cn_cont tau0)) as HE'.
  eapply compose_cont; try eassumption. eapply ofk_throw_2; try eassumption. eapply valf_val; eassumption. econstructor.
  elim(IHHstep c _ _ a2 HE' H9 Hfits).
  intros b Hb; elim Hb; clear Hb; intros Hb1 Hb2.
  exists b. split.
  eapply tstep_throw_2; try eassumption.
  eapply valf_val; eassumption.
  eassumption.
  eassumption.
- inversion H1; subst.
  inversion H6; subst.
  inversion He; subst.
  inversion H10; subst.
  econstructor. split.
  eapply tstep_throw.
  eapply valf_val; eassumption.
  eapply Of_fill. eassumption. eapply Of_dec; eassumption.
  eapply Of_dec; eassumption.
- inversion H0; subst.
  econstructor. split.
  eapply tstep_letcc.
  eapply Of_fill. eassumption. eapply Of_dec; eassumption.
  eapply Of_relPatSub; eauto using Of_dec.
  intro i; destruct i; simp_sub; eauto using Of_dec; econstructor; eauto using Of_dec.
Qed.

Lemma starn_starnf {A B f n a b a'} :
  oft nil a cn_unit -> oft nil (tm_fun A B f) (cn_arrow A B) ->
  starn n a b ->
  Of A B f 0 a a' ->
  is_val b ->
  exists b', starnf A B f n a' b' /\ Of A B f 0 b b'.
Proof.
intros He Hf Hstarn; revert a' He.
induction Hstarn; intros.
- exists a'. econstructor; eauto; econstructor; eauto.
- assert(Of A B f 0 k_hole k_hole) as Hfitshole by econstructor.
  assert (k_hole ÷ cn_unit) as HE by econstructor.
  eelim (step_stepf Hf HE He H Hfitshole); eauto.
  intros y' Hx; elim Hx; clear Hx; intros Hstep Hfits.
  eelim IHHstarn; eauto.
  intros v Hv; elim Hv; clear Hv; intros Hv Hfit.
  exists v.
  econstructor; eauto; econstructor; eauto.
  apply (preservation He HE H).
  exists (S i).
  simpl.
  econstructor; econstructor; eauto; econstructor; eauto.
Qed.

Lemma starnf_starn {A B f n a' b' a} :
  oft nil a cn_unit -> oft nil (tm_fun A B f) (cn_arrow A B) ->
  starnf A B f n a' b' ->
  Of A B f n a a' ->
  exists b, starn n a b /\ Of A B f 0 b b'.
Proof.
intros Ha Hf Hstarnf; revert a Ha.
induction Hstarnf; intros.
- exists a. econstructor. econstructor. eassumption.
- assert(Of A B f (S i) k_hole k_hole) by econstructor.
  assert(k_hole ÷ cn_unit) by econstructor.
  elim (stepf_step H2 Ha Hf H H1 H0).
  intros y' Hx; elim Hx; clear Hx; intros Hx Hy.
  eelim IHHstarnf.
  intros v Hv; elim Hv; clear Hv; intros Hv Hpat.
  exists v.
  econstructor; eauto; econstructor; eauto.
  eapply preservation; eauto.
  eassumption.
Qed.

Lemma generalized_compactness {e A B f p e' n} :
oft nil e cn_unit ->
oft nil (tm_fun A B f) (cn_arrow A B) ->
Of A B f 0 e p ->
oft nil e' cn_unit ->
Of A B f n e' p ->
terminates n e -> terminates n e'.
Proof.
intros He Hf Hfit He' Hfit' Hterm.
elim Hterm. intros v H. elim H. clear H. intros Hstar Hval.
elim (starn_starnf He Hf Hstar Hfit Hval).
intros b' Hstarnf; elim Hstarnf; clear Hstarnf; intros Hstarnf Hfit0.
elim (starnf_starn He' Hf Hstarnf Hfit').
intros v' Hv; elim Hv; clear Hv; intros Hv Hv'.
exists v'.
split. eassumption.
assert(is_valf b') as Hb'.
eapply (val_valf Hval).
eapply Hfit0.
eapply (valf_val Hb').
eapply Hv'.
Qed.


Lemma compactness {E tau e A B f} :
ofc nil tau ->
E ÷ tau ->
oft (cl_tm (cn_arrow A B) :: nil) e tau ->
oft nil (tm_fun A B f) (cn_arrow A B) ->
(exists n, terminates n (E[e.[tm_fun A B f]])) <->(exists i, (exists n, terminates n (E[e.[unroll i A B f]]))).
Proof.
intros Htau HE He Hf.
assert (oft nil (E[e.[tm_fun A B f]]) cn_unit) as He'.
eapply fill_type. simp_sub. eauto.
replace (tau) with (tau.[tm_fun A B f]) by (erewrite subst_nil_equal; eauto).
eapply subst_oft; eauto.
econstructor. econstructor. econstructor.
econstructor. rewrite subst_id. eassumption.
assert (forall i, oft nil (E[e.[unroll i A B f]]) cn_unit) as He''.
intro i.
eapply fill_type. simp_sub. eauto.
replace (tau) with (tau.[unroll i A B f]) by (erewrite subst_nil_equal; eauto).
eapply subst_oft; eauto.
econstructor. econstructor. econstructor.
econstructor. rewrite subst_id. eapply unroll_type. eassumption.
split.
- intros Hterm; elim Hterm; clear Hterm; intros n Hterm.
  exists n. exists n.
  eapply (@generalized_compactness _ A B f (E[e.[pat]]) _ n He'); eauto.

  eapply Of_fill; eauto.
  eapply Of_reflexivity_k; eauto.
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; eauto.
  intro i.
  destruct i; simp_sub; econstructor.

  eapply Of_fill; eauto.
  eapply Of_reflexivity_k; eauto.
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; eauto.
  intro i.
  destruct i; simp_sub; econstructor.
  eauto.

- intros H. elim H; clear H; intros i H; elim H; clear H; intros n Hterm.
  exists n.
  eapply (@generalized_compactness _ A B f (E[e.[pat]]) _ _ (He'' i)); eauto.

  eapply Of_fill; eauto.
  eapply Of_reflexivity_k; eauto.
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; eauto.
  intro i0.
  destruct i0; simp_sub; econstructor.
  lia.

  eapply Of_fill; eauto.
  eapply Of_reflexivity_k; eauto.
  eapply Of_relPatSub; eauto.
  eapply Of_reflexivity_term; eauto.
  intro i0.
  destruct i0; simp_sub; econstructor.
Qed.
