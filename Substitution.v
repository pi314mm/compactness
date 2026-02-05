Require Import Sequence.
Require Export TSubstGeneral.
Require Import Rules.
Require Export SyntaX.
From Stdlib Require Import Lia.

(* This file uses the substitution framework to prove the substitution theorem for the particular language *)
(* This can be for the most part ignored, but it results in the subst_oft theorem and similar lemmas *)
(* This file also defines syntactic sugar for functions that do not refer to themselves *)

Definition subst_cl s c :=
match c with
| cl_tm a => cl_tm (subst s a)
| cl_tp => cl_tp
| cl_skip => cl_skip
end.

#[export] Instance termCl : HasClassifier term := {classifier := classifier}.
#[export] Instance termSC : SubstClassifier term := {subst_cl := subst_cl}.
#[export] Instance termCL : ClassifierLemmas term.
Proof.
split; replace TSubstGeneral.subst_cl with subst_cl by reflexivity.
intros. induction t; simpl. rewrite subst_compose. reflexivity. reflexivity.
reflexivity.
intros. induction t; simpl. rewrite subst_id. reflexivity. reflexivity. reflexivity.
intros. induction t; simpl. rewrite subst_under_id. reflexivity. reflexivity. reflexivity.
Defined.

Lemma under1 {s t v} : (subst (under 1 s) t).[v] = subst (dot v s) t.
Proof.
unfold under.
simp_sub.
Qed.

Lemma under2 {s t v1 v2} : (subst (under 2 s) t).[v1,v2] = subst (dot v1 (dot v2 s)) t.
Proof.
unfold under.
simp_sub.
Qed.

Lemma under_under {a b s} :
under a (under b s) = under (a + b) s.
Proof.
induction a; simpl.
- reflexivity.
- f_equal. f_equal. eauto.
Qed.

Create HintDb substrw discriminated.

Lemma subst_var {s v} : subst s (var v) = project s v. Proof. eauto. Qed.

Lemma subst_cn_zero {s} : subst s cn_zero = cn_zero. Proof. eauto. Qed.
Lemma subst_cn_unit {s} : subst s cn_unit = cn_unit. Proof. eauto. Qed.
Lemma subst_cn_arrow {s a b} : subst s (cn_arrow a b) = cn_arrow (subst s a) (subst s b). Proof. eauto. Qed.
Lemma subst_cn_prod {s a b} : subst s (cn_prod a b) = cn_prod (subst s a) (subst s b). Proof. eauto. Qed.
Lemma subst_cn_all {s a} : subst s (cn_all a) = cn_all (subst (under 1 s) a). Proof. eauto. Qed.
Lemma subst_cn_exists {s a} : subst s (cn_exists a) = cn_exists (subst (under 1 s) a). Proof. eauto. Qed.
Lemma subst_cn_cont {s a} : subst s (cn_cont a) = cn_cont (subst s a). Proof. eauto. Qed.

Lemma subst_tm_star {s} : subst s tm_star = tm_star. Proof. eauto. Qed.
Lemma subst_tm_fun {s a b e} : subst s (tm_fun a b e) = tm_fun (subst s a) (subst s b) (subst (under 2 s) e). Proof. eauto. Qed.
Lemma subst_tm_app {s e1 e2} : subst s (tm_app e1 e2) = tm_app (subst s e1) (subst s e2). Proof. eauto. Qed.
Lemma subst_tm_pair {s e1 e2} : subst s (tm_pair e1 e2) = tm_pair (subst s e1) (subst s e2). Proof. eauto. Qed.
Lemma subst_tm_pi1 {s e} : subst s (tm_pi1 e) = tm_pi1 (subst s e). Proof. eauto. Qed.
Lemma subst_tm_pi2 {s e} : subst s (tm_pi2 e) = tm_pi2 (subst s e). Proof. eauto. Qed.
Lemma subst_tm_plam {s e} : subst s (tm_plam e) = tm_plam (subst (under 1 s) e). Proof. eauto. Qed.
Lemma subst_tm_papp {s e c} : subst s (tm_papp e c) = tm_papp (subst s e) (subst s c). Proof. eauto. Qed.
Lemma subst_tm_pack {s p e tau} : subst s (tm_pack p e tau) = tm_pack (subst s p) (subst s e) (subst (under 1 s) tau). Proof. eauto. Qed.
Lemma subst_tm_unpack {s e1 e2} : subst s (tm_unpack e1 e2) = tm_unpack (subst s e1) (subst (under 2 s) e2). Proof. eauto. Qed.
Lemma subst_tm_lett {s e1 e2} : subst s (tm_lett e1 e2) = tm_lett (subst s e1) (subst (under 1 s) e2). Proof. eauto. Qed.
Lemma subst_tm_abort {s tau e} : subst s (tm_abort tau e) = tm_abort (subst s tau) (subst s e). Proof. eauto. Qed.
Lemma subst_tm_letcc {s c e} : subst s (tm_letcc c e) = tm_letcc (subst s c) (subst (under 1 s) e). Proof. eauto. Qed.
Lemma subst_tm_throw {s e1 e2} : subst s (tm_throw e1 e2) = tm_throw (subst s e1) (subst s e2). Proof. eauto. Qed.
Lemma subst_tm_cont {s k} : subst s (tm_cont k) = tm_cont (subst s k). Proof. eauto. Qed.

Lemma subst_k_hole {s} : subst s k_hole = k_hole. Proof. eauto. Qed.

Global Hint Rewrite
@subst_var

@subst_cn_zero
@subst_cn_unit
@subst_cn_arrow
@subst_cn_prod
@subst_cn_all
@subst_cn_exists
@subst_cn_cont

@subst_tm_star
@subst_tm_fun
@subst_tm_app
@subst_tm_pair
@subst_tm_pi1
@subst_tm_pi2
@subst_tm_plam
@subst_tm_papp
@subst_tm_pack
@subst_tm_unpack
@subst_tm_lett
@subst_tm_abort
@subst_tm_letcc
@subst_tm_throw
@subst_tm_cont

@subst_k_hole

: subst.


Lemma subst_var_var : Subst.var = var. Proof. auto. Qed.

Global Hint Rewrite @subst_var_var @project_dot @project_zero @project_sh @subst_id : subst.
Global Hint Rewrite @under_under nshift_term_eq_sh shift_term_eq_sh @under1 @under2 : subst.

Lemma subst_tm_lam {s a b e} : subst s (tm_lam a b e) = tm_lam (subst s a) (subst s b) (subst (under 1 s) e). Proof. unfold tm_lam. simp_sub. f_equal. f_equal. unfold under. simp_sub. Qed.

Global Hint Rewrite @subst_tm_lam : subst.

(* substitutends for static terms *)
Inductive sof : context -> term -> classifier -> Prop :=
| sof_tp {G c}
    : ofc G c
      -> sof G c cl_tp

| sof_tm {G e t}
    : sof G e (cl_tm t)

| sof_skip {G e}
    : sof G e (cl_skip)
.


(* substitutends for terms *)
Inductive dof : context -> term -> classifier -> Prop :=
| dof_tp {G c}
    : ofc G c
      -> dof G c cl_tp

| dof_tm {G e t}
    : oft G e t
      -> dof G e (cl_tm t)

| dof_skip {G e}
    : dof G e (cl_skip)
.


(* substitutends for value terms *)
Inductive vof : context -> term -> classifier -> Prop :=
| vof_tp {G c}
    : ofc G c
      -> vof G c cl_tp

| vof_tm {G e t}
    : oft G e t
      -> is_val e
      -> vof G e (cl_tm t)

| vof_skip {G e}
    : vof G e (cl_skip)
.


Lemma sof_behaved : 
  behaved sof.
Proof.
intros G i c Hindex.
destruct c; simp_sub; auto using sof.
econstructor.
econstructor.
econstructor.
eauto.
Qed.


Lemma dof_behaved : 
  behaved dof.
Proof.
intros G i t Hindex.
destruct t; simp_sub; eauto using dof; repeat econstructor; eassumption.
Qed.


Lemma dof_sof :
  forall G1 s G2, dof G1 s G2 -> sof G1 s G2.
Proof.
intros G1 s G2 Hof.
inversion Hof; intros; subst; auto using sof.
Qed.


Lemma subof_dof_sof :
  forall G1 s G2,
    subof dof G1 s G2
    -> subof sof G1 s G2.
Proof.
eauto using subof_mono, dof_sof.
Qed.

Lemma subof_wc_bind_sof_cn :
  forall G G' s,
    subof (wc sof) G s G'
    -> subof (wc sof) (cl_tp :: G) (dot (var 0) (Subst.compose s (sh 1))) (cl_tp :: G').
Proof.
intros G G' s Hsubof.
replace (cl_tp) with (subst_cl s cl_tp) by eauto.
apply subof_wc_bind; auto.
exact sof_behaved.
Qed.


Lemma subof_wc_bind_dof_cn :
  forall G G' s,
    subof (wc dof) G s G'
    -> subof (wc dof) (cl_tp :: G) (dot (var 0) (Subst.compose s (sh 1))) (cl_tp :: G').
Proof.
intros G G' s Hsubof.
replace (cl_tp) with (subst_cl s cl_tp) by eauto.
apply subof_wc_bind; auto.
exact dof_behaved.
Qed.


Lemma subof_wc_bind_dof_tm :
  forall G G' s t,
    subof (wc dof) G s G'
    -> subof (wc dof) (cl_tm (subst s t) :: G) (dot (var 0) (Subst.compose s (sh 1))) (cl_tm t :: G').
Proof.
intros G G' s t Hsubof.
replace (cl_tm (subst s t)) with (subst_cl s (cl_tm t)) by (simp_sub; reflexivity).
apply subof_wc_bind; auto.
exact dof_behaved.
Qed.


Lemma subst_ofc_wc :
  forall G1 G2 s c,
    subof (wc sof) G1 s G2
    -> ofc G2 c
    -> ofc G1 (subst s c).
Proof.
intros G1 G2 s c Hs Hof.
revert G1 s Hs.
induction Hof; intros.
(* var *)
assert (subof sof G1 s G) as Hs'.
  apply (subof_mono (wc sof)); auto; [].
  intros; apply wc_elim; auto.

simp_sub.
assert(sof G1 (project s i) (TSubstGeneral.subst_cl (Subst.compose (sh (S i)) s) cl_tp)).
eapply subof_index.
eapply sof_behaved.
eassumption.
eassumption.
inversion H0; eauto.
simp_sub. econstructor.
simp_sub. econstructor.
simp_sub. econstructor. auto. auto.
simp_sub. econstructor. auto. auto.
simp_sub. econstructor; auto.
eapply IHHof.
unfold under.
simp_sub.
eapply subof_wc_bind_sof_cn.
assumption.

simp_sub. econstructor. eapply IHHof.
unfold under; simp_sub.
eapply subof_wc_bind_sof_cn.
assumption.

simp_sub. econstructor; auto.

Qed.


Lemma subst_sof_wc :
  forall G1 G2 s t c,
    subof (wc sof) G1 s G2
    -> sof G2 t c
    -> sof G1 (subst s t) (subst_cl s c).
Proof.
intros G1 G2 s t c Hs H.
destruct H; simp_sub; eauto using subst_ofc_wc, sof.
Qed.


Lemma sof_wc :
  forall G t c,
    sof G t c -> wc sof G t c.
Proof.
exact (wc_intro _ subst_sof_wc).
Qed.


Lemma subst_ofc :
  forall G1 G2 s c,
    subof sof G1 s G2
    -> ofc G2 c
    -> ofc G1 (subst s c).
Proof.
intros G1 G2 s c Hs H.
eauto using subst_ofc_wc, subof_mono, sof_wc.
Qed.


Lemma subst1_ofc :
  forall G c c',
    ofc G c
    -> ofc (cl_tp :: G) c'
    -> ofc G (subst (dot c (sh 0)) c').
Proof.
intros.
eapply subst_ofc; eauto; [].
apply subof_dot; auto using subof_id; [].
simp_sub.
auto using sof.
Qed.


Lemma weaken_ofc :
  forall G1 G2 c,
    ofc G1 c
    -> ofc (app G2 G1) (subst (sh (length G2)) c).
Proof.
intros G1 G2 c H.
eapply subst_ofc; eauto; [].
apply subof_sh; [].
apply app_truncate; auto.
Qed.


Lemma weaken1_ofc :
  forall G A c,
    ofc G c
    -> ofc (A :: G) (subst (sh 1) c).
Proof.
intros G A c H.
replace (A :: G) with (app (A :: nil) G) by auto.
eapply weaken_ofc.
assumption.
Qed.


Lemma sof_wclo :
  wclo sof.
Proof.
intros G t C C' H.
inversion H; intros; subst; eauto using sof, weaken1_ofc.
Qed.


Lemma subof_bind_sof_cn :
  forall G G' s,
    subof sof G s G'
    -> subof sof (cl_tp :: G) (dot (var 0) (Subst.compose s (sh 1))) (cl_tp :: G').
Proof.
intros G G' s Hsubof.
replace cl_tp with (subst_cl s cl_tp) by simp_sub.
apply subof_wclo_bind; eauto using sof_behaved, sof_wclo.
Qed.


Lemma subof_under_sof :
  forall G1 G1' G2 s,
    subof sof G1 s G1'
    -> subof sof (app (subst_ctx s G2) G1) (under (length G2) s) (app G2 G1').
Proof.
intros G1 G1' G2 s Hsubof.
apply subof_under; auto using sof_behaved; [].
intros; apply sof_wc; auto.
Qed.


Lemma subof_weaken_sof :
  forall G1 G2 s G,
    subof sof G1 s G
    -> subof sof (app G2 G1) (Subst.compose s (sh (length G2))) G.
Proof.
intros G1 G2 s G Hsubof.
apply subof_wclo_weaken; auto using sof_wclo.
Qed.

Lemma subst_equal {tau s G} : ofc G tau -> subst (under (length G) s) tau = tau.
Proof.
intro H.
revert s.
induction H; intros; simp_sub; try (f_equal; eauto; fail).
- eapply project_under_lt.
  eapply index_length.
  eapply H.
Qed.

Corollary subst_nil_equal {tau s} : ofc nil tau -> subst s tau = tau.
Proof.
replace s with (under (length (nil : context)) s).
eapply subst_equal.
eauto.
Qed.

Lemma subst_equal_tm {e tau s G} :
  (oft G e tau -> subst (under (length G) s) e = e).
Proof.
intro H.
revert s.
pose (P (G:context) (e:term) (tau:term) := forall s, subst (under (length G) s) e = e).
pose (P' (E:term) (tau:term) (tau':term) := forall s, subst s E = E).
replace (forall s : sub, subst (under (length G) s) e = e) with (P G e tau) by auto.
revert G e tau H.
eapply (oft_ind' P P'); unfold P; unfold P'; intros; simp_sub.
- apply project_under_lt.
eapply index_length.
eapply H.
- f_equal; eauto. eapply subst_equal. eassumption. eapply subst_equal. eassumption.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; eauto. eapply subst_equal. eassumption.
- f_equal; eauto. eapply subst_equal. eassumption.
  replace (under (1 + length G) s)
  with (under (length (cl_tp :: G)) s) by (simpl; simp_sub).
  eapply subst_equal. eassumption.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; eauto. eapply subst_equal. eassumption.
- f_equal; eauto. eapply subst_equal. eassumption.
- f_equal; eauto.
- f_equal; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto. eapply subst_nil_equal; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto. eapply subst_nil_equal; eauto.
- f_equal; simpl in *; eauto. eapply subst_nil_equal; eauto.
  replace (dot (Subst.var 0) (shift_sub s)) with (under (length (cl_tp :: nil)) s) by (simpl; simp_sub).
 eapply subst_equal; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
- f_equal; simpl in *; eauto.
Qed.

Corollary subst_nil_equal_tm {e tau s} : oft nil e tau -> subst s e = e.
Proof.
replace s with (under (length (nil : context)) s).
eapply subst_equal_tm.
eauto.
Qed.

Corollary subst_nil_equal_k {k tau s} : ofc nil tau -> k ÷ tau -> subst s k = k.
Proof.
intros Htau HK.
assert (oft nil (tm_cont k) (cn_cont tau)).
econstructor; simpl; eauto. rewrite subst_id; reflexivity.
eapply (@subst_nil_equal_tm _ _ s) in H. simp_sub in H. inversion H. rewrite H1. eauto.
Qed.

Lemma subst_oft_wc :
  forall G1 G2 s e t,
    subof (wc dof) G1 s G2
    -> oft G2 e t
    -> oft G1 (subst s e) (subst s t).
Proof.
assert (forall G1 s G2, subof (wc dof) G1 s G2 -> subof sof G1 s G2) as Hsd.
  intros.
  apply (subof_mono (wc dof)); auto; [].
  intros.
  apply dof_sof; [].
  eapply wc_elim; eauto.
assert (forall G1 G2 s c, subof (wc dof) G1 s G2 -> ofc G2 c -> ofc G1 (subst s c)) as Hsubtp.
  intros G1 G2 s c Hsubof Hofc.
  eapply subst_ofc; eauto.
intros G1 G2 s e t Hs Hof.
revert G1 s Hs.
induction Hof; intros.

(* var *)
- assert (subof dof G1 s G) as Hs'.
  apply (subof_mono (wc dof)); auto; [].
  intros; apply wc_elim; auto.
simp_sub.
assert(dof G1 (project s i) (TSubstGeneral.subst_cl (Subst.compose (sh (S i)) s) (cl_tm t))).
eapply subof_index.
eapply dof_behaved.
eassumption.
eassumption.
inversion H0; eauto.

(* star *)
- econstructor.

(* fun *)
- 
simp_sub.
simpl Nat.add.
apply oft_fun; eauto; [].
replace (subst (sh 2) (subst s t2)) with (subst (under 2 s) (subst (sh 2) t2)) by (unfold under; simp_sub).
eapply IHHof.
replace 2 with (1+1) by lia.
rewrite <- under_under.
pose (x := under 1 s).
fold x.
unfold under. rewrite shift_sub_eq_compose_sh.
replace (cn_arrow (subst (sh 1) (subst s t1)) (subst (sh 1) (subst s t2))) with
(subst x (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2))).
eapply subof_wc_bind_dof_tm.
unfold x.
simpl. rewrite shift_sub_eq_compose_sh.
eapply subof_wc_bind_dof_tm.
eassumption.
simp_sub. repeat rewrite <- subst_compose. simpl. repeat rewrite shift_sub_eq_compose_sh.
reflexivity.

(* app *)
- econstructor. eapply IHHof1. assumption. eapply IHHof2. assumption.

(* pair *)
- econstructor. eapply IHHof1. assumption. eapply IHHof2. assumption.

(* pi1 *)
- econstructor. eapply IHHof. assumption.

(* pi2 *)
- econstructor. eapply IHHof. assumption.

(* plam *)
- simp_sub.
apply oft_plam; eauto; [].
apply IHHof; [].
unfold under.
replace ((shift_sub s)) with (Subst.compose s (sh 1)) by (Subst.simp_sub; try exact termSubst; reflexivity).
apply subof_wc_bind_dof_cn; auto.

(* papp *)
- Subst.simp_sub.
revert IHHof. simp_sub. intro IHHof.
rewrite -> split_dot.
rewrite -> subst_compose.
eapply oft_papp; eauto.
rewrite <- shift_sub_eq_compose_sh.
eapply IHHof.
assumption.

(* pack *)
- simp_sub.
  apply oft_pack; eauto using subst_ofc.
  simp_sub.
  replace (subst (dot (subst s c) s) t) with (subst s t.[c]) by (Subst.simp_sub; try exact termSubst; reflexivity).
  eapply IHHof.
  assumption.

  eapply subst_ofc; eauto; [].
  simpl.
  simp_sub.
  apply subof_bind_sof_cn; [].
  apply Hsd; auto.

(* unpack *)
- simp_sub.
assert (oft G1 (subst s e1) (cn_exists (subst (under 1 s) t))) as Hof1' by eauto.
apply (oft_unpack Hof1').
replace (subst (sh 2) (subst s t')) with (subst (under 2 s) (subst (sh 2) t'))
by (simpl; simp_sub).
eapply IHHof2.
unfold under; simpl.
rewrite traverse_var.
rewrite shift_var_ge; try lia.
simp_sub; simpl.
replace (dot (var 1) (compose s (sh 2))) with (compose (dot (var 0) (compose s (sh 1))) (sh 1)) by simp_sub.
eapply subof_wc_bind_dof_tm; auto.
eapply subof_wc_bind_dof_cn; auto.
simp_sub.

(* lett *)
- simp_sub. unfold under. simp_sub.
eapply oft_lett; eauto; [].
Subst.simp_sub; try exact termSubst.
replace (Subst.compose s (sh 1)) with (Subst.compose (sh 1) (dot (var 0) (Subst.compose s (sh 1)))).
rewrite -> subst_compose.
apply IHHof2; [].
apply subof_wc_bind_dof_tm; auto.
simp_sub.

(* abort *)
- simp_sub.
econstructor. eapply Hsubtp; eassumption.
replace (cn_zero) with (subst s cn_zero).
eapply IHHof. eassumption. simp_sub.


(* letcc *)
- simp_sub. unfold under. simp_sub.
econstructor. eapply Hsubtp; eassumption.
Subst.simp_sub; try exact termSubst.
replace (subst (Subst.compose s (sh 1)) tau) with  ((subst (dot (Subst.var 0) (Subst.compose s (sh 1))) (subst (sh 1) tau))).
eapply IHHof.
replace ((cn_cont (subst s tau))) with ((subst s (cn_cont tau))).
apply subof_wc_bind_dof_tm; auto.
simp_sub.
simp_sub.

(* throw *)
- econstructor. eapply IHHof1. assumption. eapply IHHof2. assumption.

(* cont *)
- simp_sub.
  econstructor.
  eassumption.
  erewrite subst_nil_equal_k.
  eassumption. eassumption. eassumption.
  subst.
  Subst.simp_sub; try exact termSubst.
rewrite subst_nil_equal.
rewrite subst_nil_equal.
reflexivity.
eassumption.
eassumption.
Qed.


Lemma subst_dof_wc :
  forall G1 G2 s t A,
    subof (wc dof) G1 s G2
    -> dof G2 t A
    -> dof G1 (subst s t) (subst_cl s A).
Proof.
intros G1 G2 s t A Hs Hdof.
assert (subof sof G1 s G2).
  apply (subof_mono (wc dof)); auto; [].
  intros.
  apply dof_sof; [].
  eapply wc_elim; eauto.
destruct Hdof; simp_sub; eauto using subst_ofc, subst_oft_wc, dof.
Qed.


Lemma dof_wc :
  forall G t A,
    dof G t A -> wc dof G t A.
Proof.
exact (wc_intro _ subst_dof_wc).
Qed.


Lemma subst_oft :
  forall G1 G2 s e t,
    subof dof G1 s G2
    -> oft G2 e t
    -> oft G1 (subst s e) (subst s t).
Proof.
eauto using subof_mono, dof_wc, subst_oft_wc.
Qed.

Lemma subst_oft' :
  forall G1 G2 s e t t',
    subof dof G1 s G2
    -> oft G2 e t
    -> t' = (subst s t)
    -> oft G1 (subst s e) t'.
Proof.
intros. rewrite H1.
eapply subst_oft; eassumption.
Qed.


Lemma subst1_oft_cn :
  forall G c e t,
    ofc G c
    -> oft (cl_tp :: G) e t
    -> oft G (subst (dot c (sh 0)) e) (subst (dot c (sh 0)) t).
Proof.
intros.
eapply subst_oft; eauto; [].
apply subof_dot; auto using subof_id; [].
simp_sub.
apply dof_tp; auto.
Qed.


Lemma subst1_oft_tm :
  forall G e t e' t',
    oft G e t
    -> oft (cl_tm t :: G) e' t'
    -> oft G (subst (dot e (sh 0)) e') (subst (dot e (sh 0)) t').
Proof.
intros.
eapply subst_oft; eauto; [].
apply subof_dot; auto using subof_id; [].
Subst.simp_sub.
apply dof_tm; auto.
rewrite subst_id.
eassumption.
Qed.


Lemma dof_wclo :
  wclo dof.
Proof.
intros G t C C' H.
inversion H; intros; subst; simp_sub; eauto using dof, subst_ofc, subst_oft, weaken1.
Qed.

Lemma subof_under_dof :
  forall G1 G1' G2 s,
    subof dof G1 s G1'
    -> subof dof (app (subst_ctx s G2) G1) (under (length G2) s) (app G2 G1').
Proof.
intros G1 G1' G2 s Hsubof.
apply subof_under; auto using dof_behaved; [].
intros; apply dof_wc; auto.
Qed.

Lemma subof_weaken_dof :
  forall G1 G2 s G,
    subof dof G1 s G
    -> subof dof (app G2 G1) (Subst.compose s (sh (length G2))) G.
Proof.
intros G1 G2 s G Hsubof.
apply subof_wclo_weaken; auto using dof_wclo.
Qed.

Lemma weaken_oft :
  forall G1 G2 c x,
    oft G1 x c
    -> oft (app G2 G1) (subst (sh (length G2)) x) (subst (sh (length G2)) c).
Proof.
intros G1 G2 c x H.
eapply subst_oft; eauto; [].
apply subof_sh; [].
apply app_truncate; auto.
Qed.

Lemma vof_dof {G s G'} : subof vof G s G' -> subof dof G s G'.
Proof.
intros.
induction H.
econstructor. eassumption. inversion H0; subst. econstructor. eassumption. econstructor. eassumption.
econstructor.
econstructor. eassumption.
Qed.

Lemma subof_vof_dof :
  forall G1 s G2,
    subof vof G1 s G2
    -> subof dof G1 s G2.
Proof.
eauto using subof_mono, vof_dof.
Qed.

Lemma subst_out_context {E tau tau' e x} :
ofk E tau tau' ->
E[e.[x]] = E[e].[x].
Proof.
induction 1; simpl; eauto; simp_sub; f_equal; eauto;
try (repeat erewrite fill_in_term; eauto; repeat erewrite subst_nil_equal_tm; eauto; fail);
try (repeat erewrite fill_in_type; eauto; repeat erewrite subst_nil_equal; eauto; fail).
- repeat erewrite fill_in_term; eauto.
  apply (@subst_equal_tm _ _ (dot x (sh 0)) _) in H0.
  replace (length (cl_tm tau1 :: nil)) with 1 in H0 by eauto.
  simp_sub in H0.
- repeat erewrite fill_in_type; eauto.
  apply (@subst_equal _ (dot x (sh 0)) _) in H1.
  replace (length (cl_tp :: nil)) with 1 in H1 by eauto.
  simp_sub in H1.
- repeat erewrite fill_in_term; eauto.
  apply (@subst_equal_tm _ _ (dot x (sh 0)) _) in H0.
  replace (length (cl_tm t :: cl_tp :: nil)) with 2 in H0 by eauto.
  simp_sub in H0.
Qed.

Lemma subst_out_context' {E s tau tau' e} :
ofk E tau tau' ->
E[subst s e] = subst s (E[e]).
Proof.
induction 1; simpl; eauto; simp_sub; f_equal; eauto;
try (repeat erewrite fill_in_term; eauto; repeat erewrite subst_nil_equal_tm; eauto; fail);
try (repeat erewrite fill_in_type; eauto; repeat erewrite subst_nil_equal; eauto; fail).
- repeat erewrite fill_in_term; eauto.
  apply (@subst_equal_tm _ _ s _) in H0.
  replace (length (cl_tm tau1 :: nil)) with 1 in H0 by eauto.
  simp_sub in H0.
- repeat erewrite fill_in_type; eauto.
  apply (@subst_equal _ s _) in H1.
  replace (length (cl_tp :: nil)) with 1 in H1 by eauto.
  simp_sub in H1.
- repeat erewrite fill_in_term; eauto.
  apply (@subst_equal_tm _ _ s _) in H0.
  replace (length (cl_tm t :: cl_tp :: nil)) with 2 in H0 by eauto.
  simp_sub in H0.
Qed.

(* ---------------------------------------------------------------------------------- *)
(* Definitions of functions that do not refer to themselves *)
(* ---------------------------------------------------------------------------------- *)

Lemma oft_lam {G t1 t2 e}:
ofc G t1
      -> ofc G t2
      -> oft (cl_tm t1 :: G) e (subst (sh 1) t2)
      -> oft G (tm_lam t1 t2 e) (cn_arrow t1 t2)
.
Proof.
unfold tm_lam.
intros.
econstructor; eauto.
replace (subst (sh 2) t2) with (subst (sh 1) (subst (sh 1) t2)).
replace (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) with
((cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: nil) ++ cl_tm t1 :: G) by auto.
eapply weaken_oft.
eassumption.
rewrite <- subst_compose.
rewrite compose_sh.
simpl. reflexivity.
Qed.

Lemma tstep_app4 {E a b e1 v2} : is_val v2
      -> tstep E (tm_app (tm_lam a b e1) v2) (E[e1.[v2]]).
Proof.
intros.
unfold tm_lam.
replace (e1.[v2]) with ((subst (sh 1) e1).[(tm_fun a b (subst (sh 1) e1)),v2]).
eapply tstep_app3; eauto.
rewrite <- subst_compose.
Subst.simp_sub.
Qed.



