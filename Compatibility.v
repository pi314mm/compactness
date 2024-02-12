Require Import SyntaX.
Require Import Rules.
Require Import Sequence.
Require Import LogicalRelation.
Require Import Substitution.
Require Import Kleene.
Require Import Relation.
Require Import Lia.
Require Import Compactness.
Require Import CompactnessClosed.

Lemma admissibility {G e e' tau eta A B f A' B' f'} :
relatedEta G eta ->
ofc G tau ->
oft (cl_tm (cn_arrow A B) :: nil) e (subst (getleft eta) tau) ->
oft (cl_tm (cn_arrow A' B') :: nil) e' (subst (getright eta) tau) ->
oft nil (tm_fun A B f) (cn_arrow A B) ->
oft nil (tm_fun A' B' f') (cn_arrow A' B') ->
(forall i, Exp V eta tau e.[unroll i A B f] e'.[unroll i A' B' f']) ->
Exp V eta tau e.[tm_fun A B f] e'.[tm_fun A' B' f'].
Proof.
intros Hrel Htau He He' H3 H2 allH E E' EH E'H KH.
split; intros; erewrite compactness in H; eauto; elim H; clear H; intros i H.
eapply compactness; eauto.
eapply subst_ofc; eauto; eapply subof_sof_right; eauto.
exists i; eauto.
apply (allH i E E' EH E'H KH). eauto.
eapply subst_ofc; eauto; eapply subof_sof_left; eauto.
eapply compactness; eauto.
eapply subst_ofc; eauto; eapply subof_sof_left; eauto.
exists i; eauto.
apply (allH i E E' EH E'H KH). eauto.
eapply subst_ofc; eauto; eapply subof_sof_right; eauto.
Qed.

Lemma admissibility_closed {G e e' tau eta A B f A' B' f'} :
relatedEta G eta ->
ofc G tau ->
oft (cl_tm (cn_arrow_closed A B) :: nil) e (subst (getleft eta) tau) ->
oft (cl_tm (cn_arrow_closed A' B') :: nil) e' (subst (getright eta) tau) ->
oft nil (tm_fun_closed A B f) (cn_arrow_closed A B) ->
oft nil (tm_fun_closed A' B' f') (cn_arrow_closed A' B') ->
(forall i, Exp V eta tau e.[unroll_closed i A B f] e'.[unroll_closed i A' B' f']) ->
Exp V eta tau e.[tm_fun_closed A B f] e'.[tm_fun_closed A' B' f'].
Proof.
intros Hrel Htau He He' H3 H2 allH E E' EH E'H KH.
split; intros; erewrite compactness_closed' in H; eauto; elim H; clear H; intros i H.
eapply compactness_closed'; eauto.
eapply subst_ofc; eauto; eapply subof_sof_right; eauto.
exists i; eauto.
apply (allH i E E' EH E'H KH). eauto.
eapply subst_ofc; eauto; eapply subof_sof_left; eauto.
eapply compactness_closed'; eauto.
eapply subst_ofc; eauto; eapply subof_sof_left; eauto.
exists i; eauto.
apply (allH i E E' EH E'H KH). eauto.
eapply subst_ofc; eauto; eapply subof_sof_right; eauto.
Qed.

Lemma productCompatibility_V {eta e1 e1' tau1 e2 e2' tau2} :
  V eta tau1 e1 e1' ->
  V eta tau2 e2 e2' ->
  V eta (cn_prod tau1 tau2) (tm_pair e1 e2) (tm_pair e1' e2')
.
Proof.
intros; simpl; eauto.
Qed.

Lemma productCompatibility {G e1 e1' tau1 e2 e2' tau2} :
  logEq G e1 e1' tau1
  -> logEq G e2 e2' tau2
  -> logEq G (tm_pair e1 e2) (tm_pair e1' e2') (cn_prod tau1 tau2)
.
Proof.
intros He1 He2.
elimLogEq He1 HGe1 HGe1'; elimLogEq He2 HGe2 HGe2'.
split. econstructor; eauto.
split. econstructor; eauto.
simp_sub.
intros eta relatedSub Hnilpair Hnilpair'.
inversion Hnilpair; clear Hnilpair; subst.
inversion Hnilpair'; clear Hnilpair'; subst.
intros E E' HE HE' HK.
pose (E1  := E o (tm_pair (k_hole) (subst (getleft eta) e2 ))).
pose (E1' := E' o (tm_pair (k_hole) (subst (getright eta) e2'))).
simp_sub.
replace (E[tm_pair (subst (getleft eta) e1) (subst (getleft eta) e2)]) with (E1[subst (getleft eta) e1]).
replace (E'[tm_pair (subst (getright eta) e1') (subst (getright eta) e2')]) with (E1'[subst (getright eta) e1']).
eapply He1; try eassumption.
unfold E1. eapply compose_cont. econstructor. econstructor. eassumption. revert HE. simp_sub. eauto.
unfold E1'. eapply compose_cont. econstructor. econstructor. eassumption. revert HE. simp_sub. eauto.
intros v1 v1' typev1 typev1' Hv1.
pose (E2  := E o (tm_pair v1  k_hole)).
pose (E2' := E' o (tm_pair v1' k_hole)).
replace (E1[v1]) with (E2[subst (getleft eta) e2]).
replace (E1'[v1']) with (E2'[subst (getright eta) e2']).
eapply He2; try eassumption.
unfold E2. eapply compose_cont. eapply ofk_pair_2. eassumption. eapply (V_is_val relatedSub typev1 typev1' Hv1). econstructor. revert HE. simp_sub. eauto.
unfold E2'. eapply compose_cont. eapply ofk_pair_2. eassumption. eapply (V_is_val relatedSub typev1 typev1' Hv1). econstructor. revert HE. simp_sub. eauto.
intros v2 v2' typev2 typev2' Hv2.
replace (E2[v2]) with (E[tm_pair v1 v2]).
replace (E2'[v2']) with (E'[tm_pair v1' v2']).
eapply HK.
simp_sub. econstructor; eassumption.
simp_sub. econstructor; eassumption.
eapply productCompatibility_V; eauto.
unfold E2'; simpl; erewrite <- fill_associativity; simpl. rewrite (fill_in_term typev1'). reflexivity.
unfold E2; simpl; erewrite <- fill_associativity; simpl. rewrite (fill_in_term typev1). reflexivity.
unfold E1'; unfold E2'; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl. repeat (rewrite (fill_in_term typev1')). 
replace ((subst (getright eta) e2')[v1']) with (subst (getright eta) e2'). 
reflexivity.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; unfold E2; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl.
repeat (rewrite (fill_in_term typev1)). 
replace ((subst (getleft eta) e2)[v1]) with (subst (getleft eta) e2). 
reflexivity.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
unfold E1'; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal. erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal. erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
Qed.

Lemma projectionLeftCompatibility {G e e' tau1 tau2} :
  logEq G e e' (cn_prod tau1 tau2)
  -> logEq G (tm_pi1 e) (tm_pi1 e') tau1
.
Proof.
intros He.
elimLogEq He HGe HGe'.
split. econstructor; eauto.
split. econstructor; eauto.
simp_sub.
intros eta relatedSub Hnilpair Hnilpair'.
unfold Exp.
intros E E' HE HE' HK.
pose (E1  := E o (tm_pi1 (k_hole))).
pose (E1' := E' o (tm_pi1 (k_hole))).
simp_sub.
replace (E[tm_pi1 (subst (getleft eta) e)]) with (E1[subst (getleft eta) e]) by (unfold E1; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
replace (E'[tm_pi1 (subst (getright eta) e')]) with (E1'[subst (getright eta) e']) by (unfold E1'; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
apply (He eta); try assumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
simp_sub. unfold E1. eapply compose_cont. econstructor. econstructor. eassumption.
simp_sub. unfold E1'. eapply compose_cont. econstructor. econstructor. eassumption.
intros v v'.
replace (E1[v]) with (E[tm_pi1 v]) by (unfold E1; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
replace (E1'[v']) with (E'[tm_pi1 v']) by (unfold E1'; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
elim v; try (simpl; intros; contradiction).
elim v'; try (simpl; intros; contradiction).
intros v1' _ v2' _ v1 _ v2 _. 
simp_sub. intros Hoftpair1 Hoftpair2 HV.
elim HV. clear HV; intros HV1 HV2.
inversion Hoftpair1; subst.
inversion Hoftpair2; subst.
apply (kleeneHeadLeft (E[v1])).
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_pi12.
elim (V_is_val relatedSub H3 H4 HV1); eauto.
elim (V_is_val relatedSub H5 H7 HV2); eauto.
apply (kleeneHeadRight (E'[v1'])).
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_pi12.
elim (V_is_val relatedSub H3 H4 HV1); eauto.
elim (V_is_val relatedSub H5 H7 HV2); eauto.
eapply HK.
replace (subst (getleft eta) (cn_prod tau1 tau2)) with (cn_prod (subst (getleft eta) tau1) (subst (getleft eta) tau2)) in Hoftpair1 by (simp_sub; reflexivity).
inversion Hoftpair1; subst. eassumption.
replace (subst (getright eta) (cn_prod tau1 tau2)) with (cn_prod (subst (getright eta) tau1) (subst (getright eta) tau2)) in Hoftpair2 by (simp_sub; reflexivity).
inversion Hoftpair2; subst. eassumption.
eassumption.
Qed.

Lemma projectionRightCompatibility {G e e' tau1 tau2} :
  logEq G e e' (cn_prod tau1 tau2)
  -> logEq G (tm_pi2 e) (tm_pi2 e') tau2
.
Proof.
intros He.
elimLogEq He HGe HGe'.
split. econstructor; eauto.
split. econstructor; eauto.
simp_sub.
intros eta relatedSub Hnilpair Hnilpair'.
unfold Exp.
intros E E' HE HE' HK.
pose (E1  := E o (tm_pi2 (k_hole))).
pose (E1' := E' o (tm_pi2 (k_hole))).
simp_sub.
replace (E[tm_pi2 (subst (getleft eta) e)]) with (E1[subst (getleft eta) e]) by (unfold E1; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
replace (E'[tm_pi2 (subst (getright eta) e')]) with (E1'[subst (getright eta) e']) by (unfold E1'; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
apply (He eta); try assumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
simp_sub. unfold E1. eapply compose_cont. econstructor. econstructor. eassumption.
simp_sub. unfold E1'. eapply compose_cont. econstructor. econstructor. eassumption.
intros v v'.
replace (E1[v]) with (E[tm_pi2 v]) by (unfold E1; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
replace (E1'[v']) with (E'[tm_pi2 v']) by (unfold E1'; erewrite <- fill_associativity; simpl; try reflexivity; eassumption).
elim v; try (simpl; intros; contradiction).
elim v'; try (simpl; intros; contradiction).
intros v1' _ v2' _ v1 _ v2 _. 
simp_sub. intros Hoftpair1 Hoftpair2 HV.
elim HV. clear HV; intros HV1 HV2.
inversion Hoftpair1; subst.
inversion Hoftpair2; subst.
apply (kleeneHeadLeft (E[v2])).
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_pi22.
elim (V_is_val relatedSub H3 H4 HV1); eauto.
elim (V_is_val relatedSub H5 H7 HV2); eauto.
apply (kleeneHeadRight (E'[v2'])).
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_pi22.
elim (V_is_val relatedSub H3 H4 HV1); eauto.
elim (V_is_val relatedSub H5 H7 HV2); eauto.
eapply HK.
replace (subst (getleft eta) (cn_prod tau1 tau2)) with (cn_prod (subst (getleft eta) tau1) (subst (getleft eta) tau2)) in Hoftpair1 by (simp_sub; reflexivity).
inversion Hoftpair1; subst. eassumption.
replace (subst (getright eta) (cn_prod tau1 tau2)) with (cn_prod (subst (getright eta) tau1) (subst (getright eta) tau2)) in Hoftpair2 by (simp_sub; reflexivity).
inversion Hoftpair2; subst. eassumption.
eassumption.
Qed.

(*
Lemma lamCompatibility {G e e' t1 t2} :
  ofc G t1 ->
  logEq (cl_tm t1 :: G) e e' (subst (sh 1) t2)
-> logEq G (tm_lam t1 e) (tm_lam t1 e') (cn_arrow t1 t2).
Proof.
intros Ht1 He.
elimLogEq He HGe HGe'.
split. econstructor; eauto.
split. econstructor; eauto.
intros eta relatedSub Hnillam Hnillam'.
intros E E' HE HE' HK.
eapply HK.
eassumption.
eassumption.
simp_sub.
intros v1 v1' typev1 typev1' HV.
pose (eta' := (Dyn v1 v1' :: eta)).
Subst.simp_sub; try exact termSubst. repeat rewrite subst_var. repeat rewrite project_zero.
replace (dot v1 (getleft eta)) with (getleft eta') by eauto.
replace (dot v1' (getright eta)) with (getright eta') by eauto.
Search Exp.
intros E0 E0' HE0 HE0' HKE0.
assert((subst (getleft eta') (subst (sh 1) t2))=(subst (getleft eta) t2)) as Hleftt2.
unfold eta'. simpl. simp_sub.
assert((subst (getright eta') (subst (sh 1) t2))=(subst (getright eta) t2)) as Hrightt2.
unfold eta'. simpl. simp_sub.
assert(relatedEta (cl_tm t1 :: G) eta') as Hreleta'.
econstructor; try eassumption.
eapply (V_is_val relatedSub typev1 typev1' HV).
eapply (V_is_val relatedSub typev1 typev1' HV).
eapply (He eta'). eassumption.
rewrite Hleftt2.
revert Hnillam. simp_sub. intros H. inversion H; subst.
replace (subst (dot v1 (getleft eta)) e) with ((subst
                                                  (dot (Subst.var 0)
                                                     (shift_sub (getleft eta))) e).[v1]).
replace (subst (getleft eta) t2) with ((subst (sh 1) (subst (getleft eta) t2)).[v1]).
eapply subst1_oft_tm. eassumption. eassumption.
simp_sub.
simp_sub.
rewrite Hrightt2.
revert Hnillam'. simp_sub. intros H. inversion H; subst.
replace (subst (dot v1' (getright eta)) e') with ((subst
                                                  (dot (Subst.var 0)
                                                     (shift_sub (getright eta))) e').[v1']).
replace (subst (getright eta) t2) with ((subst (sh 1) (subst (getright eta) t2)).[v1']).
eapply subst1_oft_tm. eassumption. eassumption.
simp_sub.
simp_sub.
rewrite Hleftt2. eassumption.
rewrite Hrightt2. eassumption.
replace eta' with ((Dyn v1 v1' :: nil) ++ eta) by eauto.
erewrite -> substetaK. eassumption.
Qed.
*)
Lemma funCompatibility_V {G eta e e' t1 t2} :
ofc G t1 ->
ofc G t2 ->
logEq (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) e e' (subst (sh 2) t2) ->
relatedEta G eta ->
V eta (cn_arrow t1 t2)
  (tm_fun (subst (getleft eta) t1) (subst (getleft eta) t2) (subst (under 2 (getleft eta)) e))
  (tm_fun (subst (getright eta) t1) (subst (getright eta) t2) (subst (under 2 (getright eta)) e'))
.
Proof.
intros Ht1 Ht2 He relatedSub.
elimLogEq He HGe HGe'.
assert (ofc nil (subst (getleft eta) t1)) as Ht1nil by (eapply subst_ofc; eauto; eapply subof_sof_left; eauto).
assert (ofc nil (subst (getleft eta) t2)) as Ht2nil by (eapply subst_ofc; eauto; eapply subof_sof_left; eauto).

assert (ofc nil (subst (getright eta) t1)) as Ht1nil' by (eapply subst_ofc; eauto; eapply subof_sof_right; eauto).
assert (ofc nil (subst (getright eta) t2)) as Ht2nil' by (eapply subst_ofc; eauto; eapply subof_sof_right; eauto).

assert(oft nil (tm_fun (subst (getleft eta) t1) (subst (getleft eta) t2)
                   (subst (under 2 (getleft eta)) e)) (cn_arrow (subst (getleft eta) t1)
                                                          (subst (getleft eta) t2))) as Hnillam.
{econstructor; eauto.
replace (subst (sh 2) (subst (getleft eta) t2)) with (subst (under 2 (getleft eta)) (subst (sh 2) t2)).
remember (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
eapply subst_oft; eauto.
replace (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (cl_tm (cn_arrow (subst (sh 1) (subst (getleft eta) t1)) (subst (sh 1) (subst (getleft eta) t2)))
   :: cl_tm (subst (getleft eta) t1) :: nil) with (subst_ctx (getleft eta) G').
replace 2 with (length G') by (subst; eauto).
eapply subof_under_left; eauto.
subst; simpl; simp_sub; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; simp_sub; simp_sub.
simp_sub. unfold under; simp_sub.
}

assert (oft nil (tm_fun (subst (getright eta) t1) (subst (getright eta) t2)
                    (subst (under 2 (getright eta)) e')) (cn_arrow (subst (getright eta) t1)
                                                             (subst (getright eta) t2))) as Hnillam'.
{econstructor; eauto.
replace (subst (sh 2) (subst (getright eta) t2)) with (subst (under 2 (getright eta)) (subst (sh 2) t2)).
remember (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
eapply subst_oft; eauto.
replace (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (cl_tm (cn_arrow (subst (sh 1) (subst (getright eta) t1)) (subst (sh 1) (subst (getright eta) t2)))
   :: cl_tm (subst (getright eta) t1) :: nil) with (subst_ctx (getright eta) G').
replace 2 with (length G') by (subst; eauto).
eapply subof_under_right; eauto.
subst; simpl; simp_sub; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; simp_sub; simp_sub.
unfold under; simp_sub.
}


intros v1 v1' typev1 typev1' HV.
repeat rewrite under2.
rewrite <- under1.
replace (subst
     (dot
        (tm_fun (subst (getright eta) t1) (subst (getright eta) t2)
           (subst (under 2 (getright eta)) e')) 
        (dot v1' (getright eta))) e') with ((subst (under 1 (dot v1' (getright eta))) e').[tm_fun
                                              (subst (getright eta) t1)
                                              (subst (getright eta) t2)
                                              (subst
                                              (under 2 (getright eta)) e')]) by (rewrite under1; reflexivity).
eapply admissibility; eauto.

inversion Hnillam; subst.
repeat rewrite (subst_nil_equal H3) in H5.
repeat rewrite (subst_nil_equal H4) in H5.
replace (dot (Subst.var 0)(dot(Subst.traverse nat S shift_var 0 (Subst.var 0))(shift_sub (shift_sub (getleft eta))))) with (under 2 (getleft eta)) in H5 by eauto.
replace (subst (under 1 (dot v1 (getleft eta))) e) with
(subst (under 1 (dot v1 (sh 0))) (subst (under 2 (getleft eta)) e)) by (unfold under; Subst.simp_sub; f_equal).
replace (subst (getleft eta) t2) with (subst (under 1 (dot v1 (sh 0))) (subst (getleft eta) t2)) by (rewrite (subst_nil_equal H4); eauto).
eapply subst_oft; eauto.
repeat econstructor.
rewrite shift_term_eq_sh.
eapply subst_oft; eauto; repeat econstructor.
rewrite (subst_nil_equal H4).
rewrite (subst_nil_equal (ofc_arrow H3 H4)).
replace (cn_arrow (subst (getleft eta) t1) (subst (getleft eta) t2)) with
(subst (sh 1) (cn_arrow (subst (getleft eta) t1) (subst (getleft eta) t2))) at 2 by
(rewrite (subst_nil_equal (ofc_arrow H3 H4)); eauto).
econstructor.
econstructor.

inversion Hnillam'; subst.
repeat rewrite (subst_nil_equal H3) in H5.
repeat rewrite (subst_nil_equal H4) in H5.
replace (dot (Subst.var 0)(dot(Subst.traverse nat S shift_var 0 (Subst.var 0))(shift_sub (shift_sub (getright eta))))) with (under 2 (getright eta)) in H5 by eauto.
replace (subst (under 1 (dot v1' (getright eta))) e') with
(subst (under 1 (dot v1' (sh 0))) (subst (under 2 (getright eta)) e')) by (unfold under; simp_sub; f_equal).
replace (subst (getright eta) t2) with (subst (under 1 (dot v1' (sh 0))) (subst (getright eta) t2)) by (rewrite (subst_nil_equal H4); eauto).
eapply subst_oft; eauto.
repeat econstructor.
rewrite shift_term_eq_sh.
eapply subst_oft; eauto; repeat econstructor.
rewrite (subst_nil_equal H4).
rewrite (subst_nil_equal (ofc_arrow H3 H4)).
replace (cn_arrow (subst (getright eta) t1) (subst (getright eta) t2)) with
(subst (sh 1) (cn_arrow (subst (getright eta) t1) (subst (getright eta) t2))) at 2 by
(rewrite (subst_nil_equal (ofc_arrow H3 H4)); eauto).
econstructor.
econstructor.

(*
econstructor.
eapply subst_ofc; eauto. eapply subof_sof_left. eauto.
eapply subst_ofc; eauto. eapply subof_sof_left. eauto.
replace (subst (sh 2) (subst (getleft eta) t2)) with (subst (under 2 (getleft eta)) (subst (sh 2) t2)).
eapply subst_oft; eauto.
remember (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
replace (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (cl_tm
     (cn_arrow (subst (sh 1) (subst (getleft eta) t1)) (subst (sh 1) (subst (getleft eta) t2)))
   :: cl_tm (subst (getleft eta) t1) :: nil) with (subst_ctx (getleft eta) G').
replace 2 with (length G') by (subst G'; eauto).
eapply subof_under_left. eauto.
subst G'; simpl; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; Subst.simp_sub; try exact termSubst.
f_equal. f_equal.
simp_sub. f_equal.
Subst.simp_sub; try exact termSubst; eauto.
Subst.simp_sub; try exact termSubst; eauto.
Subst.simp_sub; try exact termSubst; eauto.

econstructor.
eapply subst_ofc; eauto. eapply subof_sof_right. eauto.
eapply subst_ofc; eauto. eapply subof_sof_right. eauto.
replace (subst (sh 2) (subst (getright eta) t2)) with (subst (under 2 (getright eta)) (subst (sh 2) t2)).
eapply subst_oft; eauto.
remember (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
replace (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (cl_tm
     (cn_arrow (subst (sh 1) (subst (getright eta) t1)) (subst (sh 1) (subst (getright eta) t2)))
   :: cl_tm (subst (getright eta) t1) :: nil) with (subst_ctx (getright eta) G').
replace 2 with (length G') by (subst G'; eauto).
eapply subof_under_right. eauto.
subst G'; simpl; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; Subst.simp_sub; try exact termSubst.
f_equal. f_equal.
simp_sub. f_equal.
Subst.simp_sub; try exact termSubst; eauto.
Subst.simp_sub; try exact termSubst; eauto.
Subst.simp_sub; try exact termSubst; eauto.*)

intro i.
repeat rewrite under1.
remember (subst (getleft eta) t1) as A.
remember (subst (getleft eta) t2) as B.
remember (subst (under 2 (getleft eta)) e) as f.
remember (subst (getright eta) t1) as A'.
remember (subst (getright eta) t2) as B'.
remember (subst (under 2 (getright eta)) e') as f'.
pose (eta':= Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v1 v1' :: eta).
replace (dot (unroll i A B f) (dot v1 (getleft eta))) with (getleft eta') by (subst; simpl; f_equal).
replace (dot (unroll i A' B' f') (dot v1' (getright eta))) with (getright eta') by (subst; simpl; f_equal).
eapply (@substetaExp (Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v1 v1' :: nil)).
replace ((Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v1 v1' :: nil) ++ eta) with eta' by eauto.
replace (length (Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v1 v1' :: nil)) with 2 by eauto.
assert (forall i, oft nil (unroll i A B f) (cn_arrow (subst (getleft eta) t1) (subst (getleft eta) t2))) as Hunrolltype1.
intros. subst. eapply unroll_type.
replace (tm_fun (subst (getleft eta) t1) (subst (getleft eta) t2) (subst (under 2 (getleft eta)) e))
with (subst (getleft eta) (tm_fun t1 t2 e)) by (simp_sub; reflexivity).
replace (cn_arrow (subst (getleft eta) t1) (subst (getleft eta) t2))
with (subst (getleft eta) (cn_arrow t1 t2)) by (simp_sub; reflexivity).
eapply subst_oft; eauto. eapply vof_dof; eapply subof_left; eauto. econstructor; eauto.
assert (forall i, oft nil (unroll i A' B' f') (cn_arrow (subst (getright eta) t1) (subst (getright eta) t2))) as Hunrolltype2.
intros. subst. eapply unroll_type.
replace (tm_fun (subst (getright eta) t1) (subst (getright eta) t2) (subst (under 2 (getright eta)) e'))
with (subst (getright eta) (tm_fun t1 t2 e')) by (simp_sub; reflexivity).
replace (cn_arrow (subst (getright eta) t1) (subst (getright eta) t2))
with (subst (getright eta) (cn_arrow t1 t2)) by (simp_sub; reflexivity).
eapply subst_oft; eauto. eapply vof_dof; eapply subof_right; eauto. econstructor; eauto.
assert (relatedEta (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) eta').
econstructor.
- simp_sub; simpl.
- simp_sub; simpl.
- destruct i; eauto; econstructor.
- destruct i; eauto; econstructor.
- assert (is_val v1 /\ is_val v1') as H.
  eapply V_is_val; subst; eauto.
  elim H; clear H; intros H1 H2.
  subst; econstructor; eauto.
- {replace (Dyn v1 v1' :: eta) with ((Dyn v1 v1' :: nil) ++ eta) by eauto.
  replace (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) with (subst (sh (length (Dyn v1 v1' :: nil))) (cn_arrow t1 t2)) by (simp_sub; eauto).
  eapply substetaV.
  induction i; simpl; intros v2 v2' Hv2 Hv2' HV2.

  simp_sub. repeat rewrite project_dot. repeat rewrite project_zero.
  intros E1 E1' HE1 HE1' HK1.
  split; intros H; elim H; clear H; intros n H.
  apply (infinite_loop_doesn't_terminate HE1) in H.
  elim H.
  assert (is_val v2 /\ is_val v2') as Hv.
  eapply V_is_val; subst; eauto.
  elim Hv; clear Hv; intros H1 H2.
  eauto.
  apply (infinite_loop_doesn't_terminate HE1') in H.
  elim H.
  assert (is_val v2 /\ is_val v2') as Hv.
  eapply V_is_val; subst; eauto.
  elim Hv; clear Hv; intros H1 H2.
  eauto.

  Subst.simp_sub; try exact termSubst.
  rewrite (subst_nil_equal_tm (Hunrolltype1 i)).
  rewrite (subst_nil_equal_tm (Hunrolltype2 i)).
  pose (eta2 := (Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v2 v2' :: eta)).
  replace (f.[unroll i A B f,v2]) with (subst (getleft eta2) e) by (subst; subst eta2; rewrite under2; simpl; reflexivity).
  replace (f'.[unroll i A' B' f',v2']) with (subst (getright eta2) e') by (subst; subst eta2; rewrite under2; simpl; reflexivity).
  eapply (@substetaExp (Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v2 v2' :: nil)).
  replace ((Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v2 v2' :: nil) ++ eta) with eta2 by eauto.
  replace (length (Dyn (unroll i A B f) (unroll i A' B' f') :: Dyn v2 v2' :: nil)) with 2 by eauto.
  assert (relatedEta (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) eta2).
  econstructor.
  - simp_sub; simpl.
  - simp_sub; simpl.
  - destruct i; eauto; econstructor.
  - destruct i; eauto; econstructor.
  - assert (is_val v2 /\ is_val v2') as H.
  eapply V_is_val; subst; eauto.
  elim H; clear H; intros H1 H2.
  subst; econstructor; eauto.
  - replace (Dyn v2 v2' :: eta) with ((Dyn v2 v2' :: nil) ++ eta) by eauto.
  replace (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) with (subst (sh (length (Dyn v2 v2' :: nil))) (cn_arrow t1 t2)) by (simp_sub; eauto).
  eapply substetaV.
  eapply IHi.
  - eapply He; eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_left. eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_right. eauto.
  }
- eapply He; eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_left. eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_right. eauto.
Qed.

Lemma clear_cl_tm_relatedEta {G G_closed eta} :
clear_cl_tm G G_closed ->
relatedEta G eta ->
relatedEta G_closed eta.
Proof.
intros Hclear; revert eta; induction Hclear; intros eta Heta; inversion Heta; econstructor; eauto.
Qed.

Lemma fun_closedCompatibility_V {G G_closed eta e e' t1 t2} :
ofc G t1 ->
ofc G t2 ->
clear_cl_tm G G_closed ->
logEq (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G_closed) e e' (subst (sh 2) t2) ->
relatedEta G eta ->
V eta (cn_arrow_closed t1 t2)
  (tm_fun_closed (subst (getleft eta) t1) (subst (getleft eta) t2) (subst (under 2 (getleft eta)) e))
  (tm_fun_closed (subst (getright eta) t1) (subst (getright eta) t2) (subst (under 2 (getright eta)) e'))
.
Proof.
intros Ht1 Ht2 Hclear He relatedSub.
elimLogEq He HGe HGe'.
assert (ofc nil (subst (getleft eta) t1)) as Ht1nil by (eapply subst_ofc; eauto; eapply subof_sof_left; eauto).
assert (ofc nil (subst (getleft eta) t2)) as Ht2nil by (eapply subst_ofc; eauto; eapply subof_sof_left; eauto).

assert (ofc nil (subst (getright eta) t1)) as Ht1nil' by (eapply subst_ofc; eauto; eapply subof_sof_right; eauto).
assert (ofc nil (subst (getright eta) t2)) as Ht2nil' by (eapply subst_ofc; eauto; eapply subof_sof_right; eauto).

assert(oft nil (tm_fun_closed (subst (getleft eta) t1) (subst (getleft eta) t2)
                   (subst (under 2 (getleft eta)) e)) (cn_arrow_closed (subst (getleft eta) t1)
                                                          (subst (getleft eta) t2))) as Hnillam.
{econstructor; eauto.
econstructor.
replace (subst (sh 2) (subst (getleft eta) t2)) with (subst (under 2 (getleft eta)) (subst (sh 2) t2)).
remember (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
eapply subst_oft; eauto.
replace (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G_closed) with (G' ++ G_closed) by (subst G'; eauto).
replace (cl_tm (cn_arrow_closed (subst (sh 1) (subst (getleft eta) t1)) (subst (sh 1) (subst (getleft eta) t2)))
   :: cl_tm (subst (getleft eta) t1) :: nil) with (subst_ctx (getleft eta) G').
replace 2 with (length G') by (subst; eauto).
eapply subof_under_left; eauto.
eapply clear_cl_tm_relatedEta; eauto.
subst; simpl; simp_sub; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; simp_sub; simp_sub.
simp_sub. unfold under; simp_sub.
}


assert (oft nil (tm_fun_closed (subst (getright eta) t1) (subst (getright eta) t2)
                    (subst (under 2 (getright eta)) e')) (cn_arrow_closed (subst (getright eta) t1)
                                                             (subst (getright eta) t2))) as Hnillam'.
{econstructor; eauto.
econstructor.
replace (subst (sh 2) (subst (getright eta) t2)) with (subst (under 2 (getright eta)) (subst (sh 2) t2)).
remember (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: nil) as G'.
eapply subst_oft; eauto.
replace (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G_closed) with (G' ++ G_closed) by (subst G'; eauto).
replace (cl_tm (cn_arrow_closed (subst (sh 1) (subst (getright eta) t1)) (subst (sh 1) (subst (getright eta) t2)))
   :: cl_tm (subst (getright eta) t1) :: nil) with (subst_ctx (getright eta) G').
replace 2 with (length G') by (subst; eauto).
eapply subof_under_right; eauto.
eapply clear_cl_tm_relatedEta; eauto.
subst; simpl; simp_sub; replace TSubstGeneral.subst_cl with subst_cl by eauto; simpl; simp_sub; simp_sub.
simp_sub. unfold under; simp_sub.
}

intros v1 v1' typev1 typev1' HV.
repeat rewrite under2.
rewrite <- under1.
replace (subst
     (dot
        (tm_fun_closed (subst (getright eta) t1) (subst (getright eta) t2)
           (subst (under 2 (getright eta)) e')) 
        (dot v1' (getright eta))) e') with ((subst (under 1 (dot v1' (getright eta))) e').[tm_fun_closed
                                              (subst (getright eta) t1)
                                              (subst (getright eta) t2)
                                              (subst
                                              (under 2 (getright eta)) e')]) by (rewrite under1; reflexivity).
eapply admissibility_closed; eauto.

inversion Hnillam; subst.
inversion H5; subst.
repeat rewrite (subst_nil_equal H2) in H6.
repeat rewrite (subst_nil_equal H4) in H6.
replace (dot (Subst.var 0)(dot(Subst.traverse nat S shift_var 0 (Subst.var 0))(shift_sub (shift_sub (getleft eta))))) with (under 2 (getleft eta)) in H6 by eauto.
replace (subst (under 1 (dot v1 (getleft eta))) e) with
(subst (under 1 (dot v1 (sh 0))) (subst (under 2 (getleft eta)) e)) by (unfold under; Subst.simp_sub; try exact termSubst; f_equal).
replace (subst (getleft eta) t2) with (subst (under 1 (dot v1 (sh 0))) (subst (getleft eta) t2)) by (rewrite (subst_nil_equal H4); eauto).
eapply subst_oft; eauto.
repeat econstructor.
rewrite shift_term_eq_sh.
eapply subst_oft; eauto; repeat econstructor.
rewrite (subst_nil_equal H4).
rewrite (subst_nil_equal (ofc_arrow_closed H2 H4)).
replace (cn_arrow_closed (subst (getleft eta) t1) (subst (getleft eta) t2)) with
(subst (sh 1) (cn_arrow_closed (subst (getleft eta) t1) (subst (getleft eta) t2))) at 2 by
(rewrite (subst_nil_equal (ofc_arrow_closed H2 H4)); eauto).
econstructor.
econstructor.


inversion Hnillam'; subst.
inversion H5; subst.
repeat rewrite (subst_nil_equal H2) in H6.
repeat rewrite (subst_nil_equal H4) in H6.
replace (dot (Subst.var 0)(dot(Subst.traverse nat S shift_var 0 (Subst.var 0))(shift_sub (shift_sub (getright eta))))) with (under 2 (getright eta)) in H6 by eauto.
replace (subst (under 1 (dot v1' (getright eta))) e') with
(subst (under 1 (dot v1' (sh 0))) (subst (under 2 (getright eta)) e')) by (unfold under; Subst.simp_sub; try exact termSubst; f_equal).
replace (subst (getright eta) t2) with (subst (under 1 (dot v1' (sh 0))) (subst (getright eta) t2)) by (rewrite (subst_nil_equal H4); eauto).
eapply subst_oft; eauto.
repeat econstructor.
rewrite shift_term_eq_sh.
eapply subst_oft; eauto; repeat econstructor.
rewrite (subst_nil_equal H4).
rewrite (subst_nil_equal (ofc_arrow_closed H2 H4)).
replace (cn_arrow_closed (subst (getright eta) t1) (subst (getright eta) t2)) with
(subst (sh 1) (cn_arrow_closed (subst (getright eta) t1) (subst (getright eta) t2))) at 2 by
(rewrite (subst_nil_equal (ofc_arrow_closed H2 H4)); eauto).
econstructor.
econstructor.


intro i.
repeat rewrite under1.
remember (subst (getleft eta) t1) as A.
remember (subst (getleft eta) t2) as B.
remember (subst (under 2 (getleft eta)) e) as f.
remember (subst (getright eta) t1) as A'.
remember (subst (getright eta) t2) as B'.
remember (subst (under 2 (getright eta)) e') as f'.
pose (eta':= Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v1 v1' :: eta).
replace (dot (unroll_closed i A B f) (dot v1 (getleft eta))) with (getleft eta') by (subst; simpl; f_equal).
replace (dot (unroll_closed i A' B' f') (dot v1' (getright eta))) with (getright eta') by (subst; simpl; f_equal).
eapply (@substetaExp (Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v1 v1' :: nil)).
replace ((Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v1 v1' :: nil) ++ eta) with eta' by eauto.
replace (length (Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v1 v1' :: nil)) with 2 by eauto.
assert (forall i, oft nil (unroll_closed i A B f) (cn_arrow_closed (subst (getleft eta) t1) (subst (getleft eta) t2))) as Hunrolltype1.
intros. subst. eapply unroll_closed_type; eauto.
assert (forall i, oft nil (unroll_closed i A' B' f') (cn_arrow_closed (subst (getright eta) t1) (subst (getright eta) t2))) as Hunrolltype2.
intros. subst. eapply unroll_closed_type; eauto.
(*replace (tm_fun_closed (subst (getleft eta) t1) (subst (getleft eta) t2) (subst (under 2 (getleft eta)) e))
with (subst (getleft eta) (tm_fun_closed t1 t2 e)) by (simp_sub; reflexivity).
replace (cn_arrow_closed (subst (getleft eta) t1) (subst (getleft eta) t2))
with (subst (getleft eta) (cn_arrow_closed t1 t2)) by (simp_sub; reflexivity).*)
assert (relatedEta (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G_closed) eta') as Hreleta'.
econstructor.
- simp_sub; simpl.
- simp_sub; simpl.
- destruct i; eauto; econstructor.
- destruct i; eauto; econstructor.
- assert (is_val v1 /\ is_val v1') as H.
  eapply V_is_val; subst; eauto.
  elim H; clear H; intros H1 H2.
  subst; econstructor; eauto.
  eapply clear_cl_tm_relatedEta; eauto.
- {replace (Dyn v1 v1' :: eta) with ((Dyn v1 v1' :: nil) ++ eta) by eauto.
  replace (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) with (subst (sh (length (Dyn v1 v1' :: nil))) (cn_arrow_closed t1 t2)) by (simp_sub; eauto).
  eapply substetaV.
  induction i; simpl; intros v2 v2' Hv2 Hv2' HV2.

  simp_sub. repeat rewrite project_dot. repeat rewrite project_zero.
  intros E1 E1' HE1 HE1' HK1.
  split; intros H; elim H; clear H; intros n H.
  apply (infinite_loop_doesn't_terminate_closed HE1) in H.
  elim H.
  assert (is_val v2 /\ is_val v2') as Hv.
  eapply V_is_val; subst; eauto.
  elim Hv; clear Hv; intros H1 H2.
  eauto.
  apply (infinite_loop_doesn't_terminate_closed HE1') in H.
  elim H.
  assert (is_val v2 /\ is_val v2') as Hv.
  eapply V_is_val; subst; eauto.
  elim Hv; clear Hv; intros H1 H2.
  eauto.

  Subst.simp_sub; try exact termSubst.
  rewrite (subst_nil_equal_tm (Hunrolltype1 i)).
  rewrite (subst_nil_equal_tm (Hunrolltype2 i)).
  pose (eta2 := (Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v2 v2' :: eta)).
  replace (f.[unroll_closed i A B f,v2]) with (subst (getleft eta2) e) by (subst; subst eta2; rewrite under2; simpl; reflexivity).
  replace (f'.[unroll_closed i A' B' f',v2']) with (subst (getright eta2) e') by (subst; subst eta2; rewrite under2; simpl; reflexivity).
  eapply (@substetaExp (Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v2 v2' :: nil)).
  replace ((Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v2 v2' :: nil) ++ eta) with eta2 by eauto.
  replace (length (Dyn (unroll_closed i A B f) (unroll_closed i A' B' f') :: Dyn v2 v2' :: nil)) with 2 by eauto.
  assert (relatedEta (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G_closed) eta2).
  econstructor.
  -simp_sub; simpl.
  -simp_sub; simpl.
  - destruct i; eauto; econstructor.
  - destruct i; eauto; econstructor.
  - assert (is_val v2 /\ is_val v2') as Hv.
    eapply V_is_val; subst; eauto.
    elim Hv; clear Hv; intros H1 H2.
    subst; econstructor; eauto.
    eapply clear_cl_tm_relatedEta; eauto.
  - replace (Dyn v2 v2' :: eta) with ((Dyn v2 v2' :: nil) ++ eta) by eauto.
  replace (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) with (subst (sh (length (Dyn v2 v2' :: nil))) (cn_arrow_closed t1 t2)) by (simp_sub; eauto).
  eapply substetaV.
  eapply IHi.
  - eapply He; eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_left. eauto.
  eapply subst_oft; eauto. eapply vof_dof. eapply subof_right. eauto.
  }
-
eapply He; eauto.
eapply subst_oft; eauto. eapply vof_dof; eapply subof_left; eauto.
eapply subst_oft; eauto. eapply vof_dof; eapply subof_right; eauto.
Qed.

Lemma funCompatibility {G e e' t1 t2} :
  ofc G t1 ->
  ofc G t2 ->
  logEq (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) e e' (subst (sh 2) t2)
-> logEq G (tm_fun t1 t2 e) (tm_fun t1 t2 e') (cn_arrow t1 t2).
Proof.
intros Ht1 Ht2 He.
elimLogEq He HGe HGe'.
split. econstructor; eauto.
split. econstructor; eauto.
intros eta relatedSub.
simp_sub.
intros Hnillam Hnillam'.
intros E E' HE HE' HK.
eapply HK.
eassumption.
eassumption.
eapply funCompatibility_V; eauto.
split; eauto; split; eauto.
Qed.


Lemma fun_closedCompatibility {G G' e e' t1 t2} :
  ofc G t1 ->
  ofc G t2 ->
  clear_cl_tm G G' ->
  logEq (cl_tm (cn_arrow_closed (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G') e e' (subst (sh 2) t2)
-> logEq G (tm_fun_closed t1 t2 e) (tm_fun_closed t1 t2 e') (cn_arrow_closed t1 t2).
Proof.
intros Ht1 Ht2 Hclear He.
elimLogEq He HGe HGe'.
split. econstructor; eauto.
split. econstructor; eauto.
intros eta relatedSub.
simp_sub.
intros Hnillam Hnillam'.
intros E E' HE HE' HK.
eapply HK.
eassumption.
eassumption.
eapply fun_closedCompatibility_V; eauto.
split; eauto; split; eauto.
Qed.

Lemma applicationCompatibility {G e1 e1' tau1 e2 e2' tau2} :
  logEq G e1 e1' (cn_arrow tau1 tau2)
  -> logEq G e2 e2' tau1
  -> logEq G (tm_app e1 e2) (tm_app e1' e2') tau2
.
Proof.
intros He1 He2.
elimLogEq He1 HGe1 HGe1'.
elimLogEq He2 HGe2 HGe2'.
split. econstructor; eauto.
split. econstructor; eauto.
simp_sub.
intros eta relatedSub Hnilapp Hnilapp'.
unfold Exp.
intros E E' HE HE' HK.
simp_sub.
pose (E1  := E o (tm_app (k_hole) (subst (getleft eta)  e2 ))).
pose (E1' := E' o (tm_app (k_hole) (subst (getright eta) e2'))).
replace (E[tm_app (subst (getleft eta) e1) (subst (getleft eta) e2)]) with (E1[subst (getleft eta) e1]).
replace (E'[tm_app (subst (getright eta) e1') (subst (getright eta) e2')]) with (E1'[subst (getright eta) e1']).
eapply He1; try simp_sub; try eassumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
simp_sub. unfold E1. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eassumption.
simp_sub. unfold E1'. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
eassumption.
intros v1 v1' typev1 typev1' Hv1.
pose (E2  := E o (tm_app v1  k_hole)).
pose (E2' := E' o (tm_app v1' k_hole)).
replace (E1[v1]) with (E2[subst (getleft eta) e2]).
replace (E1'[v1']) with (E2'[subst (getright eta) e2']).
assert(is_val v1) as isvalv1. eapply (V_is_val relatedSub typev1 typev1' Hv1).
assert(oft nil v1 (cn_arrow (subst (getleft eta) tau1) (subst (getleft eta) tau2))) as istypev1. eassumption.
assert(is_val v1') as isvalv1'. eapply (V_is_val relatedSub typev1 typev1' Hv1).
assert(oft nil v1' (cn_arrow (subst (getright eta) tau1) (subst (getright eta) tau2))) as istypev1'. eassumption.
eapply He2; try eassumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
unfold E2. eapply compose_cont. eapply ofk_app_2. eassumption. eassumption. econstructor. revert HE. simp_sub. eauto.
unfold E2'. eapply compose_cont. eapply ofk_app_2. eassumption. eassumption. econstructor. revert HE. simp_sub. eauto.
intros v2 v2' typev2 typev2' Hv2.
replace (E2[v2]) with (E[tm_app v1 v2]).
replace (E2'[v2']) with (E'[tm_app v1' v2']).
inversion isvalv1; subst; inversion istypev1; subst.
inversion isvalv1'; subst; inversion istypev1'; subst.
eapply kleeneHeadLeft. eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_app3. eapply (V_is_val relatedSub typev2 typev2' Hv2).
eapply kleeneHeadRight. eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_app3. eapply (V_is_val relatedSub typev2 typev2' Hv2).
simpl in Hv1.
eapply Hv1. eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
unfold E2'; simpl; erewrite <- fill_associativity; simpl.
rewrite (fill_in_term istypev1'). reflexivity.
unfold E2; simpl; erewrite <- fill_associativity; simpl.
rewrite (fill_in_term istypev1). reflexivity.
unfold E1'; unfold E2'; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl.
f_equal. f_equal.
rewrite (fill_in_term typev1'). reflexivity.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; unfold E2; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl.
f_equal. f_equal.
rewrite (fill_in_term typev1). reflexivity.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
unfold E1'; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
Qed.


Lemma application_closedCompatibility {G e1 e1' tau1 e2 e2' tau2} :
  logEq G e1 e1' (cn_arrow_closed tau1 tau2)
  -> logEq G e2 e2' tau1
  -> logEq G (tm_app_closed e1 e2) (tm_app_closed e1' e2') tau2
.
Proof.
intros He1 He2.
elimLogEq He1 HGe1 HGe1'.
elimLogEq He2 HGe2 HGe2'.
split. econstructor; eauto.
split. econstructor; eauto.
simp_sub.
intros eta relatedSub Hnilapp Hnilapp'.
unfold Exp.
intros E E' HE HE' HK.
simp_sub.
pose (E1  := E o (tm_app_closed (k_hole) (subst (getleft eta)  e2 ))).
pose (E1' := E' o (tm_app_closed (k_hole) (subst (getright eta) e2'))).
replace (E[tm_app_closed (subst (getleft eta) e1) (subst (getleft eta) e2)]) with (E1[subst (getleft eta) e1]).
replace (E'[tm_app_closed (subst (getright eta) e1') (subst (getright eta) e2')]) with (E1'[subst (getright eta) e1']).
eapply He1; try simp_sub; try eassumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
simp_sub. unfold E1. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eassumption.
simp_sub. unfold E1'. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
eassumption.
intros v1 v1' typev1 typev1' Hv1.
pose (E2  := E o (tm_app_closed v1  k_hole)).
pose (E2' := E' o (tm_app_closed v1' k_hole)).
replace (E1[v1]) with (E2[subst (getleft eta) e2]).
replace (E1'[v1']) with (E2'[subst (getright eta) e2']).
assert(is_val v1) as isvalv1. eapply (V_is_val relatedSub typev1 typev1' Hv1).
assert(oft nil v1 (cn_arrow_closed (subst (getleft eta) tau1) (subst (getleft eta) tau2))) as istypev1. eassumption.
assert(is_val v1') as isvalv1'. eapply (V_is_val relatedSub typev1 typev1' Hv1).
assert(oft nil v1' (cn_arrow_closed (subst (getright eta) tau1) (subst (getright eta) tau2))) as istypev1'. eassumption.
eapply He2; try eassumption.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
unfold E2. eapply compose_cont. eapply ofk_app_closed_2. eassumption. eassumption. econstructor. revert HE. simp_sub. eauto.
unfold E2'. eapply compose_cont. eapply ofk_app_closed_2. eassumption. eassumption. econstructor. revert HE. simp_sub. eauto.
intros v2 v2' typev2 typev2' Hv2.
replace (E2[v2]) with (E[tm_app_closed v1 v2]).
replace (E2'[v2']) with (E'[tm_app_closed v1' v2']).
inversion isvalv1; subst; inversion istypev1; subst.
inversion isvalv1'; subst; inversion istypev1'; subst.
eapply kleeneHeadLeft. eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_app_closed3. eapply (V_is_val relatedSub typev2 typev2' Hv2).
eapply kleeneHeadRight. eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_app_closed3. eapply (V_is_val relatedSub typev2 typev2' Hv2).
simpl in Hv1.
eapply Hv1. eassumption. eassumption. eassumption. eassumption. eassumption. eassumption.
unfold E2'; simpl; erewrite <- fill_associativity; simpl.
rewrite (fill_in_term istypev1'). reflexivity.
unfold E2; simpl; erewrite <- fill_associativity; simpl.
rewrite (fill_in_term istypev1). reflexivity.
unfold E1'; unfold E2'; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl.
f_equal. f_equal.
rewrite (fill_in_term typev1'). reflexivity.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; unfold E2; simpl; erewrite <- fill_associativity; simpl. erewrite <- fill_associativity;
simpl.
f_equal. f_equal.
rewrite (fill_in_term typev1). reflexivity.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
unfold E1'; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold E1; simpl; erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
Qed.


Lemma variableCompatibility {G i t} : 
  index i G (cl_tm t) -> logEq G (var i) (var i) (subst (sh (S i)) t).
Proof.
intro H.
split. econstructor; eauto.
split. econstructor; eauto.
intros eta relatedSub.
revert H. revert i.
induction relatedSub.
 - intros i H. inversion H.
 - intros i Hi Hnili Hnili'.
   destruct i.
      simpl in Hi. inversion Hi.
      simp_sub. simpl. rewrite project_dot. rewrite project_dot.
      replace (Sta c c' R :: E) with ((Sta c c' R :: nil) ++ E) by eauto.
      replace (subst (sh (S (S i))) t) with (subst (sh (length (Sta c c' R :: nil))) (subst (sh (S i)) t)).
      rewrite substetaExp. eapply IHrelatedSub. inversion Hi; subst. eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. econstructor. inversion Hi; subst; eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. econstructor. inversion Hi; subst; eassumption.
      Subst.simp_sub; try exact termSubst. simpl. replace (i+1) with (S i) by lia. reflexivity.
- intros i Hi Hnili Hnili'.
   destruct i.
      simpl in Hi. inversion Hi; subst. replace (Dyn e e' :: E) with ((Dyn e e' :: nil) ++ E) by eauto.
      replace 1 with (length (Dyn e e' :: nil)) by eauto. rewrite substetaExp.
      simpl. simp_sub. eapply V_to_Exp. eassumption. eassumption. eassumption.
      simp_sub. simpl. rewrite project_dot. rewrite project_dot.
      replace (Dyn e e' :: E) with ((Dyn e e' :: nil) ++ E) by eauto.
      replace (subst (sh (S (S i))) t) with (subst (sh (length (Dyn e e' :: nil))) (subst (sh (S i)) t)).
      rewrite substetaExp. eapply IHrelatedSub. inversion Hi; subst. eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. econstructor. inversion Hi; subst; eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. econstructor. inversion Hi; subst; eassumption.
      Subst.simp_sub; try exact termSubst. simpl. replace (i+1) with (S i) by lia. reflexivity.
- intros i Hi Hnili Hnili'.
   destruct i.
      simpl in Hi. inversion Hi; subst. simp_sub. simpl. rewrite project_dot. rewrite project_dot.
      replace (Dyn e e' :: E) with ((Dyn e e' :: nil) ++ E) by eauto.
      replace (subst (sh (S (S i))) t) with (subst (sh (length (Dyn e e' :: nil))) (subst (sh (S i)) t)).
      rewrite substetaExp. eapply IHrelatedSub. inversion Hi; subst. eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. econstructor. inversion Hi; subst; eassumption.
      eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. econstructor. inversion Hi; subst; eassumption.
      Subst.simp_sub; try exact termSubst. simpl. replace (i+1) with (S i) by lia. reflexivity.
Qed.

Lemma unitCompatibility {G} : logEq G tm_star tm_star cn_unit.
Proof.
split. econstructor.
split. econstructor.
intros eta _ _ _.
simp_sub.
unfold Exp.
intros E E' HE HE' HK.
eapply HK.
simp_sub; econstructor.
simp_sub; econstructor.
simpl.
eauto.
Qed.

Lemma letCompatibility {G e1 e1' tau1 e2 e2' tau2} :
  logEq G e1 e1' tau1
  -> logEq (cl_tm tau1 :: G) e2 e2' (subst (sh 1) tau2)
  -> logEq G (tm_lett e1 e2) (tm_lett e1' e2') tau2
.
Proof.
intros He1 He2.
elimLogEq He1 HGe1 HGe1'.
elimLogEq He2 HGe2 HGe2'.
split. econstructor; eauto.
split. econstructor; eauto.
intros eta relatedSub Hnil Hnil'.
simp_sub.
pose (S := (dot (Subst.var 0) (shift_sub (getleft eta)))).
pose (S' := (dot (Subst.var 0) (shift_sub (getright eta)))).
assert(oft (cl_tm (subst (getleft eta) tau1) :: nil) (subst S e2) (subst S (subst (sh 1) tau2))) as HGe2Subst.
unfold S.
eapply (subst_oft (cl_tm (subst (getleft eta) tau1) ::nil) (cl_tm tau1 :: G)).
remember (cl_tm tau1 :: nil) as G'.
replace (cl_tm (subst (getleft eta) tau1) :: nil) with (subst_ctx (getleft eta) G') by (subst G'; eauto).
replace (cl_tm tau1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (dot (Subst.var 0) (shift_sub (getleft eta))) with (under (length G') (getleft eta)) by (subst G'; eauto).
eapply subof_under_left; eauto.
eauto.
assert(oft (cl_tm (subst (getright eta) tau1) :: nil) (subst S' e2') (subst S' (subst (sh 1) tau2))) as HGe2'Subst.
unfold S'.
eapply (subst_oft (cl_tm (subst (getright eta) tau1) ::nil) (cl_tm tau1 :: G)).
remember (cl_tm tau1 :: nil) as G'.
replace (cl_tm (subst (getright eta) tau1) :: nil) with (subst_ctx (getright eta) G') by (subst G'; eauto).
replace (cl_tm tau1 :: G) with (G' ++ G) by (subst G'; eauto).
replace (dot (Subst.var 0) (shift_sub (getright eta))) with (under (length G') (getright eta)) by (subst G'; eauto).
eapply subof_under_right; eauto.
eauto.
fold S. fold S'.
unfold Exp.
intros E E' HE HE' HK.
replace (E[tm_lett (subst (getleft eta) e1) (subst S e2)]) with (E o(tm_lett k_hole (subst S e2))[(subst (getleft eta) e1)]).
replace (E'[tm_lett (subst (getright eta) e1') (subst S' e2')]) with (E' o(tm_lett k_hole (subst S' e2'))[(subst (getright eta) e1')]).
eapply He1; eauto.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. reflexivity.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. reflexivity.
eapply compose_cont. econstructor. econstructor.
unfold S.
eapply (subst_oft' _ (cl_tm tau1 :: G)). econstructor.
Subst.simp_sub; try exact termSubst.
pose (X := (cl_tm (subst (getleft eta) tau1) :: nil)).
fold X.
replace (X) with (X ++ nil) by eauto.
replace 1 with (length X) by eauto.
eapply subof_weaken_dof.
eapply vof_dof.
eapply subof_left.
eassumption.
simp_sub. econstructor. replace (Subst.var) with var by eauto.
Subst.simp_sub; try exact termSubst.
rewrite subst_compose.
eapply oft_var.
econstructor.
eassumption.
 Subst.simp_sub; try exact termSubst. rewrite subst_compose. reflexivity. eassumption.
eapply compose_cont. econstructor. econstructor.
eapply (subst_oft' _ (cl_tm tau1 :: G)).
econstructor.
Subst.simp_sub; try exact termSubst.
pose (X := (cl_tm (subst (getright eta) tau1) :: nil)).
fold X.
replace (X) with (X ++ nil) by eauto.
replace 1 with (length X) by eauto.
eapply subof_weaken_dof.
eapply vof_dof.
eapply subof_right.
eassumption.
simp_sub. econstructor. replace (Subst.var) with var by eauto.
Subst.simp_sub; try exact termSubst.
rewrite subst_compose.
eapply oft_var.
econstructor.
eassumption.
unfold S'. Subst.simp_sub; try exact termSubst. rewrite subst_compose. reflexivity.
eassumption.
intros v v' typev typev' HV.
erewrite <- fill_associativity; simpl.
erewrite <- fill_associativity; simpl.
replace ((subst S e2)[v]) with (subst S e2).
replace ((subst S' e2')[v']) with (subst S' e2').
eapply kleeneHeadLeft.
eapply stepECompose.
econstructor. eassumption.
simpl.
eapply tstep_lett2.
eapply (V_is_val relatedSub typev typev' HV).
eapply kleeneHeadRight.
eapply stepECompose.
econstructor. eassumption.
simpl.
eapply tstep_lett2.
eapply (V_is_val relatedSub typev typev' HV).
unfold S. unfold S'.
Subst.simp_sub; try exact termSubst.
repeat (rewrite subst_var; rewrite project_zero).
pose (eta' := Dyn v v' :: eta).
replace (dot v (getleft eta)) with (getleft eta').
replace (dot v' (getright eta)) with (getright eta').
assert(relatedEta (cl_tm tau1 :: G) eta') as releta'.
econstructor.  eassumption. eassumption. (* eassumption.*) eapply (V_is_val relatedSub typev typev' HV). eapply (V_is_val relatedSub typev typev' HV). eassumption. eassumption.
eapply He2.
eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold eta'; simpl; Subst.simp_sub; try exact termSubst; eassumption.
unfold eta'; simpl; Subst.simp_sub; try exact termSubst; eassumption.
unfold eta'.
replace (Dyn v v' :: eta) with ((Dyn v v' :: nil) ++ eta) by eauto.
replace 1 with (length (Dyn v v' :: nil)) by eauto.
rewrite substetaK. eassumption.
unfold eta'; simpl; reflexivity.
unfold eta'; simpl; reflexivity.

erewrite fill_in_term. reflexivity.
eassumption.

erewrite fill_in_term. reflexivity.
eassumption.

erewrite <- fill_associativity. simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eassumption.

erewrite <- fill_associativity. simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity. eassumption.
Qed.


Lemma abortCompatibility {G e e' tau}:
  ofc G tau
  -> logEq G e e' cn_zero
  -> logEq G (tm_abort tau e) (tm_abort tau e') tau
.
Proof.
intros Hofc He.
elimLogEq He HGe HGe'.
split; try (econstructor; eassumption).
split; try (econstructor; eassumption).
intros eta Hreleta.
simp_sub.
intros Hnilabort Hnilabort'.
intros E E' HE HE' HK.
simp_sub.
replace (E[tm_abort (subst (getleft eta) tau) (subst (getleft eta) e)]) with
((E o (tm_abort (subst (getleft eta) tau) k_hole))[subst (getleft eta) e]).
replace (E'[tm_abort (subst (getright eta) tau) (subst (getright eta) e')]) with
((E' o (tm_abort (subst (getright eta) tau) k_hole))[subst (getright eta) e']).
eapply He.
eassumption.
inversion Hnilabort; subst; eassumption.
inversion Hnilabort'; subst; eassumption.
eapply compose_cont. econstructor. eapply subst_ofc.
eapply subof_dof_sof.
eapply vof_dof.
eapply subof_left.
eassumption.
eassumption.
econstructor.
eassumption.
eapply compose_cont. econstructor. eapply subst_ofc.
eapply subof_dof_sof.
eapply vof_dof.
eapply subof_right.
eassumption.
eassumption.
econstructor.
eassumption.
intros v v' Hv Hv' HV.
inversion HV.
erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_type. reflexivity.
eapply subst_ofc. eapply subof_sof_right. eauto.
eassumption.
erewrite <- fill_associativity; simpl.
f_equal. f_equal.
erewrite fill_in_type. reflexivity.
eapply subst_ofc. eapply subof_sof_left. eauto.
eauto.
Qed.

Lemma contCompatibility_V {G k k' tau eta}:
ofc nil tau ->
k ÷ tau ->
k' ÷ tau ->
K V nil tau k k' ->
relatedEta G eta ->
V eta (cn_cont (subst (sh (length G)) tau)) (tm_cont (subst (getleft eta) k))
  (tm_cont (subst (getright eta) k')).
Proof.
intros Hofc Hofk Hofk' ofHkk releta.
simpl.
replace eta with (eta ++ nil).
rewrite (relatedetalength releta).
rewrite substetaK.
repeat (erewrite subst_nil_equal_k); eassumption.
rewrite app_nil_r. reflexivity.
Qed.

Lemma contCompatibility {G k k' tau}:
ofc nil tau
-> ofk k tau cn_unit
-> ofk k' tau cn_unit
-> K V nil tau k k'
-> logEq G (tm_cont k) (tm_cont k') (cn_cont (subst (sh (length G)) tau))
.
Proof.
intros Hofc Hofk Hofk' ofHKk.
split. econstructor. eassumption. eassumption. reflexivity.
split. econstructor. eassumption. eassumption. reflexivity.
intros eta releta.
simp_sub.
intros Hk Hk'.
intros E E' HE HE' HK.
eapply HK.
simp_sub.
simp_sub.
eapply contCompatibility_V; eauto.
Qed.

Lemma plamCompatibility_V {G e e' t eta} :
logEq (cl_tp :: G) e e' t ->
relatedEta G eta ->
V eta (cn_all t) (tm_plam (subst (under 1 (getleft eta)) e))
  (tm_plam (subst (under 1 (getright eta)) e')).
Proof.
intros He releta.
elimLogEq He HGe HGe'.
simpl.
intros tau1 tau1' R tau1nil tau1'nil relR.
simp_sub.
replace (dot tau1 (getleft eta)) with (getleft (Sta tau1 tau1' R :: eta)) by eauto.
replace (dot tau1' (getright eta)) with (getright (Sta tau1 tau1' R :: eta)) by eauto.
eapply He.
econstructor.
eassumption.
eassumption.
eassumption.
eassumption.
simpl.
eapply (subst_oft _ (cl_tp :: G)).
econstructor.
eapply vof_dof.
eapply subof_left.
eassumption.
econstructor.
eassumption.
eassumption.
eapply (subst_oft _ (cl_tp :: G)).
econstructor.
eapply vof_dof.
eapply subof_right.
eassumption.
econstructor.
eassumption.
eassumption.
Qed.

Lemma plamCompatibility {G e e' t} :
logEq (cl_tp :: G) e e' t
-> logEq G (tm_plam e) (tm_plam e') (cn_all t).
Proof.
intros He.
elim He; intros HGe H; elim H; clear H; intros HGe' H.
split. econstructor. eassumption.
split. econstructor. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.
eapply HK.
eassumption.
eassumption.
eapply plamCompatibility_V; eauto.
Qed.



Lemma pappCompatibility {G e e' c t} :
logEq G e e' (cn_all t)
-> ofc G c
-> logEq G (tm_papp e c) (tm_papp e' c) (t.[c])
.
Proof.
intros He.
elimLogEq He HGe HGe'.
split. econstructor. eassumption. eassumption.
split. econstructor. eassumption. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.
replace (E[tm_papp (subst (getleft eta) e) (subst (getleft eta) c)]) with
((E o (tm_papp k_hole (subst (getleft eta) c))) [subst (getleft eta) e]).
replace (E'[tm_papp (subst (getright eta) e') (subst (getright eta) c)]) with
((E' o (tm_papp k_hole (subst (getright eta) c))) [subst (getright eta) e']).
eapply He.
eassumption.
eapply (subst_oft _ G). eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply (subst_oft _ G). eapply vof_dof. eapply subof_right. eassumption. eassumption.
simp_sub.
eapply compose_cont. econstructor. econstructor. eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. eassumption.
revert HE; unfold under; simp_sub.
eapply compose_cont. econstructor. simp_sub; econstructor. eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. eassumption.
revert HE'; unfold under; simp_sub.
intros v v'.
simp_sub.
intros nilv nilv' HV.
revert HV; destruct v; simpl; intro HV; try contradiction; revert HV; destruct v'; simpl; intro HV; try contradiction.
eapply kleeneHeadLeft.
rewrite <- fill_associativity; simpl.
replace ((subst (getleft eta) c)[tm_plam v]) with (subst (getleft eta) c).
eapply stepECompose.
econstructor.
eassumption.
simpl.
eapply tstep_papp2.
erewrite fill_in_type; eauto.
eapply subst_ofc; eauto.
eapply subof_sof_left; eauto.
eapply kleeneHeadRight.
erewrite <- (@fill_associativity E'); simpl.
replace ((subst (getright eta) c)[tm_plam v']) with (subst (getright eta) c).
eapply stepECompose.
econstructor.
eassumption.
simpl.
eapply tstep_papp2.
erewrite fill_in_type; eauto.
eapply subst_ofc; eauto.
eapply subof_sof_right; eauto.
apply (HV (subst (getleft eta) c) (subst (getright eta) c) (V eta c)).
eapply subst_ofc.
eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_ofc.
eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. eassumption.
intros. eapply V_is_val. eassumption. eassumption. eassumption. eassumption.
eauto.
eauto.
eapply typeinK. eassumption.
rewrite <- (fill_associativity). simpl.
f_equal. f_equal.
erewrite fill_in_type; eauto.
eapply subst_ofc; eauto.
eapply subof_sof_right; eauto.
rewrite <- (fill_associativity). simpl.
f_equal. f_equal.
erewrite fill_in_type; eauto.
eapply subst_ofc; eauto.
eapply subof_sof_left; eauto.
Qed.

Lemma letccCompatibility {G e e' tau}:
ofc G tau
-> logEq (cl_tm (cn_cont tau) :: G) e e' (subst (sh 1) tau)
-> logEq G (tm_letcc tau e) (tm_letcc tau e') tau
.
Proof.
intros Htau He.
elimLogEq He HGe HGe'.
split. econstructor. eassumption. eassumption.
split. econstructor. eassumption. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.
eapply kleeneHeadLeft.
eapply stepECompose. econstructor. eassumption.
econstructor.
eapply kleeneHeadRight.
eapply stepECompose. econstructor. eassumption.
econstructor.
simpl. simp_sub.
pose (eta' := (Dyn (tm_cont E) (tm_cont E') :: eta)).
replace (dot (tm_cont E) (getleft eta)) with (getleft eta').
replace (dot (tm_cont E') (getright eta)) with (getright eta').
assert (relatedEta (cl_tm (cn_cont tau) :: G) eta') as relEta.
econstructor. (* econstructor; eassumption.*)
simp_sub. econstructor. eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. eassumption. eassumption.
simpl. rewrite subst_id. reflexivity.
simp_sub. econstructor. eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. eassumption. eassumption.
simpl. rewrite subst_id. reflexivity.
econstructor.
econstructor.
eassumption.
simpl. eassumption.
eapply He.
eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
replace (subst (getleft eta') (subst (sh 1) tau)) with (subst (getleft eta) tau).
eassumption.
unfold eta'. simpl. simp_sub.
replace (subst (getright eta') (subst (sh 1) tau)) with (subst (getright eta) tau).
eassumption.
unfold eta'. simpl. simp_sub.
replace eta' with ((Dyn (tm_cont E) (tm_cont E'):: nil) ++ eta) by (unfold eta'; eauto).
replace 1 with (length (Dyn (tm_cont E) (tm_cont E'):: nil)) by eauto. 
rewrite substetaK. eassumption.
unfold eta'. simpl. reflexivity.
unfold eta'. simpl. reflexivity.
Qed.

Lemma throwCompatibility {G e1 e2 e1' e2' tau}:
logEq G e1 e1' tau
-> logEq G e2 e2' (cn_cont tau)
-> logEq G (tm_throw e1 e2) (tm_throw e1' e2') cn_zero.
Proof.
intros He1 He2.
elimLogEq He1 HGe1 HGe1'.
elimLogEq He2 HGe2 HGe2'.
split. econstructor. eassumption. eassumption.
split. econstructor. eassumption. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.
replace (E[tm_throw (subst (getleft eta) e1) (subst (getleft eta) e2)]) with
((E o (tm_throw k_hole (subst (getleft eta) e2))) [(subst (getleft eta) e1)]).
replace (E'[tm_throw (subst (getright eta) e1') (subst (getright eta) e2')]) with
((E' o (tm_throw k_hole (subst (getright eta) e2'))) [(subst (getright eta) e1')]).
eapply He1.
eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_left. eassumption. eassumption. simp_sub. eassumption.
eapply compose_cont. econstructor. econstructor.
eapply subst_oft'. eapply vof_dof. eapply subof_right. eassumption. eassumption. simp_sub. eassumption.
intros v1 v1' v1type v1'type HV1.
replace (E o (tm_throw k_hole (subst (getleft eta) e2))[v1]) with
  ((E o (tm_throw v1 k_hole))[subst (getleft eta) e2]).
replace (E' o (tm_throw k_hole (subst (getright eta) e2'))[v1']) with
  ((E' o (tm_throw v1' k_hole))[subst (getright eta) e2']).
eapply He2.
eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
eapply compose_cont. eapply ofk_throw_2. eassumption. eapply (V_is_val releta v1type v1'type HV1). econstructor. eassumption.
eapply compose_cont. eapply ofk_throw_2. eassumption. eapply (V_is_val releta v1type v1'type HV1). econstructor. eassumption.
intros v2 v2'.
elim v2; simpl; try contradiction. intros E1 _.
elim v2'; simpl; try contradiction. intros E1' _.
intros v2type v2'type HV2.
rewrite <- (fill_associativity). simpl.
rewrite (fill_in_term v1type).
rewrite <- (fill_associativity). simpl.
rewrite (fill_in_term v1'type).
eapply kleeneHeadLeft.
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_throw.
eapply (V_is_val releta v1type v1'type HV1).
eapply kleeneHeadRight.
eapply stepECompose. econstructor. eassumption. simpl. eapply tstep_throw.
eapply (V_is_val releta v1type v1'type HV1).
eapply HV2.
eassumption.
eassumption.
eassumption.
rewrite <- (fill_associativity). simpl. rewrite (fill_in_term v1'type).
rewrite <- (fill_associativity). simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
rewrite <- (fill_associativity). simpl. rewrite (fill_in_term v1type).
rewrite <- (fill_associativity). simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
rewrite <- fill_associativity. simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
rewrite <- fill_associativity. simpl.
f_equal. f_equal.
erewrite fill_in_term. reflexivity.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
Qed.

Lemma packCompatibility_V {G c e e' t eta v1 v1'} :
ofc G c ->
logEq G e e' (t.[c]) ->
ofc (cl_tp :: G) t ->
relatedEta G eta ->
oft nil v1 (subst (getleft eta) (t.[c])) ->
oft nil v1' (subst (getright eta) (t.[c])) ->
V eta (t.[c]) v1 v1' ->
V eta (cn_exists t) (tm_pack (subst (getleft eta) c) v1 (subst (under 1 (getleft eta)) t))
  (tm_pack (subst (getright eta) c) v1' (subst (under 1 (getright eta)) t))
.
Proof.
intros Hc He Ht releta v1type v1'type HV1.
elimLogEq He HGe HGe'.
simpl.
exists (V eta c).
split.
intros.
eapply V_is_val; eauto.
eapply typeinV. eassumption.
Qed.

Lemma packCompatibility {G c e e' t} :
ofc G c
-> logEq G e e' (t.[c])
-> ofc (cl_tp :: G) t
-> logEq G (tm_pack c e t) (tm_pack c e' t) (cn_exists t)
.
Proof.
intros Hc He Ht.
elim He; intros HGe H; elim H; clear H; intros HGe' H.
split. econstructor. eassumption. eassumption. eassumption.
split. econstructor. eassumption. eassumption. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.
replace (E[tm_pack (subst (getleft eta) c) (subst (getleft eta) e)
      (subst (under 1 (getleft eta)) t)])
with ((E o (tm_pack (subst (getleft eta) c) k_hole
      (subst (dot (Subst.var 0) (shift_sub (getleft eta))) t))) [(subst (getleft eta) e)])
by (
rewrite <- fill_associativity;
simpl; subst;
f_equal; f_equal;
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
try (eapply subof_sof_left; eauto; fail);
pose (G' := cl_tp :: nil);
replace (cl_tp :: G) with (G' ++ G) by eauto;
replace (dot (Subst.var 0) (shift_sub (getleft eta))) with (under (length G') (getleft eta)) by eauto;
eapply subof_under_left_sof; eauto).

replace (E'[tm_pack (subst (getright eta) c) (subst (getright eta) e')
       (subst (under 1 (getright eta)) t)])
with ((E' o (tm_pack (subst (getright eta) c) k_hole
       (subst (dot (Subst.var 0) (shift_sub (getright eta))) t)))[(subst (getright eta) e')])
by (
rewrite <- fill_associativity;
simpl; subst;
f_equal; f_equal;
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
try (eapply subof_sof_right; eauto; fail);
pose (G' := cl_tp :: nil);
replace (cl_tp :: G) with (G' ++ G) by eauto;
replace (dot (Subst.var 0) (shift_sub (getright eta))) with (under (length G') (getright eta)) by eauto;
eapply subof_under_right_sof; eauto).

eapply He.
eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
eapply compose_cont. econstructor.
eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. eassumption.
Subst.simp_sub; try exact termSubst. econstructor.
eapply subst_ofc.
replace (cl_tp :: nil) with (subst_ctx (getleft eta) (cl_tp :: nil) ++ nil) by (simp_sub; eauto).
replace ((dot (Subst.var 0) (shift_sub (getleft eta)))) with (under (length (cl_tp :: nil)) (getleft eta)) by (simpl; eauto).
eapply subof_under_sof.
eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. simpl. eassumption.
eassumption.
eapply compose_cont. econstructor.
eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. eassumption.
Subst.simp_sub; try exact termSubst. econstructor.
eapply subst_ofc.
replace (cl_tp :: nil) with (subst_ctx (getright eta) (cl_tp :: nil) ++ nil) by (simp_sub; eauto).
replace ((dot (Subst.var 0) (shift_sub (getright eta)))) with (under (length (cl_tp :: nil)) (getright eta)) by (simpl; eauto).
eapply subof_under_sof.
eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. simpl. eassumption.
eassumption.
intros v1 v1' v1type v1'type HV1.
rewrite <- (fill_associativity). simpl.
replace ((subst (dot (Subst.var 0) (shift_sub (getleft eta))) t)[v1]) with (subst (dot (Subst.var 0) (shift_sub (getleft eta))) t)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
pose (G' := cl_tp :: nil);
replace (cl_tp :: G) with (G' ++ G) by eauto;
replace (dot (Subst.var 0) (shift_sub (getleft eta))) with (under (length G') (getleft eta)) by eauto;
eapply subof_under_left_sof; eauto).

rewrite <- (fill_associativity). simpl.
replace ((subst (dot (Subst.var 0) (shift_sub (getright eta))) t)[v1']) with (subst (dot (Subst.var 0) (shift_sub (getright eta))) t)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
pose (G' := cl_tp :: nil);
replace (cl_tp :: G) with (G' ++ G) by eauto;
replace (dot (Subst.var 0) (shift_sub (getright eta))) with (under (length G') (getright eta)) by eauto;
eapply subof_under_right_sof; eauto).

eapply HK.
replace ((subst (getleft eta) c)[v1]) with (subst (getleft eta) c)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
eapply subof_sof_left; eauto).

replace ((subst (getright eta) c)[v1']) with (subst (getright eta) c)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
eapply subof_sof_right; eauto).

econstructor; inversion nile; subst; try eassumption.
revert v1type. Subst.simp_sub; try exact termSubst. eauto.

replace ((subst (getright eta) c)[v1']) with (subst (getright eta) c)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
eapply subof_sof_right; eauto).

econstructor; inversion nile'; subst; try eassumption.
revert v1'type. Subst.simp_sub; try exact termSubst. eauto.


replace ((subst (getright eta) c)[v1']) with (subst (getright eta) c)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
eapply subof_sof_right; eauto).
replace ((subst (getleft eta) c)[v1]) with (subst (getleft eta) c)
by (
erewrite fill_in_type; eauto;
eapply subst_ofc; eauto;
eapply subof_sof_left; eauto).
replace (dot (Subst.var 0) (shift_sub (getleft eta))) with (under 1 (getleft eta)) by eauto.
replace (dot (Subst.var 0) (shift_sub (getright eta))) with (under 1 (getright eta)) by eauto.

eapply packCompatibility_V; eauto.

Qed.

Lemma unpackCompatibility {G e1 e2 e1' e2' t t'} :
logEq G e1 e1' (cn_exists t)
-> logEq (cl_tm t :: cl_tp :: G) e2 e2' (subst (sh 2) t')
-> ofc G t'
-> logEq G (tm_unpack e1 e2) (tm_unpack e1' e2') t'
.
Proof.
intros He1 He2 Ht'.
elimLogEq He1 HGe1 HGe1'.
elimLogEq He2 HGe2 HGe2'.
split. econstructor. eassumption. eassumption. eassumption.
split. econstructor. eassumption. eassumption. eassumption.
intros eta releta.
simp_sub.
intros nile nile'.
intros E E'.
simp_sub.
intros HE HE' HK.

replace (E[tm_unpack (subst (getleft eta) e1) (subst (under 2 (getleft eta)) e2)]) with
((E o(tm_unpack k_hole
      (subst (under 2 (getleft eta)) e2)))[(subst (getleft eta) e1)])
by
(rewrite <- fill_associativity;
remember (under 2 (getleft eta)) as S;
remember (under 2 (getright eta)) as S';
simpl; subst;
f_equal; f_equal;
erewrite fill_in_term; eauto;
eapply subst_oft; eauto;
pose (G' := cl_tm t :: cl_tp :: nil);
replace (cl_tm t :: cl_tp :: G) with (G' ++ G) by eauto;
replace 2 with (length G') by eauto;
eapply subof_under_left; eauto).

replace (E'[tm_unpack (subst (getright eta) e1')
       (subst (under 2 (getright eta)) e2')]) with
((E' o (tm_unpack k_hole
       (subst (under 2 (getright eta)) e2')))
  [(subst (getright eta) e1')]) by
(rewrite <- fill_associativity;
remember (under 2 (getleft eta)) as S;
remember (under 2 (getright eta)) as S';
simpl; subst;
f_equal; f_equal;
erewrite fill_in_term; eauto;
eapply subst_oft; eauto;
pose (G' := cl_tm t :: cl_tp :: nil);
replace (cl_tm t :: cl_tp :: G) with (G' ++ G) by eauto;
replace 2 with (length G') by eauto;
eapply subof_under_right; eauto;
erewrite fill_in_term; eauto).


eapply He1. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eapply subst_oft. eapply vof_dof. eapply subof_right. eassumption. eassumption.
simp_sub. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'.
replace (cl_tm (subst (under 1 (getleft eta)) t) :: cl_tp :: nil)
with (subst_ctx (getleft eta) (cl_tm t :: cl_tp :: nil) ++ nil) by (simp_sub; eauto).
replace 2 with (length (cl_tm t :: cl_tp :: nil)) by (simpl; eauto).
eapply subof_under_dof.
repeat econstructor.
eapply vof_dof. eapply subof_left. eassumption. eassumption.
unfold under; Subst.simp_sub; try exact termSubst. rewrite subst_compose. eauto.
eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_left. eassumption. eassumption.
eassumption.
simp_sub. eapply compose_cont. econstructor. econstructor.
eapply subst_oft'.
replace (cl_tm (subst (under 1 (getright eta)) t) :: cl_tp :: nil)
with (subst_ctx (getright eta) (cl_tm t :: cl_tp :: nil) ++ nil) by (simp_sub; eauto).
replace 2 with (length (cl_tm t :: cl_tp :: nil)) by (simpl; eauto).
eapply subof_under_dof.
repeat econstructor.
eapply vof_dof. eapply subof_right. eassumption. eassumption.
unfold under; Subst.simp_sub; try exact termSubst. rewrite subst_compose. auto.
eapply subst_ofc. eapply subof_dof_sof. eapply vof_dof. eapply subof_right. eassumption. eassumption.
eassumption.
intros v v'.
elim v; (try (simpl; contradiction; fail)). intros c _ v1 _ tau0 _.
elim v'; (try (simpl; contradiction; fail)). intros c' _ v1' _ tau0' _.
intros nilv1 nilv1' rel.
rewrite <- (fill_associativity).
rewrite <- (fill_associativity).
remember (under 2 (getleft eta)) as S.
remember (under 2 (getright eta)) as S'.
simpl. subst.
replace ((subst (under 2 (getleft eta)) e2)[tm_pack c v1 tau0]) with (subst (under 2 (getleft eta)) e2).
replace ((subst (under 2 (getright eta)) e2')[tm_pack c' v1' tau0']) with (subst (under 2 (getright eta)) e2').
elim rel; clear rel; intros R HV1.
elim HV1; clear HV1; intros relv HV1.
assert (oft nil v1 (subst (getleft (Sta c c' R :: eta)) t)) as typev1.
simpl. revert nilv1. simp_sub. intros nilv1. inversion nilv1; subst. revert H5. Subst.simp_sub; try exact termSubst.
assert (oft nil v1' (subst (getright (Sta c c' R :: eta)) t)) as typev1'.
simpl. revert nilv1'. simp_sub. intros nilv1'. inversion nilv1'; subst. revert H5. Subst.simp_sub; try exact termSubst.
assert (relatedEta (cl_tp :: G) (Sta c c' R :: eta)) as releta'.
econstructor.
inversion nilv1; eauto.
inversion nilv1'; eauto.
eassumption.
eassumption.
eapply kleeneHeadLeft.
eapply stepECompose. econstructor. eassumption.
eapply tstep_unpack2. eapply (V_is_val releta' typev1 typev1' HV1).
eapply kleeneHeadRight.
eapply stepECompose. econstructor. eassumption.
eapply tstep_unpack2. eapply (V_is_val releta' typev1 typev1' HV1).
simpl. Subst.simp_sub; try exact termSubst. repeat (rewrite subst_var; rewrite project_zero).
replace (subst (dot v1 (dot c (getleft eta))) e2) with
  (subst (getleft (Dyn v1 v1' :: Sta c c' R :: eta)) e2) by eauto.
replace (subst (dot v1' (dot c' (getright eta))) e2') with
  (subst (getright (Dyn v1 v1' :: Sta c c' R :: eta)) e2') by eauto.
eapply He2.
econstructor.
eassumption.
eassumption.
eapply (V_is_val releta' typev1 typev1' HV1).
eapply (V_is_val releta' typev1 typev1' HV1).
eassumption.
eassumption.
eapply (subst_oft _ (cl_tm t :: cl_tp :: G)).
replace ((getleft (Dyn v1 v1' :: Sta c c' R :: eta))) with (dot v1 (getleft (Sta c c' R :: eta))) by eauto.
econstructor.
eapply vof_dof. eapply subof_left. eassumption. simp_sub. econstructor. revert typev1. eauto.
eassumption.
eapply (subst_oft _ (cl_tm t :: cl_tp :: G)).
replace ((getright (Dyn v1 v1' :: Sta c c' R :: eta))) with (dot v1' (getright (Sta c c' R :: eta))) by eauto.
econstructor.
eapply vof_dof. eapply subof_right. eassumption. simp_sub. econstructor. revert typev1. eauto.
eassumption.
simpl. Subst.simp_sub; try exact termSubst.
simpl. Subst.simp_sub; try exact termSubst.
replace ((Dyn v1 v1' :: Sta c c' R :: eta)) with ((Dyn v1 v1' :: Sta c c' R :: nil) ++ eta) by eauto.
replace 2 with (length (Dyn v1 v1' :: Sta c c' R :: nil)) by eauto.
rewrite substetaK. eassumption.
erewrite fill_in_term; eauto.
eapply subst_oft; eauto.
pose (G' := cl_tm t :: cl_tp :: nil).
replace (cl_tm t :: cl_tp :: G) with (G' ++ G) by eauto.
replace 2 with (length G') by eauto.
eapply subof_under_right; eauto.
erewrite fill_in_term; eauto.
eapply subst_oft; eauto.
pose (G' := cl_tm t :: cl_tp :: nil).
replace (cl_tm t :: cl_tp :: G) with (G' ++ G) by eauto.
replace 2 with (length G') by eauto.
eapply subof_under_left; eauto.
Qed.

Theorem FTLR {G e tau} : oft G e tau -> logEq G e e tau.
Proof.
intros Getau.
pose (P:= (fun G e tau =>
logEq G e e tau
)).
pose (P0 := (fun (E tau1 tau2 : term) =>
  forall v v', oft nil v tau1 -> oft nil v' tau1
    -> V nil tau1 v v' -> logEq nil (E[v]) (E[v']) tau2)).
eapply (oft_ind' P P0) ;subst P; subst P0; simpl; intros; subst; eauto.
- eapply variableCompatibility; eassumption.
- eapply unitCompatibility; eassumption.
- eapply funCompatibility; eauto.
  (* eapply H2. eapply subst_ofc; eauto. econstructor; eauto; repeat econstructor.*)
- eapply applicationCompatibility; eauto.
  (* eapply H0; eauto. econstructor; eauto. *)
- eapply fun_closedCompatibility; eauto.
- eapply application_closedCompatibility; eauto.
- eapply productCompatibility; eassumption.
- eapply projectionLeftCompatibility; eassumption.
- eapply projectionRightCompatibility; eassumption.
- eapply plamCompatibility; eassumption.
- eapply pappCompatibility; eassumption.
- eapply packCompatibility; eassumption.
- eapply unpackCompatibility; eassumption.
- eapply letCompatibility; eassumption.
- eapply abortCompatibility; eassumption.
- eapply letccCompatibility; eassumption.
- eapply throwCompatibility; eassumption.
- eapply contCompatibility; try eassumption.
  intros v v' typev typev' HV.
  assert(logEq nil (k[v]) (k[v']) cn_unit) as Hlog.
  eapply H1.
  simpl in typev. rewrite subst_id in typev. eassumption.
  simpl in typev'. rewrite subst_id in typev'. eassumption.
  eassumption.
  elimLogEq Hlog kv kv'.
  assert(Exp V nil cn_unit (subst (getleft nil) k[v])
         (subst (getright nil) k[v'])) as Hlog'.
  eapply Hlog. econstructor. simpl. repeat rewrite subst_id. eassumption. simpl. repeat rewrite subst_id. eassumption.
  simpl in Hlog'. repeat rewrite subst_id in Hlog'.
  assert (kleene (k_hole[k[v]]) (k_hole[k[v']])).
  eapply Hlog'. simp_sub. econstructor. simp_sub. econstructor.
  intros v1 v1' typev1 typev1'. simpl.
  destruct v1; simpl; try contradiction.
  destruct v1'; simpl; try contradiction. intros _. split; eauto.
  simpl in H2. eassumption.
- split. eassumption. split. eassumption. intros eta releta _ _. inversion releta; subst.
  simpl. repeat rewrite subst_id.
  intros E E' HE HE' HK.
  eapply HK.
  simpl. repeat rewrite subst_id. eassumption.
  simpl. repeat rewrite subst_id. eassumption.
  eassumption.
- eapply productCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply productCompatibility.
  repeat erewrite fill_in_term; eassumption.
  eapply H3. eassumption. eassumption. eassumption.
- eapply projectionLeftCompatibility.
  eapply H0. eassumption. eassumption. eassumption.
- eapply projectionRightCompatibility. eapply H0. eassumption. eassumption. eassumption.
- eapply applicationCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply applicationCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3. eassumption. eassumption. eassumption.
- eapply application_closedCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply application_closedCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3. eassumption. eassumption. eassumption.
- repeat (rewrite (fill_in_type H1)). eapply pappCompatibility. eapply H0; eassumption. eassumption.
- eapply letCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption.
- repeat (rewrite (fill_in_type H)). eapply abortCompatibility. eassumption. eapply H1; eassumption.
- repeat (rewrite (fill_in_type H2)).
  repeat (rewrite (fill_in_type H)). eapply packCompatibility. eassumption. eapply H1; eassumption. eassumption.
- eapply unpackCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption. eassumption.
- eapply throwCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption.
- eapply throwCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3; eassumption.
Qed.

Theorem FTLR_K {E tau1 tau2} : ofk E tau1 tau2 -> (forall v v', oft nil v tau1 -> oft nil v' tau1
    -> V nil tau1 v v' -> logEq nil (E[v]) (E[v']) tau2).
Proof.
intros Getau.
pose (P:= (fun G e tau =>
logEq G e e tau
)).
pose (P0 := (fun (E tau1 tau2 : term) =>
  forall v v', oft nil v tau1 -> oft nil v' tau1
    -> V nil tau1 v v' -> logEq nil (E[v]) (E[v']) tau2)).
eapply (ofk_ind' P P0) ;subst P; subst P0; simpl; intros; subst; eauto.
- eapply variableCompatibility; eassumption.
- eapply unitCompatibility; eassumption.
- eapply funCompatibility; eauto.
  (* eapply H2. eapply subst_ofc; eauto. econstructor; eauto; repeat econstructor.*)
- eapply applicationCompatibility; eauto.
  (* eapply H0; eauto. econstructor; eauto. *)
- eapply fun_closedCompatibility; eauto.
- eapply application_closedCompatibility; eauto.
- eapply productCompatibility; eassumption.
- eapply projectionLeftCompatibility; eassumption.
- eapply projectionRightCompatibility; eassumption.
- eapply plamCompatibility; eassumption.
- eapply pappCompatibility; eassumption.
- eapply packCompatibility; eassumption.
- eapply unpackCompatibility; eassumption.
- eapply letCompatibility; eassumption.
- eapply abortCompatibility; eassumption.
- eapply letccCompatibility; eassumption.
- eapply throwCompatibility; eassumption.
- eapply contCompatibility; try eassumption.
  intros v v' typev typev' HV.
  assert(logEq nil (k[v]) (k[v']) cn_unit) as Hlog.
  eapply H1.
  simpl in typev. rewrite subst_id in typev. eassumption.
  simpl in typev'. rewrite subst_id in typev'. eassumption.
  eassumption.
  elimLogEq Hlog kv kv'.
  assert(Exp V nil cn_unit (subst (getleft nil) k[v])
         (subst (getright nil) k[v'])) as Hlog'.
  eapply Hlog. econstructor. simpl. repeat rewrite subst_id. eassumption. simpl. repeat rewrite subst_id. eassumption.
  simpl in Hlog'. repeat rewrite subst_id in Hlog'.
  assert (kleene (k_hole[k[v]]) (k_hole[k[v']])).
  eapply Hlog'. simp_sub. econstructor. simp_sub. econstructor.
  intros v1 v1' typev1 typev1'. simpl. 
  destruct v1; simpl; try contradiction.
  destruct v1'; simpl; try contradiction. intros _. split; eauto.
  simpl in H2. eassumption.
- split. eassumption. split. eassumption. intros eta releta _ _. inversion releta; subst.
  simpl. repeat rewrite subst_id.
  intros E1 E1' HE HE' HK.
  eapply HK.
  simpl. repeat rewrite subst_id. eassumption.
  simpl. repeat rewrite subst_id. eassumption.
  eassumption.
- eapply productCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply productCompatibility.
  repeat erewrite fill_in_term; eassumption.
  eapply H3. eassumption. eassumption. eassumption.
- eapply projectionLeftCompatibility.
  eapply H0. eassumption. eassumption. eassumption.
- eapply projectionRightCompatibility. eapply H0. eassumption. eassumption. eassumption.
- eapply applicationCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply applicationCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3. eassumption. eassumption. eassumption.
- eapply application_closedCompatibility. eapply H0. eassumption. eassumption. eassumption.
  repeat erewrite fill_in_term; eassumption.
- eapply application_closedCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3. eassumption. eassumption. eassumption.
- repeat (rewrite (fill_in_type H1)). eapply pappCompatibility. eapply H0; eassumption. eassumption.
- eapply letCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption.
- repeat (rewrite (fill_in_type H)). eapply abortCompatibility. eassumption. eapply H1; eassumption.
- repeat (rewrite (fill_in_type H2)).
  repeat (rewrite (fill_in_type H)). eapply packCompatibility. eassumption. eapply H1; eassumption. eassumption.
- eapply unpackCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption. eassumption.
- eapply throwCompatibility. eapply H0; eassumption. repeat erewrite fill_in_term; eassumption.
- eapply throwCompatibility. repeat erewrite fill_in_term; eassumption. eapply H3; eassumption.
Qed.

Theorem FTLR_V {v tau} :
oft nil v tau ->
is_val v ->
V nil tau v v.
Proof.
intros Htau Hval.
remember nil as G.
revert HeqG.
induction Htau; intro HeqG; subst; eauto; try (inversion Hval; fail).
- simpl; eauto.
- assert (V nil (cn_arrow t1 t2)
         (tm_fun (subst (getleft nil) t1) (subst (getleft nil) t2) (subst (under 2 (getleft nil)) e))
         (tm_fun (subst (getright nil) t1) (subst (getright nil) t2) (subst (under 2 (getright nil)) e)))
  as Hfun
  by exact(funCompatibility_V H H0 (FTLR Htau) relatedEta_nil).
  replace (tm_fun (subst (getleft nil) t1) (subst (getleft nil) t2) (subst (under 2 (getleft nil)) e))
  with (tm_fun t1 t2 e) in Hfun.
  replace (tm_fun (subst (getright nil) t1) (subst (getright nil) t2) (subst (under 2 (getright nil)) e))
  with (tm_fun t1 t2 e) in Hfun.
  eauto.
  f_equal; replace (getright nil) with (sh 0 : @sub term) by eauto; try rewrite subst_id; try rewrite subst_under_id; eauto.
  f_equal; replace (getleft nil) with (sh 0 : @sub term) by eauto; try rewrite subst_id; try rewrite subst_under_id; eauto.
- assert (V nil (cn_arrow_closed t1 t2)
         (tm_fun_closed (subst (getleft nil) t1) (subst (getleft nil) t2) (subst (under 2 (getleft nil)) e))
         (tm_fun_closed (subst (getright nil) t1) (subst (getright nil) t2) (subst (under 2 (getright nil)) e)))
  as Hfun
  by exact(fun_closedCompatibility_V H H0 H1 (FTLR Htau) relatedEta_nil).
  replace (tm_fun_closed (subst (getleft nil) t1) (subst (getleft nil) t2) (subst (under 2 (getleft nil)) e))
  with (tm_fun_closed t1 t2 e) in Hfun.
  replace (tm_fun_closed (subst (getright nil) t1) (subst (getright nil) t2) (subst (under 2 (getright nil)) e))
  with (tm_fun_closed t1 t2 e) in Hfun.
  eauto.
  f_equal; replace (getright nil) with (sh 0 : @sub term) by eauto; try rewrite subst_id; try rewrite subst_under_id; eauto.
  f_equal; replace (getleft nil) with (sh 0 : @sub term) by eauto; try rewrite subst_id; try rewrite subst_under_id; eauto.
- inversion Hval; eapply productCompatibility_V; eauto.
- assert(V nil (cn_all t) (tm_plam (subst (under 1 (getleft nil)) e))
         (tm_plam (subst (under 1 (getright nil)) e))) as H by exact (plamCompatibility_V (FTLR Htau) relatedEta_nil).
  replace (getleft nil) with (sh 0 : @sub term) in H by eauto.
  replace (getright nil) with (sh 0 : @sub term) in H by eauto.
  rewrite subst_under_id in H. eauto.
- assert(V nil (cn_exists t) (tm_pack (subst (getleft nil) c) e (subst (under 1 (getleft nil)) t))
         (tm_pack (subst (getright nil) c) e (subst (under 1 (getright nil)) t))) as H1.
  apply (packCompatibility_V H (FTLR Htau) H0 relatedEta_nil).
  simpl; rewrite subst_id; eauto.
  simpl; rewrite subst_id; eauto.
  eapply IHHtau; eauto.
  inversion Hval; eauto.
  replace (getleft nil) with (sh 0 : @sub term) in H1 by eauto.
  replace (getright nil) with (sh 0 : @sub term) in H1 by eauto.
  rewrite subst_under_id in H1.
  rewrite subst_id in H1.
  eauto.
- assert(K V nil tau k k) as HK.
  clear Hval.
  intros v v'.
  simpl; rewrite subst_id.
  intros Hv Hv' HV.
  elim (FTLR_K H0 v v' Hv Hv' HV).
  intros _ H1; elim H1; clear H1; intros _ H1.
  assert(Exp V nil cn_unit (subst (getleft nil) k[v]) (subst (getright nil) k[v'])).
  apply H1; eauto.
  econstructor.
  simpl; repeat rewrite subst_id; eapply fill_type; eauto.
  simpl; repeat rewrite subst_id; eapply fill_type; eauto.
  simpl in H2; repeat rewrite subst_id in H2.
  assert (kleene k_hole[k[v]] k_hole[k[v']]).
  eapply H2; simp_sub; eauto; try exact termSubst.
  econstructor.
  econstructor.
  intros v1 v1' Hv1 Hv1' HV1.
  simpl.
  destruct v1; simpl in HV1; try elim HV1.
  destruct v1'; simpl in HV1; try elim HV1.
  econstructor; eauto.
  simpl in H2.
  eauto.
  assert(V nil (cn_cont (subst (sh (length nil)) tau)) (tm_cont (subst (getleft nil) k))
         (tm_cont (subst (getright nil) k))) as H1 by exact (contCompatibility_V H H0 H0 HK relatedEta_nil).
  replace (getleft nil) with (sh 0 : @sub term) in H1 by eauto.
  replace (getright nil) with (sh 0 : @sub term) in H1 by eauto.
  repeat rewrite subst_id in H1.
  rewrite subst_id.
  eauto.
Qed.


Lemma compatibilityLog : WeaklyCompatible logEq.
Proof.
split.
intros G e e' tau C G' tau' He He' HC Hlog.
induction HC; simpl.
- eassumption.
- repeat (rewrite (fill_in_type H)).
  repeat (rewrite (fill_in_type H0)).
  eapply funCompatibility. eassumption. eassumption. eapply IHHC; eassumption.
- eapply applicationCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR; eassumption.
- eapply applicationCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR; eassumption. eapply IHHC; eassumption.
- repeat (rewrite (fill_in_type H)).
  repeat (rewrite (fill_in_type H0)).
  eapply fun_closedCompatibility. eassumption. eassumption. eassumption. eapply IHHC; eassumption.
- eapply application_closedCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR; eassumption.
- eapply application_closedCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR; eassumption. eapply IHHC; eassumption.
- eapply plamCompatibility. eapply IHHC; eassumption.
- repeat (rewrite (fill_in_type H)). eapply pappCompatibility. eapply IHHC; eassumption. eassumption.
- repeat (rewrite (fill_in_type H)).
  repeat (rewrite (fill_in_type H0)).
  eapply packCompatibility. eassumption. eapply IHHC; eassumption. eassumption.
- eapply unpackCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption. eassumption.
- eapply unpackCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption. eapply IHHC; eassumption. eassumption.
- eapply productCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption.
- eapply productCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption. eapply IHHC; eassumption.
- eapply projectionLeftCompatibility. eapply IHHC; eassumption.
- eapply projectionRightCompatibility. eapply IHHC; eassumption.
- eapply letCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption.
- eapply letCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption. eapply IHHC; eassumption.
- repeat (rewrite (fill_in_type H)). eapply abortCompatibility. eassumption. eapply IHHC; eassumption.
- eapply throwCompatibility. eapply IHHC; eassumption. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption.
- eapply throwCompatibility. repeat erewrite fill_in_term; try eassumption. eapply FTLR. eassumption. eapply IHHC; eassumption.
Qed.