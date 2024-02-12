Require Import Rules.
Require Import SyntaX.
Require Import Substitution.
Require Import List.

Theorem preservation {E e e' tau} :
     oft nil e tau
     -> ofk E tau cn_unit
     -> tstep E e e'
     -> oft nil e' cn_unit.
Proof.
intros He HE step.
revert He HE.
generalize tau.
induction step; intros tau' He HE.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. eapply ofk_app_2. eassumption.
  eassumption. econstructor. eassumption.
- inversion He; subst. inversion H3; subst. eapply fill_type. eassumption.
  eapply (subst_oft' _ (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) tau')) :: cl_tm t1 ::  nil)); simp_sub. repeat econstructor. rewrite subst_id. eassumption.
  assert(dof nil v2 (cl_tm t1)).
  eapply dof_tm. eassumption.
  simp_sub.
  simp_sub.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. eapply ofk_pair_2. eassumption.
  eassumption. econstructor. eassumption.
- inversion He; subst. eapply IHstep. eapply H1. eapply compose_cont. econstructor. econstructor.
  eassumption.
- eapply fill_type. eassumption. inversion He; subst. inversion H3; subst. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption.
- eapply fill_type. eassumption. inversion He; subst. inversion H3; subst. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption. eassumption.
- inversion He; subst. inversion H2; subst. eapply fill_type. eassumption.
  eapply (subst_oft' _ (cl_tp :: nil)). repeat econstructor. eassumption. eassumption. reflexivity.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. eassumption.
  econstructor. eassumption. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption. eassumption. eassumption.
- inversion He; subst. inversion H2; subst. eapply fill_type. eassumption.
  eapply (subst_oft' _ (cl_tm t0 :: cl_tp :: nil)). repeat econstructor. eassumption. eassumption. eassumption.
  simp_sub.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption. eassumption.
- inversion He; subst. eapply fill_type. eassumption.
  eapply (subst_oft' _ (cl_tm t1 :: nil)). repeat econstructor. rewrite subst_id. eassumption. eassumption.
  simp_sub.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. eassumption.
  econstructor. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. econstructor. econstructor.
  eassumption. eassumption.
- inversion He; subst. eapply IHstep. eassumption. eapply compose_cont. eapply ofk_throw_2. eassumption.
  eassumption. econstructor. eassumption.
- inversion He; subst. inversion H5; subst. eapply fill_type. eassumption. rewrite subst_id in H3. eassumption.
- inversion He; subst. eapply fill_type. eassumption.
  eapply (subst_oft' _ (cl_tm (cn_cont tau') :: nil)). econstructor. econstructor. econstructor.
  rewrite subst_cl_id. eapply dof_tm. econstructor. eassumption. eassumption.
  simpl. rewrite subst_id. reflexivity.
  eassumption.
  Subst.simp_sub; try exact termSubst.
Qed.

Theorem progress {e tau} :
      oft nil e tau
   -> ((forall E, ofk E tau cn_unit -> (exists e', tstep E e e')) \/ is_val e).
Proof.
remember nil as G.
intro Getau.
revert HeqG.
pose (P:= (fun (G : context) e tau =>
G = nil -> (forall E : term, E ÷ tau -> exists e' : term, tstep E e e') \/ is_val e
)).
pose (P0 := (fun (E tau1 tau2 : term) => True)).
eapply (oft_ind' P P0) ;subst P; subst P0; simpl; intros; subst; eauto.
- inversion H.
- right. econstructor.
- right. econstructor.
- left. intros E Ediv. elim H0; eauto; intros.
  elim (H3 (E o (tm_app k_hole e2))); intros. exists x. eapply tstep_app1. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim H2; eauto; intros.
  elim (H4 (E o (tm_app e1 k_hole))); intros. exists x. eapply tstep_app2. eassumption. eassumption.
  eapply compose_cont. eapply ofk_app_2. eassumption. eassumption. econstructor. eassumption.
  inversion H3; subst; inversion H.
  eexists. eapply tstep_app3. eassumption.
- elim H0; eauto; intros.
  left. intros E Ediv. elim (H3 (E o (tm_pair k_hole e2))); intros. exists x. eapply tstep_pair1. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim H2; eauto; intros.
  left. intros E Ediv. elim (H4 (E o (tm_pair e1 k_hole))); intros. exists x. eapply tstep_pair2. eassumption. eassumption.
  eapply compose_cont. eapply ofk_pair_2. eassumption. eassumption. econstructor. eassumption.
  right. econstructor; eassumption.
- left. intros E Ediv. elim H0; eauto; intros.
  elim (H1 (E o (tm_pi1 k_hole))); intros. exists x. eapply tstep_pi11. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption.
  inversion H1; subst; inversion H. exists (E[s1]). eapply tstep_pi12. eassumption. eassumption.
- left. intros E Ediv. elim H0; eauto; intros.
  elim (H1 (E o (tm_pi2 k_hole))); intros. exists x. eapply tstep_pi21. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption.
  inversion H1; subst; inversion H. exists (E[s2]). eapply tstep_pi22. eassumption. eassumption.
- right. econstructor.
- left. intros E Ediv. elim H0; eauto; intros.
  elim (H2 (E o (tm_papp k_hole c))); intros. exists x. eapply tstep_papp1. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  inversion H2; subst; inversion H. exists (E[s1.[c]]). eapply tstep_papp2.
- elim H1; eauto; intros.
  left. intros E Ediv. elim (H3 (E o (tm_pack c k_hole t))); intros. exists x. eapply tstep_pack. eassumption.
  eapply compose_cont. econstructor. eassumption. econstructor. eassumption. eassumption.
  right. econstructor. eassumption.
- left. intros E Ediv. elim H0; eauto; intros. elim (H4 (E o (tm_unpack k_hole e2))); intros.
  exists x. eapply (tstep_unpack1). eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption. eassumption.
  inversion H4; subst; inversion H. exists (E[e2.[e0,c]]). eapply tstep_unpack2. eassumption.
- left. intros E Ediv. elim H0; eauto; intros. elim (H3 (E o (tm_lett k_hole e2))); intros.
  exists x. eapply tstep_lett1. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  exists (E[e2.[e1]]). eapply tstep_lett2. eassumption.
- left. intros E Ediv. elim H1; eauto; intros. elim (H2 (E o (tm_abort tau0 k_hole))); intros.
  exists x. eapply tstep_abort. eassumption.
  eapply compose_cont. econstructor. eassumption. econstructor. eassumption.
  inversion H2; subst; inversion H0.
- left. intros E Ediv. exists (E[e0.[tm_cont E]]). econstructor.
- left. intros E Ediv. elim H0; eauto; intros. elim (H3 (E o (tm_throw k_hole e2))); intros.
  exists x. eapply tstep_throw_1. eassumption.
  eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  elim H2; eauto; intros. elim (H4 (E o (tm_throw e1 k_hole))); intros. exists x. eapply tstep_throw_2. eassumption. eassumption.
  eapply compose_cont. eapply ofk_throw_2. eassumption. eassumption. econstructor. eassumption.
  inversion H4; subst; inversion H1. exists (E0[e1]). eapply tstep_throw. eassumption.
- right. econstructor.
Qed.
