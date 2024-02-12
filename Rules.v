Require Import SyntaX.
Require Import Sequence.
Open Scope syntax.

(* Type formation, since we have polymorphic types *)

Inductive ofc : context -> (* cn *) term -> Prop :=
| ofc_var {G i}
    : index i G cl_tp
      -> ofc G (var i)

| ofc_zero {G}
    : ofc G cn_zero

| ofc_unit {G}
    : ofc G cn_unit

| ofc_arrow {G t1 t2}
    : ofc G t1
      -> ofc G t2
      -> ofc G (cn_arrow t1 t2)

| ofc_prod {G t1 t2}
    : ofc G t1
      -> ofc G t2
      -> ofc G (cn_prod t1 t2)

| ofc_all {G t}
    : ofc (cl_tp:: G) t
      -> ofc G (cn_all t)

| ofc_exists {G t}
    : ofc (cl_tp :: G) t
      -> ofc G (cn_exists t)

| ofc_cont {G t}
    : ofc G t
      -> ofc G (cn_cont t)
.


Inductive is_val : term -> Prop :=
| Val_Fun {a b : term} (s1 : term) :
    is_val (tm_fun a b s1)
| Val_LamT (s1 : term) :
    is_val (tm_plam s1)
| Val_pair (s1 s2 : term) :
    is_val s1 -> is_val s2 -> is_val (tm_pair s1 s2)
| Val_Unit :
    is_val tm_star
| Val_pack {c e t} :
    is_val e -> is_val (tm_pack c e t)
| Val_cont {E} :
    is_val (tm_cont E)
.


Inductive oft : context -> (* tm *) term -> (* cn *) term -> Prop :=
| oft_var {G i t}
    : index i G (cl_tm t)
      -> oft G (var i) (subst (sh (S i)) t)

| oft_star {G}
    : oft G tm_star cn_unit

| oft_fun {G t1 t2 e}
    : ofc G t1
      -> ofc G t2
      -> oft (cl_tm (cn_arrow (subst (sh 1) t1) (subst (sh 1) t2)) :: cl_tm t1 :: G) e (subst (sh 2) t2)
      -> oft G (tm_fun t1 t2 e) (cn_arrow t1 t2)

| oft_app {G t1 t2 e1 e2}
    : oft G e1 (cn_arrow t1 t2)
      -> oft G e2 t1
      -> oft G (tm_app e1 e2) t2

| oft_pair {G t1 t2 e1 e2}
    : oft G e1 t1
      -> oft G e2 t2
      -> oft G (tm_pair e1 e2) (cn_prod t1 t2)

| oft_pi1 {G t1 t2 e}
    : oft G e (cn_prod t1 t2)
      -> oft G (tm_pi1 e) t1

| oft_pi2 {G t1 t2 e}
    : oft G e (cn_prod t1 t2)
      -> oft G (tm_pi2 e) t2

| oft_plam {G t e}
    : oft (cl_tp :: G) e t
      -> oft G (tm_plam e) (cn_all t)

| oft_papp {G t e c}
    : oft G e (cn_all t)
      -> ofc G c
      -> oft G (tm_papp e c) (subst (dot c (sh 0)) t)

| oft_pack {G t c e}
    : ofc G c
      -> oft G e (subst (dot c (sh 0)) t)
      -> ofc (cl_tp :: G) t
      -> oft G (tm_pack c e t) (cn_exists t)

| oft_unpack {G t t' e1 e2}
    : oft G e1 (cn_exists t)
      -> oft (cl_tm t :: cl_tp :: G) e2 (subst (sh 2) t')
      -> ofc G t'
      -> oft G (tm_unpack e1 e2) t'

| oft_lett {G t1 t2 e1 e2}
    : oft G e1 t1
      -> oft (cl_tm t1 :: G) e2 (subst (sh 1) t2)
      -> oft G (tm_lett e1 e2) t2

| oft_abort {G tau e}
    : ofc G tau
      -> oft G e cn_zero
      -> oft G (tm_abort tau e) tau

| oft_letcc {G tau e}
    : ofc G tau
      -> oft (cl_tm (cn_cont tau) :: G) e (subst (sh 1) tau)
      -> oft G (tm_letcc tau e) tau

| oft_throw {G e1 e2 tau}
    : oft G e1 tau
      -> oft G e2 (cn_cont tau)
      -> oft G (tm_throw e1 e2) cn_zero

| oft_cont {G k tau tau'}
    : ofc nil tau
      -> ofk k tau cn_unit
      -> tau' = (subst (sh (length G)) tau)
      -> oft G (tm_cont k) (cn_cont tau')
with ofk : (* k *) term -> (* cn *) term -> (* cn *) term -> Prop :=
| ofk_hole {A}
    : ofk k_hole A A

| ofk_pair_1 {E e tau tau1 tau2}
    : ofk E tau tau1
      -> oft nil e tau2
      -> ofk (tm_pair E e) tau (cn_prod tau1 tau2)

| ofk_pair_2 {E e tau tau1 tau2}
    : oft nil e tau1
      -> is_val e
      -> ofk E tau tau2
      -> ofk (tm_pair e E) tau (cn_prod tau1 tau2)

| ofk_pi1 {E tau tau1 tau2}
    : ofk E tau (cn_prod tau1 tau2)
      -> ofk (tm_pi1 E) tau tau1

| ofk_pi2 {E tau tau1 tau2}
    : ofk E tau (cn_prod tau1 tau2)
      -> ofk (tm_pi2 E) tau tau2

| ofk_app_1 {E e tau tau1 tau2}
    : ofk E tau (cn_arrow tau1 tau2)
      -> oft nil e tau1
      -> ofk (tm_app E e) tau tau2

| ofk_app_2 {E e tau tau1 tau2}
    : oft nil e (cn_arrow tau1 tau2)
      -> is_val e
      -> ofk E tau tau1
      -> ofk (tm_app e E) tau tau2

| ofk_papp {E tau tau1 c}
    : ofk E tau (cn_all tau1)
      -> ofc nil c
      -> ofk (tm_papp E c) tau (subst (dot c (sh 0)) tau1)

| ofk_lett {E e tau tau1 tau2}
    : ofk E tau tau1
      -> oft (cl_tm tau1 :: nil) e (subst (sh 1) tau2)
      -> ofk (tm_lett E e) tau tau2

| ofk_abort {E tau tau'}
    : ofc nil tau'
     ->ofk E tau cn_zero
     -> ofk (tm_abort tau' E) tau tau'

| ofk_pack {E tau tau' t1}
    : ofc nil t1
     -> ofk E tau' (subst (dot t1 (sh 0)) tau)
     -> ofc (cl_tp :: nil) tau
     -> ofk (tm_pack t1 E tau) tau' (cn_exists tau)

| ofk_unpack {t t' E e2 tau'}
    : ofk E tau' (cn_exists t)
      -> oft (cl_tm t :: cl_tp :: nil) e2 (subst (sh 2) t')
      -> ofc nil t'
      -> ofk (tm_unpack E e2) tau' t'

| ofk_throw_1 {E tau' tau e2}
    : ofk E tau' tau
      -> oft nil e2 (cn_cont tau)
      -> ofk (tm_throw E e2) tau' cn_zero

| ofk_throw_2 {E tau' tau e1}
    : oft nil e1 tau
      -> is_val e1
      -> ofk E tau' (cn_cont tau)
      -> ofk (tm_throw e1 E) tau' cn_zero
.

Notation "G |- e : tau" := (oft G e tau)
  (at level 2, left associativity,
   format "G  |-  e  :  tau" ) : syntax.

Notation "K ÷ tau" := (ofk K tau cn_unit)
  (at level 2, left associativity,
   format "K  ÷  tau" ) : syntax.

Notation "K : ( tau => tau2 )" := (ofk K tau tau2)
  (at level 2, left associativity,
   format "K  :  ( tau  =>  tau2 )" ) : syntax.


Inductive tstep : (* k *) term -> (* tm *) term -> (* tm *) term -> Prop :=
| tstep_app1 {E e1 e' e2}
    : tstep (E o (tm_app k_hole e2)) e1 e'
      -> tstep E (tm_app e1 e2) e'

| tstep_app2 {E v1 e2 e'}
    : is_val v1
      -> tstep (E o (tm_app v1 k_hole)) e2 e'
      -> tstep E (tm_app v1 e2) e'

| tstep_app3 {E A B e1 v2}
    : is_val v2
      -> tstep E (tm_app (tm_fun A B e1) v2) (E[e1.[tm_fun A B e1,v2]])

| tstep_pair1 {E e1 e2 e'}
    : tstep (E o (tm_pair k_hole e2)) e1 e'
      -> tstep E (tm_pair e1 e2) e'

| tstep_pair2 {E v1 e2 e'}
    : is_val v1
      -> tstep (E o (tm_pair v1 k_hole)) e2 e'
      -> tstep E (tm_pair v1 e2) e'

| tstep_pi11 {E e e'}
    : tstep (E o (tm_pi1 k_hole)) e e'
      -> tstep E (tm_pi1 e) e'

| tstep_pi12 {E v1 v2}
    : is_val v1
      -> is_val v2
      -> tstep E (tm_pi1 (tm_pair v1 v2)) (E[v1])

| tstep_pi21 {E e e'}
    : tstep (E o (tm_pi2 k_hole)) e e'
      -> tstep E (tm_pi2 e) e'

| tstep_pi22 {E v1 v2}
    : is_val v1
      -> is_val v2
      -> tstep E (tm_pi2 (tm_pair v1 v2)) (E[v2])

| tstep_papp1 {E e e' c}
    : tstep (E o (tm_papp k_hole c)) e e'
      -> tstep E (tm_papp e c) e'

| tstep_papp2 {E e c}
    : tstep E (tm_papp (tm_plam e) c) (E[e.[c]])

| tstep_pack {E c e e' t}
    : tstep (E o (tm_pack c k_hole t)) e e'
      -> tstep E (tm_pack c e t) e'

| tstep_unpack1 {E e1 e2 e'}
    : tstep (E o (tm_unpack k_hole e2)) e1 e'
      -> tstep E (tm_unpack e1 e2) e'

| tstep_unpack2 {E c v t e}
    : is_val v
      -> tstep E (tm_unpack (tm_pack c v t) e) (E[e.[v,c]])

| tstep_lett1 {E e1 e2 e'}
    : tstep (E o (tm_lett k_hole e2)) e1 e'
      -> tstep E (tm_lett e1 e2) e'

| tstep_lett2 {E v1 e2}
    : is_val v1
      -> tstep E (tm_lett v1 e2) (E[e2.[v1]])

| tstep_abort {E e e' c}
    : tstep (E o (tm_abort c k_hole)) e e'
      -> tstep E (tm_abort c e) e'

| tstep_throw_1 {E e1 e2 e'}
    : tstep (E o (tm_throw k_hole e2)) e1 e'
      -> tstep E (tm_throw e1 e2) e'

| tstep_throw_2 {E e1 e2 e'}
    : is_val e1
      -> tstep (E o (tm_throw e1 k_hole)) e2 e'
      -> tstep E (tm_throw e1 e2) e'

| tstep_throw {E v E'}
    : is_val v
      -> tstep E (tm_throw v (tm_cont E')) (E'[v])

| tstep_letcc {E tau e}
    : tstep E (tm_letcc tau e) (E[e.[tm_cont E]])
.


Scheme oft_ind' := Minimality for oft Sort Prop
  with ofk_ind' := Minimality for ofk Sort Prop.


(* ------------------------------ Useful Lemmas ------------------------------------- *)

Lemma oft_var' {G i t s}: 
 index i G (cl_tm t)
 -> s = (subst (sh (S i)) t)
 -> oft G (var i) s.
Proof.
intros; subst. econstructor. eassumption.
Qed.

Lemma fill_in_type {G tau e'} :
  ofc G tau -> fill tau e' = tau.
Proof.
induction 1; simpl; f_equal; try eassumption; reflexivity.
Qed.

Lemma fill_in_term {G e tau e'} :
  oft G e tau -> fill e e' = e.
Proof.
induction 1; simpl; f_equal; try eassumption; try reflexivity; eapply fill_in_type; eassumption.
Qed.

Lemma compose_cont {E E' tau1 tau2 tau3} :
  ofk E tau1 tau2 -> ofk E' tau2 tau3 -> ofk (E' o E) tau1 tau3.
Proof.
intros H1 H2. revert H1. revert E tau1.
induction H2; intros Es tau1s HEs; simpl; try rewrite (fill_in_term H); try rewrite (fill_in_type H); try (econstructor; auto; fail).
- eassumption.
- eapply ofk_app_2; auto. eassumption.
- rewrite (fill_in_type H0); eapply ofk_pack; auto.
- eapply ofk_throw_2; auto. eassumption.
Qed.

Lemma fill_type {E tau tau' e} :
  ofk E tau tau' -> oft nil e tau -> oft nil (E[e]) tau'.
Proof.
induction 1; simpl; auto; intro H';
repeat rewrite (fill_in_term H0); repeat rewrite (fill_in_type H0); repeat rewrite (fill_in_term H');
try (econstructor; auto; apply IHofk).
- rewrite (fill_in_term H). econstructor; auto.
- rewrite (fill_in_term H). econstructor; auto. eassumption.
- rewrite (fill_in_type H). econstructor; auto.
- rewrite (fill_in_type H). rewrite (fill_in_type H1). econstructor; auto.
- rewrite (fill_in_term H). econstructor; auto. eassumption.
Qed.

Lemma hasHole {E tau tau'} : ofk E tau tau' -> E o k_hole = E.
Proof.
induction 1; simpl; eauto; f_equal; auto; try (eapply fill_in_type; eassumption; fail); eapply fill_in_term; eassumption.
Qed.

Lemma fill_associativity {E E' E''} :
  E o (E' o E'') = E o E' o E''.
Proof.
revert E' E''.
induction E; simpl; intros; try reflexivity; f_equal; auto;
try (repeat(erewrite fill_in_type); eauto; fail); repeat(erewrite fill_in_term); eauto.
Qed.

Lemma stepECompose {E E' e e' tau tau'} : 
ofk E tau' cn_unit ->
ofk E' tau tau' ->
tstep (E o E') e e' -> tstep E (E'[e]) e'.
Proof.
intros H1 H2. revert H1.
revert E.
induction H2; simpl; intros K HE Hstep.
- rewrite (hasHole HE) in Hstep. eassumption.
- econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. erewrite fill_in_term; eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (e0[e][E]) with e0. eassumption. erewrite fill_in_term. erewrite fill_in_term. reflexivity.
  eassumption. erewrite fill_in_term; eassumption.
- erewrite fill_in_term. eapply tstep_pair2. eassumption. eapply IHofk. eapply compose_cont. eapply ofk_pair_2. eassumption. eassumption. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. replace (e0[E]) with e0. eassumption. erewrite fill_in_term. reflexivity. eassumption. eassumption.
- econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. eassumption.
- econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. eassumption.
- replace (e0[e]) with e0. econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (e0[E]) with e0. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
- replace (e0[e]) with e0. eapply tstep_app2. eassumption. eapply IHofk. eapply compose_cont. eapply ofk_app_2. eassumption. eassumption. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. replace (e0[E]) with e0. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
- replace (c[e]) with c. econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (c[E]) with c. eassumption.
  rewrite (fill_in_type H); reflexivity.
  rewrite (fill_in_type H); reflexivity.
- replace (e0[e]) with e0. econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (e0[E]) with e0. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
- replace (tau'[e]) with tau'. econstructor. eapply IHofk. eapply compose_cont. econstructor. eassumption. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. replace (tau'[E]) with tau'. eassumption.
  rewrite (fill_in_type H); reflexivity.
  rewrite (fill_in_type H); reflexivity.
- replace (tau[e]) with tau. replace (t1[e]) with t1. econstructor. eapply IHofk. eapply compose_cont. econstructor. eassumption. econstructor. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (tau[E]) with tau. replace (t1[E]) with t1. eassumption.
  rewrite (fill_in_type H); reflexivity.
  rewrite (fill_in_type H0); reflexivity.
  rewrite (fill_in_type H); reflexivity.
  rewrite (fill_in_type H0); reflexivity.
- replace (e2[e]) with e2. econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (e2[E]) with e2. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
- replace (e2[e]) with e2. econstructor. eapply IHofk. eapply compose_cont. econstructor. econstructor. eassumption. eassumption.
  erewrite <- fill_associativity. simpl. replace (e2[E]) with e2. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
- replace (e1[e]) with e1. eapply tstep_throw_2. eassumption. eapply IHofk. eapply compose_cont. eapply ofk_throw_2. eassumption. eassumption. econstructor. eassumption.
  erewrite <- fill_associativity. simpl. replace (e1[E]) with e1. eassumption.
  rewrite (fill_in_term H); reflexivity.
  rewrite (fill_in_term H); reflexivity.
Qed.


Lemma val_isn't_step {E v e} : tstep E v e -> is_val v -> False.
Proof.
intros Hstep Hval; revert Hstep; revert E e.
induction Hval; intros.
- inversion Hstep.
- inversion Hstep.
- inversion Hstep; subst. eapply IHHval1. eassumption. eapply IHHval2. eassumption.
- inversion Hstep.
- inversion Hstep; subst. eapply IHHval. eassumption.
- inversion Hstep.
Qed. 


Lemma deterministic {E e e' e''} : tstep E e e' -> tstep E e e'' -> e' = e''.
Proof.
intros Hstep1. revert e''. induction Hstep1; intros e'' Hstep2; inversion Hstep2; subst; auto.
- eelim val_isn't_step. exact Hstep1. eassumption.
- eelim val_isn't_step; try apply Hstep1. econstructor.
- eelim val_isn't_step. exact H4. eassumption.
- eelim val_isn't_step. eapply Hstep1. eassumption.
- eelim val_isn't_step. eapply H4. econstructor.
- eelim val_isn't_step. eapply H5. eassumption.
- eelim val_isn't_step. exact Hstep1. eassumption.
- eelim val_isn't_step. exact H4. eassumption.
- eelim val_isn't_step. exact Hstep1. econstructor; eauto.
- eelim val_isn't_step. exact H3. econstructor; eauto.
- eelim val_isn't_step. exact Hstep1. econstructor; eauto.
- eelim val_isn't_step. exact H3. econstructor; eauto.
- eelim val_isn't_step. exact Hstep1. econstructor.
- eelim val_isn't_step. exact H3. econstructor.
- eelim val_isn't_step. exact Hstep1. econstructor; eauto.
- eelim val_isn't_step. exact H4. econstructor; eauto.
- eelim val_isn't_step. exact Hstep1. eassumption.
- eelim val_isn't_step. exact H4. eassumption.
- eelim val_isn't_step. exact Hstep1. eassumption.
- eelim val_isn't_step. exact Hstep1. eassumption.
- eelim val_isn't_step. exact H4. eassumption.
- eelim val_isn't_step. exact Hstep1. econstructor.
- eelim val_isn't_step. exact H4. eassumption.
- eelim val_isn't_step. exact H5. econstructor.
Qed.