Require Import Subst.
From Stdlib Require Import Lia.
Require Import Sequence.

Class HasClassifier (term : Type) := classifier : Type.
Class SubstClassifier (term : Type)
{HV : HasVar term} {HT : HasTraverse term} {HS : SubstType term} {HC : HasClassifier term} :=
subst_cl : @sub term -> classifier -> classifier
.
Class ClassifierLemmas (term : Type)
{HV : HasVar term} {HT : HasTraverse term} {HS : SubstType term}
{HC : HasClassifier term} {SC : SubstClassifier term} := {

subst_cl_compose :
  forall t s1 s2,
    subst_cl (compose s2 s1) t = subst_cl s1 (subst_cl s2 t);

subst_cl_id :
  forall t,
    subst_cl (sh 0) t = t;

subst_cl_under_id :
  forall n t,
    subst_cl (under n (sh 0)) t = t
}.

Section TSubst.

Context `{term : Type} `{CL : ClassifierLemmas term}.


Definition behaved (R : list classifier -> term -> classifier -> Prop) : Prop :=
  forall G i c,
    index i G c
    -> R G (var i) (subst_cl (sh (S i)) c).

Inductive subof (R : list classifier -> term -> classifier -> Prop) : list classifier -> sub -> list classifier -> Prop :=
| subof_dot {G t s c G'}
    : subof R G s G'
      -> R G t (subst_cl s c)
      -> subof R G (dot t s) (c :: G')

| subof_sh {G n G'}
    : truncate n G G'
      -> subof R G (sh n) G'.

Hint Constructors subof : static.


Lemma subof_mono :
  forall (R : _ -> _ -> _ -> Prop) (R' : _ -> _ -> _ -> Prop),
    (forall G1 t c, R G1 t c -> R' G1 t c)
    -> forall G1 G2 s, subof R G1 s G2 -> subof R' G1 s G2.
Proof.
intros R R' HR G1 G2 s Hs.
induction Hs.
(* dot *)
apply subof_dot.
apply IHHs.
apply HR, H.

(* sh *)
apply subof_sh.
auto.
Qed.


Hint Resolve subof_mono : substlem.


(* weakening closed *)
Definition wclo (R : list classifier -> term -> classifier -> Prop) :=
  forall G t C C',
    R G t C
    -> R (C' :: G) (subst (sh 1) t) (subst_cl (sh 1) C).

(* weakening closure: need to strengthen the induction hypothesis for substitution *)
Definition wc (R : list classifier -> term -> classifier -> Prop) (G : list classifier) (t : term) (c : classifier) : Prop :=
  forall G' n, truncate n G' G -> R G' (subst (sh n) t) (subst_cl (sh n) c).


Lemma subof_wclo_weaken1 :
  forall R G1 G2 s C,
    wclo R
    -> subof R G1 s G2
    -> subof R (C :: G1) (compose s (sh 1)) G2.
Proof.
intros R G1 G2 s C Hclo Hs.
induction Hs.

(* dot *)
intros.
simp_sub; eauto.
apply subof_dot; eauto; [].
rewrite -> subst_cl_compose; [].
apply Hclo; assumption.

(* sh *)
intros.
simp_sub; eauto.
apply subof_sh; eauto.
replace (n + 1) with (S n) by lia.
econstructor. eassumption.
Qed.

Lemma subof_wclo_weaken :
  forall R G1 G2 G s,
    wclo R
    -> subof R G1 s G
    -> subof R (app G2 G1) (compose s (sh (length G2))) G.
Proof.
intros R G1 G2 G s Hclo Hsubof.
induction G2.

(* nil *)
simpl.
simp_sub; eauto.

(* cons *)
intros.
simpl length.
rewrite <- app_comm_cons.
replace (compose s (sh (S (length G2)))) with (compose (compose s (sh (length G2))) (sh 1)).
eapply subof_wclo_weaken1.
assumption.
assumption.
simp_sub.
f_equal.
f_equal.
lia.
Qed.


Lemma subof_wclo_bind :
  forall R,
    behaved R
    -> wclo R
    -> forall G G' s c,
         subof R G s G'
         -> subof R ((subst_cl s c) :: G) (dot (var 0) (compose s (sh 1))) (c :: G').
Proof.
intros R HR Hclo G G' s c Hs.
apply subof_dot.
  apply subof_wclo_weaken1; auto.
  rewrite subst_cl_compose.
  apply HR; eauto using subst_cl.
  econstructor.
Qed.


Lemma wc_mono :
  forall (R1 : _ -> _ -> _ -> Prop) (R2 : _ -> _ -> _ -> Prop),
    (forall G t c, R1 G t c -> R2 G t c)
    -> forall G t c,
         wc R1 G t c -> wc R2 G t c.
Proof.
intros R1 R2 HR.
intros G t c H.
unfold wc.
auto.
Qed.


Hint Resolve wc_mono : substlem.


Lemma wc_elim :
  forall R G t c,
    wc R G t c -> R G t c.
Proof.
intros R G t c H.
unfold wc in H.
assert (truncate 0 G G) as Htrunc.
econstructor.
pose proof (H _ _ Htrunc) as H'.
rewrite subst_id in H'.
rewrite subst_cl_id in H'.
assumption.
Qed.

Lemma wc_weaken :
  forall R G1 G2 n t c,
    truncate n G1 G2
    -> wc R G2 t c
    -> wc R G1 (subst (sh n) t) (subst_cl (sh n) c).
Proof.
intros R G1 G2 n t c Htr Ht.
intros G3 m Htr'.
rewrite <- subst_cl_compose.
simp_sub; eauto.
apply Ht.
replace (n+m) with (m+n) by lia.
eapply truncate_sum; eauto.
Qed.

Lemma wc_behaved :
  forall R,
    behaved R -> behaved (wc R).
Proof.
intros R HR.
unfold behaved.
intros G i c Hindex.
intros G' n Htrunc.
rewrite <- subst_cl_compose.
repeat simp_sub; eauto.
replace (S i + n) with (S (n+i)) by lia.
rewrite subst_var. rewrite project_sh.
apply HR.
eapply truncate_index_sum; eauto.
Qed.

Lemma wc_wclo :
  forall R, wclo (wc R).
Proof.
intros R G t C C' HR.
eapply wc_weaken; eauto.
econstructor. econstructor.
Qed.

Lemma subof_wc_bind :
  forall R,
    behaved R
    -> forall G G' s c,
         subof (wc R) G s G'
         -> subof (wc R) (subst_cl s c :: G) (dot (var 0) (compose s (sh 1))) (c :: G').
Proof.
intros R HR G G' s c Hs.
apply subof_wclo_bind; auto using wc_behaved, wc_wclo.
Qed.

Lemma subof_index :
  forall R,
    behaved R
    -> forall G1 G2 s i c,
         subof R G1 s G2
         -> index i G2 c
         -> R G1 (@project term var s i) (subst_cl (compose (sh (S i)) s) c).
Proof.
intros R HR G1 G2 s i c Hs Hindex.
generalize dependent i.
induction Hs; intros i Hindex.
(* dot *)
destruct i.
simp_sub.
inversion Hindex as [x l |]; subst x l c0.
apply H.

rewrite -> project_dot.
rewrite -> compose_sh_succ_dot.
apply IHHs.
inversion Hindex; subst.
assumption.

(* sh *)
simp_sub.
replace (S i+n) with (S (n+i)) by lia.
apply HR.
eapply truncate_index_sum; eauto.
Qed.


Lemma wc_intro :
  forall R,
    (forall G1 G2 s t c,
       subof (wc R) G1 s G2
       -> R G2 t c
       -> R G1 (subst s t) (subst_cl s c))
    -> forall G t c,
         R G t c -> wc R G t c.
Proof.
intros R HR G t c H.
intros G' n Htrunc.
eapply HR.
eapply subof_sh.
eassumption.
eassumption.
Qed.

Lemma subof_id :
  forall R G, subof R G (sh 0) G.
Proof.
intros R G.
apply subof_sh.
apply truncate_0.
Qed.

Hint Resolve subof_id : static.


Lemma subof_sh_all :
  forall R G1 G2 s,
    subof R G1 s G2
    -> compose (sh (length G2)) s = sh (length G1).
Proof.
intros R G1 G2 s Hs.
induction Hs.
(* dot *)
simpl length.
simp_sub.

(* sh *)
assert (length G = n + length G').
eapply truncate_length; eassumption.
simp_sub.
f_equal.
lia.
Qed.


Lemma subof_close :
  forall R G,
    subof R G (sh (length G)) nil.
Proof.
intros R G.
apply subof_sh.
apply truncate_all.
Qed.



Fixpoint subst_ctx (s : sub) (G : list classifier) {struct G} : list classifier :=
  (match G with
   | nil => nil
   | (c :: G') => subst_cl (under (length G') s) c :: subst_ctx s G'
   end).


Lemma subst_ctx_cons :
  forall s G c,
    subst_ctx s (c :: G) = subst_cl (under (length G) s) c :: subst_ctx s G.
Proof.
intros.
reflexivity.
Qed.


Lemma subst_ctx_length :
  forall s G,
    length (subst_ctx s G) = length G.
Proof.
intros s G.
induction G.
(* 0 *)
reflexivity.

(* S *)
simpl.
f_equal; apply IHG.
Qed.


Lemma index_subst_ctx :
  forall G i c s,
    index i G c
    -> index i (subst_ctx s G) (subst_cl (under (length G - i - 1) s) c).
Proof.
intros G i c s Hindex.
induction Hindex.
(* 0 *)
intros.
simpl.
replace (length l - 0) with (length l) by lia.
apply index_0.

(* S *)
assert (n < length (subst_ctx s l)).
eapply index_length.
eapply IHHindex.
rewrite -> subst_ctx_length in H.
simpl.
apply index_S.
eassumption.
Qed.


Lemma subst_ctx_compose :
  forall G s1 s2,
    subst_ctx (compose s2 s1) G = subst_ctx s1 (subst_ctx s2 G).
Proof.
intros G.
induction G.

(* nil *)
intros s1 s2.
reflexivity.

(* cons *)
intros.
simpl.
f_equal; auto; [].
simp_sub; eauto.
rewrite -> subst_ctx_length; [].
rewrite <- subst_cl_compose.
rewrite -> dist_compose_under; [].
reflexivity.
Qed.


Lemma subst_ctx_id :
  forall G, subst_ctx (sh 0) G = G.
Proof.
intros G.
induction G; auto; [].
(* cons *)
simpl.
f_equal; auto; [].
rewrite -> subst_cl_under_id; auto.
Qed.

Lemma subof_under :
  forall R,
    behaved R
    -> (forall G t c, R G t c -> wc R G t c)
    -> forall G1 G1' G2 s,
         subof R G1 s G1'
         -> subof R (app (subst_ctx s G2) G1) (under (length G2) s) (app G2 G1').
Proof.
intros R Hbehaved Hwc G1 G1' G2 s Hofs.
induction G2 as [| c G2].
(* nil *)
simpl.
assumption.

(* cons *)
simpl subst_ctx.
simpl length.
simpl app.
simp_sub; eauto.
apply (subof_mono (wc R)); [apply wc_elim |].
rewrite under_succ.
apply subof_wc_bind; auto.
apply (subof_mono R); [apply Hwc |].
apply IHG2; auto.
Qed.


Lemma weaken1 :
  forall R G A,
    subof R (A :: G) (sh 1) G.
Proof.
intros R G A.
apply subof_sh; auto.
econstructor. econstructor.
Qed.


Lemma weaken2 :
  forall R G A B,
    subof R (B :: A :: G) (sh 2) G.
Proof.
intros R G A B.
apply subof_sh; auto. econstructor. econstructor. econstructor.
Qed.


End TSubst.
