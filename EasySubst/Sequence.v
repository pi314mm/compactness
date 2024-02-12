
Require Export List.
Require Import Lia.


(* General list facts *)


Import ListNotations.

#[export] Hint Rewrite <- app_assoc app_comm_cons : canonlist.
#[export] Hint Rewrite -> app_nil_l app_nil_r : canonlist.


(* Lists indexed numerically. *)

Inductive truncate {T:Type} : nat -> list T -> list T -> Prop :=
| truncate_0 {l}
    : truncate 0 l l

| truncate_S {i x l l'}
    : truncate i l l'
      -> truncate (S i) (x :: l) l'.


Inductive index {T:Type} : nat -> list T -> T -> Prop :=
| index_0 {x l}
    : index 0 (x :: l) x
| index_S {n x l y}
    : index n l y
      -> index (S n) (x :: l) y.



Lemma truncate_index :
  forall (T:Type) i l (x:T) l',
    truncate i l (x :: l')
    -> index i l x.
Proof.
intros T i.
induction i.
(* 0 *)
intros l x l' H.
inversion H; subst.
apply index_0.

(* S *)
intros l x l' H.
inversion H; subst.
apply index_S.
eapply IHi.
apply H1.
Qed.


Lemma truncate_sum :
  forall (T:Type) m n (l:list T) l' l'',
    truncate m l l'
    -> truncate n l' l''
    -> truncate (m+n) l l''.
Proof.
intros T m n l l' l'' H1 H2.
revert H2; induction H1.
(* 0 *)
intros.
simpl. eassumption.

(* S *)
intros.
replace (S i + n) with (S (i+n)) by lia.
apply truncate_S; auto.
Qed.


Lemma truncate_index_sum :
  forall (T:Type) m n (l:list T) l' x,
    truncate m l l'
    -> index n l' x
    -> index (m+n) l x.
Proof.
intros T m n l l' x.
revert l.
induction m; intros l Htrunc Hindex.
inversion Htrunc; subst.
replace (0+n) with n by lia.
eassumption.
replace (S m + n) with (S (m+n)) by lia.
inversion Htrunc; subst.
econstructor.
eapply IHm; eassumption.
Qed.


Lemma truncate_length :
  forall (T:Type) n (l:list T) l',
    truncate n l l'
    -> length l = n + length l'.
Proof.
intros T n l l' H.
induction H.
auto.  
simpl.
lia.
Qed.


Lemma truncate_all :
  forall (A : Type) (l : list A),
    truncate (length l) l nil.
Proof.
intros A l.
induction l; simpl; auto.
econstructor. econstructor. eassumption.
Qed.


Lemma index_length :
  forall (T:Type) (l : list T) i x,
    index i l x
    -> i < length l.
Proof.
intros T l i x H.
induction H. simpl. lia.
simpl. lia.
Qed.

Lemma index_app_lt :
  forall (T:Type) (l1 l2:list T) i x,
    i < length l1
    -> index i (l1 ++ l2) x
    -> index i l1 x.
Proof.
intros T l1 l2 i x Hlt Hindex.
revert l1 Hlt Hindex.
induction i.
(* 0 *)
intros.
destruct l1.
  simpl in Hlt; exfalso; lia.

  simpl in Hindex.
  inversion Hindex; intros.
  subst t.
  apply index_0.

(* S *)
intros.
destruct l1.
  simpl in Hlt; exfalso; lia.

  simpl in Hindex.
  inversion Hindex; intros.
  apply index_S.
  apply IHi.
    simpl in Hlt; lia.

    assumption.
Qed.

Lemma index_app_ge :
  forall (T:Type) (l1 l2:list T) i x,
    i >= length l1
    -> index i (l1 ++ l2) x
    -> index (i - length l1) l2 x.
Proof.
intros T l1 l2 i x Hge Hindex.
revert i Hge Hindex.
induction l1.
(* nil *)
intros.
simpl in Hindex.
simpl.
replace (i-0) with i by lia.
assumption.

(* cons *)
intros.
simpl.
replace (i - S (length l1)) with (i - 1 - length l1) by lia.
simpl in Hge.
apply IHl1.
  lia.
  simpl in Hindex.
  inversion Hindex; intros.
    exfalso; lia.

    rewrite <- H2.
    rewrite <- H2 in H3.
    replace (S n - 1) with n by lia.
    assumption.
Qed.


Lemma index_app_left :
  forall (T:Type) (l1 l2:list T) i x,
    index i l1 x
    -> index i (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induction Hindex.
(* 0 *)
apply index_0.

(* S *)
simpl.
apply index_S.
assumption.
Qed.


Lemma index_app_right :
  forall (T:Type) (l1 l2:list T) i x,
    index i l2 x
    -> index (i + length l1) (l1 ++ l2) x.
Proof.
intros T l1 l2 i x Hindex.
induction l1.
(* nil *)
simpl.
replace (i+0) with i by lia.
assumption.

(* cons *)
simpl.
replace (i + S (length l1)) with (S (i + length l1)) by lia.
apply index_S.
assumption.
Qed.


Lemma app_truncate :
  forall (T:Type) (l1 l2:list T),
    truncate (length l1) (l1 ++ l2) l2.
Proof.
intros T l1 l2.
induction l1.
(* nil *)
simpl.
apply truncate_0.

(* cons *)
simpl.
apply truncate_S.
assumption.
Qed.


Lemma truncate_app :
  forall (T : Type) n (l l' : list T),
    truncate n l l'
    -> exists l'', l = l'' ++ l' /\ length l'' = n.
Proof.
intros T n l l' Htrunc.
induction Htrunc.
(* 0 *)
exists nil.
simpl; auto.

(* S *)
destruct IHHtrunc as (l'' & Heq & Hlen).
exists (x :: l'').
split.
  simpl.
  f_equal; auto.

  simpl.
  f_equal; auto.
Qed.


Lemma index_in :
  forall (T : Type) n (l : list T) x,
    index n l x
    -> In x l.
Proof.
intros T n l x Hindex.
induction Hindex.
(* 0 *)
left; auto.

(* S *)
right; auto.
Qed.

