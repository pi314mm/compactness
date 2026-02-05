From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Ltac prove_traverse_parametric ind :=
intros S S' R enter enter' resolve resolve' s s' t Henter Hresolve Hs;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s' Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try
  ((match goal with
    | IH : (forall (s : S) (s' : S'), _ -> _ = ?f _ ?t)
      |- _ = ?g _ ?t
      => apply IH
    end);
   repeat (apply Henter);
   apply Hs).


Ltac prove_traverse_id ind :=
intros S R enter resolve s t Henter Hresolve Hs;
generalize dependent s;
induction t using ind; intros s Hs;
[apply Hresolve; apply Hs | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try ((match goal with
      | IH : (forall (s : S), _ -> _ = ?t)
        |- _ = ?t
        => apply IH
      end);
     repeat (apply Henter);
     apply Hs).


Ltac prove_traverse_compose ind :=
intros S S' enter enter' resolve resolve' s s' t;
generalize dependent s';
generalize dependent s;
induction t using ind; intros s s';
[simpl; reflexivity | ..];  (* deal with first goal (var) *)
simpl;
try reflexivity;  (* dispense with trivial goals *)
f_equal;
(* find and apply IH *)
try (match goal with
      | IH : (forall (s : S) (s' : S'), _ = ?f ?t)
        |- _ = ?g ?t
        => apply IH
      end).


Class HasVar (term : Type) := var : nat -> term.

Class HasTraverse (term : Type) {HV : HasVar term} := 
  traverse : forall S:Type, (S -> S) -> (S -> nat -> term) -> S -> term -> term.

(*Arguments var {_ _} x.
Arguments traverse {_ _ _} S enter resolve !s /.*)

Class SubstType (term : Type) {HV : HasVar term} {HT : HasTraverse term} :=
  { 
  traverse_var :
  forall S enter resolve s i,
    traverse S enter resolve s (var i) = resolve s i;

  traverse_parametric :
  forall (S:Type) (S':Type) (R : S -> S' -> Prop) enter enter' resolve resolve' s s' t,
    (forall s s', R s s' -> R (enter s) (enter' s'))
    -> (forall s s' i, R s s' -> resolve s i = resolve' s' i)
    -> R s s'
    -> traverse S enter resolve s t = traverse S' enter' resolve' s' t;

  traverse_id :
  forall (S:Type) (R : S -> Prop) enter resolve s t,
    (forall s, R s -> R (enter s))
    -> (forall s i, R s -> resolve s i = var i)
    -> R s
    -> traverse S enter resolve s t = t;

  traverse_compose :
  forall (S:Type) (S':Type) enter enter' resolve resolve' s s' t,
    traverse S enter resolve s (traverse S' enter' resolve' s' t)
    = traverse (S * S')
      (fun p => let (s, s') := p in (enter s, enter' s'))
      (fun p i => let (s, s') := p in traverse S enter resolve s (resolve' s' i))
      (s, s') t
 }.

Section Subst_defns.

Context `{term : Type} `{ST : SubstType term}.

Inductive sub : Type :=
| dot : term -> sub -> sub
| sh : nat -> sub.

Fixpoint lift (f : term -> term) (s : sub) :=
match s with
| dot m s => dot (f m) (lift f s)
| sh i => sh i
end
.

Fixpoint trunc (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       (match s with
        | sh m => sh (m + n)
        | dot _ s' => trunc n' s'
        end)
   end).


Definition project (s : sub) (n : nat) : term :=
  (match trunc n s with
   | dot t _ => t
   | sh i => var i
   end).


Definition shift_var (n : nat) (i : nat) : term :=
  if lt_dec i n then
    var i
  else
    var (S i).



Fixpoint shift_sub (s : sub) {struct s} : sub :=
  (match s with
   | dot t s' =>
       dot (traverse nat S shift_var 0 t) (shift_sub s')
   | sh m =>
       sh (S m)
   end).


Definition subst : sub -> term -> term :=
  traverse sub (fun s' => dot (var 0) (shift_sub s')) project.

(* Composition is written in digrammatic order. *)
Fixpoint compose (s1 : sub) (s2 : sub) {struct s1} : sub :=
  (match s1 with
   | dot t s1' => dot (subst s2 t) (compose s1' s2)
   | sh n => trunc n s2
   end).


Fixpoint under (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' =>
       dot (var 0) (shift_sub (under n' s))
   end).


Lemma subst_eq_traverse :
  forall s t,
    subst s t = traverse sub (under 1) project s t.
Proof.
auto.
Qed.


Lemma subst_var : forall s i,
  subst s (var i) = project s i.
Proof.
intros s i.
unfold subst.
apply traverse_var.
Qed.


(* Trunc *)

Definition trunc1 (s : sub) :=
  (match s with
   | dot _ s' => s'
   | sh n => sh (S n)
   end).


Lemma trunc_sh :
  forall m n,
    trunc m (sh n) = sh (m+n).
Proof.
intros m n.
destruct m; auto; [].
simpl.
f_equal; lia.
Qed.


Lemma trunc_succ_outer :
  forall n s,
    trunc (S n) s = trunc1 (trunc n s).
Proof.
intro n.
induction n.

(* 0 *)
intro s.
destruct s; auto; [].
simpl.
replace (n+1) with (S n); [reflexivity | lia].

(* S *)
destruct s; [|].
  (* dot *)
  replace (trunc (S (S n)) (dot t s)) with (trunc (S n) s) by reflexivity.
  replace (trunc (S n) (dot t s)) with (trunc n s) by reflexivity.
  apply IHn.

  (* sh *)
  simpl.
  f_equal; lia.
Qed.


Lemma trunc_sum :
  forall m n s,
    trunc m (trunc n s) = trunc (m+n) s.
Proof.
intros m n s.
induction m.

(* Z *)
reflexivity.

(* S *)
replace (S m + n) with (S (m + n)); [ | auto].
rewrite -> !trunc_succ_outer; [].
f_equal; auto.
Qed.


Lemma trunc_succ_inner :
  forall n s,
    trunc (S n) s = trunc n (trunc1 s).
Proof.
intros n s.
replace (S n) with (n+1); [| lia].
rewrite <- (trunc_sum n 1); [].
f_equal; [].
unfold trunc1.
destruct s; auto; [].
simpl.
f_equal; lia.
Qed.


Lemma trunc1_under :
  forall n s,
    n >= 1
    -> trunc1 (under n s) = shift_sub (under (n-1) s).
Proof.
intros n s H.
destruct n; [lia |].
simpl.
replace (n-0) with n by lia.
reflexivity.
Qed.


Lemma project_zero :
  forall t s,
    project (dot t s) 0 = t.
Proof.
auto.
Qed.


Lemma project_dot :
  forall t s i,
    project (dot t s) (S i) = project s i.
Proof.
intros t s i.
unfold project.
simpl.
reflexivity.
Qed.


Lemma project_sh :
  forall n i,
    project (sh n) i = var (n+i).
Proof.
intros n i.
unfold project.
rewrite -> trunc_sh; [].
f_equal; lia.
Qed.


(* Shift-var *)

Lemma shift_var_lt :
  forall n i,
    i < n -> shift_var n i = var i.
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); auto; lia.
Qed.


Lemma shift_var_ge :
  forall n i,
    i >= n -> shift_var n i = var (S i).
Proof.
intros n i H.
unfold shift_var.
destruct (lt_dec i n); auto; lia.
Qed.


(* Shift-term *)

Fixpoint nshift_term (n : nat) (t : term) {struct n} : term :=
  (match n with
   | 0 => t
   | S n' => traverse nat S shift_var 0 (nshift_term n' t)
   end).


Lemma shift_term_var :
  forall n i,
    traverse nat S shift_var n (var i) = shift_var n i.
Proof.
intros n i.
apply traverse_var.
Qed.


Lemma nshift_term_var :
  forall n i,
    nshift_term n (var i) = var (n+i).
Proof.
intros n i.
induction n.

(* 0 *)
reflexivity.

(* S *)
simpl.
rewrite -> IHn; [].
rewrite -> shift_term_var; [].
unfold shift_var.
destruct (lt_dec (n+1) 0); [lia |].
reflexivity.
Qed.


Lemma nshift_term_sum :
  forall m n s,
    nshift_term m (nshift_term n s) = nshift_term (m+n) s.
Proof.
intros m n s.
induction m.

(* 0 *)
reflexivity.

(* S *)
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Lemma nshift_term_succ_inner :
  forall n s,
    nshift_term (S n) s = nshift_term n (traverse nat S shift_var 0 s).
Proof.
intros n s.
replace (S n) with (n+1) by lia.
rewrite <- nshift_term_sum.
reflexivity.
Qed.


Lemma shift_term_commute :
  forall n t,
    traverse nat S shift_var (S n) (traverse nat S shift_var 0 t) = traverse nat S shift_var 0 (traverse nat S shift_var n t).
Proof.
intros n t.
rewrite -> !traverse_compose; [].
apply (traverse_parametric (nat * nat) (nat * nat)
       (fun p p' => let (m, i) := p in
        let (i', m') := p' in
                         i = i' /\ m = i+1+n /\ m' = i+n)); auto; [|].

(* enter *)
intros (m, i) (i', m').
lia.

(* resolve *)
clear t.
intros (m, i) (i', m') j (H1 & H2 & H3).
subst i' m m'.
change (traverse nat S shift_var (i+1+n) (shift_var i j) = traverse nat S shift_var i (shift_var (i+n) j)).
unfold shift_var.
destruct (lt_dec j i); [|].
  (* j < i *)
  destruct (lt_dec j (i+n)); [| lia].
  rewrite -> !shift_term_var.
  rewrite -> !shift_var_lt by lia.
  reflexivity.

  (* j >= i *)
  destruct (lt_dec j (i+n)); [|].
    (* i <= j < i+n *)
    rewrite -> !shift_term_var; [].
    rewrite -> shift_var_lt by lia.
    rewrite -> shift_var_ge by lia.
    reflexivity.

    (* j >= i+n *)
    rewrite -> !shift_term_var.
    rewrite -> !shift_var_ge by lia.
    reflexivity.
Qed.


Lemma nshift_term_commute :
  forall m n t,
    m >= n
    -> traverse nat S shift_var m (nshift_term n t) = nshift_term n (traverse nat S shift_var (m-n) t).
Proof.
intros m n.
revert m.
induction n.

(* Z *)
intros m t H.
replace (m-0) with m by lia.
reflexivity.

(* S *)
intros m t H.
simpl.
replace m with (S (m-1)) by lia.
rewrite -> shift_term_commute.
f_equal; [].
rewrite -> (IHn (m-1)) by lia.
auto.
Qed.


Lemma nshift_term_commute_eq :
  forall n t,
    traverse nat S shift_var n (nshift_term n t) = nshift_term (S n) t.
Proof.
intros n t.
rewrite -> nshift_term_succ_inner.
replace 0 with (n-n) by lia.
apply nshift_term_commute; [].
lia.
Qed.


(* Shift-sub *)

Fixpoint nshift_sub (n : nat) (s : sub) {struct n} : sub :=
  (match n with
   | 0 => s
   | S n' => shift_sub (nshift_sub n' s)
   end).


Lemma nshift_sub_dot :
  forall n t s,
    nshift_sub n (dot t s) = dot (nshift_term n t) (nshift_sub n s).
Proof.
intros n t s.
induction n.

(* Z *)
auto.

(* S *)
simpl.
rewrite -> IHn.
reflexivity.
Qed.


Lemma nshift_sub_sh :
  forall m n,
    nshift_sub m (sh n) = sh (m+n).
Proof.
intros m n.
induction m.

(* Z *)
auto.

(* S *)
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Lemma trunc_shift_sub :
  forall n s,
    trunc n (shift_sub s) = shift_sub (trunc n s).
Proof.
intros n.
induction n.

(* 0 *)
auto.

(* S *)
intros s.
destruct s; auto; [].
simpl.
apply IHn.
Qed.


Lemma trunc_nshift_sub :
  forall n m s,
    trunc n (nshift_sub m s) = nshift_sub m (trunc n s).
Proof.
intros n m s.
induction m.

(* Z *)
auto.

(* S *)
simpl.
rewrite -> trunc_shift_sub; [].
f_equal; auto.
Qed.


Lemma nshift_sub_sum :
  forall m n s,
    nshift_sub m (nshift_sub n s) = nshift_sub (m+n) s.
Proof.
intros m n s.
induction m.

(* 0 *)
reflexivity.

(* S *)
simpl.
rewrite -> IHm.
reflexivity.
Qed.


Lemma nshift_sub_succ_inner :
  forall n s,
    nshift_sub (S n) s = nshift_sub n (shift_sub s).
Proof.
intros n s.
replace (S n) with (n+1) by lia.
rewrite <- nshift_sub_sum; [].
reflexivity.
Qed.


Lemma shift_sub_trunc :
  forall s n,
    shift_sub (trunc n s) = trunc n (shift_sub s).
Proof.
intro s.
induction s.

(* dot *)
intros n.
destruct n as [| n']; auto; [].
apply IHs.

(* sh *)
intros n0.
rewrite -> !trunc_sh.
simpl.
rewrite -> trunc_sh.
auto.
Qed.


(* Under *)

Lemma trunc_under :
  forall m n s,
    m <= n
    -> trunc m (under n s) = nshift_sub m (under (n-m) s).
Proof.
intros m.
induction m.

(* 0 *)
intros n s H.
simpl.
replace (n-0) with n by lia.
reflexivity.

(* S *)
intros n s H.
rewrite -> trunc_succ_inner; [].
rewrite -> trunc1_under by lia.
rewrite -> trunc_shift_sub; [].
rewrite -> IHm; [| lia].
simpl.
replace (n-1-m) with (n - S m) by lia.
reflexivity.
Qed.


Lemma project_under_lt :
  forall n s i,
    i < n
    -> project (under n s) i = var i.
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under; [| lia].
remember (n-i) as x.
destruct x; [lia |].
simpl.
rewrite -> nshift_sub_dot; [].
rewrite -> nshift_term_var; [].
replace (i+0) with i by lia.
reflexivity.
Qed.


Lemma trunc_under_more :
  forall m n s,
    m >= n
    -> trunc m (under n s) = trunc (m-n) (nshift_sub n s).
Proof.
intros m n s H.
replace m with ((m-n)+n) by lia.
rewrite <- trunc_sum; [].
f_equal; [|].
  lia.

  rewrite -> trunc_under; auto; [].
  replace (n-n) with 0 by lia.
  reflexivity.
Qed.


Lemma project_under_ge_nshift :
  forall n s i,
    i >= n
    -> project (under n s) i = nshift_term n (project s (i-n)).
Proof.
intros n s i H.
unfold project.
rewrite -> trunc_under_more; [| lia].
rewrite -> trunc_nshift_sub; [].
destruct (trunc (i-n) s); [|].
  rewrite -> nshift_sub_dot; [].
  reflexivity.

  rewrite -> nshift_sub_sh; [].
  rewrite -> nshift_term_var; [].
  reflexivity.
Qed.


Lemma subst_shift_sub :
  forall s t,
    subst (shift_sub s) t = traverse nat S shift_var 0 (subst s t).
Proof.
intros s t.
unfold subst.
rewrite -> traverse_compose.
apply (traverse_parametric sub (nat * sub)
       (fun s1 p => let (n, s2) := p in s1 = under n (shift_sub s) /\ s2 = under n s)); auto; [|].

(* enter *)
clear t.
intros s1 (n, s2) (->, ->).
auto.

(* resolve *)
clear t.
intros s1 (n, s2) i (->, ->).
destruct (lt_dec i n); [|].
  (* i < n *)
  rewrite -> !project_under_lt by lia.
  rewrite -> traverse_var; [].
  unfold shift_var.
  destruct (lt_dec i n); auto; [].
  lia.

  (* i >= n *)
  unfold project.
  rewrite -> !trunc_under_more by lia.
  rewrite -> !trunc_nshift_sub.
  rewrite -> trunc_shift_sub.
  rewrite <- nshift_sub_succ_inner.
  destruct (trunc (i-n) s); [|].
    rewrite -> nshift_sub_dot.
    rewrite -> nshift_sub_dot.
    fold (traverse nat S shift_var n (nshift_term n t)).
    symmetry; apply nshift_term_commute_eq.

  rewrite -> !nshift_sub_sh.
  simpl.
  rewrite -> traverse_var.
  unfold shift_var.
  destruct (lt_dec (n+n1) n); auto; [].
  lia.
Qed.


Lemma subst_dot_shift_term :
  forall t s t',
    subst (dot t s) (traverse nat S shift_var 0 t') = subst s t'.
Proof.
intros t s t'.
unfold subst.
rewrite -> traverse_compose.
apply (traverse_parametric (sub * nat) sub
         (fun p s2 => let (s1, i) := p in s1 = under i (dot t s) /\ s2 = under i s)); auto; [|].

(* enter *)
clear t'.
intros (s1, i) s2 (-> & ->).
auto.

(* resolve *)
clear t'.
intros (s1, i) s2 j (-> & ->).
fold (subst (under i (dot t s)) (shift_var i j)).
unfold shift_var.
destruct (lt_dec j i); [|].
  (* j < i *)
  rewrite -> subst_var.
  rewrite -> !project_under_lt by assumption.
  reflexivity.

  (* j >= i *)
  rewrite -> subst_var.
  rewrite -> !project_under_ge_nshift by lia.
  f_equal.
  replace (S j - i) with (S (j-i)) by lia.
  rewrite -> project_dot.
  reflexivity.
Qed.


Lemma shift_term_eq_subst_under_sh :
  forall t n,
    traverse nat S shift_var n t = subst (under n (sh 1)) t.
Proof.
intros t n.
unfold subst.
apply (traverse_parametric nat sub (fun n s => s = under n (sh 1))); auto; [|].

(* enter *)
clear t n.
intros n s ->.
reflexivity.

(* resolve *)
clear t n.
intros n s i ->.
unfold shift_var.
destruct (lt_dec i n); [|].
  (* i < n *)
  symmetry; apply project_under_lt; auto.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by lia.
  rewrite -> project_sh.
  rewrite -> nshift_term_var.
  f_equal; lia.
Qed.


Lemma shift_term_eq_sh :
  forall t,
    traverse nat S shift_var 0 t = subst (sh 1) t.
Proof.
intro t.
apply shift_term_eq_subst_under_sh.
Qed.


Lemma shift_sub_eq_compose_sh :
  forall s,
    shift_sub s = compose s (sh 1).
Proof.
intro s.
induction s.

(* dot *)
simpl.
f_equal; [|].
  apply shift_term_eq_sh.

  apply IHs.

(* sh *)
simpl.
rewrite -> trunc_sh; [].
f_equal; lia.
Qed.


(* Composition *)

Lemma compose_shift_sub_left :
  forall s1 s2,
    compose s1 (shift_sub s2) = shift_sub (compose s1 s2).
Proof.
intros s1 s2.
induction s1.

(* dot *)
simpl.
f_equal; auto; [].
apply subst_shift_sub.

(* sh *)
symmetry.
apply shift_sub_trunc.
Qed.


Lemma compose_shift_sub_right :
  forall s1 s2 t,
    compose (shift_sub s1) (dot t s2) = compose s1 s2.
Proof.
intros s1 s2 t.
induction s1.

(* dot *)
simpl.
f_equal; [|].
  apply subst_dot_shift_term.

  apply IHs1.

(* sh *)
auto.
Qed.


Lemma compose_sh :
  forall n s,
    compose (sh n) s = trunc n s.
Proof.
auto.
Qed.


Lemma trunc_compose :
  forall i s1 s2,
    trunc i (compose s1 s2) = compose (trunc i s1) s2.
Proof.
intros i.
induction i.

(* 0 *)
reflexivity.

(* S *)
intros s1 s2.
destruct s1.
  (* dot *)
  apply IHi.

  (* sh *)
  rewrite -> trunc_sh, !compose_sh.
  apply trunc_sum.
Qed.


Lemma project_compose :
  forall i s1 s2,
    project (compose s1 s2) i = subst s2 (project s1 i).
Proof.
intros i s1 s2.
unfold project.
rewrite -> trunc_compose.
generalize (trunc i s1); intro s.
destruct s; auto.
rewrite subst_var.
rewrite compose_sh.
auto.
Qed.


(* The main lemma *)
Lemma subst_compose :
  forall t s1 s2,
    subst (compose s2 s1) t = subst s1 (subst s2 t).
Proof.
intros t s1 s2.
unfold subst.
rewrite -> traverse_compose; [].
apply (traverse_parametric sub (sub * sub) (fun s p => let (s1, s2) := p in s = compose s2 s1)); auto; [|].

(* enter *)
clear t s1 s2.
intros s (s1, s2) ->.
simpl.
f_equal.
unfold subst.
rewrite traverse_var.
rewrite project_zero.
reflexivity.

rewrite <- compose_shift_sub_left.
rewrite -> compose_shift_sub_right.
reflexivity.

(* resolve *)
clear t s1 s2.
intros s (s1 & s2) i ->.
apply project_compose.
Qed.


Lemma compose_assoc :
  forall s1 s2 s3,
    compose (compose s1 s2) s3 = compose s1 (compose s2 s3).
Proof.
intros s1 s2 s3.
induction s1.

(* dot *)
simpl.
f_equal; auto using subst_compose.

(* sh *)
rewrite -> !compose_sh; [].
symmetry.
apply trunc_compose.
Qed.


(* Various equivalencies *)

Lemma compose_dot :
  forall t s1 s2,
    compose (dot t s1) s2 = dot (subst s2 t) (compose s1 s2).
Proof.
auto.
Qed.


Lemma compose_sh_0 :
  forall s,
    compose (sh 0) s = s.
Proof.
auto.
Qed.


Lemma compose_sh_succ_dot :
  forall t s n,
    compose (sh (S n)) (dot t s) = compose (sh n) s.
Proof.
auto.
Qed.


Lemma compose_sh_sh :
  forall m n,
    compose (sh m) (sh n) = sh (m+n).
Proof.
intros m n.
simpl.
rewrite -> trunc_sh; [].
f_equal.
Qed.


Lemma compose_id_left :
  forall s,
    compose (sh 0) s = s.
Proof.
apply compose_sh_0.
Qed.


Lemma subst_under_id :
  forall n t,
    subst (under n (sh 0)) t = t.
Proof.
intros m t.
unfold subst.
apply (traverse_id sub (fun s => exists n, s = under n (sh 0))); eauto; [|].

(* enter *)
clear t.
intros s (n, ->).
exists (S n).
reflexivity.

(* resolve *)
clear t.
intros s i (n, ->).
destruct (lt_dec i n); [|].
  (* i < n *)
  apply project_under_lt; assumption.

  (* i >= n *)
  rewrite -> project_under_ge_nshift by lia.
  unfold id.
  rewrite -> project_sh; [].
  rewrite -> nshift_term_var; [].
  f_equal; lia.
Qed.


Lemma subst_id :
  forall t,
    subst (sh 0) t = t.
Proof.
intro t.
change (subst (under 0 (sh 0)) t = t).
apply subst_under_id.
Qed.


Lemma compose_id_right :
  forall s,
    compose s (sh 0) = s.
Proof.
intro s.
induction s.

(* dot *)
simpl.
f_equal; [|].
  apply subst_id.

  apply IHs.

(* sh *)
simpl.
unfold id.
rewrite -> trunc_sh.
f_equal; lia.
Qed.


Lemma trunc_eq_compose_sh :
  forall n s,
    trunc n s = compose (sh n) s.
Proof.
intros n s.
destruct n; auto.
Qed.


Lemma subst1_shift1 :
  forall t t', subst (dot t (sh 0)) (subst (sh 1) t') = t'.
Proof.
intros t t'.
rewrite <- subst_compose; [].
rewrite -> compose_sh_succ_dot; [].
rewrite -> compose_sh_0; [].
apply subst_id.
Qed.


Lemma under_zero :
  forall s, under 0 s = s.
Proof.
auto.
Qed.


Lemma under_succ :
  forall n s,
    under (S n) s = dot (var 0) (compose (under n s) (sh 1)).
Proof.
intros n s.
unfold under.
rewrite -> shift_sub_eq_compose_sh.
reflexivity.
Qed.


Lemma dist_compose_under :
  forall n s1 s2,
    compose (under n s1) (under n s2) = under n (compose s1 s2).
Proof.
intros n s1 s2.
induction n.

(* 0 *)
rewrite -> !under_zero; [].
reflexivity.

(* S *)
rewrite -> !under_succ; [].
rewrite -> compose_dot; [].

f_equal.
unfold subst.
rewrite traverse_var.
rewrite project_zero.
reflexivity.
rewrite -> compose_assoc.
rewrite -> compose_sh_succ_dot.
rewrite -> compose_sh_0.
rewrite <- compose_assoc.
rewrite -> IHn.
reflexivity.
Qed.


Lemma subst_dot0_sh :
  forall t,
    subst (dot (var 0) (sh 1)) t = t.
Proof.
intro t.
rewrite -> (subst_under_id 1 t) at 1.
reflexivity.
Qed.


Lemma nshift_term_eq_sh :
  forall n t,
    nshift_term n t = subst (sh n) t.
Proof.
intros n t.
induction n as [| n IH].

(* 0 *)
rewrite subst_id.
simpl.
reflexivity.

(* S *)
simpl.
rewrite -> IH.
rewrite -> shift_term_eq_sh.
rewrite <- subst_compose.
rewrite compose_sh_sh.
replace (n + 1) with (S n) by lia.
reflexivity.
Qed.

Lemma compose_sh_under_leq :
  forall i n s,
    i <= n
    -> compose (sh i) (under n s) = compose (under (n - i) s) (sh i).
Proof.
intros i n s Hleq.
revert n Hleq.
induction i.

(* 0 *)
intros n _.
rewrite compose_sh_0.
rewrite compose_id_right.
replace (n - 0) with n by lia.
reflexivity.

(* S *)
intros n Hleq.
destruct n as [| n']; [lia |].
rewrite -> under_succ; [].
rewrite -> compose_sh_succ_dot; [].
rewrite <- compose_assoc; [].
rewrite -> IHi; [| lia].
rewrite compose_assoc.
rewrite compose_sh_sh.
replace (S n' - S i) with (n' - i) by lia.
replace (i + 1) with (S i) by lia.
reflexivity.
Qed.

Lemma compose_sh_under :
  forall i n s,
    compose (sh i) (under (i + n) s) = compose (under n s) (sh i).
Proof.
intros i n s.
rewrite compose_sh_under_leq.
replace (i + n - i) with n by lia.
reflexivity.
lia.
Qed. 

Lemma compose_sh_under_geq :
  forall i n s,
    i >= n
    -> compose (sh i) (under n s) = compose (sh (i - n)) (compose s (sh n)).
Proof.
intros i n s Hgeq.
replace (sh i) with (sh ((i - n) + n)) by (f_equal; lia).
rewrite <- compose_sh_sh; [].
rewrite -> compose_assoc; [].
rewrite -> compose_sh_under_leq; [| auto].
replace (n - n) with 0 by lia.
rewrite -> under_zero; [].
reflexivity.
Qed.

Lemma compose_sh1_under :
  forall n s,
    compose (sh 1) (under (S n) s) = compose (under n s) (sh 1).
Proof.
intros n s.
exact (compose_sh_under 1 n s).
Qed.

Lemma project_under_ge :
  forall n s i,
    i >= n
    -> project (under n s) i = subst (sh n) (project s (i-n)).
Proof.
intros n s i H.
rewrite <- nshift_term_eq_sh.
apply project_under_ge_nshift; auto.
Qed.


Lemma split_dot :
  forall t s,
    dot t s = compose (dot (var 0) (compose s (sh 1))) (dot t (sh 0)).
Proof.
intros t s.
simpl.
f_equal.
rewrite subst_var. rewrite project_zero. reflexivity.
rewrite compose_assoc.
simpl.
rewrite compose_id_right.
reflexivity.
Qed.


Lemma split_dot_compose :
  forall m s n,
    subst (dot m s) n = subst (dot m (sh 0)) (subst (dot (var 0) (compose s (sh 1))) n).
Proof.
intros m s n.
rewrite -> split_dot.
rewrite -> subst_compose.
reflexivity.
Qed.

Lemma subst_dot01_sh :
  forall t,
    subst (dot (var 0) (dot (var 1) (sh 2))) t = t.
Proof.
intro t.
replace (dot (var 0) (dot (var 1) (sh 2))) with (under 2 (sh 0)).
rewrite -> (subst_under_id 2 t) at 1.
reflexivity.
simpl.
rewrite traverse_var. rewrite shift_var_ge.
reflexivity.
lia.
Qed.


Lemma subst_dot1_sh :
  forall t,
    subst (dot (var 1) (sh 2)) t = subst (sh 1) t.
Proof.
intro t.
replace (subst (sh 1) t) with (subst (sh 1) (subst (dot (var 0) (sh 1)) t)).
rewrite <- subst_compose; [].
simpl.
replace (subst (sh 1) (var 0)) with (var 1).
reflexivity.
rewrite subst_var. rewrite project_sh.
simpl.
reflexivity.
rewrite subst_dot0_sh.
reflexivity.
Qed.

(* TODO
Lemma under_succ2 :
  forall n s,
    under (S (S n)) s = dot (var 0) (dot (var 1) (compose (under n s) (sh 2))).
Proof.
intros n s.
rewrite -> under_succ.
f_equal; [].
rewrite -> under_succ.
simp_sub.
reflexivity.
Qed.

Section StrongInduction.

  Variable P:nat -> Prop.

  (** The stronger inductive hypothesis given in strong induction. The standard
  [nat ] induction principle provides only n = pred m, with [P 0] required
  separately. *)
  Hypothesis IH : forall m, (forall n, n < m -> P n) -> P m.

  (** * Strengthen the induction hypothesis. *)

  Local Lemma strong_induction_all : forall n,
      (forall m, m <= n -> P m).
  Proof.
    induction n; intros;
      match goal with
      | [ H: _ <= _ |- _ ] =>
        inversion H
      end; eauto.
  apply IH; intros.
    exfalso; inversion H; lia.
  eapply IH. intros. eapply IHn. lia.
  Qed.

  Theorem strong_induction : forall n, P n.
  Proof.
    eauto using strong_induction_all.
  Qed.

End StrongInduction.


Lemma shift_eq_invert :
  forall n t t',
    subst (sh n) t = subst (sh n) t'
    -> t = t'.
Proof.
induction n using strong_induction.
intros t t' Heq.
induction n.
rewrite subst_id in Heq.
rewrite subst_id in Heq.
eassumption.
assert(subst (sh 1) t = subst (sh 1) t').
replace (sh (S n)) with (compose (sh 1) (sh n)) in Heq.
rewrite subst_compose in Heq.
rewrite subst_compose in Heq.
assert(n < S n). lia.
eapply (H _ H0 _ _ Heq).
simpl. replace (n+1) with (S n) by lia. reflexivity.
induction n.
rewrite subst_id in Heq.
rewrite subst_id in Heq.
eassumption.
assert(1 < S n). 
eapply (H _ _ _ _ H0).

Qed.

*)
Lemma subst_under_var :
  forall s i j,
    i < j
    -> subst (under j s) (var i) = var i.
Proof.
intros s i j Hlt.
rewrite subst_var.
rewrite -> project_under_lt; auto.
Qed.


End Subst_defns.


Create HintDb subst.
(*Hint Unfold id sh1 subst1 shift1 : subst.*)
#[export] Hint Rewrite @project_zero @project_dot @project_sh : subst.
#[export] Hint Rewrite @subst_id @subst1_shift1 : subst.
#[export] Hint Rewrite @compose_dot @compose_sh_0 @compose_sh_succ_dot @compose_sh_sh @compose_id_left @compose_id_right : subst.
#[export] Hint Rewrite @compose_assoc : subst.
#[export] Hint Rewrite <- @subst_compose : subst.
#[export] Hint Rewrite @under_zero @dist_compose_under : subst.
#[export] Hint Rewrite @subst_under_id @subst_dot0_sh : subst.
#[export] Hint Rewrite @shift_sub_eq_compose_sh : subst.
#[export] Hint Rewrite @nshift_term_eq_sh : subst.


Ltac simp_sub
  := autorewrite with subst;
     eauto with subst.

Tactic Notation "simp_sub" "in" hyp(H)
  := autorewrite with subst in H; eauto with subst.
