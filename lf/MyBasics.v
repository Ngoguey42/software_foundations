(*
https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html
*)

(* ************************************************************************** *)
(* Exercise: 1 star, standard (nandb) *)
Definition nandb (b c : bool) : bool :=
  match b, c with
  | false, _ | _, false => true
  | _, _ => false
  end.
Example test_nandb1 : (nandb true false = true). Proof. reflexivity. Qed.
Example test_nandb2 : (nandb false false = true). Proof. reflexivity. Qed.
Example test_nandb3 : (nandb false true = true). Proof. reflexivity. Qed.
Example test_nandb4 : (nandb true true = false). Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (andb3) *)
Definition andb3 (b c d : bool) : bool :=
  match b, c, d with
  | true, true, true => true
  | _, _, _ => false
  end.

Example test_andb31: (andb3 true true true) = true. Proof. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false. Proof. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false. Proof. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false. Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (factorial) *)
Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => n * factorial (n')
  end.

Example test_factorial1: (factorial 3) = 6. Proof. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (10 * 12). Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (ltb) *)
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | O, S _ | S _, O => false
  | S n', S m' => eqb n' m'
 end.
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, O | O, S _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
  end.
Definition ltb (n m : nat) : bool :=
  match eqb n m, leb n m with
  | false, true => true
  | _, _ => false
  end.
Example test_ltb1: (ltb 2 2) = false. Proof. reflexivity. Qed.
Example test_ltb2: (ltb 2 4) = true. Proof. reflexivity. Qed.
Example test_ltb3: (ltb 4 2) = false. Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
    n = m ->
    m = o ->
    n + m = m + o.
Proof.
  intros n m o H1 H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (mult_n_1) *)
Check mult_n_Sm.
Check mult_n_O.
Theorem mult_n_1 : forall p : nat, p * 1 = p.
Proof.
  intro a.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
  intros b c.
  destruct b, c.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
  - reflexivity.
  - simpl. intros H. rewrite -> H. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (zero_nbeq_plus_1) *)
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Theorem zero_nbeq_plus_1 : forall n : nat, 0 =? (n + 1) = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, optional (decreasing) *)
Fail Fixpoint forever (n m: nat) : nat :=
  match n, m with
  | S n, S m => forever m n
  | _, _ => O
  end.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (identity_fn_applied_twice) *)
Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  (forall (b : bool), f (f b) = b).
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (negation_fn_applied_twice) *)
Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - reflexivity.
  - reflexivity.
Qed.
Theorem negation_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  (forall (b : bool), f (f b) = b).
Proof.
  intros f H b.
  rewrite -> H.
  rewrite -> H.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, optional (andb_eq_orb) *)
Theorem andb_eq_orb : forall b c, andb b c = orb b c -> b = c.
Proof.
  intros b c.
  destruct b.
  - { simpl. intros H. rewrite <- H. reflexivity. }
  - { simpl. intros H. rewrite <- H. reflexivity. }
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard (binary) *)
