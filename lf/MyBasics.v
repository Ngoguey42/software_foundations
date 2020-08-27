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
Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin)
.

(* incr / dect *)
Fixpoint incr (m : bin) : bin :=
  match m with
  | B0 m' => B1 m'
  | _ => B0 m
  end.
Fixpoint decr (m : bin) : bin :=
  match m with
  | Z => Z
  | B0 m' => m'
  | B1 m' => B0 m'
  end.
Theorem incr_decr_identity : forall a : bin, decr (incr a) = a.
Proof.
  intros a.
  destruct a.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

(* euclidean division on nat (useless) *)
Fixpoint _divmod (x y quot rem : nat) : (nat * nat) :=
  match x with
  | O => (quot, rem)
  | S x' => match rem with
            | O =>      _divmod x' y (S quot) y
            | S rem' => _divmod x' y quot rem'
            end
  end.
Definition divmod x y :=
  match y with
  | O => (y, y)
  | S y' =>
    match _divmod x y' 0 y' with
    | (quot, rem) => (quot, y' - rem)
    end
  end.
Definition div x y := fst (divmod x y).
Definition mod x y := snd (divmod x y).
Example divmod1 : divmod 5 1 = (5, 0). Proof. compute. reflexivity. Qed.
Example divmod2 : divmod 5 2 = (2, 1). Proof. compute. reflexivity. Qed.
Example divmod3 : divmod 5 3 = (1, 2). Proof. compute. reflexivity. Qed.
Example divmod4 : divmod 5 4 = (1, 1). Proof. compute. reflexivity. Qed.
Example divmod5 : divmod 5 5 = (1, 0). Proof. compute. reflexivity. Qed.
Example divmod6 : divmod 5 6 = (0, 5). Proof. compute. reflexivity. Qed.
(* conversions *)
Fixpoint _bin_to_nat (m : bin) (weight : nat) : nat :=
  match m with
  | Z => O
  | B1 m' => weight + _bin_to_nat m' (weight * 2)
  | B0 m' => _bin_to_nat m' (weight * 2)
  end.
Definition bin_to_nat (m : bin) : nat := _bin_to_nat m 1.
(* tests *)
Example test_bin_incr1 : (incr (B1 Z)) = B0 (B1 Z). Proof. reflexivity. Qed.
Example test_bin_incr2 : (incr (B0 (B1 Z))) = B1 (B1 Z). Proof. reflexivity. Qed.
Example test_bin_incr3 : (incr (B1 (B1 Z))) = B0 (B1 (B1 Z)). Proof. reflexivity. Qed.
Example test_bin_incr4 : bin_to_nat (B0 (B1 Z)) = 2. Proof. reflexivity. Qed.
Example test_bin_incr5 : bin_to_nat (incr (B1 Z)) = 1 + bin_to_nat (B1 Z). Proof. reflexivity. Qed.
Example test_bin_incr6 :  bin_to_nat (incr (incr (B1 Z))) = 2 + bin_to_nat (B1 Z). Proof. reflexivity. Qed.
