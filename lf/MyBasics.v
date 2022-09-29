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

(* Exercise: 1 star, standard (nandb) - experiments *)
Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.
Definition andb (b c : bool) : bool :=
  match b, c with
  | true, true => true
  | _, _ => false
  end.
Definition nandb_bis (b c : bool) : bool := notb (andb b c).
Theorem nandbs_equivalents : forall b c : bool,
    (nandb b c) = (nandb_bis b c).
Proof.
  intros b c.
  destruct b, c.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

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
  intros [].
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
  intros [].
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
(* Exercise: 3 stars, standard, optional (andb_eq_orb)

false & false = false | false  ||| false = false
 true &  true =  true | true   ||| true = true

 true & false =  true | false  ||| false = true
false &  true = false | true   ||| false = true *)
Theorem andb_eq_orb_cheat : forall b c, andb b c = orb b c -> b = c.
Proof.
  intros b c.
  destruct b, c.
  - reflexivity.
  - simpl. intros H. rewrite -> H.  reflexivity.
  - simpl. intros H. rewrite -> H.  reflexivity.
  - reflexivity.
Qed.
Theorem andb_eq_orb_cheat2 : forall b c, andb b c = orb b c -> b = c.
Proof.
intros [|] [|] H.
- reflexivity.
- simpl in H. rewrite H. reflexivity.
- simpl in H. exact H.
- reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard (binary) *)

(* bin *)
Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin).
Definition zero_bin : bin := Z.
Definition one_bin : bin := B1 Z.
Definition two_bin : bin := B0 one_bin.
Definition three_bin : bin := B1 one_bin.
Definition four_bin : bin := B0 two_bin.
Definition five_bin : bin := B1 two_bin.
Definition six_bin : bin := B0 three_bin.
Definition seven_bin : bin := B1 three_bin.
Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.
Example test_bin_incr0 : incr zero_bin = one_bin. Proof. reflexivity. Qed.
Example test_bin_incr1 : incr one_bin = two_bin. Proof. reflexivity. Qed.
Example test_bin_incr2 : incr two_bin = three_bin. Proof. reflexivity. Qed.
Example test_bin_incr3 : incr three_bin = four_bin. Proof. reflexivity. Qed.
Example test_bin_incr4 : incr four_bin = five_bin. Proof. reflexivity. Qed.
Example test_bin_incr5 : incr five_bin = six_bin. Proof. reflexivity. Qed.
Example test_bin_incr6 : incr six_bin = seven_bin. Proof. reflexivity. Qed.

(* conversions *)
Fixpoint bin_to_nat' (m : bin) (weight : nat) : nat :=
  match m with
  | Z => O
  | B1 m' => weight + bin_to_nat' m' (weight * 2)
  | B0 m' => bin_to_nat' m' (weight * 2)
  end.
Definition bin_to_nat (m : bin) : nat := bin_to_nat' m 1.
Definition zero_nat : nat := O.
Definition one_nat : nat := S zero_nat.
Definition two_nat : nat := S one_nat.
Definition three_nat : nat := S two_nat.
Definition four_nat : nat := S three_nat.
Definition five_nat : nat := S four_nat.
Definition six_nat : nat := S five_nat.
Definition seven_nat : nat := S six_nat.
Example test_bin_to_nat_0 : bin_to_nat zero_bin = zero_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_1 : bin_to_nat one_bin = one_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_2 : bin_to_nat two_bin = two_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_3 : bin_to_nat three_bin = three_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_4 : bin_to_nat four_bin = four_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_5 : bin_to_nat five_bin = five_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_6 : bin_to_nat six_bin = six_nat. Proof. reflexivity. Qed.
Example test_bin_to_nat_7 : bin_to_nat seven_bin = seven_nat. Proof. reflexivity. Qed.

(* experiments *)
Fixpoint decr (m : bin) : bin :=
  match m with
  | Z => Z
  | B1 Z => Z
  | B0 (B1 Z) => B1 Z
  | B1 x => B0 x
  | B0 x => B1 (decr x)
  end.
Example test_bin_decr0 : decr zero_bin = zero_bin. Proof. reflexivity. Qed.
Example test_bin_decr1 : decr one_bin = zero_bin. Proof. reflexivity. Qed.
Example test_bin_decr2 : decr two_bin = one_bin. Proof. reflexivity. Qed.
Example test_bin_decr3 : decr three_bin = two_bin. Proof. reflexivity. Qed.
Example test_bin_decr4 : decr four_bin = three_bin. Proof. reflexivity. Qed.
Example test_bin_decr5 : decr five_bin = four_bin. Proof. reflexivity. Qed.
Example test_bin_decr6 : decr six_bin = five_bin. Proof. reflexivity. Qed.
Example test_bin_decr7 : decr seven_bin = six_bin. Proof. reflexivity. Qed.
Theorem incr_decr_inverse : forall x, decr (incr x) = x.
Proof.
Admitted.

(* experiments *)
Fixpoint nat_to_bin (x : nat) : bin :=
  match x with
  | O => Z
  | S x => incr (nat_to_bin x)
  end.
Theorem bin_to_nat_to_bin : forall x : bin, nat_to_bin (bin_to_nat x) = x.
Proof.
Admitted.
