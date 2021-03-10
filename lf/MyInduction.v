Require Arith. (* Required at toplevel, but not imported yet *)

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, especially useful (basic_induction) *)
Theorem plus_n_O : forall n : nat,
    n = n + 0.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.
Theorem mult_0_r : forall n : nat, n * 0 = 0.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
Theorem plus_comm : forall n m : nat, n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - rewrite <- plus_n_Sm. simpl. rewrite <- IHn'. reflexivity.
Qed.
Theorem plus_assoc : forall n m p : nat, n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard (double_plus) *)
Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.
Theorem double_plus : forall n : nat, double n = n + n.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. simpl. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, optional (evenb_S) *)
Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.
Theorem evenb_S : forall n : nat, evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - {
      rewrite -> IHn'.
      simpl.
      assert (invol: forall b : bool, negb (negb b) = b). {
        intros n. destruct n. - reflexivity. - reflexivity.
      }
      rewrite -> invol.
      reflexivity.
    }
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, especially useful (mult_comm) *)
Theorem plus_swap : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: m + (n + p) = m + n + p). {
    rewrite <- plus_assoc. reflexivity.
  }
  rewrite -> H.
  assert (H': m + n = n + m). {
    rewrite -> plus_comm. reflexivity.
  }
  rewrite -> H'.
  reflexivity.
Qed.
Theorem mult_n_Sm : forall n m : nat, m * S n = m + m * n.
Proof.
  intros n m.
  induction m as [|m' IHm'].
  - reflexivity.
  - simpl.
    rewrite -> IHm'.
    rewrite -> plus_assoc.
    assert (H: n + m' = m' + n).
    { rewrite -> plus_comm. reflexivity. }
    rewrite -> H.
    rewrite -> plus_assoc.
    reflexivity.
Qed.
Theorem mult_comm : forall n m : nat, m * n = n * m.
Proof.
  intros n m.

  induction n as [|n' IHn'].
  - rewrite -> mult_0_r. simpl. reflexivity.
  - {
      rewrite -> mult_n_Sm.
      rewrite -> IHn'.
      simpl. (* Magic simplification *)
      reflexivity.
    }
Qed.
Module Again0.
  Import Arith.
  Theorem mult_comm : forall n m : nat, m * n = n * m.
  Proof.
    intros n m.
    ring.
Qed.
End Again0.
Module Again1.
  Theorem mult_comm : forall n m : nat, m * n = n * m.
  Proof.
    (* I didn't find a way to make it work with `intros n m` *)
    (* intros n m. *)
    induction n as [|n' IHn']; induction m as [|m' IHm'].
    - reflexivity.
    - simpl. rewrite -> IHm'. reflexivity.
    - simpl. rewrite <- IHn'. reflexivity.
    - simpl.
      rewrite <- IHn'.
      rewrite -> IHm'.
      simpl.
      rewrite -> IHn'.
      rewrite -> plus_assoc.
      rewrite -> plus_assoc.
      assert (H: n' + m' = m' + n').
      { rewrite -> plus_comm. reflexivity. }
      rewrite -> H.
      reflexivity.
  Qed.
End Again1.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, optional (more_exercises) *)
Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O, O | O, S _ => true
  | S _, O => false
  | S n', S m' => leb n' m'
end.
Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb n' m'
  | _, _ => false
end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Theorem leb_refl : forall n : nat, true = (n <=? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.
Theorem zero_nbeq_S : forall n : nat, 0 =? (S n) = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
Theorem andb_false_r : forall b : bool, andb b false = false.
Proof.
  intros b.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed.
Theorem plus_ble_compat_l : forall n m p : nat,
    n <=? m = true ->
    (p + n) <=? (p + m) = true.
Proof.
  intros n m p H.
  simpl.
  induction p as [|p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.
Theorem S_nbeq_0 : forall n : nat, (S n) =? 0 = false.
Proof.
  intros n.
  simpl.
  reflexivity.
Qed.
Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n.
  simpl.
  rewrite -> plus_comm.
  simpl.
  reflexivity.
Qed.
Theorem all3_spec : forall b c : bool,
    orb (andb b c) (orb (negb b) (negb c)) = true.
Proof.
  intros b c.
  destruct b; destruct c.
  reflexivity. reflexivity. reflexivity. reflexivity.
Qed.
Theorem plus_comm_acb : forall a b c : nat, a + b + c = a + c + b.
Proof.
  intros a b c.
  induction c as [|c' IHc'].
  - rewrite <- 2! plus_n_O. reflexivity.
  - rewrite <- 2! plus_n_Sm.
    simpl.
    rewrite -> IHc'. reflexivity.
Qed.
Theorem plus_comm_acbd : forall a b c d : nat, a + b + c + d = a + c + b + d.
Proof.
  intros a b c.
  rewrite -> plus_comm_acb.
  reflexivity.
Qed.
Theorem mult_plus_distr_r : forall n m p : nat,
    (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p' IHp'].
  - simpl.
    rewrite -> 3! mult_0_r.
    reflexivity.
  - rewrite -> mult_n_Sm.
    rewrite -> IHp'.
    rewrite -> 2! mult_n_Sm. (* kill successors on the right *)
    rewrite -> 2! plus_assoc. (* kill parentheses *)
    rewrite -> plus_comm_acbd.
    reflexivity.
Qed.
Theorem mult_assoc : forall a b c : nat, a * (b * c) = (a * b) * c.
Proof.
  intros a b c.
  induction a as [|a IHa].
  - simpl. reflexivity.
  - simpl.
    rewrite -> IHa.
    rewrite <- mult_plus_distr_r.
    reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, optional (eqb_refl) *)
Theorem eqb_refl : forall n : nat, true = (n =? n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, optional (plus_swap') *)
Theorem plus_swap' : forall n m p : nat, n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  replace (n + (m + p)) with (n + m + p).
  replace (n + m) with (m + n).
  replace (m + n + p) with (m + (n + p)).
  reflexivity.
  rewrite -> plus_assoc. reflexivity.
  rewrite <- plus_comm. reflexivity.
  rewrite -> plus_assoc. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, especially useful (binary_commute) *)
Inductive bin : Type :=
| Z
| B0 (n : bin)
| B1 (n : bin)
.

  (* | B1 (B0 Z) => B1 (B1 Z) *)
  (* | B1 Z      => B1 (B1 Z) *)
  (* | B1 (B1 m') => incr B1 m' *)

Definition zero :=                      Z.
Definition zero' :=                  B0 Z.
Definition zero'' :=             B0 (B0 Z).
Definition one :=                    B1 Z.
Definition one' :=               B1 (B0 Z).
Definition one'' :=          B1 (B0 (B0 Z)).
Definition two :=                B0 (B1 Z).
Definition two' :=           B0 (B1 (B0 Z)).
Definition two'' :=      B0 (B1 (B0 (B0 Z))).
Definition three :=              B1 (B1 Z).
Definition three' :=         B1 (B1 (B0 Z)).
Definition three'' :=    B1 (B1 (B0 (B0 Z))).
Definition four :=           B0 (B0 (B1 Z)).
Definition four' :=      B0 (B0 (B1 (B0 Z))).
Definition four'' := B0 (B0 (B1 (B0 (B0 Z)))).

Inductive parent : Type :=
| Root
| All1
| Some0
.

Inductive child : Type :=
| All0
| Some1
.

(* Fixpoint _incr (all_ones_before : bool) (m : bin) : (bool * bin) := *)
(*   match all_ones_before, m with *)
(*   | true, B1 m' => *)
(*     (match _incr true m' with *)
(*     | true => (true, Z) *)
(*     | false => (true, Z) *)
(*     end) *)
(*   | true, _ => (true, Z) *)
(*   | false, _ => (true, Z) *)
(*   end. *)

Fixpoint _incr (p : parent) (m : bin) : (bin * child) :=
  match p, m with
  | Root, B1 m' =>
    match _incr All1 m' with
    | (n, All0) => (Z, Some1) (* absurd *)
    | (n, Some1) => (Z, Some1)
    end
  | All1, B1 m' =>
    match _incr All1 m' with
    | (n, All0) => (Z, Some1)
    | (n, Some1) => (Z, Some1)
    end
  | Some0, B1 m' =>
    match _incr Some0 m' with
    | (n, All0) => (Z, Some1)
    | (n, Some1) => (Z, Some1)
    end
  | Root, B0 m' =>
    match _incr Some0 m' with
    | (n, All0) => (Z, Some1)
    | (n, Some1) => (Z, Some1)
    end
  | All1, B0 m' =>
    match _incr Some0 m' with
    | (n, All0) => (Z, Some1)
    | (n, Some1) => (Z, Some1)
    end
  | Some0, B0 m' =>
    match _incr Some0 m' with
    | (n, All0) => (Z, Some1)
    | (n, Some1) => (Z, Some1)
    end
  | Root, Z => (B1 Z, Some1) (* 0 + 1 *)
  | All1, Z => (B1 Z, Some1)
  | Some0, Z => (Z, All0)

  end.

Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 m' => B1 m'
  | B1 m' => B0 (B1 m)
  end.
Example test0 : (incr zero) = one. Proof. reflexivity. Qed.
Example test1 : (incr one) = two. Proof. compute. reflexivity. Qed.
Example test2 : (incr two) = three. Proof. reflexivity. Qed.
Example test3 : (incr three) = four. Proof. reflexivity. Qed.

Fixpoint _bin_to_nat (m : bin) (weight : nat) : nat :=
  match m with
  | Z => O
  | B1 m' => weight + _bin_to_nat m' (weight * 2)
  | B0 m' => _bin_to_nat m' (weight * 2)
  end.
Definition bin_to_nat (m : bin) : nat := _bin_to_nat m 1.


Example test0 : bin_to_nat zero = 0. Proof. reflexivity. Qed.
Example test1 : bin_to_nat one = 1. Proof. reflexivity. Qed.
Example test2 : bin_to_nat two = 2. Proof. reflexivity. Qed.
Example test3 : bin_to_nat three = 3. Proof. reflexivity. Qed.
Example test4 : bin_to_nat four = 4. Proof. reflexivity. Qed.


Example test1 : bin_to_nat (incr Z) = 1. Proof. reflexivity. Qed.
Example test1' : bin_to_nat (B1 Z) = 1. Proof. reflexivity. Qed.
Example test2 : bin_to_nat (incr (incr Z)) = 2. Proof. reflexivity. Qed.
Example test2' : bin_to_nat (incr (B1 Z)) = 2. Proof. reflexivity. Qed.
Example test2'' : bin_to_nat (B0 (B1 Z)) = 2. Proof. reflexivity. Qed.

Theorem bin_to_nat_pres_incr : forall b : bin, bin_to_nat (incr b) = S (bin_to_nat b).
Proof.
  intros b.
  destruct b.
  - simpl. compute. reflexivity.
  - simpl.

    replace (bin_to_nat Z) with 0.
    replace (bin_to_nat (B0 Z)) with 1.
    reflexivity.
    compute.


Qed.

Theorem truc : forall b


(* ************************************************************************** *)
