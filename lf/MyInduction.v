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
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard (eqb_refl) *)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
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
Fixpoint eqb' (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S n', S m' => eqb' n' m'
  | _, _ => false
end.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.
Notation "x =? y" := (eqb' x y) (at level 70) : nat_scope.
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
Fixpoint incr (m : bin) : bin :=
  match m with
  | Z => B1 Z
  | B0 n => B1 n
  | B1 n => B0 (incr n)
  end.
Fixpoint bin_to_nat (m : bin) : nat :=
  match m with
  | Z => O
  | B1 m' => 2 * (bin_to_nat m') + 1
  | B0 m' => 2 * (bin_to_nat m')
  end.
Theorem bin_to_nat_pres_incr : forall b : bin,
    bin_to_nat (incr b) = 1 + bin_to_nat b.
Proof.
  assert (H: forall a, S a = a + 1). {
    intros a.
    induction a as [|a IHa].
    - reflexivity.
    - simpl. rewrite <- IHa. reflexivity.
  }
  intros b.
  induction b as [|b IHb|b IHb].
  - reflexivity.
  - {
      simpl.
      rewrite <- H.
      reflexivity.
    }
  - {
      simpl.
      rewrite -> IHb.
      simpl.
      rewrite <- plus_n_O.
      rewrite <- plus_assoc.
      rewrite <- H.
      reflexivity.
    }
Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard (nat_bin_nat) *)
Fixpoint nat_to_bin (x : nat) : bin :=
  match x with
  | O => Z
  | S x => incr (nat_to_bin x)
  end.
Theorem incr_and_nat_to_bin : forall n, nat_to_bin (S n) = incr (nat_to_bin n).
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - { simpl. reflexivity. }
Qed.
Theorem nat_bin_nat : forall n, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - {
      rewrite -> incr_and_nat_to_bin.
      rewrite -> bin_to_nat_pres_incr.
      rewrite -> IHn.
      reflexivity.
    }
Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, advanced (double_bin) *)
(* plus_n_Sm: forall n m : nat, S (n + m) = n + S m *)
(* plus_Sn_m: forall n m : nat, S n + m = S (n + m) *)
Lemma double_incr : forall n : nat, double (S n) = S (S (double n)).
Proof.
  intros n.
  induction n as [|n IHn].
  - reflexivity.
  - {
      rewrite -> IHn.
      rewrite -> double_plus.
      rewrite -> double_plus.
      rewrite <- plus_n_Sm.
      rewrite <- plus_n_Sm.
      rewrite -> plus_Sn_m.
      rewrite -> plus_Sn_m.
      reflexivity.
    }
Qed.

Definition double_bin (b:bin) : bin
(* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Example double_bin_zero : double_bin Z = Z.
(* FILL IN HERE *) Admitted.

Lemma double_incr_bin : forall b,
    double_bin (incr b) = incr (incr (double_bin b)).
Proof.
  (* FILL IN HERE *) Admitted.

(* ************************************************************************** *)
(* Exercise: 4 stars, advanced (bin_nat_bin) *)

Fixpoint normalize (b:bin) : bin
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Theorem bin_nat_bin : forall b, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  (* FILL IN HERE *) Admitted.

(* ************************************************************************** *)
