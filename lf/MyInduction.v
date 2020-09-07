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
