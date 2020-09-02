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
(* ************************************************************************** *)
(* ************************************************************************** *)
