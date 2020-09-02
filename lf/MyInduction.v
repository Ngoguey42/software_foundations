
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
Theorem mult_0_r : forall n : nat,  n * 0 = 0.
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
Theorem plus_swap : forall n m p : nat,
    n + (m + p) = m + (n + p).
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
Theorem mult_comm : forall n m : nat,
    m * n = n * m.
Proof.
  intros n m.

  assert (mult0: forall x : nat, x * 0 = 0). {
    intros x.
    induction x as [|x' IHx'].
    - reflexivity.
    - simpl. rewrite -> IHx'. reflexivity.
  }

  assert (S0_is_plus1 : forall x : nat, S x = x + 1). {
    intros x.
    induction x as [|x' IHx'].
    - reflexivity.
    - simpl. rewrite -> IHx'. reflexivity.
  }

  assert (mult_plus1: forall x y : nat, x * (1 + y) = x * y + x). {
    intros x y.
    induction x as [|x' IHx'].
    - simpl. reflexivity.
    - {
        assert (H: S x' = x' + 1). { rewrite -> S0_is_plus1. reflexivity. }
        assert (H': 1 + y = y + 1). { rewrite -> plus_comm. reflexivity. }

        simpl.



        (* rewrite -> H. *)
        (* rewrite <- H'. *)
        (* rewrite -> IHx'. *)
        (* rew *)

        (* rewrite -> S0_is_plus1. *)
        (* simpl. rewrite -> IHx'. *)
      }
  }


  induction n as [|n' IHn'].
  - simpl. rewrite -> mult0. reflexivity.
  -



  - simpl.

Qed.
(* ************************************************************************** *)
(* ************************************************************************** *)
(* ************************************************************************** *)
