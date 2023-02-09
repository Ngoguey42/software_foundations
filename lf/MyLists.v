(* ************************************************************************** *)
(* ************************************************************************** *)
(* Pairs of Numbers *)
Module NatList.
Inductive natprod : Type :=
| pair (n1 n2 : nat).
Check (pair 3 2) : natprod.
Definition fst (p : natprod) : nat :=
  match p with
  | pair x _ => x
  end.
Definition snd (p : natprod) : nat :=
  match p with
  | pair _ y => y
  end.
Compute (fst (pair 2 3)) : nat.
Notation "( x , y )" := (pair x y).
Compute (fst (2, 3)) : nat.
Definition fst' (p : natprod) : nat :=
  match p with
  | (x,y) => x
  end.
Definition snd' (p : natprod) : nat :=
  match p with
  | (x,y) => y
  end.
Definition swap_pair (p : natprod) : natprod :=
  match p with
  | (x,y) => (y,x)
  end.
Theorem surjective_impairing' : forall (n m : nat),
    (n, m) = (fst (n, m), snd (n, m)).
Proof.  reflexivity.
Qed.
Theorem surjective_impairing : forall (p : natprod),
    p = (fst p, snd p).
Proof.
  intros p.
  destruct p as [n m].
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard (snd_fst_is_swap) *)
Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Exercise: 1 star, standard, optional (fst_swap_is_snd) *)
Theorem fst_swap_is_snd : forall (p : natprod),
    fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as [n m].
  simpl.
  reflexivity.
Qed.

(* ************************************************************************** *)
(* Lists of Numbers *)
Inductive natlist : Type :=
| nil
| cons (n : nat) (l : natlist).
Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Notation "x :: l" := (cons x l)
                       (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S count => n :: (repeat n count)
  end.
Fixpoint length (l : natlist) : nat :=
  match l with
  | [] => 0
  | _ :: tl => 1 + length tl
  end.
Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
  | [] => l2
  | hd :: tl => hd :: (app tl l2)
  end.
Notation "x ++ y" := (app x y)
                       (right associativity, at level 60).
Example test_app1 : [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2 : nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3 : [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.
Definition hd (default : nat) (l :natlist) : nat :=
  match l with
  | [] => default
  | hd :: _ => hd
  end.
Definition tl (l : natlist) : natlist :=
  match l with
  | [] => []
  | _ :: tl => tl
  end.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, especially useful (list_funs) *)
Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
  | [] => []
  | 0 :: tl => nonzeros tl
  | hd :: tl => hd :: nonzeros tl
  end.
Example test_nonzeros :
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
Proof. simpl. reflexivity. Qed.
Fixpoint is_odd (n : nat) : bool :=
  match n with
  | 0 => false
  | 1 => true
  | S (S n) => is_odd n
  end.
Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
  | [] => []
  | hd :: tl =>
    if is_odd hd then hd :: oddmembers tl
    else oddmembers tl
  end.
Example test_oddmembers :
  oddmembers [0;1;0;2;3;0;0] = [1;3].
Proof. reflexivity. Qed.
Definition countoddmembers (l : natlist) : nat :=
  length (oddmembers l).
Example test_countoddmembers1:
  countoddmembers [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers2:
  countoddmembers [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers3:
  countoddmembers nil = 0.
Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, advanced (alternate) *)
Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
  | [], [] => []
  | [], l2 => l2
  | l1, [] => l1
  | hd1 :: tl1, hd2 :: tl2 => hd1 :: hd2 :: (alternate tl1 tl2)
  end.
Example test_alternate1:
  alternate [1;3;5] [2;4;6] = [1;2;3;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity. Qed.
Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity. Qed.
Example test_alternate4:
  alternate [] [20;30] = [20;30].
Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, especially useful (bag_functions) *)
Definition bag := natlist.
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
  | [] => 0
  | hd :: tl =>
    if Nat.eqb hd v then 1 + count v tl
    else count v tl
  end.
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.
Definition sum : bag -> bag -> bag := app.
Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.
Definition add (v : nat) (s : bag) : bag := v :: s.
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.
Fixpoint member (v : nat) (s : bag) : bool :=
  match s with
  | [] => false
  | hd :: tl =>
    if Nat.eqb hd v then true
    else member v tl
  end.
Example test_member1: member 1 [1;4;1] = true.
Proof. reflexivity. Qed.
Example test_member2: member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 3 stars, standard, optional (bag_more_functions) *)
Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
  | [] => []
  | hd :: tl =>
    if Nat.eqb hd v then tl
    else hd :: remove_one v tl
  end.
Example test_remove_one1:
  count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:
  count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:
  count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:
  count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.
Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
  | [] => []
  | hd :: tl =>
    if Nat.eqb hd v then remove_all v tl
    else hd :: remove_all v tl
  end.
Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.
Fixpoint included (s1 : bag) (s2 : bag) : bool :=
  match s1 with
  | [] => true
  | hd :: tl =>
    if member hd s2 then included tl (remove_one hd s2)
    else false
  end.
Example test_included1: included [1;2] [2;1;4;1] = true.
Proof. reflexivity. Qed.
Example test_included2: included [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

(* ************************************************************************** *)
(* Exercise: 2 stars, standard, especially useful (add_inc_count) *)
Theorem eq_n_n_true : forall n : nat,
    Nat.eqb n n = true.
Proof.
  intros n.
  induction n as [|n' IHn].
  - reflexivity.
  - simpl. rewrite -> IHn. reflexivity.
Qed.
Theorem add_inc_count : forall (n : nat) (s : bag),
    count n s + 1 = count n (n :: s) .
Proof.
  intros n s.
  induction s as [|n' s' IHs].
  - simpl.
    rewrite -> eq_n_n_true.
    reflexivity.
  - simpl.
    rewrite -> eq_n_n_true.
    assert (H: forall a, S a = a + 1). {
      intros a.
      induction a as [|a IHa].
      - reflexivity.
      - simpl. rewrite <- IHa. reflexivity.
    }
    rewrite <- H.
    reflexivity.
Qed.

(* ************************************************************************** *)
(* Reasoning About Lists *)
