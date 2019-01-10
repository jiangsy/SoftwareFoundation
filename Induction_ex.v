Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.  Qed.


Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

(* may have simpler solution *)
Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite <- plus_n_Sm.
    induction m as [|m' IHm'].
    + simpl. rewrite <- plus_n_O. reflexivity. 
    + rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.

Lemma double_plus : forall n, double n = n + n .
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity.
Qed.

Theorem evenb_S : forall n : nat,
  evenb (S n) = negb (evenb n).
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite -> IHn'. simpl.  rewrite -> negb_involutive. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H0: n + (m + p) = n + m + p). {rewrite -> plus_assoc. reflexivity. }
  rewrite -> H0.
  assert (H1: n + m = m + n). {rewrite -> plus_comm. reflexivity. }
  rewrite -> H1.
  rewrite -> plus_assoc.
  reflexivity.
Qed.

(* note: induction on m not n ! *)
Theorem mult_m_Sn : forall m n : nat,
  m * S n = m * n + m.
Proof.
  intros m n.
  induction m as [|m' IHm'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHm'. rewrite -> plus_n_Sm. rewrite -> plus_n_Sm. rewrite -> plus_assoc. reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - rewrite -> mult_0_r. simpl. reflexivity.
  - simpl. rewrite -> mult_m_Sn. rewrite -> IHn'. rewrite <- plus_comm. reflexivity.
Qed.


Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem leb_refl : forall n:nat,
  true = leb n n.
Proof.
  intro n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite <- IHn'. reflexivity.
Qed.

Theorem zero_nbeq_S : forall n:nat,
  beq_nat 0 (S n) = false.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem andb_false_r : forall b : bool,
  andb b false = false.
Proof.
  intros b.
  destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem plus_ble_compat_l : forall n m p : nat,
  leb n m = true -> leb (p + n) (p + m) = true.
Proof.
  intros n m p.
  intros H.
  induction p as [|p' IHp'].
  - simpl. rewrite -> H. reflexivity.
  - simpl. rewrite -> IHp'. reflexivity.
Qed.


Theorem S_nbeq_0 : forall n:nat,
  beq_nat (S n) 0 = false.
Proof.
  intros n.
  destruct n as [|n'].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.


Theorem mult_1_l : forall n:nat, 1 * n = n.
Proof.
  intros n.
  destruct n as [|n'].
  - simpl. reflexivity.
  - simpl. rewrite -> plus_n_O. simpl. reflexivity.
Qed.


Theorem all3_spec : forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
               (negb c))
  = true.
Proof.
  intros b c.
  destruct b.
  destruct c.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.
 

Theorem mult_plus_distr_r : forall n m p : nat,
  (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p.
  induction p as [|p' IHp'].
  - rewrite -> mult_0_r. rewrite -> mult_0_r. rewrite -> mult_0_r. simpl. reflexivity.
  - rewrite -> mult_m_Sn. rewrite -> mult_m_Sn. rewrite -> mult_m_Sn.
    rewrite -> IHp'.  
    rewrite <- plus_assoc.  
    assert (H0: m * p' + (n + m) =  n + (m * p' + m)). {rewrite -> plus_swap. reflexivity. }
    rewrite -> H0. rewrite -> plus_assoc. reflexivity.
Qed.


Theorem mult_assoc : forall n m p : nat,
  n * (m * p) = (n * m) * p.
Proof.
  intros n m p.
  induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> mult_plus_distr_r. rewrite -> IHn'. reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite -> IHn'. reflexivity.
Qed.
