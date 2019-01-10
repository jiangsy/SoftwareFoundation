Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
   intros b.
   intros c.
   destruct b. 
   - destruct c.
     + reflexivity.
     + intros H.
       rewrite <- test_orb1.
       rewrite <- test_andb1. 
       rewrite -> H.
       reflexivity.
   - destruct c.
     + intros H.
       rewrite <- test_orb3.
       rewrite <- test_andb3.
       rewrite -> H.
       reflexivity.
     + reflexivity.
Qed.

Inductive binary : Type :=
    | Zero : binary
    | Twice : binary -> binary
    | TwicePlusOne : binary -> binary.

Fixpoint  incr ( b: binary) : binary :=
    match b with
    | Zero => TwicePlusOne Zero
    | Twice b' => TwicePlusOne b'
    | TwicePlusOne b' => Twice (incr b')
    end.

Fixpoint  bin_to_nat ( b: binary) : nat :=
    match b with
    | Zero => 0
    | Twice b' =>  mult (bin_to_nat b') 2
    | TwicePlusOne b' => 1 + mult (bin_to_nat b') 2
    end.