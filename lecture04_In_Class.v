(* 
  Lemma `zero_in_middle_v0` proves that `n + 0 + m = n + m` for any natural numbers n and m.
  This is proven by induction on `n`, simplifying the base and inductive cases.

  rewrite -> IHn rewrites from left to right using the inductive hypothesis.
  rewrite <- IHn would rewrite in the reverse direction (from right to left).
  rewrite IHn without the arrow defaults to left-to-right rewriting.


*)
Lemma zero_in_middle_v0:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.             (* Introduce `n` and `m` into the proof context. *)
  induction n.        (* Perform induction on `n`. Base case: `n = 0`, Inductive case: `n = S n'`. *)
  - simpl.            (* In the base case, simplify `0 + 0 + m` to `m`. *)
    reflexivity.      (* The goal `m = m` is trivially true, so reflexivity concludes the proof. *)
  - simpl.            (* In the inductive case, simplify `(S n') + 0 + m` to `S (n' + 0 + m)`. *)
    rewrite <- IHn.      (* Apply the inductive hypothesis, reducing `n' + 0 + m` to `n' + m`. *)
    reflexivity.      (* Now `S (n' + m) = S (n' + m)` is trivially true, so reflexivity concludes. *)
Qed.

(* In class  note 
 - Lemma. is  cheap version of theorem. 
 -  reflexivity also simplify 
 - The indentation separate the  differengt subproof that we are defining
 -  We can use Check or Print to test result of theorem  *)



 (* YAn made this below  exo in class *)

Lemma add_assoc: 
   forall n  m o, (n + m ) + o = n + (m + o).
    
   Proof. 
    intros. 
    induction n.
    - simpl. 
      reflexivity.
    - simpl.
      rewrite IHn. 
      reflexivity.
   Qed.



     





(* 
  Lemma `zero_in_middle_v1` also proves that `n + 0 + m = n + m`, but instead of using direct induction,
  it asserts a helper lemma about `n + 0 = n`, applies it, and then finishes the proof.
*)
Lemma zero_in_middle_v1:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.             (* Introduce `n` and `m` into the proof context. *)
  assert (Hx: n + 0 = n). { (* Assert a helper lemma: `n + 0 = n`. *)
    rewrite <- plus_n_O.    (* Use the standard theorem `plus_n_O` which states `n + 0 = n`. *)
    reflexivity.            (* Complete the proof of the helper lemma `n + 0 = n`. *)
  }
  rewrite Hx.         (* Rewrite `n + 0 + m` using `Hx`, converting it to `n + m`. *)
  reflexivity.        (* The goal `n + m = n + m` is trivially true, reflexivity concludes. *)
Qed.
Lemma zero_in_middle_v1_2:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.             (* Introduce `n` and `m` into the proof context. *)
  rewrite <- plus_n_O.
  reflexivity.      (* Rewrite `n + 0 + m` using `Hx`, converting it to `n + m`. *)
          (* The goal `n + m = n + m` is trivially true, reflexivity concludes. *)
Qed.
 (*You can use the  rewrite directly to replace any part of your code  by  your theorem *)








(* Assert:  you define another proof in o your proof. and  you have to define the  proof 
            *)
(* 
  Lemma `n_plus_zero_eq_n` proves that `n + 0 = n` for any natural number `n`.
  This lemma uses `plus_n_O`, a known theorem stating this property.
*)
Lemma n_plus_zero_eq_n:
  forall n, n + 0 = n.
Proof.
  intros.             (* Introduce `n` into the proof context. *)
  rewrite <- plus_n_O.    (* Use the theorem `plus_n_O`, which states `n + 0 = n`. *)
  reflexivity.        (* The goal is now trivially true, reflexivity concludes the proof. *)
Qed.







(* 
  Lemma `zero_in_middle_v2` proves that `n + 0 + m = n + m`.
  This time, it calls the lemma `n_plus_zero_eq_n` to simplify `n + 0` to `n`.
*)
Lemma zero_in_middle_v2:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.                 (* Introduce `n` and `m` into the proof context. *)
  rewrite n_plus_zero_eq_n.  (* Rewrite `n + 0 + m` as `n + m` using `n_plus_zero_eq_n`. *)
  reflexivity.            (* The goal `n + m = n + m` is trivially true, so reflexivity concludes. *)
Qed.







(* 
  Lemma `add_assoc` is another version of the addition associativity proof.
  It simplifies the problem without needing extra assertions.
*)
Lemma add_assoc_1:
  forall n m o, (n + m) + o = n + (m + o).
Proof.
  intros.              (* Introduce `n`, `m`, and `o` into the proof context. *)
  induction n.         (* Perform induction on `n`. *)
  - simpl.             (* Base case: simplify `(0 + m) + o` to `m + o`. *)
    reflexivity.       (* `m + o = m + o` is trivially true, so reflexivity concludes the base case. *)
  - simpl.             (* Inductive case: simplify `(S n + m) + o`. *)
    rewrite IHn.       (* Apply the inductive hypothesis: `(n + m) + o = n + (m + o)`. *)
    reflexivity.       (* The goal `S n + (m + o) = S (n + (m + o))` is trivially true. *)
Qed.







(* 
  Lemma `zero_in_middle_v3` is another version of proving `n + 0 + m = n + m`,
  using associativity and previous lemmas.
*)
Lemma zero_in_middle_v3:
  forall n m, n + 0 + m = n + m.
Proof.
  intros.                     (* Introduce `n` and `m` into the proof context. *)
  assert (Ha := add_assoc). (* Assert the associativity lemma `add_assoc_v2`. *)
  assert (Ha1 := Ha n).        (* Apply associativity to `n`. *)
  assert (Ha2 := Ha1 0).       (* Apply associativity to `n + 0`. *)
  assert (Ha3 := Ha2 m).       (* Apply associativity to the entire expression `n + 0 + m`. *)
  rewrite (add_assoc n 0 m). (* Directly rewrite the goal using `add_assoc_v2`. *)
  simpl.                      (* Simplify the goal, leaving `n + m = n + m`. *)
  reflexivity.                (* Trivially true, so reflexivity concludes the proof. *)
Qed.



(* 
  Goal demonstrating basic logical reasoning: proving that if `a = b` and `b = c`,
  then `a = c`. This is a simple example of transitivity of equality.
  This proof is a direct demonstration of the transitivity of equality.
*)
Goal
  forall (a b c : nat),
  a = b ->             (* Assumption that `a = b`. *)
  b = c ->             (* Assumption that `b = c`. *)
  a = c.               (* Goal: prove `a = c`. *)
Proof.
  intros.              (* Introduce `a`, `b`, `c`, and the hypotheses into the proof context. *)
  rewrite H.           (* Rewrite `a` with `b` in the goal using the hypothesis `a = b`. *)
  rewrite H0.            (* Use the hypothesis `b = c` to conclude that `a = c`. *)
  reflexivity.
Qed.






(* 
  Goal demonstrating basic logical reasoning: proving that if `a = b` and `b = c`,
  then `a = c`. This is a simple example of transitivity of equality.

 This proof involves a conditional hypothesis about equality, which is also valid but slightly more complex.

  *)
Goal
  forall (a b c:nat),
  a = b ->             (* Assumption that `a = b`. *)
  (a = b -> b = c) ->  (* Assumption that `b = c` follows from `a = b`. *)
  b = c.               (* Goal: prove `b = c`. *)
Proof.
  intros.              (* Introduce `a`, `b`, `c`, and the hypotheses into the proof context. *)
  assert (Ha := H0 H). (* Assert `Ha` as the result of applying the second hypothesis to the first. *)
  rewrite Ha.          (* Rewrite the goal using `Ha`. *)
  reflexivity.         (* Trivially true, so reflexivity concludes the proof. *)
Qed.

(* 
  Define an inductive type `natprod`, which represents a pair of two natural numbers.
  We introduce a constructor `pair` to create pairs of numbers.
*)
Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

(* 
  Introduce a notation `(x, y)` to make pairs more readable. 
  Instead of writing `pair x y`, you can now use `(x, y)`.
*)
Notation "( x , y )" := (pair x y).

(* Compute the pair (1, 2) using the new notation. *)
Compute (1, 2).

(* 
  Define a function `fst` to get the first element of a pair.
  The function matches a `pair` and returns the first component `x`.
*)
Definition fst (p : natprod) : nat :=
  match p with
  | pair x y => x    (* For a pair `(x, y)`, return `x`. *)
  end.

(* 
  Define a function `snd` to get the second element of a pair.
  The function matches a `pair` and returns the second component `y`.
*)
Definition snd (p : natprod) : nat :=
  match p with
  | (x, y) => y      (* Using the notation `(x, y)`, return `y`. *)
  end.

(* 
  Theorem `surjective_pairing` proves that any pair `p` is equal to the pair constructed
  from its first and second elements, i.e., `p = (fst p, snd p)`.
*)
Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.           (* Introduce `p` into the proof context. *)
  destruct p.         (* Perform case analysis on `p` using pattern matching. *)
  simpl.              (* Simplify the goal `pair x y = pair (fst (pair x y)) (snd (pair x y))`. *)
  reflexivity.        (* Trivially true as `fst (pair x y) = x` and `snd (pair x y) = y`. *)
Qed.



(*Wednesday will be polymorphic datatype*)








