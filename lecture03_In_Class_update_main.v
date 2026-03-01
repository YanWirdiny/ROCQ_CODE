(**
  Theorem `plus_id_example` demonstrates the basic use of `rewrite` in Coq.
  It proves that if `n = m`, then `n + n = m + m`. 
  - It first introduces `n` and `m`, followed by their equality `n_m_eq`.
  - Then it rewrites `n` as `m` in the goal, simplifying it to `reflexivity`.

  In Coq, the rewrite tactic is used to replace one side of an equality
  with the other in the goal or in hypotheses. You use rewrite when you
  have an equation (either from a hypothesis or a previously proven theorem)
  and you want to apply it to transform the current goal or proof context.
*)


Theorem plus_id_example : forall n m : nat,
  n = m ->              (* Hypothesis: `n = m` *)
  n + n = m + m.        (* Goal: `n + n = m + m` *)
Proof.
  (*intros. *)
  
  intros n m.           (* Introduces `n` and `m` into the proof context *)
  intros n_m_eq.        (* Introduces the hypothesis `n = m` *)
  
  rewrite n_m_eq.    (* Rewrites `n` in the goal using `n_m_eq` (i.e., `n = m`) *)
  
  reflexivity.          (* Concludes the proof since both sides are now identical *)
Qed.

(**
  Theorem `plus_id_exercise` extends the idea of the previous theorem.
  It proves that if `n = m` and `m = o`, then `n + m = m + o`.
  - It uses two `rewrite` steps to rewrite both `m` and `n` in the goal.
*)
Theorem plus_id_exercise : forall n m o : nat,
  n = m ->              (* Hypothesis: `n = m` *)
  m = o ->              (* Hypothesis: `m = o` *)
  n + m = m + o.        (* Goal: `n + m = m + o` *)
Proof.
(*
  intros n m o.         (* Introduces `n`, `m`, and `o` into the context *)
  intros n_m_eq.        (* Introduces the hypothesis `n = m` *)
  intros m_o_eq.        (* Introduces the hypothesis `m = o` *)
  rewrite <- m_o_eq.    (* Rewrites `o` as `m` in the goal using `m = o` *)
  rewrite n_m_eq.    (* Rewrites `n` as `m` in the goal using `n = m` *) *)

  (*or below if you dont want to choose the specifi*)
  intros.
  rewrite <- H0.
  rewrite <- H. 

  reflexivity.          (* Both sides are now identical, so the proof is complete *)
Qed.


(* Define a recursive function 'plus' that takes two natural numbers, n and m, and returns their sum *)
Fixpoint plus (n m : nat) : nat :=
  match n with                    (* Analyze n to decide which case applies *)
  | O => m                        (* Base case: if n is 0, then 0 + m is just m *)
  | S n' => S (plus n' m)         (* Recursive case: if n is S n' (i.e., n = n' + 1), 
                                    then n + m is defined as the successor of (n' + m) *)
  end.




(**
   (boolean equality on natural numbers):
  `beq_nat` is a recursive function that compares two natural numbers `n` and `m`.
  It returns `true` if they are equal and `false` otherwise.
  - It recursively compares each constructor of the numbers (`O` or `S`).


n' is a placeholder for the number that comes before the current number.
Sn' tells you that you have a non-zero number, and you can work with its predecessor n′in a recursive function


*)

Check nat.
Locate bool.

Fixpoint beq_nat (n m : nat) : bool :=
  match n with
  | O => match m with   (* If `n` is `O`, check if `m` is `O` as well *)
         | O => true    (* If both `n` and `m` are `O`, return `true` *)
         | S m' => false (* If `m` is a successor (`S`), return `false` *)
         end
  | S n' => match m with (* If `n` is a successor, match `m` *)
            | O => false  (* If `m` is `O`, return `false` *)
            | S m' => beq_nat n' m' (* Recursively call `beq_nat` on the successors *)
            end
  end.

(**
  Theorem `try1` proves that `beq_nat 3 3 = true`.
  This theorem uses `simpl` to unfold the definition of `beq_nat` and checks the result.
*)
Theorem try1:
   beq_nat 3 3 = true.   (* Goal: `beq_nat` returns true for equal inputs 3 and 3 *)
Proof.
   simpl.                (* `simpl` unfolds the defianition of `beq_nat` and evaluates *)
   reflexivity.          (* Both sides are identical, so the proof is complete *)
Qed.

Check plus.
Locate plus.

(**
  Theorem `plus_1_neq_0_firsttry` proves that for any natural number `n`, 
  `beq_nat (n + 1) 0 = false`. 
  It uses `destruct` to perform case analysis on `n` and handles each case.
*)
Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (plus n 1) O = false. (* Goal: `beq_nat` shows `n + 1` is not 0 *)
Proof.
  intros n.            (* Introduce `n` into the context *)
  (*simpl.               (* Simplifies the goal by unfolding `plus` *) *)
  Print Nat.add.       (* Prints the definition of addition (for understanding) *)
  destruct n as [| n']. (* Performs case analysis on `n`. `O` or successor `S x` *)
  ** (* Case n = O *)
    simpl.             (* Simplifies the base case where `n = O` *)
    reflexivity.       (* The goal is `false = false`, so the proof is complete *)
  ** (* Case n = S x *)
    simpl.             (* Simplifies the successor case where `n = S x` *)
    reflexivity.       (* The goal is `false = false`, so the proof is complete *)
Qed.



(*
  When to use `destruct`:
  - You need case analysis on an inductive value (nat/bool/list/etc.).
    Example: goal has `match n with ...` or `plus n 1` and it won’t simplify
    until you know whether `n` is `O` or `S n'`.
  - You have a hypothesis you want to break apart:
      H : A /\ B        -> destruct H as [HA HB].
      H : exists x, P x -> destruct H as [x Hx].
  - You want to split on a boolean:
      b : bool -> destruct b.  (* creates cases b = true and b = false *)

  When NOT to use `destruct`:
  - The theorem is naturally proved by induction over a recursive structure.
    If the statement is "for all n, ..." and the proof needs the fact for `n'`
    to prove it for `S n'`, use `induction n` (you need an induction hypothesis).
  - If `simpl`/`reflexivity` already solves the goal, destruct just adds cases.
  - If a hypothesis is an equality, prefer `rewrite` over destruct.
    Example: H : n = m -> rewrite H (or rewrite <- H) instead of destructing.
*)


Theorem demo : forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros.
  
  (* Option A: rewrite *)
  rewrite <- H. reflexivity.
Qed.

Theorem demo2 : forall n m : nat, n = m -> n + 1 = m + 1.
Proof.
  intros n m H.
  (* Option B: destruct use the fact that n = m to substitute,
   then delete the equality hypothesis” *) 
  destruct H. 
  reflexivity.
Qed.

(*

If you have H : x = y and you just want to substitute one side for the other,
 prefer rewrite (clear and directional).

Use destruct H when you want the equality to “disappear completely”
and you are okay with Coq substituting everywhere
(common in short proofs, sometimes useful with dependent stuff,
but can also be messier). 
   
*)


 
(*
  Theorem `plus_n_O` proves that for any natural number `n`,
  `n = n + 0`. 
  - The first proof attempt gets stuck because case analysis isn't enough.

  
Base case (n = 0): This works fine because 0 = 0 + 0 simplifies easily, 
and reflexivity proves it.


Successor case (n = S n'): The goal here is S n' = S n' + 0, 
which simplifies to S n' = S (n' + 0). At this point, we are 
stuck because we do not have an induction hypothesis that would 
allow us to assume n' = n' + 0 for the smaller value n'.


*)

(*
Theorem plus_n_O: forall n:nat,
  n = n + 0.           (* Goal: `n` is equal to `n + 0` for any natural number *)
Proof.
  intros n.            (* Introduce `n` into the context *)
  simpl.               (* Simplify the goal *)
  Print Nat.add.       (* Print the definition of `Nat.add` to see how addition is handled *)
  destruct n.          (* Perform case analysis on `n` *)
  - simpl.             (* Simplifies the base case where `n = O` *)
    reflexivity.       (* Proves `0 = 0 + 0`, which is true *)
  - simpl.             (* Simplifies the successor case where `n = S n'` *)
    (* This proof gets stuck because it doesn't simplify fully without recursion *)
Qed.

*)


(* When we run simpl on beq_nat (plus n 1) O, 
Coq looks at the definition of beq_nat and 
sees that it expects its first argument to
 be either O or S something. But plus n 1
 is just a call to the plus function with
 an arbitrary n, and since plus is defined
 to simplify on its first argument 
(which is not immediately in the form O or S something),
 it does not reduce plus n 1 to a form that beq_nat can pattern-match on. 

we NEED induction!

when dealing with recursive functions like plus that depend on an inductive argument,
we need induction to “unlock” the recursive structure.

 
*)




(**
  Theorem `plus_n_O` proves the same statement as above using induction instead of case analysis.
  Induction allows us to handle the recursive structure of natural numbers.
  - Base case: `0 = 0 + 0`.
  - Inductive case: Assume `n' = n' + 0` and prove `S n' = S n' + 0`.
*)
Theorem plus_n_O : forall n:nat,
  n = n + 0.           (* Goal: Prove `n = n + 0` for any natural number `n` *)
Proof.
  intros n.            (* Introduce `n` into the context *)
  simpl.               (* Simplify the goal initially *)
  Print Nat.add.       (* Print the definition of `Nat.add` for understanding *)
  induction n as [ | n' IH]. (* Perform induction on `n`, introducing `IH` as the inductive hypothesis *)
  - simpl.             (* Base case: simplify for `n = O` *)
    reflexivity.       (* Proves `0 = 0 + 0`, which is true *)
  - simpl.             (* Inductive case: simplify for `n = S n'` *)
    rewrite <- IH.     (* Use the inductive hypothesis `n' = n' + 0` to rewrite *)
    reflexivity.       (* Prove `S n' = S (n' + 0)`, which completes the proof *)
Qed.




