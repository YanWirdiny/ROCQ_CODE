(* 
  Definition: Assigns the natural number 5 to the identifier `z`.
  Here, `z` is of type `nat` (natural number).
*)
Definition z : nat := 5.


(* 
  Theorem: `add_n_0` states that for any natural number `x`, adding 0 to `x` results in `x`.
  This is a fundamental property of addition in natural numbers.
*)
Theorem add_n_0 : forall x, x + 0 = x.
Proof.
  intros.
  induction x.
  reflexivity.
  simpl.
  rewrite IHx.
  reflexivity.
Qed.

Check 10 + 0 = 10.
(* 
  Theorem: `g'` demonstrates that adding 0 to 10 yields 10.
  It utilizes the previously defined theorem `add_n_0` to prove this specific case.
*)
Theorem g' :
  10 + 0 = 10.
Proof.
  apply add_n_0.  (* 
                   Applies the theorem `add_n_0` to the current goal.
                   Since `add_n_0` proves that `x + 0 = x` for any `x`,
                   applying it with `x = 10` concludes that `10 + 0 = 10`.
                  *)
Qed.  (* 
      Ends the proof, confirming that 10 + 0 = 10 is true.
      `Qed` signifies the successful completion of the proof.
     *)


(*
  g is a named proof of 10 + 0 = 10.
  We obtain it by applying the theorem add_n_0 to 10 (add_n_0 10).
*)


Definition g : 10 + 0 = 10 := add_n_0 10.
Check g.
Check 10 + 0 = 10.

(*
  A proposition is a statement that can be true or false.
  In Coq, propositions are logical statements (like x = y, P -> Q, or forall n, n + 0 = n).
  Instead of evaluating a proposition to true/false, we prove it by constructing a proof.
*)

(* boolean value (computation) *)
Definition b : bool := Nat.eqb 2 3.   (* b computes to false *)

(* proposition (logic) *)
Definition P : Prop := (2 = 3).       (* P is a statement, not a computed boolean *)



Check Nat.eqb. (*  return data type *)
Locate Nat.eqb.

Theorem is_correct:
  Nat.eqb 2 2 = true.
Proof.
  simpl.
  reflexivity.  (* 
                Uses the `reflexivity` tactic to confirm that both sides of the equation are equal.
                Since `Nat.eqb 2 2` evaluates to `true`, and the right side is `true`, the proof is complete.
               *)
Qed.


(* 
  Theorem: `is_correct` asserts that `Nat.eqb 2 3` evaluates to `false`.
  This theorem confirms that 2 and 3 are indeed distinct natural numbers.
*)

Theorem is_correct2:
  Nat.eqb 2 3 = false.
Proof. 
  reflexivity.  (* 
                Uses the `reflexivity` tactic to confirm that both sides of the equation are equal.
                Since `Nat.eqb 2 3` evaluates to `false`, and the right side is `false`, the proof is complete.
               *)
Qed.


(* 
  Inductive Type: Defines a product type `prod` that pairs elements of types `T1` and `T2`.
  It has a single constructor `pair` that takes an element of `T1` and an element of `T2`.
  This is analogous to tuples or pairs in other programming languages.
*)
Inductive prod (T1 T2:Type) :=
  | pair : T1 -> T2 -> prod T1 T2.


(* 
  Inductive Type: Defines `twoproofs` which pairs proofs of propositions `P` and `Q`.
  The constructor `proof_pair` takes proofs of `P` and `Q` and constructs a `twoproofs P Q`.
  This is useful for bundling multiple proofs together.
*)
Inductive twoproofs (P Q:Prop) :=
  | proof_pair : P -> Q -> twoproofs P Q.


(* 
  Goal: Proves that there exists a `twoproofs` instance for the propositions `forall x:nat, x = x` and `1 = 1`.
  - `forall x:nat, x = x` is a universally quantified statement asserting reflexivity of equality.
  - `1 = 1` is a simple equality statement.
*)
Goal
  twoproofs (forall (x:nat), x = x) (1 = 1).
Proof.
  apply proof_pair.  (* 
                     Applies the `proof_pair` constructor to build the required `twoproofs` instance.
                     This splits the goal into proving each component: `forall x:nat, x = x` and `1 = 1`.
                    *)
  - intros. reflexivity.  (* 
                           First subgoal: Prove `forall x:nat, x = x`.
                           `intros` introduces an arbitrary natural number `x`.
                           `reflexivity` confirms that `x = x` holds for any `x`.
                          *)
  - reflexivity.          (* 
                           Second subgoal: Prove `1 = 1`.
                           `reflexivity` directly confirms that `1 = 1` is true.
                          *)
Qed.


(* 
  Goal: From a `twoproofs` instance, extract the proof of `P`.
  This demonstrates how to destructure inductive proofs to access individual components.
*)
Goal forall (P Q:Prop),
  twoproofs P Q ->
  P.
Proof.
  intros.          (* 
                    Introduces propositions `P`, `Q`, and the hypothesis `twoproofs P Q`.
                   *)
  destruct H.      (* 
                    Breaks down the `twoproofs P Q` hypothesis into its components.
                    After destructuring, you obtain `p : P` and `q : Q`.
                   *)

  apply p.         (* 
                    Applies the extracted proof of `P` to satisfy the goal.
                    Since `p` is a proof of `P`, this concludes the proof.
                   *)
Qed.


(* 
  Example: Demonstrates the use of logical conjunction.
  - The goal states that `3 + 4 = 7` and `2 * 2 = 4` both hold.
  - `apply conj` is used to split the goal into two separate subgoals.
*)
Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply conj.         (* 
                      Splits the conjunction into two separate goals:
                      1. `3 + 4 = 7`
                      2. `2 * 2 = 4`
                     *)
  - reflexivity.      (* 
                       Proves the first part `3 + 4 = 7` using reflexivity.
                       Since `3 + 4` indeed equals `7`, the proof succeeds.
                      *)
  - reflexivity.      (* 
                       Proves the second part `2 * 2 = 4` using reflexivity.
                       Since `2 * 2` equals `4`, the proof is complete.
                      *)
Qed.


(* 
  Inductive Type: Defines a custom logical OR type `l_or` for propositions `P` and `Q`.
  - `is_left` constructs a proof when `P` holds.
  - `is_right` constructs a proof when `Q` holds.
  This mimics the behavior of the standard logical OR (`\/`) but is user-defined.
*)

Inductive l_or (P Q:Prop) : Prop := 
(* l_or is an inductive type representing a logical OR between propositions P OR Q. 
   It defines two cases: when P holds OR when Q holds. *)

  | is_left: P -> l_or P Q 
  (* The first constructor 'is_left' states that if P holds, 
     then the proposition l_or P Q is true. This represents the case where P is true (the left side of the OR). *)

  | is_right: Q -> l_or P Q. 
  (* The second constructor 'is_right' states that if Q holds, 
     then the proposition l_or P Q is true. This represents the case where Q is true (the right side of the OR). *)



     
(* Inductive l_XOR (P Q:Prop) : Prop := 
  | is_left: ~ P -> l_or P Q *)



(* 
  Goal: Constructs a proof of `l_or (1 = 10) (0 = 0)`.
  - Demonstrates selecting the right side of the OR, since `0 = 0` is true.
*)

Goal
  l_or (1 = 10) (0 = 0).
Proof.
  apply is_right.      (* 
                       Chooses the `is_right` constructor to prove `0 = 0`.
                       Since `0 = 0` is trivially true, this completes the proof.
                      *)
  reflexivity.         (* 
                       Proves `0 = 0` using reflexivity.
                      *)
Qed.


(* 
  Goal: Constructs a nested proof using `l_or`.
  - Proves `l_or (1 = 10) (l_or (3 + 4 = 7) (2 * 2 = 4))`.
  - Selects the left option of the inner `l_or` to demonstrate nesting.
*)
Goal 
  l_or (1 = 10) (l_or (3 + 4 = 7) (2 * 2 = 4)).
Proof.
  apply is_right.        (* 
                           Chooses the `is_right` constructor for the outer `l_or`, focusing on the inner `l_or`.
                          *)
  apply is_left.         (* 
                           Chooses the `is_left` constructor for the inner `l_or` to prove `3 + 4 = 7`.
                          *)
  reflexivity.           (* 
                           Proves `3 + 4 = 7` using reflexivity.
                          *)
Qed.

(**********************************************)


(* 
  Lemma: `or_example` shows that if either `n = 0` or `m = 0`, then `n * m = 0`.
  Idea:
  - Do case analysis on the disjunction.
  - If n = 0, the product is 0 by simplification.
  - If m = 0, prove n * 0 = 0 by induction on n (because simpl alone will not fully reduce n * 0).
*)
Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m Hor.                          (* Introduce n, m, and Hor : n = 0 \/ m = 0. *)
  destruct Hor as [Hn0 | Hm0].             (* Split into two cases: Hn0 : n = 0, or Hm0 : m = 0. *)

  - rewrite Hn0.                           (* Case 1: replace n with 0 in the goal. *)
    simpl.                                 (* Compute 0 * m to 0 by unfolding multiplication. *)
    reflexivity.                           (* Goal is now 0 = 0. *)

  - rewrite Hm0.                           (* Case 2: replace m with 0 in the goal, so goal becomes n * 0 = 0. *)
    induction n as [| n' IH].              (* Prove n * 0 = 0 by induction on n. *)

    + simpl.                               (* Base case: 0 * 0 reduces to 0. *)
      reflexivity.                         (* Goal is 0 = 0. *)

    + simpl.                               (* Step: (S n') * 0 becomes 0 + (n' * 0). *)
      rewrite IH.                          (* Replace (n' * 0) with 0 using the induction hypothesis. *)
      simpl.                               (* Compute 0 + 0 to 0. *)
      reflexivity.                         (* Goal is 0 = 0. *)
Qed.


(*
  Lemma: `or_example2` handles a nested disjunction:
    n = 0 \/ m = 0 \/ n = 0 * m  ->  n * m = 0.

  Note: The third case here is `n = 0 * m` (not `n = m`).
  Since 0 * m simplifies to 0, that third case also forces n = 0.
*)
Lemma or_example2 :
  forall n m : nat, n = 0 \/ m = 0 \/ n = 0 * m -> n * m = 0.
Proof.
 intros n m H.                            (* Introduce n, m, and H : n = 0 \/ m = 0 \/ n = 0 * m. *)
  destruct H as [Hn0 | [Hm0 | HnEq]].      (* Three cases:
                                              1) Hn0  : n = 0
                                              2) Hm0  : m = 0
                                              3) HnEq : n = 0 * m
                                           *)

  - rewrite Hn0.                           (* Case 1: replace n with 0. *)
    simpl.                                 (* Compute 0 * m to 0. *)
    reflexivity.                           (* Goal is 0 = 0. *)

  - rewrite Hm0.                           (* Case 2: replace m with 0, goal becomes n * 0 = 0. *)
    induction n as [| n' IH].              (* Prove n * 0 = 0 by induction on n. *)

    + simpl.                               (* Base case: 0 * 0 reduces to 0. *)
      reflexivity.                         (* Goal is 0 = 0. *)

    + simpl.                               (* Step: (S n') * 0 becomes 0 + (n' * 0). *)
      rewrite IH.                          (* Replace (n' * 0) with 0. *)
      simpl.                               (* Compute 0 + 0 to 0. *)
      reflexivity.                         (* Goal is 0 = 0. *)

  - rewrite HnEq.                          (* Case 3: replace n with (0 * m), goal becomes (0 * m) * m = 0. *)
    simpl.                                 (* Simplify 0 * m to 0, then simplify 0 * m to 0. *)
    reflexivity.      
                       (* Goal is 0 = 0. *)
Qed.


(**********************************************)




(* 
  Inductive Type: Defines `Truth` as an inductive proposition with a single constructor `proof_of_truth`.
  - This represents a trivially true proposition.
*)
Inductive Truth : Prop :=        (* 'Truth' is an inductive proposition (Prop) that represents truth itself. *)
  | proof_of_truth: Truth.       (* 'proof_of_truth' is a constructor that serves as a proof of the proposition 'Truth'. (Type Truth afte :) *)
                                 (* It means that whenever 'Truth' is needed, 'proof_of_truth' can be used to prove it. *)


  
(* 
  Goal: Proves that `Truth` holds by applying the constructor `proof_of_truth`.
  - Demonstrates how to construct a proof for an inductively defined proposition.
*)
Goal
  Truth.
Proof.
  apply proof_of_truth.  (* 
                           Constructs a proof of `Truth` using its only constructor.
                           Since `Truth` has no additional requirements, this completes the proof.
                          *)
Qed.


(* 
  Inductive Type: Defines `Falsehood` as an inductive proposition that can only be constructed from a contradiction.
  - `bogus` takes a proof of `0 = 1` and constructs a `Falsehood`.
  - This models propositions that are inherently false or lead to contradictions.
*)
Inductive Falsehood : Prop :=
  | bogus : 0 = 1 -> Falsehood.


(* 
  Goal: From `Falsehood`, prove that `10 = 0`.
  - Demonstrates how a contradiction leads to an arbitrary conclusion using the principle of explosion.
*)
Goal
  Falsehood -> 10 = 0.
Proof.
  intros.                (* Introduces the hypothesis `H : Falsehood`. *)
  destruct H.            (* Breaks down the `Falsehood` hypothesis to access the underlying contradiction `0 = 1`. *)
  inversion H.           (* Analyzes the impossible equality `0 = 1`, leading to a contradiction.
                           Since `0 = 1` cannot hold, this step derives `False`, completing the proof.
                          *)
Qed.


(* 
  Goal: From `Falsehood`, prove that `10 = 10`.
  - Although `10 = 10` is trivially true, the proof still follows from the contradiction.
  - This further illustrates the principle of explosion, where from `Falsehood`, any proposition can be derived.
*)
Goal
  Falsehood -> 10 = 10.  (* We want to prove that if we assume `Falsehood` (i.e., a contradiction), 
                           then the statement `10 = 10` is true. This is possible because once we 
                           assume a contradiction, anything can follow (this is known as "ex falso quodlibet"). *)
Proof.
  intros.                (* Introduces the hypothesis `H : Falsehood`. We now have `H` in our context, 
                           which means we have a contradiction at hand. *)
  destruct H.            (* Since `H : Falsehood`, we destruct or analyze it. 
                           A hypothesis of type `Falsehood` is an impossible situation, so 
                           destructing it allows us to proceed. *)
  inversion H.           (* `H` represents a contradiction (something like `0 = 1` or some other impossible situation). 
                           `inversion` analyzes the impossible situation, deriving a contradiction from it. 
                           Since contradictions allow us to prove anything, we can conclude `10 = 10` from this step. *)
Qed.


(* 
  Commented Out Inductive Type: Represents the standard `False` proposition in Coq.
  - In Coq, `False` is defined as an inductive type with no constructors, signifying an uninhabited type.
  - This line is commented out to prevent redefinition since `False` is already a built-in proposition.
*)
(* Inductive False : Prop :=. *)


(* 
  Goal: From `False`, prove that `0 = 1`.
  - Demonstrates that from an uninhabited type (`False`), any proposition can be derived.
  - This is another illustration of the principle of explosion.
*)
Goal
  False -> 0 = 1.
Proof.
  intros.      (* Introduces the hypothesis `H : False`. *)
  destruct H.  (* Attempts to destruct `H`, but since `False` has no constructors, this leads to an immediate contradiction.
                - Coq recognizes that there are no possible ways to construct `H`, thus the proof is complete.
               *)
Qed.

(**********************************************************************)

(* The unfold tactic is used to expand definitions, making underlying expressions explicit for manipulation. *)

(* Define the function 'square' which calculates the square of a natural number *)
Definition square (n : nat) := n * n.

(* State the goal: For all natural numbers x and y, square x plus square y equals x squared plus y squared *)
Goal forall x y : nat, square x + square y = x * x + y * y.
Proof.
  intros x y.
  (* Introduce variables x and y into the context *)
  (* Our current goal is:
     square x + square y = x * x + y * y
  *)


(* expanding your function or definition to its   formula  (Yan Notes)*)



  unfold square.
  (* Unfold the definition of 'square' in the goal *)
  (* After unfolding, the goal becomes:
     x * x + y * y = x * x + y * y
  *)

  reflexivity.
  (* Since both sides are identical, we can conclude by 'reflexivity' *)
Qed.
(* The proof is complete *)

(**********************************************************************)

(* 
  Definition: Defines `neg P` as the negation of proposition `P`, meaning `P` implies `False`.
  - This is a standard way to represent negation in Coq.
*)
Definition neg P := P -> False.



(* 
  Goal: Proves that `neg (0 = 1)` holds. (not in coq is ~)
  - Shows that `0 = 1` leads to a contradiction, thus `neg (0 = 1)` is true.
*)
Goal
  neg (0 = 1). (*~ ( 0 = 1)*)
Proof.
  unfold neg.      (*  unfold
                    Expands the definition of `neg`, changing the goal from `neg (0 = 1)` to `(0 = 1) -> False`.
                   *)
  intros.          (* Introduces the hypothesis `H : 0 = 1`. *)
  inversion H.     (* Analyzes the impossible equality `0 = 1`, leading to a contradiction.
                    - Since `0` and `1` are distinct natural numbers, `H` cannot hold.
                   *)
Qed.


Goal
  ~ ( 0 = 1).
Proof.
  unfold not.                             
  intros.        
  inversion H.                          
Qed.




  
  