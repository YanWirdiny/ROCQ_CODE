Require Import Coq.Lists.List.   (* Import the List library *)

(* Yan Note 
Use Locate to find a  proof  already set to find it.
*)




(* 
  Description of `contradiction`:
  - The `contradiction` tactic in Coq is used when we already have a hypothesis that directly 
    leads to a contradiction. It allows us to derive any conclusion (even seemingly absurd ones) 
    when `False` is part of the assumptions. Once we have `False` or conflicting assumptions, 
    `contradiction` resolves the proof immediately.
  
  Example: If `False` is assumed, we can prove any proposition, including `2 = 3`. 
  Since `False` is contradictory, the proof is automatically concluded using `contradiction`.
*)

Theorem false_example : False -> 2 = 3.
Proof.
  intros H.  (* Introduce the assumption `H : False` into the context. *)
  contradiction.  (* Since we have `False` in the context, the `contradiction` tactic immediately resolves 
                     the proof, as `False` implies any proposition (even `2 = 3`). *)
Qed.


(* 
  Description of `inversion`:
  - The `inversion` tactic is used in Coq to analyze equalities and inductive types by breaking them down into their constructors.
  - It examines the structure of data types and derives all possible cases that satisfy the equality.
  - If the equality is between different constructors **without variables**, `inversion` can immediately lead to a contradiction.
  - If variables are involved, `inversion` generates new equalities (hypotheses) that may require further proof steps.
  
  Examples:
  - **Immediate Contradiction:**
    - If we have `H: S n = 0`, `inversion H` immediately concludes `False` because `S n` and `0` are different constructors with no variables to unify.
  - **Further Steps Needed:**
    - If we have `H: S n = n`, `inversion H` yields `H1: n = n'` (where `n'` is from the constructor), but we need additional steps to derive a contradiction, such as applying the induction hypothesis or other tactics.
  - **Breaking Down Components:**
    - In the case of lists, if `H: cons h t = cons h' t'`, `inversion H` gives us `h = h'` and `t = t'`, which may require further proof steps.

  For equalities: It breaks down equalities between constructed terms, generating all possible cases where the equality could hold.
  For inductive hypotheses: It analyzes the structure of an inductive hypothesis, creating subgoals for each possible constructor that could have been used to build the term.
  Contradiction detection: If it finds any impossible cases, it automatically solves those subgoals.
  Simplification: It simplifies hypotheses and generates new ones based on the inferred information.

    *)


(* A simple inductive type representing lists of natural numbers. *)
Inductive natlist : Type :=
  | nil : natlist            (* Represents an empty list. *)
  | cons : nat -> natlist -> natlist.  (* Represents a list with a head element (nat) and a tail (natlist). *)


(* 
  Theorem: There is no way `nil` can be equal to `cons 1 l`. 
  This is trivially true, and `inversion` will help us prove it by showing that the structure of the two terms is incompatible.
*)
Theorem inversion_example_contradiction : forall l : natlist, nil = cons 1 l -> False.
Proof.
  intros.  (* Introduce `l` and the assumption `H : nil = cons 1 l`. *)
  inversion H.  (* Use `inversion` to analyze the structure. 
                   Since `nil` and `cons` are distinct constructors, `inversion` leads to a contradiction and completes the proof. *)
Qed.




(**********************************************************)



(* 
  - The symbol `<>` in Coq represents "not equal to."
    It is shorthand for `~ (x = y)`, which means that `x` and `y` are not equal.
  
  - The symbol `~` in Coq is used to express logical negation.
    It is equivalent to the function `not` and means "it is not the case that..."
    Formally, `~ P` is defined as `P -> False`, meaning assuming `P` leads to a contradiction.
*)

(* Problem Statement:
   Prove that if x is not equal to y (x <> y), then assuming x = y leads to a contradiction.
   This demonstrates the use of negation and inequality in Coq.
*)

Theorem not_equal_example : forall x y : nat, x <> y -> x = y -> False.
Proof.
  (* Introduce the variables x and y, and the hypothesis that x <> y and x = y *)
  intros x y Hneq Heq.
  
  (* Apply contradiction, because Hneq (x <> y) and Heq (x = y) can't both be true *)
  contradiction.
Qed.
(***********************************************************************************)


(* 
  Description:
  - The symbol `~` in Coq is used for logical negation. 
    It is equivalent to `P -> False`, meaning that assuming `P` leads to a contradiction.
  
  - We can express `x <> y` as `~ (x = y)`, meaning "it is not the case that x equals y."
*)

(* Problem Statement:
   Prove that if ~ (x = y) (i.e., x is not equal to y), then assuming x = y leads to a contradiction.
   This uses negation directly with the `~` symbol.
*)

Theorem not_equal_example_with_negation : forall x y : nat, ~ (x = y) -> x = y -> False.
Proof.
  (* Introduce the variables x and y, and the hypothesis that ~ (x = y) and x = y *)
  intros x y Hneq Heq.
  
  (* Apply contradiction, because Hneq (~ (x = y)) and Heq (x = y) can't both be true *)
  contradiction.
Qed.

(***********************************************************************************)
(* 
  Definition of XOR (exclusive or) in terms of logical operations:
  XOR is true if exactly one of P or Q is true, but not both.
  This is defined as: (P \/ Q) /\ ~ (P /\ Q).
*)
Definition L_xor (P Q : Prop) : Prop :=
  (P \/ Q) /\ ~ (P /\ Q).

(***********************************************************************************)

(* Why Use l_xor?
The inductive definition (l_xor) is often more practical in Coq proofs because:

It avoids nested disjunctions (e.g., P \/ Q followed by ~(P /\ Q)).

It directly exposes the two exclusive cases, simplifying pattern matching.

It integrates better with Coq's proof automation (e.g., destruct or inversion). *) 

(* 
  Inductive Type: Defines `l_xor` as an inductive proposition representing XOR (exclusive or).
  - XOR is true if exactly one of P or Q is true, but not both.
  - This custom `l_xor` type has two constructors:
    1. `is_left_xor` - P is true, Q is false.
    2. `is_right_xor` - Q is true, P is false.
*)

Inductive l_xor (P Q : Prop) : Prop :=
  | is_left_xor: P -> ~ Q -> l_xor P Q    (* If P is true and Q is false, XOR is true. *)
  | is_right_xor: Q -> ~ P -> l_xor P Q.  (* If Q is true and P is false, XOR is true. *)


(* 
  Goal: Constructs a proof of `l_xor (1 = 1) (0 = 1)`.
  - Demonstrates selecting the left side of the XOR, as `1 = 1` is true and `0 = 1` is false.
*)
Goal
  l_xor (1 = 1) (0 = 1).
Proof.
  apply is_left_xor.    (* Choose the `is_left_xor` constructor, which expects `P` to be true and `Q` to be false. *)
  - reflexivity.        (* Prove `1 = 1` using reflexivity, as it is trivially true. *)
  - intros H. inversion H. (* Show that `0 = 1` leads to a contradiction, proving `~ Q` (negation of Q). *)
Qed.


(* 
  Goal: Constructs a proof of `l_xor (0 = 1) (1 = 1)`.
  - Demonstrates selecting the right side of the XOR, as `1 = 1` is true and `0 = 1` is false.
*)
Goal
  l_xor (0 = 1) (1 = 1).
Proof.
  apply is_right_xor.    (* Choose the `is_right_xor` constructor, which expects `Q` to be true and `P` to be false. *)
  - reflexivity.         (* Prove `1 = 1` using reflexivity, as it is trivially true. *)
  - intros H. inversion H. (* Show that `0 = 1` leads to a contradiction, proving `~ P` (negation of P). *)
Qed.



 
(* 
  Theorem xor_false: Proves that it is impossible for XOR (exclusive or) to hold between `1 = 1` and `2 = 2`.
  
  Description:
  - The XOR operation is true when exactly one of the two propositions is true, but not both.
  - In this case, both `1 = 1` and `2 = 2` are true, so XOR cannot hold. 
  - Therefore, we are proving that `~ (l_xor (1 = 1) (2 = 2))`, meaning "It is not the case that XOR between `1 = 1` and `2 = 2` holds."

  Proof Strategy:
  - We destructure the `l_xor` hypothesis into its two possible cases (`is_left_xor` and `is_right_xor`):
    1. In the first case, we assume `1 = 1` is true and `2 = 2` is false, but this leads to a contradiction because `2 = 2` is actually true.
    2. In the second case, we assume `2 = 2` is true and `1 = 1` is false, but this also leads to a contradiction because `1 = 1` is true.
  - In both cases, we derive contradictions, showing that XOR between `1 = 1` and `2 = 2` is false.
*)

Theorem xor_false : ~ (l_xor (1 = 1) (2 = 2)).
Proof.
  intros Hxor.   (* Assume `l_xor (1 = 1) (2 = 2)` holds, i.e., XOR between `1 = 1` and `2 = 2` holds. *)
  destruct Hxor as [H1 Hnot2 | H2 Hnot1].  (* Break down the XOR hypothesis into its two cases: *)

  - (* Case 1: If `is_left_xor`, then `1 = 1` is true and `~ (2 = 2)` must hold. *)
    contradiction.  (* `Hnot2` leads to a contradiction because `2 = 2` is true, contradicting `~ (2 = 2)`. *)

  - (* Case 2: If `is_right_xor`, then `2 = 2` is true and `~ (1 = 1)` must hold. *)
    contradiction.  (* `Hnot1` leads to a contradiction because `1 = 1` is true, contradicting `~ (1 = 1)`. *)
Qed.




(******************************************************************************)

Theorem successor_distributive : forall n m : nat, S (n + m) = n + S m.
Proof.
  (* Introduce `n` and `m` as natural numbers. *)
  intros n m.
  
  (* Perform induction on `n`. *)
  induction n as [| n' IH].

  - (* Base case: n = 0 *)
    simpl. (* Simplify `S (0 + m)` to `S m` *)
    reflexivity. (* `S m = 0 + S m` is trivially true *)

  - (* Inductive step: Assume the property holds for `n'` and prove for `S n'` *)
    simpl. (* Simplify the left-hand side `S (S n' + m)` to `S (n' + m)` *)
    rewrite IH. (* Use the inductive hypothesis: `S (n' + m) = n' + S m` *)
    reflexivity. (* Now the equation `S (n' + S m) = S n' + S m` holds true *)
Qed.



(***********************************************************************************)


(* Problem: Given natural numbers a, b, c, propositions P and Q, and assumptions:
   - H: P -> a = b
   - H0: Q \/ P
   - H1: b = c
   Prove that a = c.
*)
Goal
  forall
  (a b c: nat)        (* a, b, c are natural numbers *)
  (P Q: Prop)         (* P and Q are propositions *)
  (H: P -> a = b)     (* H is the assumption that P implies a = b *)
  (H0: Q \/ P)        (* H0 is the assumption that Q or P holds *)
  (H1: b = c),        (* H1 is the assumption that b = c *)
  a = c.              (* Goal: prove that a = c *)
Proof.
  intros.             (* Introduce all variables and assumptions into the context *)
  destruct H0 as [Hq | Hp].
Abort.                (* Abort the proof *)



(* Add an assumption: Q implies a = b *)
Goal
  forall
  (a b c: nat)
  (P Q: Prop)
  (H: P -> a = b)
  (H0: Q \/ P)
  (H1: b = c)
  (H2: Q -> a = b),  (* New hypothesis *)
  a = c.
Proof.
  intros.
  destruct H0 as [Hq | Hp].
  - apply H2 in Hq.  (* Use Q -> a = b *)
    transitivity b; auto.
  - apply H in Hp.   (* Use P -> a = b *)
    transitivity b; auto.
Qed.



(* Prove that Q is impossible *)
Goal
  forall
  (a b c: nat)
  (P Q: Prop)
  (H: P -> a = b)
  (H0: Q \/ P)
  (H1: b = c)
  (H2: ~Q),          (* New hypothesis: Q is false *)
  a = c.
Proof.
  intros.
  destruct H0 as [Hq | Hp].
  - contradiction.   (* Q is false, so this case is impossible *)
  - apply H in Hp.   (* Use P -> a = b *)
    transitivity b; auto.
Qed.



(*

(* Problem: Given natural numbers a, b, c, propositions P and Q, and assumptions:
   - (P -> a = b)
   - Q \/ P
   - b = c
   Prove that a = c.
*)
Goal
  forall
  (a b c: nat)            (* a, b, c are natural numbers *)
  (P Q: Prop),            (* P and Q are propositions *)
  (P -> a = b) ->         (* Assumption: P implies a = b *)
  Q \/ P ->               (* Assumption: Q or P holds *)
  b = c ->                (* Assumption: b = c *)
  a = c.                  (* Goal: prove that a = c *)
Proof.
  intros.                 (* Introduce all variables and assumptions into the context *)
Abort.                    (* Abort the proof *)


*)





(* Problem: Prove that there exists a natural number n such that n * 5 = n. *)
Goal
  exists n, n * 5 = n.    (* Goal: There exists n such that n * 5 = n *)
Proof.
  exists 0.               (* Provide the witness n = 0 *)
  reflexivity.            (* Prove 0 * 5 = 0 by computation *)
Qed.






(* 
   This defines the inductive type `ex`, which is Coq's way of expressing
   existential quantification. The type `ex A P` represents the proposition
   "there exists an `x` of type `A` such that the predicate `P x` holds".
*)

Inductive ex (A : Type) (P : A -> Prop) : Prop := 
  (* 
     This defines the constructor `ex_intro`. It takes two arguments:
     1. A witness `x : A`, meaning an element of type `A`.
     2. A proof that the predicate `P x` holds for that particular `x`.
     It then constructs a proof that `ex A P` holds, meaning that 
     "there exists an `x` of type `A` such that `P x` is true."
  *)
  | ex_intro : forall (x : A), P x -> ex A P.
  (* The constructor introduces the existential quantifier. *)



Goal
  forall n,
  (exists m, m < n) ->    (* Assumption: There exists m such that m < n *)
  n <> 0.                 (* Goal: Prove that n is not equal to 0 *)
Proof.
  intros n H.             (* Introduce n and the assumption H into the context *)
  destruct H as [m m_lt_n].  (* Destructure the existential to get m and the proof m < n *)
  unfold not.             (* Unfold the definition of "not", which is `n = 0 -> False` *)
  intros n_eq_0.          (* Assume n = 0 and show that this leads to a contradiction *)
  rewrite n_eq_0 in m_lt_n. (* Substitute n = 0 in the assumption m < n *)
  inversion m_lt_n.       (* Derive a contradiction from m < 0, which is impossible *)
Qed.



Require Import Coq.Arith.EqNat.  (* Import the required module for Nat.eqb_eq *)

Goal
  forall n m (E: Nat.eqb n m = true),  (* Assumption: Nat.eqb n m = true *)
  m = n.                               (* Goal: Prove m = n *)
Proof.
  intros n m E.                        (* Introduce n, m, and E into the context *)

  (* We cannot directly apply E because Nat.eqb n m = true is a boolean equality, 
     and Coq's goal m = n is a propositional equality. 
     Boolean equalities (true/false) and propositional equalities (n = m) are different 
     in Coq and can't be applied directly. *)

  (* Attempting to do something like `apply E` will fail:  *)
     Fail apply E.

Abort.





(* Problem: Prove that for all n, S n <> n (the successor of n is not equal to n) *)
Goal
 forall n, S n <> n.                (* Goal: For all n, S n is not equal to n *)
Proof.
  intros.                           (* Introduce n *)
  unfold not.                       (* Unfold the definition of not (P -> False) *)
  intros.                           (* Assume S n = n *)
  induction n.                      (* Proceed by induction on n *)
  - inversion H.                    (* Base case: S 0 = 0 leads to contradiction *)
  - inversion H.                    (* Inductive case: S n = n leads to contradiction *)
    contradiction.                  (* Derive contradiction from the impossible equality *)  
    (*
    apply IHn.
    apply H1.
    *)
Qed.


Check le_n.
Print le_n.

Print le_S.
Check le_S.

(* Problem: Prove that for all n, 5 + n <= 6 + n *)
Goal
  forall n,
  5 + n <= 6 + n.        (* Goal: 5 + n is less than or equal to 6 + n *)
Proof.
  intros.                (* Introduce n *)
  simpl.                 (* Simplify expressions *)
  apply le_S.            (* Apply le_S: if a <= b, then S a <= S b *)
  apply le_n.            (* Apply le_n: n <= n *)
Qed.


(* Problem: Prove that for all n, n + 5 <= n + 6 *)
Goal
  forall n,
  n + 5 <= n + 6.        (* Goal: n + 5 is less than or equal to n + 6 *)
Proof.
  intros.                (* Introduce n *)
  simpl.                 (* Simplify expressions *)
Abort.                   (* Proof is incomplete; may require induction *)



(* Problem: Prove that for all P, if ~~P and (P \/ ~P), then P *)
Goal
  forall (P:Prop),
  ~ ~ P ->               (* Assumption: Double negation ~~P *)
  P \/ ~ P ->            (* Assumption: Excluded middle P ∨ ~P *)
  P.                     (* Goal: Prove P *)
Proof.
  intros.                (* Introduce P, H: ~~P, H0: P ∨ ~P *)
  destruct H0.           (* Case analysis on H0: P ∨ ~P *)
  - assumption.          (* Case 1: P holds. Directly conclude P. *)
  - unfold not in *.     (* Case 2: ~P holds. Expand definitions of `not`. *)
    apply H in H0.       (* Apply ~~P to ~P, deriving a contradiction. *)
    inversion H0.        (* Resolve contradiction to conclude P. *)
Qed.

(* Problem: Prove that for all P Q, if (P -> Q) and (P \/ ~P), then ~P \/ Q *)
Goal
  forall P Q : Prop,
  (P -> Q) ->            (* Assumption: P implies Q *)
  (P \/ ~ P) ->          (* Assumption: P or not P *)
  ~ P \/ Q.              (* Goal: Prove not P or Q *)
Proof.
  intros.                (* Introduce P, Q, and assumptions *)
  destruct H0 as [Ha | Hb]. (* Case analysis on H0 *)
  - right.               (* In case P holds *)
    apply H.             (* Apply P -> Q *)
    assumption.          (* Use Ha: P *)
  - left.                (* In case ~P holds *)
    assumption.          (* Use Hb: ~P *)
Qed.

(* Problem: Prove that for all P Q, if (P -> Q), ~Q, and P, then False *)
Goal forall P Q : Prop,
  (P -> Q) ->            (* Assumption: P implies Q *)
  ~ Q ->                 (* Assumption: not Q *)
  P ->                   (* Assumption: P *)
  False.                 (* Goal: Derive contradiction *)
Proof.
  intros.                (* Introduce P, Q, and assumptions *)
  unfold not in H0.      (* Unfold not Q to Q -> False *)
  apply H in H1.         (* Apply P -> Q to get Q *)
  contradiction.         (* Derive False from Q and ~Q *)
  (*
  unfold not in H0.
  apply H in H1.
  apply H0 in H1.
  assumption.
  *)  
  (*
  apply H0.
  apply H.
  assumption.
  *)
Qed.



(* 
   Goal: Prove that if two functions f and g are equal (f = g), 
   then for any argument x, applying f and g to x results in the same value (f x = g x).
   
   This demonstrates that equality of functions (in Coq's logic) entails 
   pointwise equality, via substitutivity of equals (Leibniz's law).
*)

Goal
  forall A B : Type,            (* A and B are arbitrary types *)
  forall (f g : A -> B),        (* f and g are functions from A to B *)
  f = g ->                      (* Assumption: f and g are equal *)
  forall x : A,                 (* For any x of type A *)
  f x = g x.                    (* Goal: f x equals g x *)

Proof.
  intros.                       (* Introduce A, B, f, g, the assumption f = g, and x *)
  rewrite H.                    (* Use the equality f = g (from H) to rewrite f as g *)
  reflexivity.                  (* Since f and g are now the same, f x = g x is trivially true *)
Qed.


Theorem successor_addition : forall n m : nat, S (n + m) = n + S m.
Proof.
  intros n m.
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    simpl.
    reflexivity.
  - (* Inductive step: n = S n' *)
    simpl.
    rewrite IH.
    reflexivity.
Qed.



