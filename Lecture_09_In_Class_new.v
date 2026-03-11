(* Import necessary modules from the Coq standard library and Turing library *)
Require Import Coq.Strings.Ascii.   (* Provides definitions and operations for ASCII characters *)
Require Import Coq.Lists.List.      (* Provides definitions and operations for lists *)
Require Import Turing.Util.         (* Imports utility functions from the Turing library *)
Require Import Turing.Lang.         (* Imports language definitions from the Turing library *)

(* Import notations for lists and languages *)
Import ListNotations.               (* Enables the use of list notation, e.g., [a; b; c] *)
Import LangNotations.               (* Enables convenient notation for language operations *)

(* Open scopes for character and language notation *)
Open Scope char_scope.              (* Allows character literals like "a" *)
Open Scope lang_scope.              (* Allows language operation notations like U for union *)

(* Print the definition of Nil, the language containing only the empty word *)
Print Nil.

(* Define Void as the language that contains no words *)
Definition Void (w: word) := False.  (* Void rejects all words by definition *)


(* Lemma: No word is in the Void language *)
Lemma all_words_rejected:
  forall (w: word),        (* For any word w *)
   ~ In w Void.            (* w is not in Void *)
Proof.
  intros.                  (* Introduce arbitrary word w into the proof context *)
  unfold In, not, Void.    (* Replace the high-level definitions of In, not, and Void with their logical representations: 
                              - In means membership in a language.
                              - not means negation.
                              - Void is defined as False, meaning no words can exist in it. *)
  intros N.                (* Assume w ∈ Void to work towards a contradiction *)
  assumption.           (* Directly reach a contradiction because Void w := False, meaning no word can ever be in Void *)
  
Qed.



Lemma all_words_rejected2:
  forall (w: word),
    ~ In w Void.
Proof.
  intros.
  unfold In, not, Void.
  intros N.
  inversion N.
Qed.

(* Define All as the language that contains all possible words *)
Definition All (w: word) := True.    (* All accepts every word by definition *)


(* Lemma: Every word is in the All language *)
Lemma all_words_in_all:
  forall (w: word),        (* For any word w *)
  In w All.                (* w is in All *)
Proof.
  intros.                  (* Introduce arbitrary word w into the proof context *)
  unfold All, In.          (* Unfold definitions to simplify the goal: All is True, so w is trivially in All. *)
  Print True.              (* Print the definition of True for understanding *)
  apply I.                 (* I is the canonical proof of True in Coq. Since True is always true, this completes the proof. *)
Qed.


(* 
Illustration of language powers:
L = { ["a"] }            -- Language containing the word ["a"]
L ^^ 0 = Nil = { [] }    -- Zero power results in the language containing only the empty word
L ^^ 1 = { ["a"] }       -- First power is the language itself
L ^^ 2 = L >> L ^^ 1 = { ["a"; "a"] }  -- Second power concatenates L with itself
L ^^ 3 = { ["a"; "a"; "a"] }           -- Third power concatenates L three times
*)



(*
  Inductive definition of the language L^n (L raised to the nth power):
  - L^n contains all words formed by concatenating n words from L.
  - Base case: L^0 contains only the empty word "nil".
  - Inductive step: A word in L^(n+1) is formed by prepending a word from L 
    to a word in L^n.
*)

(* If w2 ∈ L^n

w1 ∈ L

w3 = w1 ++ w2

Then:

w3 ∈ L^(n+1) *)



Print Pow.

Inductive Pow (L: language) : nat -> word -> Prop :=
| pow_nil:  (* Base case: L^0 contains the empty word *)
  Pow L 0 nil
| pow_cons: (* Inductive case: Build L^(n+1) from L^n and L *)
  forall n w1 w2 w3,  (* For all n, words w1, w2, w3 *)
    In w2 (Pow L n) -> (* If w2 is in L^n *)
    In w1 L ->         (* and w1 is in L *)
    w3 = w1 ++ w2 ->   (* and w3 is the concatenation w1 ++ w2 *)
    Pow L (S n) w3.    (* Then w3 is in L^(n+1) *)


Print Pow.

(* Lemma: The word ["a"; "a"; "a"] is in the third power of the language containing ["a"] *)
Lemma in_aaa:
  In ["a"; "a"; "a"] (Pow "a" 3).   (* ["a"; "a"; "a"] is in Pow "a" 3 *)
Proof.
  unfold In.                         (* Unfold the definition of In to work directly with the membership relation *)
  (* Apply the pow_cons constructor to build the proof step by step for constructing powers of languages.
     pow_cons states that if w1 is in L and w2 is in Pow L n, then w1 ++ w2 is in Pow L (n+1). *)
  apply pow_cons with (w1 := ["a"]) (w2 := ["a"; "a"]). 
  - (* Prove that ["a"; "a"] is in Pow "a" 2. We recursively build the proof using pow_cons again. *)
    apply pow_cons with (w1 := ["a"]) (w2 := ["a"]).
    + (* Prove that ["a"] is in Pow "a" 1, and again apply pow_cons *)
      apply pow_cons with (w1 := ["a"]) (w2 := []).
      * (* Base case: The empty word is in Pow "a" 0, because any language raised to the power of 0 is Nil *)
        apply pow_nil.
      * (* Show that ["a"] = ["a"] ++ [] by simple concatenation of list theory *)
        reflexivity.
      * (* Show that [] = [] to conclude this part of the proof *)
        reflexivity.
    + (* Show that ["a"; "a"] = ["a"] ++ ["a"] *)
      reflexivity.
    + (* Show that ["a"] = ["a"] *)
      reflexivity.
  - (* Show that ["a"; "a"; "a"] = ["a"] ++ ["a"; "a"] *)
    Print Char. 
    apply char_in.  (* You can also use reflexivity here to complete this part of the proof *)
  - (* Show that ["a"; "a"] = ["a"; "a"] by reflexivity *)
    reflexivity.
Qed.



(* many_a n builds a word containing exactly n copies of "a" *)
Fixpoint many_a (n : nat) : word :=
  match n with
  | 0 => []                       (* no copies of "a" gives the empty word *)
  | S n' => "a" :: many_a n'      (* one more copy of "a" in front *)
  end.

(* Goal: show that the word with n copies of "a"
   belongs to the n-th power of the language "a" *)
Lemma in_many_a_pow :
  forall n,
    In (many_a n) (Pow "a" n).
Proof.

  (* Replace "In w L" with its actual meaning, so the goal becomes
     directly about Pow. *)
  unfold In.

  (* We prove the statement for every n by induction on n.

     This creates:
     1. Base case: n = 0
     2. Inductive case: n = S n'

     In the inductive case, IH means:
     many_a n' is already in Pow "a" n'
  *)
  induction n as [| n' IH].

  - (* Base case: n = 0 *)

    (* Simplify many_a 0.
       It becomes [].
       So now the goal is to show:
       Pow "a" 0 []
    *)
    simpl.

    (* pow_nil is exactly the constructor that says
       the empty word belongs to the 0-th power of a language *)
    apply pow_nil.

  - (* Inductive case: n = S n' *)

    (* Simplify many_a (S n').
       It becomes "a" :: many_a n'

       So the goal is now to show that this bigger word belongs to
       Pow "a" (S n')
    *)
    simpl.

    (* We use the constructor pow_cons.

       pow_cons says:
       if w2 is in Pow L n,
       and w1 is in L,
       and w3 = w1 ++ w2,
       then w3 is in Pow L (S n).

       Here we choose:
       w1 = ["a"]          the first piece
       w2 = many_a n'      the rest of the word
       w3 = ["a"] ++ many_a n'   the whole word
    *)
    apply pow_cons with
      (w1 := ["a"])
      (w2 := many_a n')
      (w3 := ["a"] ++ many_a n').

    + (* First subgoal:
         prove that the rest of the word, many_a n',
         is already in Pow "a" n'.

         This is exactly what the induction hypothesis IH says.
      *)
      apply IH.

    + (* Second subgoal:
         prove that ["a"] is in the language "a".

         char_in is the rule that says the one-letter word ["a"]
         belongs to the language containing the character "a".
      *)
      apply char_in.

    + (* Third subgoal:
         prove that the whole word is really the concatenation
         of the first piece and the rest.

         After simplification, this is just a basic equality of lists,
         so reflexivity solves it.
      *)
      reflexivity.
Qed.

Print char_in.

(* Example: the word with 1000 copies of "a" *)
Lemma in_1000_a :
  In (many_a 1000) (Pow "a" 1000).
Proof.
  apply in_many_a_pow.          (* follows from the general lemma *)
Qed.

(*
Inversion lemma for membership in the power of the character language {c}:

  Lemma: For any character c and natural number n,
  any word w in the language (Char c)^n (i.e., the nth power of the singleton language {[c]})
  must be the list containing exactly n repetitions of the character c.
  
  Proof Strategy:
  - Induction on n: Prove the base case (n=0) and inductive step (n -> n+1).
  - Base Case: (Char c)^0 contains only the empty word [].
  - Inductive Step: Assume (Char c)^n contains words of n c's. Show (Char c)^(n+1) contains words of (n+1) c's.
*)

Print pow1.

Lemma pow_char_in_inv:
  forall c n w,                      (* For any character c, natural number n, and word w *)
  In w (Pow (Char c) n) ->           (* If w is in the nth power of the language { [c] } *)
  w = Util.pow1 c n.                 (* Then w is the list consisting of n repetitions of c *)
Proof.
  induction n; intros. {             (* Induction on n, breaking the proof into base case (n=0) and inductive step *)
    simpl.                           (* Simplify Pow (Char c) 0 to its definition, which is just Nil (empty word) *)
    unfold In in H.                  (* Unfold the membership relation In to simplify the context *)

    (* You can memorize this part whenever we work with some proof of an inductive proposition. 
       Perform inversion on hypothesis H, breaking it down based on its inductive structure.
       In this case, inversion reveals that w must be the empty list [] in the base case (n=0).
       This is due to how Pow is inductively defined. *)
    inversion H.


(* subst replaces variables using equalities found in the context,
   turning goals into simpler expressions. *)

    subst.      

    clear H.          (* Remove the hypothesis H from the proof context, as it is no longer needed after the inversion step. 
                      H has served its purpose by providing w = []. *)

    reflexivity.                     (* Conclude that w = [] in the base case *)
  }
  (* c ^^ n represents the n-th power of the language containing the character *)

  
  simpl.                             (* Simplify Pow (Char c) (S n), which expands to concatenating c with Pow (Char c) n *)
  
(* Use inversion H; subst; clear H. when H is a proof of an inductive fact and we want to unpack its constructor information, apply equalities, and discard the old hypothesis. *)
  
  
  inversion H. subst. clear H.       (* Invert the structure of H, substitute and clear to break down w into components 
                                        based on the definition of Pow for (S n) *)

  (* H1 ((c ^^ n) w2): Hypothesis H1 states that w2 is in the language c raised to the power n, meaning w2 is the word formed by repeating the character c exactly n times.
  H2 (c w1): Hypothesis H2 asserts that w1 is in the language c, which means w1 is the word consisting of the single character c. *)
                                      
  apply IHn in H1.                   (* Apply the induction hypothesis to the smaller case, reducing the problem to a smaller n *)
  subst.                             (* Substitute the resulting equality back into the proof *)
  inversion H2.                      (* Invert H2 to show that w1 = [c], since we're dealing with Pow (Char c) *)
  subst.  
  simpl.                           (* Substitute the equality w1 = [c] into the proof context *)
  reflexivity.                       (* Conclude the proof by showing that w is c repeated (S n) times *)
Qed.

(* Print the definition of Star, the Kleene star operator *)
Print Star.


(* Example: how an implication becomes a hypothesis with [intros] *)

(* inversion H breaks an inductive hypothesis into the constructor case that produced it,
generating the equalities and smaller facts that must hold. *)

Lemma implication_example :
  forall x : nat,
    x = 3 ->
    x + 1 = 4.
Proof.
  intros x H.
  (* After [intros x H]:
       x : nat
       H : x = 3

     The hypothesis [H] comes from the implication
       x = 3 -> x + 1 = 4
     in the original goal.
  *)

  subst.
  reflexivity.
Qed.

Lemma implication_shape :
  forall P Q : Prop,
    P ->
    Q ->
    P.
Proof.
  intros P Q HP HQ.
  (* Here:
       HP : P
       HQ : Q

     Both HP and HQ come from implications in the goal.
  *)
  apply HP.
Qed.

Lemma pow_char_in_inv2:
  forall b n w,
    In w (Pow (Char b) n) ->
    w = Util.pow1 b n.
Proof.
  intros b n.
  induction n as [| n IHn].
  - intros w H.
    simpl.
    unfold In in H.
    inversion H.
    subst w.
    clear H.
    reflexivity.
  - intros w H.
    simpl.
    inversion H.
    subst w.
    clear H.
    apply IHn in H1.
    subst w2.
    inversion H2.
    subst w1.
    simpl.
    reflexivity.
Qed.


Print Star.


Goal In [] (Star "a").
(* We want to prove that the empty word `[]` is in the Kleene star `Star "a"`,
   i.e., `[]` can be formed by concatenating zero or more copies of `["a"]`. *)
Proof.
  exists 0.
  (*
    In the definition of `Star L`, we typically have something like:
      In w (Star L) ↔ exists n, w is formed by concatenating n words from L.
    Here, we choose `n = 0` and claim that `[]` is formed by zero concatenations of "a".
  *)

  constructor.
  (*
    The `constructor` tactic automatically picks the constructor of `Star` that
    corresponds to the empty word. In a typical inductive definition of Kleene star,
    there's a base constructor stating:
      Star L 0 = { [] }
    So `constructor` applies that base case, concluding that `[]` is indeed in `Star "a"`.


   In Coq, we typically use the constructor tactic when the goal we're trying to prove 
   is an instance of an inductive type or inductive proposition, and we want to use
   one of that type’s constructors directly. 

  *)
Qed.

Goal In [] (Star "a").
Proof.
  apply star_in_nil.
Qed.




Locate Star.

(* **Lemma union_l_void:** For any language L, the union of L with the empty language Void is equivalent to L *)
Lemma union_l_void:
  forall L,
  L U Void == L.
Proof.
  (* **Step 1:** Introduce the language L into the context.
     - This allows us to work with an arbitrary language L.
  *)
  intros.

  (* **Step 2:** Unfold the definition of language equivalence (`Equiv`).
     - In the lecture, we defined language equivalence (`==`) as pointwise equivalence: two languages are equivalent if they contain the same words.
     - Formally, `Equiv L1 L2 := forall w, L1 w <-> L2 w`.
     - By unfolding `Equiv`, we transform our goal into proving that for all words `w`, `(L U Void) w <-> L w`.
  *)
  unfold Equiv.

  (* **Step 3:** Introduce the word `w` into the context for both directions of the equivalence.
     - Since we have `forall w`, we need to introduce `w`.
     - The `all: intros.` tactic applies `intros` to all goals, ensuring that `w` is introduced in both directions of the proof.
  *)
  all: intros.

  (* **Step 4:** Split the equivalence into two implications.
     - We need to prove that `(L U Void) w -> L w` and `L w -> (L U Void) w`.
     - This follows from the definition of logical equivalence (`<->`) as two implications.
  *)
  split.

  - (* **First Implication:** Assume `w ∈ (L U Void)`, prove `w ∈ L`.
        - Our assumption is `H: (L U Void) w`.
        - Our goal is to prove `L w`.
    *)
    intros.

    (* **Step 5:** Use the inversion principle for union.
       - In the lecture, we discussed how to deconstruct the membership in a union of languages.
       - Specifically, if `w ∈ (L U Void)`, then either `w ∈ L` or `w ∈ Void`.
       - We can use an existing lemma or tactic to apply this reasoning.
    *)
    Search (In _ (_ U _)).  (* The `Search (In _ (_ U _)).` command searches for lemmas involving the `In` predicate applied to a union of languages.
     It helps us find lemmas that can decompose membership in a union into cases where the word is in one of the component languages. *)
     
    apply union_in_inv in H.

    (* **Step 6:** Deconstruct the disjunction obtained from the union inversion.
       - `H` now becomes `H: L w \/ Void w`.
       - We need to consider both cases.
    *)
    destruct H.

    {
      (* **Case 1:** `w ∈ L`.
         - This is exactly our goal, so we can conclude immediately.
      *)
      assumption.
    }

    (* **Case 2:** `w ∈ Void`.
       - Recall from the lecture that `Void` is the empty language; it contains no words.
       - Therefore, the assumption `w ∈ Void` leads to a contradiction.
    *)
    contradiction.
   (* inversion H. *)

  -  (* **Second Implication:** Assume `w ∈ L`, prove `w ∈ (L U Void)`.
        - Our assumption is `L w`.
        - Our goal is to prove `(L U Void) w`.
    *)
    (* We don't need to introduce any new assumptions; we can proceed directly. *)

    (* **Step 7:** Use the left constructor of the union to show `w ∈ (L U Void)`.
       - In the lecture, we discussed that to prove membership in a union, we need to show that `w ∈ L` or `w ∈ Void`.
       - Since we have `w ∈ L`, we can use the left inclusion.
    *)
    intros H.
    unfold Union.
    
    left.

    Print In.
    
    unfold In in H.
    
    

    (* **Step 8:** Conclude that `w ∈ L`.
       - This matches our assumption, so we can conclude the proof of this implication.
    *)
    assumption.
Qed.


Search (exists w1 w2, _ = _ ++ _ /\ In _ _ /\ In _ _).
(* If a word w is in L1 >> L2, then there exist
words w1 and w2 such that w = w1 ++ w2, w1 ∈ L1, and w2 ∈ L2 *)

(* **Lemma app_l_void:** For any language L, concatenating L with Void results in Void *)
Lemma app_l_void:
  forall L,
    L >> Void == Void.
Proof.
  (* **Step 1:** Split the equivalence into two implications.
     - We aim to prove that for all words `w`, `(L >> Void) w <-> Void w`.
     - Since `Void w` is always false (as `Void` contains no words), we need to show that `(L >> Void) w` is also always false.
  *)
  split.

  (* **Step 2:** Introduce the word `w` into the context.
     - We need to work with an arbitrary word `w`.
  *)
  all: intros. (* Apply the tactic intros. to all remaining subgoals *)
 
  - (* **First Implication:** Assume `w ∈ (L >> Void)`, prove `w ∈ Void`.
        - Since `Void` contains no words, the goal `w ∈ Void` is always false.
        - Our strategy is to show that `w ∈ (L >> Void)` leads to a contradiction.
    *)
    (* **Step 3:** Use the inversion principle for concatenation.
       - From the lecture, concatenation `L >> Void` contains words formed by concatenating words from `L` with words from `Void`.
       - Since `Void` contains no words, there are no words from `Void` to concatenate, so `L >> Void` should be empty.
       - Formally, we proceed by applying the inversion principle for concatenation.
    *)
    apply app_in_inv in H.

    (* **Step 4:** Deconstruct the existence obtained from the concatenation inversion.
       - `H` now provides us with words `w1` and `w2` such that:
         - `w = w1 ++ w2`
         - `w1 ∈ L`        (* This is `Ha` *)
         - `w2 ∈ Void`     (* This is `Hb` *)
       - We need to analyze these to reach a contradiction.
    *)
    destruct H as [w1 [w2 [Ha [Hb Hc]]]].

    (* **Step 5:** Substitute `w` with `w1 ++ w2` to reflect the concatenation.
       - This helps to make the structure of `w` explicit.
    *)
    subst.

    (* **Step 6:** Observe that `w2 ∈ Void`.
       - Since `Void` contains no words, `w2 ∈ Void` is false.
       - Therefore, `Hc` leads to a contradiction.
    *)
    contradiction.

  - (* **Second Implication:** Assume `w ∈ Void`, prove `w ∈ (L >> Void)`.
        - Since `w ∈ Void` is always false, this assumption cannot hold.
        - Therefore, this implication holds vacuously.
    *)
    contradiction.
Qed.






(* **Lemma not_in_void:** States that for any word `w`, it is not the case that `w` is in `Void`.
   In other words, no word belongs to the empty language `Void`. *)
   Lemma not_in_void:
   forall w,
   ~ In w Void.
 Proof.
   (* **Introduce the arbitrary word `w` into the context.**
      - We are stating that `w` is any word (a list of ASCII characters).
      - This allows us to reason about any possible word in the proof.
   *)
   intros w.
 
   (* **Assume, for the sake of contradiction, that `w ∈ Void`.**
      - Our goal is `~ In w Void`, which is equivalent to `In w Void -> False`.
      - By writing `intros N`, we introduce the assumption `N : In w Void`.
        Coq knows that `N` must be `In w Void` because it is the antecedent of the implication in our goal.
      - Even though we did not explicitly specify what `N` is, Coq infers it from the goal's structure.
      - **Key Point for Students:** Coq will recognize that this assumption leads to a contradiction based on the definitions.
   *)
   intros N.
 
   (* **Perform inversion on the assumption `N : In w Void`.**
      - The `inversion` tactic is used to analyze and deconstruct inductive hypotheses.
      - Since `Void` is defined as the empty language (contains no words), the `In` predicate
        applied to `Void` has no constructors that could have produced `N`.
      - This means that `N` cannot exist, leading Coq to infer a contradiction automatically.
      - Coq infers the contradiction at this step because it realizes that `N` is impossible.
      - The inversion effectively tells Coq that our assumption is invalid, allowing us to conclude the proof.
   *)
   inversion N.
 Qed.
 
 



(* Define Vowel as the language containing the single-character words for vowels *)
Definition Vowel w :=
  w = ["a"]                         (* Word is ["a"] *)
  \/ w = ["e"]                      (* Or word is ["e"] *)
  \/ w = ["i"]                      (* Or word is ["i"] *)
  \/ w = ["o"]                      (* Or word is ["o"] *)
  \/ w = ["u"].                     (* Or word is ["u"] *)

(* Lemma: Vowel is equivalent to the union of Char c for each vowel c *)
Lemma vowel_eq:
  Vowel == (Char "a" U Char "e" U Char "i" U Char "o" U Char "u").
Proof.
  unfold Equiv.                     (* Unfold the definition of equivalence between two languages *)
  intros w.                         (* Introduce arbitrary word w into the proof context *)
  split; intros.                    (* Split the proof into two directions: proving both sides of the equivalence *)
  - (* Forward direction: Vowel w -> In w (Union of vowel characters) *)
    unfold Vowel in *.              (* Unfold the definition of Vowel to expose the disjunction of cases *)
    unfold In in H.                 (* Unfold the definition of In to work with membership *)
    intuition; subst.               (* Use the intuition tactic to handle the multiple disjunctions in the Vowel definition *)
    + left.                         (* w = ["a"], so we choose the first case in the union *)
      left.
      left.
      left.
      reflexivity.
    + left.                         (* w = ["e"], so we choose the second case *)
      left.
      left.
      right.
      reflexivity.
    + left.                         (* w = ["i"], third case *)
      left.
      right.
      reflexivity.
    + left.                         (* w = ["o"], fourth case *)
      right.
      reflexivity.
    + right.                        (* w = ["u"], fifth case *)
      reflexivity.
  - (* Backward direction: In w (Union of vowel characters) -> Vowel w *)
    destruct H.                     (* Break down the union into its individual cases *)
    + destruct H.
      * destruct H.
        { destruct H.
          { inversion H.            (* If w = ["a"], inversion confirms it and we prove Vowel w = ["a"] *)
            subst.
            unfold In, Char in *.
            unfold Vowel.
            intuition.
          }
          inversion H.              (* Contradiction for other cases *)
          admit.
        }
        inversion H.
        admit.
      * inversion H.
        admit.
    + inversion H.
      admit.
Admitted.                            (* Admit the remaining cases for simplicity *)



(* ============================================================ *)
(* Two ways to define odd numbers in Rocq / Coq                 *)
(* ============================================================ *)

(* ------------------------------------------------------------ *)
(* About Fixpoint vs Definition                                 *)
(* ------------------------------------------------------------ *)
(* Fixpoint:
   - Used to define a recursive function.
   - The function calls itself on a smaller input.
   - Rocq checks that recursion is structurally decreasing,
     so the computation will terminate.
   - Example: oddb, length, factorial.

   Definition:
   - Used to define something without recursion.
   - It is just a direct name for an expression, function,
     constant, or formula.
   - No recursive self-calls are allowed in a plain Definition.
   - Example: Definition two := 2.
              Definition is_zero (n : nat) := n = 0.

   So:

   - Use Fixpoint when you want recursion and computation by
     repeatedly reducing the input.
   - Use Definition when no recursive step is needed.

   In this file:
   - oddb uses Fixpoint because it checks oddness recursively.
   - odd uses Inductive because it defines oddness as a property,
     not as a computation.
*)
(* ------------------------------------------------------------ *)


(* ------------------------------------------------------------ *)
(* 1. Recursive definition                                      *)
(* ------------------------------------------------------------ *)
(* This version COMPUTES whether a natural number is odd.       *)
(* The output is a boolean value: true or false.                *)
(*                                                              *)
(* Why Fixpoint here?                                           *)
(* Because the function calls itself on a smaller number n'.    *)
(*                                                              *)
(* Idea:                                                        *)
(* - 0 is not odd                                               *)
(* - 1 is odd                                                   *)
(* - for n >= 2, remove 2 and check again                       *)
(* ------------------------------------------------------------ *)

(* A recursive definition can also be used in formal proofs, especially when it defines

   a computable test or a proposition; however, inductive definitions are usually cleaner for proof-oriented reasoning. *)


Fixpoint oddb (n : nat) : bool :=
  match n with
  | 0 =>
      false
      (* 0 is not odd *)
  | 1 =>
      true
      (* 1 is odd *)
  | S (S n') =>
      oddb n'
      (* n is odd exactly when n - 2 is odd *)
  end.

(* Some sample computations *)

Compute oddb 0.   (* false *)
Compute oddb 1.   (* true *)
Compute oddb 2.   (* false *)
Compute oddb 5.   (* true *)

Example oddb_5 : oddb 5 = true.
Proof.
  simpl.
  reflexivity.
Qed.


(* ------------------------------------------------------------ *)
(* 2. Inductive definition                                      *)
(* ------------------------------------------------------------ *)
(* This version DOES NOT compute true/false.                    *)
(* Instead, it defines oddness as a logical property.           *)
(*                                                              *)
(* odd n means: "n is odd".                                     *)
(*                                                              *)
(* Why not Fixpoint here?                                       *)
(* Because we are not computing a value.                        *)
(* We are defining what counts as a valid proof of oddness.     *)
(*                                                              *)
(* Idea:                                                        *)
(* - 1 is odd                                                   *)
(* - if n is odd, then n + 2 is also odd                        *)
(* ------------------------------------------------------------ *)

Inductive odd : nat -> Prop :=
| odd_1 :
    odd 1
    (* Base constructor: 1 is odd *)
| odd_SS :
    forall n : nat,
      odd n ->
      odd (S (S n)).
    (* Inductive constructor:
       if n is odd, then n + 2 is odd *)


(* Examples of proving that specific numbers are odd *)

Example odd_3 : odd 3.
Proof.
  apply odd_SS.
  apply odd_1.
Qed.

Example odd_5 : odd 5.
Proof.
  apply odd_SS.
  apply odd_SS.
  apply odd_1.
Qed.


(* ============================================================ *)
(* Summary                                                      *)
(* ============================================================ *)
(* oddb : nat -> bool                                           *)
(*   Uses Fixpoint because it recursively computes oddness.     *)
(*                                                              *)
(* odd : nat -> Prop                                            *)
(*   Uses Inductive because it defines oddness as a property    *)
(*   that can be proved.                                        *)
(*                                                              *)
(* Definition would be used only when we want a direct          *)
(* non-recursive definition.                                    *)
(* ============================================================ *)








