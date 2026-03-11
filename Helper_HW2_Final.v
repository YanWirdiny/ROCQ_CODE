Require Import List.
Import ListNotations.

(* Import the List module, which provides definitions and functions for lists.
   Import ListNotations allows us to use convenient list syntax like [a; b; c]. *)

(* Exercise with existential quantifiers and lists *)

Goal
    Exists (fun x => x = 10) [1; 2; 4; 10].   (* Goal: Prove that there exists an element x in the list [1; 2; 4; 10] such that x = 10 *)
Proof.
    (* The 'Exists' predicate is defined recursively with two constructors:
       - 'Exists_cons_hd' when the predicate holds for the head of the list.
       - 'Exists_cons_tl' when the predicate holds in the tail.
       Since the head (1) does not satisfy x = 10, we use 'Exists_cons_tl' to move to the tail. *)
    apply Exists_cons_tl.
    (* The head is now 2, which still does not satisfy x = 10.
       We apply 'Exists_cons_tl' again to consider the next element. *)
    apply Exists_cons_tl.
    (* The head is now 4, which also does not satisfy x = 10.
       We apply 'Exists_cons_tl' once more. *)
    apply Exists_cons_tl.
    (* Now the head is 10, which satisfies x = 10.
       We use 'Exists_cons_hd' to indicate that the predicate holds for the head. *)
    apply Exists_cons_hd.
    (* Prove that 10 equals 10 using 'reflexivity', satisfying the predicate. *)
    reflexivity.
Qed.

Print Exists.


(* Print the definition of List.In to understand its structure *)
Print List.In.

(* Goal: Prove that 10 is an element of the list [1; 2; 4; 10] *)
Goal In 10 [1; 2; 4; 10].
Proof.
    (* Simplify the 'In' predicate; it unfolds into a series of 'or's. *)
    simpl.
    (* The 'In' predicate becomes:
       10 = 1 \/ 10 = 2 \/ 10 = 4 \/ 10 = 10 \/ False.
       We need to navigate through the 'or's using 'right' and 'left'. *)
      (* Skip 4 *)
    right.
    right.
    right.
    left.

       (* Found 10 *)
    (* Prove that 10 equals 10 *)
    reflexivity.
Qed.





(* Goal: Prove that if a list has length 0, then it contains no elements *)
Goal
    forall (A:Type) (l:list A),
    length l = 0 ->
    forall x, ~ In x l.
Proof.
    (* Introduce the type A, list l, and the assumption length l = 0 *)
    intros.
    (* Unfold the definition of 'not'; we need to show that In x l leads to a contradiction *)
    unfold not.
    (* Assume that x is in l, aiming for a contradiction *)
    intros N.

    (* Perform case analysis on the list l *)
    destruct l.
    {
        (* Case when l is empty (nil) *)
        simpl in *. (* simpl in *. attempts to simplify everywhere 
                  it possibly can incuding the goa; and each hypothesis. *)

        (* Since In x [] simplifies to False, N is a proof of False *)

        apply N.
    }

    (* Case when l is non-empty (a :: l) *)
    simpl in *.
    (* length (a :: l) simplifies to S (length l), contradicting length l = 0 *)
    inversion H.  (* This contradiction arises because S n cannot be equal to 0 *)
Qed.




(* Goal: Prove that if a list has non-zero length, then there exists an element in it *)
Goal
    forall (A:Type) (l:list A),
    length l <> 0 ->
    exists x, In x l.
Proof.
    (* Introduce the type A, list l, and the assumption length l <> 0 *)
    intros.
    (* Perform case analysis on the list l *)
    destruct l.
    {
        (* Case when l is empty (nil) *)
        simpl in *.
        (* This leads to a contradiction since length [] = 0, but we assumed length l <> 0 *)
        (* Alternatively, demonstrate the contradiction explicitly *)
        (* Assert that 0 = 0, which is obviously true *)
        assert (Ha: 0 = 0).
        {
            reflexivity.
        }
        (* Apply the assumption length l <> 0 to Ha (length l = 0) *)
        apply H in Ha.
        (* This leads to a contradiction *)
        contradiction.
    }

    (* Case when l is non-empty (a :: l) *)
    simpl in *.
    (* We can choose 'a' as the existing element *)
    exists a.
    (* 'a' is at the head of the list, so In a (a :: l) holds via 'left' *)
    left.
    (* Prove that a equals a *)
    reflexivity.
Qed.



(* contradiction: use it when there is an immediate logical clash in the context (e.g. P and ~P, or something of type False).

inversion: use it to analyze an inductive equality (e.g. S n = 0) or break down a constructor based statement, sometimes yielding contradictions from mismatched constructors. *)



(* Goal: Prove that if x is in l1 ++ l2, then x is in l1 or x is in l2 *)
Goal
  forall (A : Type) (x : A) (l1 l2 : list A),
    In x (l1 ++ l2) -> In x l1 \/ In x l2.
Proof.
  (* Introduce all universally quantified variables and the assumption into the context *)
  intros A x l1 l2 H.

  (* Proceed by induction on the list l1 because '++' (append) is defined recursively on its first argument *)
  induction l1 as [| a l1' IHl1'].
  - (* Base case: l1 is the empty list [] *)
    (* Simplify concatenation: [] ++ l2 simplifies to l2 *)
    simpl in H.
    (* Since l1 is empty, x cannot be in l1, so we conclude x is in l2 *)
    right.
    (* Now H: In x l2 *)
    (* Since x is in l2, the assumption holds *)
    assumption.

  - (* Inductive case: l1 is a :: l1', where a is the head and l1' is the tail *)
    (* Simplify the concatenation: (a :: l1') ++ l2 becomes a :: (l1' ++ l2) *)
    simpl in H.
    (* Now H: In x (a :: (l1' ++ l2)), which unfolds to x = a \/ In x (l1' ++ l2) *)
    destruct H as [H_eq_a | H_in_tail].
    + (* Case when x equals the head 'a' *)
      (* Then x is in l1 by being its head *)
      left.
      (* Use the constructor In_head to show x ∈ a :: l1' *)
      left.
      (* x is in l1 via 'left' *)
      assumption.

    + (* Case when x is in (l1' ++ l2) *)
      (* Apply the induction hypothesis to H_in_tail *)
      apply IHl1' in H_in_tail.
      (* Now H_in_tail: In x l1' \/ In x l2 *)
      (* Clear IHl1' to simplify the context *)
      (* Now H: In x l1' \/ In x l2 *)
      destruct H_in_tail as [H_in_l1' | H_in_l2].
      * (* Subcase when x is in l1' *)
        (* Then x is in l1 by being in its tail *)
        left.
        (* x is in l1 via 'right' *)
        right.
        (* Apply H_in_l1' *)
        assumption.
      * (* Subcase when x is in l2 *)
        (* Then x is in l2 *)
        right.
        (* Apply H_in_l2 *)
        assumption.
Qed.





(* Prove the converse: if x is in l1 or l2, then x is in l1 ++ l2 *)
Goal
  forall (A : Type) (x : A) (l1 l2 : list A),
    (In x l1 \/ In x l2) ->
    In x (l1 ++ l2).
Proof.
  (* Introduce all universally quantified variables and the assumption into the context *)
  intros A x l1 l2 H.

  (* Proceed by induction on l1 because '++' is defined recursively on its first argument *)
  induction l1 as [| a l1' IHl1'].
  {
    (* Base case: l1 is empty *)
    (* Simplify concatenation: [] ++ l2 simplifies to l2 *)
    simpl in *.
    (* Since l1 is empty, In x l1 is False *)
    destruct H as [H_in_l | H_in_l2].
    {
      (* x cannot be in an empty list *)
      (* H_in_l1: In x [] *)
      contradiction.
    }
    (* x is in l2, so In x ([] ++ l2) holds *)
    (* Our goal simplifies to In x l2 *)
    assumption.
  }

  (* Inductive step: l1 is a :: l1', where a is the head and l1' is the tail *)
  (* Simplify the concatenation: (a :: l1') ++ l2 becomes a :: (l1' ++ l2) *)
  simpl in *.
  (* Our goal is to show In x (a :: (l1' ++ l2)) *)
  (* We consider two cases based on the assumption H *)
  destruct H as [H_in_l1 | H_in_l2].
  {
    (* Case when x is in l1 *)
    (* Since l1 = a :: l1', we further destruct H_in_l1 *)
    destruct H_in_l1 as [H_eq_a | H_in_l1'].
    {
      (* Subcase when x equals the head 'a' *)
      (* H_eq_a: x = a *)
      (* Since x = a, In x (a :: (l1' ++ l2)) holds via 'left' *)
      left.
      (* x equals a, so In x (a :: l1 ++ l2) via 'left' *)
      assumption.
    }
    {
      (* Subcase when x is in the tail l1' *)
      (* H_in_l1': In x l1' *)
      (* Create a new assumption Ha to apply the induction hypothesis *)
      assert (Ha: In x l1' \/ In x l2).
      {
        (* x is in l1' *)
        left.
        assumption.
      }
      (* Apply induction hypothesis to Ha *)
      apply IHl1' in Ha.
      (* Since x is not the head, we use 'right' to show In x (a :: (l1' ++ l2)) *)
      right.
      assumption.
    }
  }
  {
    (* Case when x is in l2 *)
    (* H_in_l2: In x l2 *)
    (* Create a new assumption Ha to apply the induction hypothesis *)
    assert (Ha: In x l1' \/ In x l2).
    {
      (* x is in l2 *)
      right.
      assumption.
    }
    (* Apply induction hypothesis to Ha *)
    apply IHl1' in Ha.
    (* Since x is not the head, we use 'right' to show In x (a :: (l1' ++ l2)) *)
    right.
    assumption.
  }
Qed.



(* The tactic sequence inversion H; subst; clear H. is commonly used in Coq for case analysis on inductive hypotheses, simplifying equations, and cleaning up the proof context.

Use inversion H; subst; clear H. when:

You need to decompose an inductive hypothesis (inversion).

Equations need substitution (subst).

The original hypothesis is no longer needed (clear H).


 *)



Print le. (* less than equal to *)

(* 
   Lemma: If S x <= y, then x <= y.

   This lemma states that if we have a successor of x (written as S x)
   that is less than or equal to y, then x itself must also be less
   than or equal to y.
*)
Lemma asd:
  forall x y,
    S x <= y ->
    x <= y.
Proof.
  (*
    We perform induction on y. The reason is that `<=` is defined
    recursively on its second argument, so a natural proof approach
    is to analyze cases based on y.
  *)
  induction y.

  (*
    The tactic `all: intros.` introduces all universally quantified
    variables (here x, y) and assumptions (S x <= y) in *both* subgoals
    that arise from `induction y`. It's a convenient way to handle
    introduce variables for each branch in one command.
  *)
  all: intros.

  - (*
       Base case: y = 0
       We must prove that if S x <= 0, then x <= 0.

       Intuitively, there is no natural number x such that S x <= 0,
       because S x is always at least 1. Thus we expect this to be impossible
       and derive a contradiction from the assumption S x <= 0.
    *)
    inversion H;           (*
                              `inversion H` performs a case analysis on H, 
                              which says S x <= 0. But there's no way for 
                              S x to be <= 0, so this immediately leads to a 
                              contradiction (no subgoal to prove).
                           *)
    subst; clear H.         (*
                              `subst` replaces variables according to any 
                              equalities found by `inversion`. `clear H` then 
                              removes the now redundant hypothesis from the 
                              context, since its contents have been used up.
                           *)

  - (*
       Inductive step: y = S y (the successor of y)

       We must prove that if S x <= S y, then x <= S y. We analyze the 
       assumption S x <= S y more closely by inversion.
    *)
    inversion H; subst; clear H.  (*
                                     Again we do `inversion` on S x <= S y, 
                                     which has two possible cases in Coq's 
                                     definition of <=:
                                     
                                     1) S x = S y  (via constructor le_n)
                                     2) S x <= y   (via constructor le_S)
                                  *)
    {
      (*
        Case 1: S x = S y
        If S x = S y, then x = y, and we must show x <= y. 
        That's immediate, since any number is <= itself.
      *)
      apply le_S.    (*
                        We use le_S to go from x <= x to S x <= S x. 
                        But we already have S x = S y, so effectively 
                        we prove x <= y by stepping through x <= x.
                     *)
      apply le_n.    (*
                        le_n states that any number is <= itself, i.e., 
                        x <= x. This finishes this subgoal.
                     *)
    }
    (*
      Case 2: S x <= y
      If S x <= y, then by the induction hypothesis (IH) applied to S x <= y, 
      we get x <= y. From that, we can deduce x <= S y by applying le_S again.
    *)
    apply IHy in H1.  (*
                         The induction hypothesis says: if S x <= y, then x <= y, 
                         because we're inducting on y. 
                      *)
    apply le_S.       
    assumption.       (*
                         We already have x <= y by IH, so applying `assumption` 
                         resolves x <= y immediately, and le_S upgrades it to
                         x <= S y.
                      *)
Qed.