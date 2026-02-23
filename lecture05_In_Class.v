(* We define a polymorphic list data type to avoid redundancy 
when defining lists for different types like natural numbers and booleans. By parameterizing 
the list over a type X, we can create lists of any type.

Define a polymorphic list data type parameterized by a type X.
X : Type means that X is a type (such as nat, bool, etc.), 
list X will be a list containing elements of type X.
The := symbol in this context is used to introduce 
how the list type is constructed, defining its constructors. *)

Inductive list (X : Type) : Type :=
  | nil                              (* Constructor for the empty list *)
  | cons : X -> list X -> list X.    (* Constructor to add an element of type X to a list of X 
                                      cons adds an element of type X to the front (head) of an existing list of type list X.*)                        


(* Check the type of nil without specifying the type parameter *)
Check nil.
(* Output: nil : forall X : Type, list X *)

(* Check the type of nil when specifying the type parameter as nat *)
Check (nil nat).
(* Output: nil nat : list nat *)

(* Construct a list of natural numbers: 1 :: nil *)
Check cons nat 1 (nil nat).
(* Output: cons nat 1 (nil nat) : list nat *)





(* Construct a list of booleans using type inference with underscores
  - The underscore `_` in Coq is used for type inference. It tells Coq to infer the type 
    based on the surrounding context rather than explicitly specifying it.
  
  - In the expression `cons _ true (cons _ true (nil _))`, Coq automatically infers the type `bool` 
    for the elements and the list.

  - `cons _ true`: The `_` tells Coq to infer the type of the list. Since `true` is a boolean value (`bool`), 
    Coq infers that the type of the list must be `list bool`.

  - `nil _`: Similarly, the `_` here tells Coq to infer the type of the empty list. Since the earlier elements 
    are booleans, Coq infers that `nil` must be of type `list bool`.
  
  - So, the whole expression is inferred as a list of booleans: `list bool`.
  
  `_` allows Coq to automatically determine the type of the elements and the list 
  without explicitly providing it, which is useful when the type can be inferred from context.

*)

Check cons _ true (cons _ true (nil _)).
(* Output: cons bool true (cons bool true (nil bool)) : list bool *)




(* Construct a list of natural numbers using type inference *)
Check cons _ 1 (nil _).
(* Output: cons nat 1 (nil nat) : list nat *)

(* This will fail because we're trying to construct a list of booleans with a natural number *)
Fail Check cons nat 1 (nil bool).
(* Error: The term "1" has type "nat" while it is expected to have type "bool" *)



(* Compute a list of natural numbers: 1 :: 2 :: nil *)
(* :: means cons...*)   
Compute cons _ 1 (cons _ 2 (nil _)).
(* Output: cons nat 1 (cons nat 2 (nil nat)) *)


(* Check the type of list *)
Check list.
(* Output: list : Type -> Type *)



(**************************************************************************************)

(*
  Defining a Sum Type to Hold Booleans or Naturals

  To create a list that can hold both booleans and natural numbers, we define a sum type 
  `bool_or_nat`. This allows us to encapsulate both types within a single list.
*)

(* Define an inductive type that can be either a bool or a nat *)
Inductive bool_or_nat :=

  (* Constructor for booleans:
     a_bool : bool -> bool_or_nat:
     This constructor takes a boolean (bool) as an argument and
     returns a value of type bool_or_nat. It's used to wrap a
     boolean in the bool_or_nat type. *)
  | a_bool : bool -> bool_or_nat

  (* Constructor for natural numbers:
     a_nat : nat -> bool_or_nat:
     This constructor takes a natural number (nat) as an argument and
     returns a value of type bool_or_nat. It's used to wrap a
     natural number in the bool_or_nat type. *)
  | a_nat : nat -> bool_or_nat.


(* Check the type of a list of bool_or_nat *)
Check list bool_or_nat.




(* 
  This function takes a type `X` and a value `x` of type `X`,
  and it simply returns `x`.

  Type: forall X : Type, X -> X
  Meaning: For any type `X`, this function takes a value of type `X` 
  and returns the same value. It is a polymorphic identity function.
*)
Check (fun (X : Type) (x : X) => x).
(* Output: fun (X : Type) (x : X) => x : forall X : Type, X -> X *)





(* 
  This function takes `f` (a function from `nat` to `nat`) 
  and applies it to `0`.

  Type: (nat -> nat) -> nat
  Meaning: This function takes another function `f: nat -> nat` as input,
  applies it to `0`, and returns a natural number.
*)
Check (fun (f : nat -> nat) => f 0).
(* Output: fun (f : nat -> nat) => f 0 : (nat -> nat) -> nat *)

Definition add_one (n : nat) : nat := n + 1.
Definition double (n : nat) : nat := n * 2.


Compute (fun (f : nat -> nat) => f 0) add_one.
Compute (fun (f : nat -> nat) => f 10) double.
(* Output: 1 *)



(**************************************************************************************)



(* 
  Define the append function for lists of type X 
  This function appends two lists of type X. It's a polymorphic function
  that works for lists of any type X.

   - {X : Type} means the function is polymorphic and works for any type X.
   - l1 and l2 are the two lists we want to append.
   - The return type is list X, which means the function returns a list of type X.
   - The function uses pattern matching on l1:
     - If l1 is empty (`nil _`), return l2 (base case). The `_` is used to infer 
       the type of the empty list (`nil` requires a type in this custom list definition).
     - If l1 has elements (`cons _ h t`), recursively append the tail of l1 to l2, 
       and prepend the head element (h) to the result (recursive case).
       
       (cons constructs a new list by prepending an element (the head) to an existing list (the tail)).
       The `_` allows Coq to infer the type `X` when constructing the list with `cons`.)

*)


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  (* Match on the first list l1 to determine how to append *)
  match l1 with
  | nil _ => l2    (* If the first list is empty, return the second list directly *)
                  (* This is the base case, no more recursion needed *)
  | cons _ h t => cons X h (app t l2)
                  (* If the first list is not empty, prepend the head (h) to the result of 
                     appending the tail (t) of the first list with the second list (l2). *)
                  (* This is the recursive case: call `app` on the tail of l1 and l2. *)
  end.

Compute app (cons _ 1 (cons _ 2 (nil _))) (cons _ 3 (cons _ 4 (nil _))).

Compute app (cons _ (a_bool true) (cons _ (a_nat 42) (nil _))) (cons _ (a_nat 3) (nil _)).

Compute app (cons _ false (cons _ false (nil _))) (cons _ false (cons _ false (nil _))).

Compute app (cons _ 3 (cons _ 4 (nil _))) (cons _ 5 (cons _ 6 (nil _))).

Compute app (cons _ 1 (cons _ 2 (nil nat))) (cons _ 3 (cons _ 4 (nil nat))).
Compute app (cons _ 1 (cons _ 2 (nil _))) (cons _ 3 (cons _ 4 (nil _))).


(*  exercise 


*)
Fixpoint snoc [X: Type] (l : list X ) (x : X) : list X := 
match l with
| nil _  =>  cons X x (nil X) (*.  we add cons*)
| cons  _ H  T  => cons X H ( snoc  T x  )
end.





(* Prac: make the order reversed *)

Fixpoint app_reverse {X : Type} (l1 l2 : list X) : list X :=
  match l2 with
  | nil _ => l1    (* If the second list is empty, return the first list (l1). *)
  | cons _ h t => cons X h (app_reverse l1 t)
                (* Recursively append the first list to the tail of the second list (l2). *)
  end.

Compute app_reverse (cons _ 1 (cons _ 2 (nil _))) (cons _ 3 (cons _ 4 (nil _))).

Compute app_reverse (cons _ (a_bool true) (cons _ (a_nat 42) (nil _))) (cons _ (a_nat 3) (nil _)).

Compute app_reverse (cons _ false (cons _ false (nil _))) (cons _ false (cons _ false (nil _))).

Compute app_reverse (cons _ 3 (cons _ 4 (nil _))) (cons _ 5 (cons _ 6 (nil _))).

Compute app_reverse (cons _ 1 (cons _ 2 (nil nat))) (cons _ 3 (cons _ 4 (nil nat))).
Compute app_reverse (cons _ 1 (cons _ 2 (nil _))) (cons _ 3 (cons _ 4 (nil _))).




(* The first _ in cons _ true tells Coq to infer that the type is bool, because true is of type bool.
The second _ in nil _ is also inferred as bool, because nil must match the type of the list *)
Check cons _ true (nil _).


(**************************************************************************************)




(*
  Using Implicit Arguments with Lists

  We redefine the list data type and make some arguments implicit to simplify its usage. 
  This leverages Coq's ability to infer certain parameters, reducing redundancy.


 Implicit arguments are a feature in Coq that allows the system to automatically 
 infer certain function or constructor arguments based on the context in which 
 they are used. This feature can significantly reduce the verbosity of code and
make it more readable.

*)

(* 
  Define another polymorphic list data type `list2`.
  This list type is similar to the default Coq `list` type but custom-defined for flexibility.
  
  - `X : Type` means that the list is polymorphic, meaning that it works for any type `X`.
  - `nil2` represents the empty list.
  - `cons2` is used to add an element of type `X` to the front of the list, creating a new list.
*)
Inductive list2 (X : Type) : Type :=
  | nil2                                     (* `nil2` is the constructor for the empty list of type X. *)
  | cons2 : X -> list2 X -> list2 X.         (* `cons2` is the constructor that takes an element of type X 
                                                and a list2 of type X, and produces a new list with that element as the head. *)


(* 
  The `Arguments` command is used to make some parameters implicit.
  - This reduces the need to explicitly pass type parameters when Coq can infer them.
  
  Here, the type `X` is inferred from the context when `nil2` is used, so we make it implicit. 
  This means we don't need to write `nil2 nat` or `nil2 bool`—Coq will infer it automatically.
*)
Arguments nil2 {_}.                           (* Make the type parameter `X` implicit for `nil2`, allowing Coq to infer the type. *)


(* 
  Similarly, we make the type parameter `X` implicit for the `cons2` constructor.
  Coq will infer the type of the element being inserted into the list, reducing redundancy.
  
  - `x` is the head element of the list.
  - `y` is the tail of the list (a `list2`).
*)
Arguments cons2 {X} x y.                      (* Make the type parameter `X` implicit for `cons2`, allowing Coq to infer it. *)


(* 
  Define the append function for `list2`, called `app2`. 
  This function appends two lists (`l1` and `l2`) of the same type `X`.
  
  - `Fixpoint` defines a recursive function, which is required for this list append operation.
  - `l1` and `l2` are the two input lists to be appended together.
  - If `l1` is empty, the function simply returns `l2` (base case).
  - If `l1` is non-empty, it recursively appends the tail of `l1` to `l2` and prepends the head of `l1` to the result.
  - The return type is `list2 X`, which is a list of type `X`.
*)
Fixpoint app2 {X : Type} (l1 l2 : list2 X) : list2 X :=
  match l1 with
  | nil2 => l2                                (* Base case: If the first list `l1` is empty, return the second list `l2`. *)
  | cons2 h t => cons2 h (app2 t l2)          (* Recursive case: Prepend the head `h` of `l1` to the result of 
                                                 recursively appending the tail `t` of `l1` to `l2`. *)
  end.


(* Compute nil2; since the type parameter is implicit, Coq may not infer it without context *)
Compute nil2.
(* Output: nil2 : list2 ?X *)

(* Use @ to specify the type parameter explicitly when needed *)
Compute @nil2 nat.
(* Output: nil2 : list2 nat *)



(**************************************************************************************)


(* 
  Proving Transitivity of Equality

  We show here how to prove that equality is transitive for any type `T`.
  Transitivity of equality means that if `x = y` and `y = z`, then `x = z` holds true.
  This property is essential in proofs and is demonstrated using Coq's basic tactics 
  like `rewrite` and `apply`.
  
  - `forall (T : Type)` means that the theorem applies to any type `T`.
  - `x`, `y`, and `z` are variables of type `T`.
  - The goal is to prove that if `x = y` and `y = z`, then `x = z` (transitivity of equality).
*)

(*Purpose: apply is used to use a hypothesis or a known theorem to match the current goal.
 Essentially, it tries to unify the goal with the conclusion of an existing theorem or hypothesis.

Usage: You use apply when your goal matches or can be reduced to an earlier hypothesis 
or theorem by unification.*)

(* Theorem stating that equality is transitive for any type T *)
Theorem eq_trans : forall (T : Type) (x y z : T),
  x = y ->                         (* Hypothesis 1: `x = y` *)
  y = z ->                         (* Hypothesis 2: `y = z` *)
  x = z.                           (* Goal: Prove `x = z` *)
Proof.
  intros T x y z eq1 eq2.           (* Introduce the type `T` and variables `x`, `y`, and `z` 
                                       as well as the equality hypotheses `eq1` and `eq2`. *)
  rewrite -> eq1.                   (* Use `eq1` to rewrite `x` in terms of `y`. Now the goal becomes `y = z`. *)
  apply eq2.                        (* Apply `eq2`, which asserts that `y = z`, to complete the proof. *)
Qed.

Check eq_trans.



(* Purpose: rewrite is used to substitute one side of an equation with the other side.
It applies to equalities to replace terms in the goal using known equalities
(hypotheses or previously proven theorems).

Usage: You use rewrite when you want to transform the goal by replacing
a term with its equivalent value. *)

(* Theorem stating that equality is transitive for any type T *)
Theorem eq_trans_v2 : forall (T : Type) (x y z : T),
  x = y ->                         (* Hypothesis 1: `x = y` *)
  y = z ->                         (* Hypothesis 2: `y = z` *)
  x = z.                           (* Goal: Prove `x = z` *)
Proof.
  intros T x y z eq1 eq2.           (* Introduce the type `T` and variables `x`, `y`, and `z` 
                                       as well as the equality hypotheses `eq1` and `eq2`. *)
  rewrite -> eq1.                   (* Use `eq1` to rewrite `x` in terms of `y`. Now the goal becomes `y = z`. *)
  rewrite -> eq2.                   (* Use `eq2` to rewrite `y` in terms of `z`. Now the goal becomes `z = z`. *)
  reflexivity.                      (* Conclude that `z = z`, which is trivially true. *)
Qed.


(**************************************************************************************)


(* 
  Applying a Hypothesized Transitivity Function

  This theorem demonstrates a higher-order reasoning approach. 
  We prove that if we have a transitivity function `eq1` that asserts 
  `x = y -> y = z -> x = z`, then given `x = y` and `y = z`, we can conclude `x = z`.
  
  This function-based approach emphasizes using transitivity in a more flexible form.
*)

(* Theorem using a hypothesized transitivity function *)
Theorem eq_trans_2 : forall (T : Type) (x y z : T),
  (x = y -> y = z -> x = z) ->     (* Hypothesis `eq1`: A function asserting transitivity. *)
  x = y ->                         (* Hypothesis `eq2`: `x = y`. *)
  y = z ->                         (* Hypothesis `eq3`: `y = z`. *)
  x = z.                           (* Goal: Prove `x = z`. *)
Proof.
  intros T x y z eq1 eq2 eq3.       (* Introduce the type `T` and variables `x`, `y`, and `z`, 
                                       as well as the hypotheses `eq1`, `eq2`, and `eq3`. *)
  apply eq1.                        (* Apply the hypothesized transitivity function `eq1` to reduce the goal. *)
  - apply eq2.                      (* Prove `x = y` using `eq2`. *)
  - apply eq3.                      (* Prove `y = z` using `eq3`. *)
Qed.


(*
  Using Transitivity to Relate Variables

  We can use the transitivity of equality to deduce `z = 1` from the given equalities. This 
  example illustrates how to chain equalities together.


The apply eq_trans with (y := y). applies the transitivity of equality
(eq_trans) to your goal x = z, explicitly specifying that y is 
the intermediate value connecting x and z through the equalities x = y and y = z.


*)

(* Theorem stating that if x = 1, x = y, and y = z, then z = 1 *)
Theorem eq_trans_nat : forall (x y z : nat),
  x = 1 ->                         (* Hypothesis eq1 *)
  x = y ->                         (* Hypothesis eq2 *)
  y = z ->                         (* Hypothesis eq3 *)
  z = 1.
Proof.
  intros x y z eq1 eq2 eq3.        (* Introduce variables and hypotheses *)
  assert (eq4: x = z). {           (* Assert that x = z *)

    (* apply theorem_name with (parameter := value). *)
    apply eq_trans with (y:=y).    (* Use transitivity with intermediate y *)
    - apply eq2.                   (* Apply eq2: x = y *)
    - apply eq3.                   (* Apply eq3: y = z *)
    (* Alternative methods are commented out *)
    (*
    apply (eq_trans _ _ y).
    - apply eq2.
    - apply eq3.
    *)
    (*
    apply (eq_trans nat x y).
    - apply eq2.
    - apply eq3.
    *)
    (*
    assert (A := eq_trans nat x y z eq2 eq3).
    apply A.
    *)
  }
  rewrite <- eq4.                  (* Rewrite z with x using eq4 *)
  apply eq1.                       (* Apply eq1: x = 1 *)
Qed.


(* symmetry: Applies to the goal by default when used without in. *)
Theorem symmetry_example : forall (a b : nat),
  a = b -> b = a.
Proof.
  intros a b H.
  symmetry.
  apply H.
Qed.


(* symmetry in H: Applies to the hypothesis H, reversing the equality in that hypothesis. *)
Theorem symmetry_example_v2 : forall (a b : nat),
  a = b -> b = a.
Proof.
  intros a b H.
  symmetry in H.
  apply H.
Qed.



(*
  Using Symmetry and Rewrite to Prove Equality

  We can also prove `z = 1` by manipulating the equalities using symmetry and rewrite tactics.
*)

(* Theorem stating that if x = 1, x = y, and y = z, then z = 1 *)
Theorem eq_trans_nat56 : forall (x y z : nat),
  x = 1 ->                         (* Hypothesis H *)
  x = y ->                         (* Hypothesis H0 *)
  y = z ->                         (* Hypothesis H1 *)
  z = 1.
Proof.
  intros.                          (* Introduce variables and hypotheses *)
  symmetry in H1.                  (* Use symmetry on H1 to get z = y *)
  rewrite H1.                      (* Rewrite z with y *)
  rewrite <- H0.                   (* Rewrite y with x using H0 *)
  apply H.                         (* Apply H: x = 1 *)
Qed.

(*
  Proving Equality with Reversed Equality Hypothesis

  We need to prove `z = 1` given that `x = 1`, `x = y`, and `z = y`. This requires recognizing 
  that `z = y` can be flipped to `y = z` using symmetry.
*)

(* Theorem stating that if x = 1, x = y, and z = y, then z = 1 *)
Theorem eq_trans_nat43 : forall (x y z : nat),
  x = 1 ->                         (* Hypothesis eq1 *)
  x = y ->                         (* Hypothesis eq2 *)
  z = y ->                         (* Hypothesis eq3 *)
  z = 1.
Proof.
  intros x y z eq1 eq2 eq3.        (* Introduce variables and hypotheses *)
  assert (eq4: x = z). {           (* Assert that x = z *)
    apply eq_trans with (y:=y).    (* Use transitivity *)
    - apply eq2.                   (* Apply eq2: x = y *)
    - symmetry.                    (* Use symmetry on eq3 to get y = z  *)
    (* - symmetry in eq3 *)
      apply eq3.
  }
  rewrite <- eq4.                  (* Rewrite z with x *)
  apply eq1.                       (* Apply eq1: x = 1  *)
  (* assumption. *)
Qed.



(*******************************************************************************************)
(* S 2 is 3, and S 3 is 4. Since 3 ≠ 4, S 2 ≠ S 3. *)

(*
  Proving Injectivity of the Successor Function

  Constructors are injective, meaning that if `S n = S m`, 
  then `n = m`. This leverages the injectivity of constructors in inductive types.
*)

(* Theorem stating that the successor function S is injective *)
Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m eq1.                  (* Introduce variables `n`, `m`, and hypothesis `eq1` *)
  inversion eq1.                   (* Use inversion on `eq1` to extract `n = m` *)
  reflexivity.                     (* Conclude `n = m` using `reflexivity` *)
Qed.


Theorem S_injective_alt : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* The theorem eq_add_S states that if S n = S m, then n = m. *)
  apply eq_add_S in H.   (* Coq's standard library theorem *)
  apply H.
Qed.


Theorem S_injective_alt2 : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H.
  (* f_equal: A theorem stating that if a = b, then f a = f b for any function f. *)
  (* pred: The predecessor function for natural numbers, where pred 0 = 0 and pred (S n) = n. *)
  apply (f_equal pred) in H.   (* Apply the predecessor function to both sides *)
  simpl in H.                  (* Simplify `pred (S n)` to `n` *)
  (* simpl in H.                  Simplify `pred (S m)` to `m` *)
  apply H.
Qed.


(* Why Are Constructors Injective?
Constructors are injective to maintain the integrity of the inductive type definitions.
If constructors weren't injective, it would be impossible to distinguish between different
constructed values based solely on their structure, leading to logical inconsistencies 
and ambiguity in proofs.

Could There Be Exceptions in Other Contexts?
Different Definitions: If natural numbers or the successor function were defined differently,
injectivity might not hold.
Abstract Settings: In abstract algebra or other mathematical structures,
functions similar to S might not be injective. *)


(************************************************************************)

(*
  Demonstrating the Principle of Explosion

  From a contradiction, we can prove anything. Here, we show that `false = true -> False`. 
  This is known as the principle of explosion.

  The principle of explosion, also known as ex falso quodlibet,
  is a logical principle stating that from a contradiction, 
  any proposition can be inferred. In other words,
  if both a statement and its negation are accepted as true,
  then any and every statement logically follows from this inconsistency.


*)

(* Goal stating that false equals true leads to a contradiction *)
Goal
  false = true -> False.
Proof.
  intros H.                         (* Introduce the hypothesis *)
  inversion H.                      (* Invert H, leading to a contradiction *)
Qed.




(* inversion:
-Purpose: Deconstructs equalities and inductive data structures to extract
information or derive contradictions.

-Use Cases:
When dealing with equalities between constructed terms.
To analyze impossible cases due to constructor properties.
To simplify proofs by breaking down complex hypotheses.

-Example: Proving that false = true leads to False.

---------------------------------------------------------------------------------

-symmetry:
Purpose: Reverses the direction of an equality.

-Use Cases:
When you have a = b but need to use it as b = a in your proof.
To align hypotheses with goals for applying the equality.

-Example: If you have H : a = b, and your goal is b = a, applying
symmetry transforms the goal to a = b, which can then be solved using H. *)



(****************************************************************************)
(* 
When to use assumption:

When you don't need to manipulate or change the goal,
but you want to directly conclude the proof with
an already-known fact from the context.

It is faster and more straightforward than apply
when the goal and the hypothesis are already exactly the same. *)

(* assumption does not change the goal; it only verifies that
the goal matches an existing hypothesis. *)

Lemma example1 : forall (x y : nat), x = y -> x = y.
Proof.
  intros x y H.  (* Introduces x, y, and the hypothesis H : x = y *)
  assumption.    (* H already matches the goal, so we can finish the proof with assumption *)
Qed.



(* apply can transform the goal by applying a rule, theorem,
or hypothesis that may involve implications or require
additional steps (like generating subgoals). *)

Lemma example2 : forall (x y : nat), x = y -> y = x.
Proof.
  intros x y H.  (* Introduce x, y, and H : x = y *)
  apply eq_sym.  (* Use the symmetry of equality to turn the goal into x = y *)
  assumption.    (* Now the goal matches the hypothesis H, so we use assumption *)
Qed.


(****************************************************************************)


(* Search (_ + _ = _ + _). *)

