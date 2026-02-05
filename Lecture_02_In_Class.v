(**
  In Coq, **compound types** refer to types that are composed of multiple 
  elements or other types. These types can hold several values or objects, 
  possibly of different types, allowing us to define more complex structures.

  Defining Compound Types:
  Compound types can be defined using **inductive types** in Coq. They 
  are similar to structs, tuples, or tagged unions in other languages. 

  Example of defining compound types:
*)

(* Defining a basic rgb type representing primary colors *)
Inductive rgb : Type := 
  (* `red`, `green`, and `blue` are the constructors for `rgb`, each representing a color. *)
  | red : rgb                
  | green : rgb              
  | blue : rgb.

(* Defining a color type with simple and compound constructors *)
Inductive color : Type :=
  (* `black` and `white` are simple constructors representing specific colors *)
  | black : color              
  | white : color              
  (* `primary` is a compound constructor that holds an `rgb` value, representing primary colors *)
  | primary : rgb -> color.

(* Flip an RGB color to the next value in the cycle (red → green → blue → red).
   This function uses pattern matching to safely and explicitly handle all possible cases of the `rgb` type. *)
Definition flip (r:rgb) : rgb :=
  (* Pattern matching works by comparing the structure of `r` against specified patterns.
     It ensures:
     - Exhaustiveness: All possible variants of `rgb` must be covered.
     - Type safety: Patterns are checked against the type definition at compile time. *)
  match r with
  | red => green    (* Transition: red → green (cycle to the next color) *)
  | green => blue   (* Transition: green → blue (cycle to the next color) *)
  | blue => red     (* Transition: blue → red (cycle back to the first color) *)
  end.

(* Example usage:
   - flip red   → green
   - flip green → blue
   - flip blue  → red *)

(* Testing the `primary` constructor and `flip` function with computations *)
Compute primary red.          (* Tags `red` as a primary color *)
Compute flip red.             (* Flips `red` to `green` *)
Compute primary (flip red).   (* Returns the primary color of flipped `red` (green) *)
Compute flip (flip red).      (* Flips `red` twice to get `blue` *)
Compute primary (flip (flip red)). (* Returns the primary color of flipped `red` twice (blue) *)

(**
  The `color_to_rgb` function extracts the `rgb` value from `color`:
  - For `black` and `white`, it returns `red`.
  - For `primary`, it extracts the contained `rgb` value.
*)
Definition color_to_rgb (c:color) : rgb :=
  (* Pattern match on the `color` type to extract an `rgb` value *)
  match c with
  | black => red        (* Return `red` for `black` *)
  | white => red        (* Return `red` for `white` *)
  | primary x => x      (* Extract and return the contained `rgb` value for `primary` *)
  end.

(* Testing `color_to_rgb` *)
Compute color_to_rgb (primary red).  (* Extracts and returns `red` *)
Compute color_to_rgb black.          (* Returns `red` for black *)
Compute color_to_rgb (primary (color_to_rgb (primary red))). (* Correct usage *)


(**
  `f2` is similar to `color_to_rgb` but handles specific cases:
  - `primary red` returns `green`
  - `primary green` returns `blue`
  - Otherwise, returns `red`.
*)
Definition f2 (c:color) : rgb :=
  (* Pattern matching to define custom behavior for each `color` case *)
  match c with
  | black => red              (* Return `red` for `black` *)
  | white => red              (* Return `red` for `white` *)
  | primary red => green      (* Return `green` for `primary red` *)
  | primary green => blue     (* Return `blue` for `primary green` *)
  | primary _ => red          (* Default case: return `red` for other `primary` values *)
  end.

(* Testing f2 *)
Compute f2 (primary red).  (* Returns green for primary red *)

(**
  Defining `vec3`, a compound type that represents a 3-component vector of `rgb` values.
  This type is useful in Coq for reasoning, pattern matching, and recursion as described in the lecture.
*)
Inductive vec3 : Type :=
  (* `vector` constructor takes three `rgb` values to form a 3D vector *)
  | vector : rgb -> rgb -> rgb -> vec3.

(* Testing the `vector` constructor *)
Compute vector red (flip (flip red)) (flip red). (* Constructs a vector with red, blue, green *)

(**
  The `add` function performs pattern matching on `vec3`:
  - If any component is `red`, it returns `red`.
  - If any component is `green`, it returns `green`.
  - Otherwise, it returns `blue`.
*)
Definition add (v1:vec3) (v2:vec3) : rgb :=
  (* Pattern matching on the `vec3` type to determine the output color based on its components *)
  match v1 with
  | vector red _ _ => red      (* Return `red` if the first component is `red` *)
  | vector _ red _ => red      (* Return `red` if the second component is `red` *)
  | vector _ _ red => red      (* Return `red` if the third component is `red` *)
  | vector green _ _ => green  (* Return `green` if the first component is `green` *)
  | vector _ green _ => green  (* Return `green` if the second component is `green` *)
  | vector _ _ green => green  (* Return `green` if the third component is `green` *)
  | _ => blue                  (* Default case: return `blue` *)
  end.

(**
  The `peano` type represents natural numbers using zero and successors, 
  similar to the Peano numbers. 
  - `zero` represents the base case (0).
  - `succ` represents the successor (n + 1).
*)
Inductive peano : Type :=
  (* `zero` is the base case for Peano numbers *)
  | zero : peano                
  (* `succ` represents the successor of a Peano number, allowing recursion *)
  | succ : peano -> peano.

(* Testing the `peano` type *)
Compute zero.                    (* Outputs 0 - zero is defined as O, representing 0 *)
Compute succ zero.               (* Outputs 1 - successor of zero (S 0) is 1 *)
Compute succ (succ zero).        (* Outputs 2 - successor of 1 (S (S 0)) is 2 *)
Compute succ (succ (succ zero)). (* Outputs 3 - successor of 2 (S (S (S 0))) is 3 *)
(**
  `evenb` is a recursive function that checks if a Peano number is even.
  - `zero` is even, so it returns `true`.
  - `succ zero` is odd, so it returns `false`.
  - For larger numbers, it checks if n - 2 is even.
*)
Fixpoint evenb (n:peano) : bool :=
  (* Recursive pattern matching on the Peano number to determine if it's even or odd *)
  match n with
  | zero => true               (* 0 is even, so return `true` *)
  | succ zero => false         (* 1 is odd, so return `false` *)
  | succ (succ n') => evenb n' (* For numbers greater than 2, check n - 2 *)
  end.
(*n' is the predecessor of n *)
(* Testing `evenb` *)
Compute evenb zero.                             (* Returns true (0 is even) *)
Compute evenb (succ zero).                      (* Returns false (1 is odd) *)
Compute evenb (succ (succ zero)).               (* Returns true (2 is even) *)
Compute evenb (succ (succ (succ zero))).        (* Returns false (3 is odd) *)
Compute evenb (succ (succ (succ (succ zero)))). (* Returns true (4 is even) *)


(* Fixpoint for `plus`, which adds two natural numbers defined recursively *)
Fixpoint plus (n : nat) (m : nat) : nat := 
  (* Pattern match on `n` to perform addition recursively *)
  match n with
  | O => m                  (* Base case: adding 0 to `m` results in `m` *)
  | S n' => S (plus n' m)   (* Recursive case: `n` is `S n'` recursively apply addition (add 1 to result of `plus n' m` )*)
  end.

(* 

S n' means that n is one more than n'.
n' is the "rest" of the original number n (i.e., what n was before adding 1).

*)

Compute plus 100 3.


(* Example to test `plus` function *)
Example plus_O_5 : plus 0 5 = 5.
Proof.
  simpl.                      (* Simplifies the addition *)
  reflexivity.                 (* Concludes the proof as both sides are equal *)
Qed.




(* Base case (0 + n): In Coq, 0 + n simplifies directly to n without recursion.
   Therefore, `simpl` applies this base case, and Coq finishes the proof with 
   `reflexivity` as both sides (n and n) are trivially equal. *)

(* Theorem to generalize the above example *)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros g.                   (* Introduce the variable `g` *)
  simpl.                      (* Simplifies the expression `0 + n` *)
  reflexivity.                (* Proves that `0 + n = n` *)
Qed.


 
(* Recursive case (n + 0): In Coq, when `n` is a successor, the recursive definition 
   of addition applies. This requires induction to handle the recursion and prove 
   that `n + 0 = n`. *)

(* Theorem for adding n + 0 *)
Theorem plus_n_O : forall n : nat, n + 0 = n.
Proof.
  intros n.                   (* Introduce the variable `n` *)
  simpl.                      (* Simplifies the addition *)
Qed.                     (* Placeholder*)

(* In `n + 0`, Coq encounters recursion when `n` is a successor, requiring induction. 
   In `0 + n`, Coq matches the base case directly (`0 + n = n`), so `simpl` is enough. *)
