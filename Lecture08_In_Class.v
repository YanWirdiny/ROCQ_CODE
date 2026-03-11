Require Import Coq.Strings.Ascii.  (* Imports support for ASCII strings in Coq for formalizing characters and words. *)
Require Import Coq.Lists.List.      (* Imports list operations in Coq, used to represent sequences of characters (words). *)
Open Scope char_scope.              (* Opens the character scope for easier manipulation of characters. *)
Import ListNotations.               (* Imports list notations for sequences of characters, useful in defining words and languages. *)
Require Import Turing.Util.         (* Imports utility functions from the Turing library, useful for language manipulations. *)
Require Import Turing.Lang.         (* Imports language definitions from the Turing library, relevant to formal languages theory. *)

(* Definition of a word and a language *)
(* A word is a sequence of ASCII characters, modeled as a list.
   In formal languages, a word is an element of a formal language's alphabet. *)
Definition word := list ascii.



(* A language is a set of words. In Coq, we represent this as a function from words to propositions (Prop),
   which models whether a word belongs to the language.
   
   A language is a function that takes a word as input and returns a proposition (Prop).
   
   *)
Definition language := word -> Prop.



(* The membership relation:
   This definition models set membership for languages. A word [w] belongs to a language [L]
   if applying [L] to [w] returns a proof that the word is in the language. This is similar to set membership in formal languages theory. *)
Definition In (w: word) (L: language) := L w.
Print In.




(* Example: Calculate the length of the sequence ["a"; "b"; "c"].
   This checks how many characters (elements) are in the word, modeled as a list in Coq. *)
Compute List.length ["a"; "b"; "c"].




(* Definition of the substring relation between two words:
   A word [x] is a substring of another word [y] if there exist two other words [l1] and [l2]
   such that concatenating [l1], [x], and [l2] gives [y].
   This models the concept of substrings in formal languages. *)
Definition substring (x y: word) : Prop :=
  exists l1 l2,   (* There exist two words, [l1] and [l2] *)
    l1 ++ x ++ l2 = y.   (* such that concatenating [l1], [x], and [l2] gives [y] *)




(* Goal: Prove that ["b"; "c"] is a substring of ["a"; "b"; "c"].
   This verifies that ["b"; "c"] is contained as a substring within ["a"; "b"; "c"]. *)
Goal substring ["b"; "c"] ["a"; "b"; "c"].
Proof.
  (* We prove this by finding the appropriate words [l1] and [l2] that satisfy the substring definition. *)
  unfold substring.
  exists ["a"].   (* Set l1 to ["a"] *)
  exists [].      (* Set l2 to the empty word *)
  simpl.
  reflexivity.    (* The equation holds: ["a"] ++ ["b"; "c"] ++ [] = ["a"; "b"; "c"] *)
Qed.


(*

length ["c"; "a"; "r"] = 1 + length ["a"; "r"]

length ["a"; "r"] = 1 + length ["r"]

length ["r"] = 1 + length []

length [] = 0

Adding up: 1 + (1 + (1 + 0)) = 3 

*)


(* Problem: Prove that the length of the word ["c"; "a"; "r"] is 3.
   This confirms that the word consists of three characters. *)
Goal length ["c"; "a"; "r"] = 3.
Proof. reflexivity. Qed.




(* Problem: Prove the concatenation of two words.
   Here we verify that concatenating ["c"] and ["a"; "r"] results in ["c"; "a"; "r"]. *)
Goal ["c"] ++ ["a"; "r"] = ["c"; "a"; "r"].
Proof. reflexivity. Qed.




(* Problem: Verify the result of applying the power operation to the word ["c"; "a"; "r"].
   The power operation repeats the word n times. Below, it is checked for powers 3, 1, and 0. *)

(* Power of 3: ["c"; "a"; "r"] is repeated 3 times, resulting in 
   ["c"; "a"; "r"; "c"; "a"; "r"; "c"; "a"; "r"]. *)
Goal pow ["c"; "a"; "r"] 3 = ["c"; "a"; "r"; "c"; "a"; "r"; "c"; "a"; "r"].
Proof. reflexivity. Qed.



(* Power of 1: ["c"; "a"; "r"] repeated once gives the same word. *)
Goal pow ["c"; "a"; "r"] 1 = ["c"; "a"; "r"].
Proof. reflexivity. Qed.



(* Power of 0: Any word raised to power 0 results in an empty word. *)
Goal pow ["c"; "a"; "r"] 0 = []. 
Proof. reflexivity. Qed.




(* Problem: Define the formal language L1 that only accepts the word ["c"; "a"; "r"].
   This defines a formal language that contains a single word, ["c"; "a"; "r"]. *)
Definition L1 (w:word) := w = ["c"; "a"; "r"].




(* Prove that the word ["c"; "a"; "r"] is in L1.
   Since L1 is defined to only accept this word, this proof uses reflexivity to show that ["c"; "a"; "r"] belongs to L1. *)
Goal In ["c"; "a"; "r"] L1.
Proof.
  unfold L1.     (* Unfolds the definition of L1 *)
  unfold In.     (* Unfolds the membership relation In *)
  reflexivity.   (* Proves that ["c"; "a"; "r"] equals ["c"; "a"; "r"] *)
Qed.





(* Prove that the empty string is NOT in L1.
   Since L1 only accepts ["c"; "a"; "r"], the empty word cannot belong to L1.
   We use a proof by contradiction to demonstrate this. *)
Goal ~ In [] L1.
Proof.
  unfold In.
  unfold L1. (* Unfolds the definitions of In and L1 *)
  intros N.      (* Introduces the assumption that [] is in L1, leading to a contradiction *)
  inversion N.   (* Inverts the hypothesis to show that [] cannot equal ["c"; "a"; "r"] *)
Qed.






(* Problem: Define a language L2 that accepts any single vowel (a, e, i, o, u).
   This language is defined as the union of five cases, where each case matches a word containing one vowel.
   In formal languages, L2 can be interpreted as a set containing these specific words. *)
Definition L2 w := Char "a" w
  \/ Char "e" w
  \/ Char "i" w
  \/ Char "o" w
  \/ Char "u" w.







(* Prove that the word ["i"] is in L2.
   Since ["i"] is one of the vowels, it belongs to L2. The proof uses disjunction to find the correct case. *)
Goal In ["i"] L2.
Proof.
  unfold In, L2.  (* Unfolds the definitions of In and L2 *)
  unfold Char.    (* Unfolds the definition of Char *)
  right.          (* Skips the first disjunction case *)
  right.          (* Skips the next case *)
  left.           (* Selects the case where the character is "i" *)
  reflexivity.    (* Proves that ["i"] equals ["i"] *)
Qed.




(* Prove that the word ["a"; "a"] is NOT in L2.
   L2 only accepts words with a single vowel, so ["a"; "a"] is not accepted. *)
   Lemma aa_not_in_vowel: ~ In ["a"; "a"] L2.
   Proof.
     (* Unfolds the definitions of In and L2 to work with the logical structure of the proof *)
     unfold In, L2.
     
     (* Introduces the assumption that ["a"; "a"] is in L2, which leads to the case analysis.
        This introduces the assumption N:
        N: In ["a"; "a"] L2 *)
     intros N.
     
     (* Destruct the assumption N. 
        L2 is a disjunction of cases (["a"], ["e"], ["i"], ["o"], ["u"]).
        This splits the proof into five cases, each corresponding to one of the vowels. *)
     destruct N as [N|[N|[N|[N|N]]]]; (*you can chain them with a semicolon *)
     
     (* Inversion inspects each case to see if ["a"; "a"] can match a single-character word like ["a"].
        Since ["a"; "a"] has two characters and each vowel case involves a single character,
        none of these cases can hold, and each case is ruled out.
        This shows that ["a"; "a"] cannot be in L2. *)
     inversion N.
   Qed.
   






(* Problem: Prove that the empty string is in Nil.
   Nil represents the empty language (the set containing only the empty word), so the empty word belongs to it.
   This models an important base case in formal language theory. *)
Goal In [] Nil.
Proof.
  reflexivity.    (* Trivially proves that the empty list is in Nil *)
Qed.







(* Definition of Char function that checks if a word is a single character *)
Definition Char c (w:word) := 
  w = [c]. 
  (* This checks whether the word [w] is equal to a single-character list [c]. 
     It ensures that the word w consists of just the character c. *)


(* Definition Char (c : ascii) (w : word) := 
  w = [c].  *)



(* Enabling shorthand notation for Union. *)
Import LangNotations.
Infix "U" := Union.  (* Introduces convenient notation for union of languages *)








(* Problem: Prove that if a word is in L1, it is also in the union of L1 and L2.
   If a word belongs to L1, it must also belong to L1 U L2, since union includes all elements of L1. *)
Goal
  forall (w:word),      (* For any word w *)
  In w L1 ->            (* If w is in L1 *)
  In w (L1 U L2).       (* Then w is in L1 U L2 *)
Proof.
  unfold In.            (* Unfolds the definition of In *)
  intros.               (* Introduces w and the assumption that w is in L1 *)
  unfold Union.         (* Unfolds the definition of union *)
  left.                 (* Proves that w is in the first component of the union *)
  assumption.           (* Concludes the proof using the assumption *)
Qed.





Definition l1 := ["a"; "b"].
Definition l2 := ["c"; "d"].

Compute l1.
Compute l2.
Compute l1 ++ l2.
(* Output: ["a"; "b"; "c"; "d"] *)


(* Problem: Define the concatenation of two languages L1 and L2.
   In formal language theory, concatenation of two languages results in a new language that consists
   of all possible concatenations of a word from L1 with a word from L2. This is defined using the App function. *)
Definition App L1 L2 w := 
  exists w1 w2,          (* There exist two words w1 and w2 *)
  In w1 L1 /\            (* w1 is in L1 *)
  In w2 L2 /\            (* w2 is in L2 *)
  w = w1 ++ w2.          (* w is the concatenation of w1 and w2 *)




 
  
  

(* Problem: Define a concatenated language L1' that consists of the word ["c"; "a"; "r"].
   This definition uses the App constructor to combine the characters into a single word. *)
Definition L1' := App (Char "c") (App (Char "a") (Char "r")).

Print L1'.
Compute App.