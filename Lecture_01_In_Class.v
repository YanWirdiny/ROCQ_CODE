(* This is a single-line comment in Coq *)

(* This is a 
   multi-line comment 
   in Coq *)

(* The following section defines the days of the week as an inductive data type in Coq. 
   This is a basic enumerated type where each day is a separate constructor of the type 'day'.
   Each day (monday, tuesday, etc.) is represented as a constructor for the 'day' type.
*)
Inductive day : Type :=
  | monday : day               (* Constructor for Monday *)
  | tuesday : day              (* Constructor for Tuesday *)
  | wednesday : day            (* Constructor for Wednesday *)
  | thursday : day             (* Constructor for Thursday *)
  | friday : day               (* Constructor for Friday *)
  | saturday : day             (* Constructor for Saturday *)
  | sunday : day.              (* Constructor for Sunday *)

(* The next section defines a simple boolean type with two possible values: 'true' and 'false'. 
   This is an example of how to define a custom boolean type in Coq. 
   'true' and 'false' are constructors of the 'boolean' type, which mimics the built-in boolean type in Coq.
*)
Inductive boolean : Type :=
  | true : boolean             (* Constructor for true *)
  | false : boolean.           (* Constructor for false *)


(*
Inductive bollean := true | false.
*)

(* The next line computes and displays the value 'monday'. 
   This is a simple use of the 'Compute' command in Coq, which is used to evaluate expressions.
   'Compute' is used here to evaluate and return the value 'monday'.
*)
Compute monday.

(* The following line defines a new term 'foo' which is assigned the value 'monday'. 
   This is an example of defining a simple constant in Coq.
   'foo' is now a constant that holds the value 'monday'.
*)
Definition foo := monday.

(* The next block of code computes the day that follows 'monday'. 
   The 'match' expression is used to pattern match against the value 'monday' and returns 'tuesday'. 
   This demonstrates how to use pattern matching in Coq to perform computations based on specific values.
   The 'match' construct compares the value of 'monday' and returns the corresponding day.
*)
Compute
  match monday with
  | monday => tuesday           (* If the day is Monday, return Tuesday *)
  | tuesday => wednesday        (* If the day is Tuesday, return Wednesday *)
  | wednesday => thursday       (* If the day is Wednesday, return Thursday *)
  | thursday => friday          (* If the day is Thursday, return Friday *)
  | friday => monday            (* If the day is Friday, return Monday *)
  | saturday => monday          (* If the day is Saturday, return Monday *)
  | sunday => monday            (* If the day is Sunday, return Monday *)
  end.

(* The following section defines a function 'next_business_day' that takes a day as input and returns the next business day.
   The function returns 'tuesday' for 'monday', 'wednesday' for 'tuesday', and so on.
   'friday' is considered the last business day of the week, so 'monday' is returned for both 'friday', 'saturday', and 'sunday'.
   'next_business_day' maps each day to its corresponding next business day, with the weekend returning Monday.
*)
Definition next_business_day (d:day) : day :=
  match d with
  | monday => tuesday           (* If the day is Monday, return Tuesday *)
  | tuesday => wednesday        (* If the day is Tuesday, return Wednesday *)
  | wednesday => thursday       (* If the day is Wednesday, return Thursday *)
  | thursday => friday          (* If the day is Thursday, return Friday *)
  | friday => monday            (* If the day is Friday, return Monday *)
  | saturday => monday          (* If the day is Saturday, return Monday *)
  | sunday => monday            (* If the day is Sunday, return Monday *)
  end.

(* The 'next_weekday' definition is simply an alias for the 'next_business_day' function. 
   This demonstrates how to create synonyms for existing definitions in Coq.
   'next_weekday' behaves the same as 'next_business_day'.
*)
Definition next_weekday := next_business_day.

(* The following lines use the 'Compute' command to evaluate 'next_business_day' for different inputs. 
   These commands demonstrate how the function behaves when applied to 'monday', 'friday', and the result of applying it twice to 'friday'.
   The results of these evaluations show the next business day after Monday, Friday, and after two applications of the function to Friday.
*)
Compute next_business_day monday.         (* Computes the next business day after Monday (should return Tuesday) *)
Compute next_business_day friday.         (* Computes the next business day after Friday (should return Monday) *)
Compute next_business_day (next_business_day friday). (* Computes the business day after two consecutive Fridays (should return Tuesday) *)

(* The final block of code provides an example of a simple proof in Coq. 
   The example is a proof that applying 'next_business_day' twice to 'friday' results in 'tuesday'.
   The proof starts by simplifying the goal using 'simpl' and then completes the proof with 'reflexivity'. 
   This is a basic introduction to writing and proving theorems in Coq.
   'simpl' simplifies the expression and 'reflexivity' completes the proof by asserting both sides of the equation are equal.
*)
Example example1:
  next_business_day (next_business_day friday) = tuesday. (* Assertion: two business days after Friday is Tuesday *)
Proof.
  simpl. (* Simplifies the expression *)
  reflexivity. (* Completes the proof since the goal is now evident *)
Qed.

(** 
    Second, we can record what we _expect_ the result to be in the form of a Coq example.
    The following example tests that applying 'next_weekday' twice to 'saturday' returns 'tuesday'. 
*)
Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday. (* Assertion: two weekdays after Saturday is Tuesday *)

Proof.
  simpl. (* Simplifies the expression *)
  reflexivity. (* Completes the proof *)
Qed.


Example test3:
  (next_weekday (next_weekday (next_weekday monday))) = thursday.

Proof.
  simpl. (* Simplifies the expression *)
  reflexivity. (* Completes the proof *)
Qed.



(* The following 'Check' commands are used to examine the types of certain expressions in Coq. 
   These checks are useful for confirming that terms and functions behave as expected within Coq's type system.
   'Check' will return the type of each item it is applied to.
*)
Check test_next_weekday.       (* Verifies the type of 'test_next_weekday' *)
Check saturday.                (* Verifies the type of 'saturday' *)
Check next_weekday.            (* Verifies the type of 'next_weekday' *)
Check next_weekday saturday.   (* Verifies the type of 'next_weekday applied to saturday' *)
