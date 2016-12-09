Require Export P05.
Import ListNotations.


(** **** Exercise: 3 stars (stack_compiler)  *)
(** HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a stack. For instance, the expression

      (2*3)+(3*(4-2))

   would be entered as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated 
   on the right and the contents of the stack on the left):

      []            |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The task of this exercise is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

(*
Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : id -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.
*)

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements.  In a sense, it is
    immaterial what we do, since our compiler will never emit such a
    malformed program. *)

Print sinstr.
Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
                 : list nat 
:= 
match prog with
| (SPush n)::pl => s_execute st (n::stack) pl
| (SLoad id)::pl => s_execute st ((st id)::stack) pl
| SPlus::pl => 
(match stack with
| n1::n2::sl => s_execute st ((n1 + n2)::sl) pl
| _ => s_execute st stack pl
end)
| SMinus::pl =>
(match stack with
| n1::n2::sl => s_execute st ((n2 - n1)::sl) pl
| _ => s_execute st stack pl
end)
| S_Mult::pl =>
(match stack with
| n1::n2::sl => s_execute st ((n1 * n2)::sl) pl
| _ => s_execute st stack pl
end)
| [] => stack
end.

Example s_execute1 :
     s_execute empty_state []
       [SPush 5; SPush 3; SPush 1; SMinus]
   = [2; 5].
Proof. unfold s_execute. reflexivity. Qed.

Example s_execute2 :
     s_execute (t_update empty_state X 3) [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = [15; 4].
Proof. unfold s_execute. reflexivity. Qed. 

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)

Print aexp.
Fixpoint s_compile (e : aexp) : list sinstr 
:= 
match e with
| ANum n => [ SPush n ]
| AId id => [ SLoad id ]
| APlus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SPlus]
| AMinus a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMinus]
| AMult a1 a2 => (s_compile a1) ++ (s_compile a2) ++ [SMult]
end.

(** After you've defined [s_compile], prove the following to test
    that it works. *)

Example s_compile1 :
    s_compile (AMinus (AId X) (AMult (ANum 2) (AId Y)))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof.
unfold s_compile. simpl. reflexivity.
Qed.

(** **** Exercise: 4 stars, advanced (stack_compiler_correct)  *)
(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an [SPlus], [SMinus], or
    [SMult] instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Lemma s_compile_correct_general : forall (st:state) (e:aexp) (ls:list nat) (t : list sinstr),
  s_execute st ls ((s_compile e) ++ t) = 
  s_execute st ([ aeval st e ] ++ ls) t.
Proof.
intros st e.
generalize dependent st.
induction e ; try (intros ; simpl ; reflexivity) ; 
try (intros ; simpl ;
  rewrite app_assoc with (l := s_compile e1) (m := s_compile e2);
  rewrite <- app_assoc with (l := (s_compile e1 ++ s_compile e2));
  rewrite <- app_assoc with (m := s_compile e2);
  rewrite IHe1; rewrite IHe2; simpl).
{ rewrite plus_comm. reflexivity. }
{ reflexivity. }
{ rewrite mult_comm. reflexivity. }
Qed.

Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = [ aeval st e ].
Proof.
intros.
replace (s_compile e) with (s_compile e ++ []).
- rewrite s_compile_correct_general with (st := st) (e := e) (ls := []) (t := []).
  reflexivity.
- symmetry. apply app_nil_end.
Qed.