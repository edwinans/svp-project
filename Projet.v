
Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From PLF Require Import Maps Imp.

Module BreakImp.
(** **** Exercise: 4 stars, advanced (break_imp)

    Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    exercise we consider how to add [break] to Imp and "downgrading"
    the while statement into the loop statement (equivalanet to while
    true). First, we need to change the language of commands *)

Inductive com : Type :=
  | CSkip
  | CBreak                        (* <--- NEW *)
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CLoop (c : com).            (* <--- DOWNGRADED *)

Notation "'break'" := CBreak (in custom com at level 0).
Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAsgn x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'loop' y 'endloop'" :=
         (CLoop y)
            (in custom com at level 89, y at level 99) : com_scope.

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       loop
         if ~(0 = Y) then
           loop
             break
           endloop;
           X := 1;
           Y := Y - 1
         else break
       endloop

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [loop c end], the semantics is
      as follows: The only difference is that we execute [c] and check
      the signal that it raises. If that signal is [SContinue], then
      the execution proceeds (the loop iterates once again). Otherwise,
      we stop the execution of the loop, and the resulting state is
      the same as the one resulting from the execution of the current
      iteration. In either case, since [break] only terminates the
      innermost loop, [loop] signals [SContinue]. *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      st =[CSkip]=> st / SContinue
  | E_Break : forall st,
      st =[CBreak]=> st / SBreak
  | E_Asgn  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st) / SContinue
  | E_Seq_Continue : forall c1 c2 st st' st'' s',
      st  =[ c1 ]=> st' / SContinue ->
      st' =[ c2 ]=> st'' / s'->
      st  =[ c1 ; c2 ]=> st'' / s'
  | E_Seq_Break : forall c1 c2 st st',
      st  =[ c1 ]=> st' / SBreak ->
      st  =[ c1 ; c2 ]=> st' / SBreak
  | E_IfTrue : forall st st' s' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' / s'->
      st =[ if b then c1 else c2 end]=> st' / s'
  | E_IfFalse : forall st st' s' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' / s'->
      st =[ if b then c1 else c2 end]=> st' / s'
  | E_Loop_Continue : forall st st' st'' s' c,
      st =[c]=> st' / SContinue->
      st' =[ loop c endloop ]=> st'' / s' ->
      st  =[ loop c endloop ]=> st'' / s'
  | E_Loop_Break : forall st st' c,
      st =[c]=> st' / SBreak->
      st =[ loop c endloop ]=> st' / SContinue


  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').

(** Now prove the following properties of your definition of [ceval]: *)

Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros.
  inversion H; subst.
  - inversion H2.
  - inversion H5. reflexivity.
Qed. 


Theorem loop_continue : forall c st st' s,
  st =[ loop c endloop ]=> st' / s ->
  s = SContinue.
Proof.
    (* FILL IN HERE *) Admitted. 


Theorem while_stops_on_break : forall c st st',
  st =[ c ]=> st' / SBreak ->
  st =[ loop c endloop ]=> st' / SContinue.
Proof.
    (* FILL IN HERE *) Admitted. 



Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
    (* FILL IN HERE *) Admitted. 


Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
    (* FILL IN HERE *) Admitted. 

(** [] *)

(** **** Exercise: 3 stars, advanced, optional (while_break_true) *)
Theorem while_break_true : forall c st st',
  st =[ loop c endloop ]=> st' / SContinue ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
    (* FILL IN HERE *) Admitted. 

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (ceval_deterministic) *)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     st =[ c ]=> st1 / s1 ->
     st =[ c ]=> st2 / s2 ->
     st1 = st2 /\ s1 = s2.
Proof.
    (* FILL IN HERE *) Admitted. 


(** [] *)
End BreakImp.

(* From now on regular Imp has a nice syntax, but not the variant with loop and break. *)

(* Let us define the translation from Imp to the variant: *)
Fixpoint traduct_while (pw: Imp.com): BreakImp.com :=
  match pw with
  | <{ skip }> => BreakImp.CSkip
  | <{ x := a }> => BreakImp.CAsgn x a
  | <{ c1; c2 }> => BreakImp.CSeq (traduct_while c1) (traduct_while c2)
  | <{ if b then c1 else c2 end }> => BreakImp.CIf b (traduct_while c1) (traduct_while c2)
  | <{ while b do c end }> =>
      BreakImp.CLoop (BreakImp.CIf b (traduct_while c) BreakImp.CBreak)
  end.

(* Now let us prove that we can simulate a regular imp program with a
   simple translated program in the variant. *)
Theorem equiv_while_loopbreak: forall (c:Imp.com)(c':BreakImp.com) st st1,
      c' = traduct_while c -> 
      (st =[ c ]=> st1) ->
      BreakImp.ceval c' st BreakImp.SContinue st1.
Proof.
    (* FILL IN HERE *) Admitted. 




(** **** BONUS Exercise: 3 stars, standard, optional (short_circuit)

    Most modern programming languages use a "short-circuit" evaluation
    rule for boolean [and]: to evaluate [BAnd b1 b2], first evaluate
    [b1].  If it evaluates to [false], then the entire [BAnd]
    expression evaluates to [false] immediately, without evaluating
    [b2].  Otherwise, [b2] is evaluated to determine the result of the
    [BAnd] expression.

    Write an alternate version of [beval] that performs short-circuit
    evaluation of [BAnd] in this manner, and prove that it is
    equivalent to [beval].  (N.b. This is only true because expression
    evaluation in Imp is rather simple.  In a bigger language where
    evaluating an expression might diverge, the short-circuiting [BAnd]
    would _not_ be equivalent to the original, since it would make more
    programs terminate.) *)

(* FILL IN HERE

    [] *)
