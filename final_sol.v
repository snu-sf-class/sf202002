(** Final Exam *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List.
From Coq Require Import Strings.String.
From Coq Require Import Relations.
From Coq Require Import Logic.FunctionalExtensionality.
Import ListNotations.

(** ############################################################### **)
(**                                                                 **)
(** *                             Maps                              **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Identifiers *)

Definition eqb_string (x y : string) : bool :=
  if string_dec x y then true else false.

Theorem eqb_string_refl : forall s : string, true = eqb_string s s.
Proof.
  intros s. unfold eqb_string.
  destruct (string_dec s s) as [Hs_eq | Hs_not_eq].
  - reflexivity.
  - destruct Hs_not_eq. reflexivity.
Qed.

Theorem eqb_string_true_iff : forall x y : string,
    eqb_string x y = true <-> x = y.
Proof.
   intros x y.
   unfold eqb_string.
   destruct (string_dec x y) as [Hs_eq | Hs_not_eq].
   - rewrite Hs_eq. split. reflexivity. reflexivity.
   - split.
     + intros contra. discriminate contra.
     + intros H. exfalso. apply Hs_not_eq. apply H.
Qed.

Theorem eqb_string_false_iff : forall x y : string,
    eqb_string x y = false <-> x <> y.
Proof.
  intros x y. rewrite <- eqb_string_true_iff.
  rewrite not_true_iff_false. reflexivity. Qed.

Theorem false_eqb_string : forall x y : string,
   x <> y -> eqb_string x y = false.
Proof.
  intros x y. rewrite eqb_string_false_iff.
  intros H. apply H. Qed.

(* ################################################################# *)
(** * Total Maps *)

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
  (fun _ => v).

Definition t_update {A : Type} (m : total_map A)
                    (x : string) (v : A) :=
  fun x' => if eqb_string x x' then v else m x'.

Definition examplemap :=
  t_update (t_update (t_empty false) "foo" true)
           "bar" true.

Notation "'_' '!->' v" := (t_empty v)
  (at level 100, right associativity).

Example example_empty := (_ !-> false).

Notation "x '!->' v ';' m" := (t_update m x v)
                              (at level 100, v at next level, right associativity).

Definition examplemap' :=
  ( "bar" !-> true;
    "foo" !-> true;
    _     !-> false
  ).

Lemma t_apply_empty : forall (A : Type) (x : string) (v : A),
    (_ !-> v) x = v.
Proof.
  eauto.
Qed.

Lemma t_update_eq : forall (A : Type) (m : total_map A) x v,
    (x !-> v ; m) x = v.
Proof.
  intros. unfold t_update. rewrite <-eqb_string_refl. eauto.
Qed.

Theorem t_update_neq : forall (A : Type) (m : total_map A) x1 x2 v,
    x1 <> x2 ->
    (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold t_update. rewrite false_eqb_string; eauto.
Qed.

Lemma t_update_shadow : forall (A : Type) (m : total_map A) x v1 v2,
    (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update. destruct (eqb_string x x0); eauto.
Qed.

Lemma eqb_stringP : forall x y : string,
    reflect (x = y) (eqb_string x y).
Proof.
  intros. destruct (eqb_string x y) eqn:EQ.
  - apply eqb_string_true_iff in EQ. eauto using reflect.
  - apply eqb_string_false_iff in EQ. eauto using reflect.
Qed.

Theorem t_update_same : forall (A : Type) (m : total_map A) x,
    (x !-> m x ; m) = m.
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update. destruct (eqb_string _ _) eqn: EQ; eauto.
  apply eqb_string_true_iff in EQ. subst. eauto.
Qed.

Theorem t_update_permute : forall (A : Type) (m : total_map A)
                                  v1 v2 x1 x2,
    x2 <> x1 ->
    (x1 !-> v1 ; x2 !-> v2 ; m)
    =
    (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. apply functional_extensionality. intros.
  unfold t_update.
  destruct (eqb_string x1 x) eqn: EQ1; eauto.
  destruct (eqb_string x2 x) eqn: EQ2; eauto.
  apply eqb_string_true_iff in EQ1.
  apply eqb_string_true_iff in EQ2.
  subst. contradiction.
Qed.

(* ################################################################# *)
(** * Partial maps *)

Definition partial_map (A : Type) := total_map (option A).

Definition empty {A : Type} : partial_map A :=
  t_empty None.

Definition update {A : Type} (m : partial_map A)
           (x : string) (v : A) :=
  (x !-> Some v ; m).

Notation "x '|->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).

Notation "x '|->' v" := (update empty x v)
  (at level 100).

Example examplepmap :=
  ("Church" |-> true ; "Turing" |-> false).

Lemma apply_empty : forall (A : Type) (x : string),
    @empty A x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (A : Type) (m : partial_map A) x v,
    (x |-> v ; m) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall (A : Type) (m : partial_map A) x1 x2 v,
    x2 <> x1 ->
    (x2 |-> v ; m) x1 = m x1.
Proof.
  intros A m x1 x2 v H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (A : Type) (m : partial_map A) x v1 v2,
    (x |-> v2 ; x |-> v1 ; m) = (x |-> v2 ; m).
Proof.
  intros A m x v1 v2. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall (A : Type) (m : partial_map A) x v,
    m x = Some v ->
    (x |-> v ; m) = m.
Proof.
  intros A m x v H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall (A : Type) (m : partial_map A)
                                x1 x2 v1 v2,
    x2 <> x1 ->
    (x1 |-> v1 ; x2 |-> v2 ; m) = (x2 |-> v2 ; x1 |-> v1 ; m).
Proof.
  intros A m x1 x2 v1 v2. unfold update.
  apply t_update_permute.
Qed.

Definition inclusion {A : Type} (m m' : partial_map A) :=
  forall x v, m x = Some v -> m' x = Some v.
  
Lemma inclusion_update : forall (A : Type) (m m': partial_map A)
                              x vx,
  inclusion m m' ->
  inclusion (x |-> vx ; m) (x |-> vx ; m').
Proof.
  unfold inclusion.
  intros A m m' x vx H.
  intros y vy.
  destruct (eqb_stringP x y) as [Hxy | Hxy].
  - rewrite Hxy. 
    rewrite update_eq. rewrite update_eq. intro H1. apply H1.
  - rewrite update_neq. rewrite update_neq.
    + apply H.
    + apply Hxy.
    + apply Hxy.
Qed.

(** ############################################################### **)
(**                                                                 **)
(** *             Imp: Simple Imperative Programs                   **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Expressions *)

(** ** Syntax  *)

Inductive aexp : Type :=
  | ANum (n : nat)
  | AId (x : string)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.
Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
                  (in custom com at level 0, only parsing,
                  f constr at level 0, x constr at level 9,
                  y constr at level 9) : com_scope.
Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'"  := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x = y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b"  := (BNot b) (in custom com at level 75, right associativity).

Open Scope com_scope.

(** ** Evaluation *)

Definition state := total_map nat.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x                                (* <--- NEW *)
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.

Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | <{true}>      => true
  | <{false}>     => false
  | <{a1 = a2}>   => (aeval st a1) =? (aeval st a2)
  | <{a1 <= a2}>  => (aeval st a1) <=? (aeval st a2)
  | <{~ b1}>      => negb (beval st b1)
  | <{b1 && b2}>  => andb (beval st b1) (beval st b2)
  end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (t_update empty_st x v) (at level 100).

(* ################################################################# *)
(** * Commands *)

(** ** Syntax *)

Inductive com : Type :=
  | CSkip
  | CAss (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

Notation "'skip'"  :=
         CSkip (in custom com at level 0) : com_scope.
Notation "x := y"  :=
         (CAss x y)
            (in custom com at level 0, x constr at level 0,
             y at level 85, no associativity) : com_scope.
Notation "x ; y" :=
         (CSeq x y)
           (in custom com at level 90, right associativity) : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
         (CIf x y z)
           (in custom com at level 89, x at level 99,
            y at level 99, z at level 99) : com_scope.
Notation "'while' x 'do' y 'end'" :=
         (CWhile x y)
            (in custom com at level 89, x at level 99, y at level 99) : com_scope.

(** ** Evaluation Relation *)

Reserved Notation
         "st '=[' c ']=>' st'"
         (at level 40, c custom com at level 99,
          st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
      st =[ skip ]=> st
  | E_Ass  : forall st a n x,
      aeval st a = n ->
      st =[ x := a ]=> (x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
      st  =[ c1 ]=> st'  ->
      st' =[ c2 ]=> st'' ->
      st  =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall st st' b c1 c2,
      beval st b = true ->
      st =[ c1 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
      beval st b = false ->
      st =[ c2 ]=> st' ->
      st =[ if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall b st c,
      beval st b = false ->
      st =[ while b do c end ]=> st
  | E_WhileTrue : forall st st' st'' b c,
      beval st b = true ->
      st  =[ c ]=> st' ->
      st' =[ while b do c end ]=> st'' ->
      st  =[ while b do c end ]=> st''

  where "st =[ c ]=> st'" := (ceval c st st').

Hint Constructors ceval : core.

(** ############################################################### **)
(**                                                                 **)
(** *                        Hoare Logic                            **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Assertions *)

Definition Assertion := state -> Prop.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Declare Scope hoare_spec_scope.
Notation "P ->> Q" := (assert_implies P Q)
                      (at level 80) : hoare_spec_scope.
Open Scope hoare_spec_scope.

Notation "P <<->> Q" :=
  (P ->> Q /\ Q ->> P) (at level 80) : hoare_spec_scope.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.

Notation assert P := (P%assertion : Assertion).
Notation mkAexp a := (a%assertion : Aexp).

Notation "~ P" := (fun st => ~ assert P st) : assertion_scope.
Notation "P /\ Q" := (fun st => assert P st /\ assert Q st) : assertion_scope.
Notation "P \/ Q" := (fun st => assert P st \/ assert Q st) : assertion_scope.
Notation "P -> Q" := (fun st => assert P st ->  assert Q st) : assertion_scope.
Notation "P <-> Q" := (fun st => assert P st <->  assert Q st) : assertion_scope.
Notation "a = b" := (fun st => mkAexp a st = mkAexp b st) : assertion_scope.
Notation "a <> b" := (fun st => mkAexp a st <> mkAexp b st) : assertion_scope.
Notation "a <= b" := (fun st => mkAexp a st <= mkAexp b st) : assertion_scope.
Notation "a < b" := (fun st => mkAexp a st < mkAexp b st) : assertion_scope.
Notation "a >= b" := (fun st => mkAexp a st >= mkAexp b st) : assertion_scope.
Notation "a > b" := (fun st => mkAexp a st > mkAexp b st) : assertion_scope.
Notation "a + b" := (fun st => mkAexp a st + mkAexp b st) : assertion_scope.
Notation "a - b" := (fun st => mkAexp a st - mkAexp b st) : assertion_scope.
Notation "a * b" := (fun st => mkAexp a st * mkAexp b st) : assertion_scope.

(* ################################################################# *)
(** * Hoare Triples, Formally *)

Definition hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st'  ->
     P st  ->
     Q st'.

Notation "{{ P }}  c  {{ Q }}" :=
  (hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.

(* ################################################################# *)
(** * Proof Rules *)

(** ** Assignment *)

Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).

Theorem hoare_asgn : forall Q X a,
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  unfold hoare_triple.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assn_sub in HQ. assumption.
Qed.

(** ** Consequence *)

Theorem hoare_consequence_pre : forall (P P' Q : Assertion) c,
  {{P'}} c {{Q}} ->
  P ->> P' ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P P' Q c Hhoare Himp st st' Heval Hpre.
  apply Hhoare with (st := st).
  - assumption.
  - apply Himp. assumption.
Qed.

Theorem hoare_consequence_post : forall (P Q Q' : Assertion) c,
  {{P}} c {{Q'}} ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  unfold hoare_triple, "->>".
  intros P Q Q' c Hhoare Himp st st' Heval Hpre.
  apply Himp.
  apply Hhoare with (st := st).
  - assumption.
  - assumption.
Qed.

Theorem hoare_consequence : forall (P P' Q Q' : Assertion) c,
  {{P'}} c {{Q'}} ->
  P ->> P' ->
  Q' ->> Q ->
  {{P}} c {{Q}}.
Proof.
  intros P P' Q Q' c Htriple Hpre Hpost.
  apply hoare_consequence_pre with (P' := P').
  - apply hoare_consequence_post with (Q' := Q').
    + assumption.
    + assumption.
  - assumption.
Qed.

Hint Unfold assert_implies hoare_triple assn_sub t_update : core.
Hint Unfold assert_of_Prop Aexp_of_nat Aexp_of_aexp : core.

(** ** Skip *)

Theorem hoare_skip : forall P,
     {{P}} skip {{P}}.
Proof.
  intros P st st' H HP. inversion H; subst. assumption.
Qed.

(** ** Sequencing *)

Theorem hoare_seq : forall P Q R c1 c2,
     {{Q}} c2 {{R}} ->
     {{P}} c1 {{Q}} ->
     {{P}} c1; c2 {{R}}.
Proof.
  unfold hoare_triple.
  intros P Q R c1 c2 H1 H2 st st' H12 Pre.
  inversion H12; subst.
  eauto.
Qed.

(** ** Conditionals *)

Definition bassn b : Assertion :=
  fun st => (beval st b = true).

Coercion bassn : bexp >-> Assertion.

Arguments bassn /.
Hint Unfold bassn : core.

Lemma bexp_eval_true : forall b st,
  beval st b = true -> (bassn b) st.
Proof. auto. Qed.

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassn b) st).
Proof. congruence. Qed.

Hint Resolve bexp_eval_false : core.

Theorem hoare_if : forall P Q (b:bexp) c1 c2,
  {{ P /\ b }} c1 {{Q}} ->
  {{ P /\ ~ b}} c2 {{Q}} ->
  {{P}} if b then c1 else c2 end {{Q}}.
Proof.
  intros P Q b c1 c2 HTrue HFalse st st' HE HP.
  inversion HE; subst; eauto.
Qed.

Theorem hoare_if_wp : forall P1 P2 Q (b:bexp) c1 c2,
    {{ P1 }} c1 {{ Q }} ->
    {{ P2 }} c2 {{ Q }} ->
    {{ (b -> P1) /\ (~ b -> P2) }} if b then c1 else c2 end {{ Q }}.
Proof.
  intros P1 P2 Q b c1 c2 HTrue HFalse st st' HE [HP1 HP2].
  inversion HE; subst; eauto.
Qed.

(** ** While Loops *)

Theorem hoare_while : forall P (b:bexp) c,
  {{P /\ b}} c {{P}} ->
  {{P}} while b do c end {{P /\ ~ b}}.
Proof.
  intros P b c Hhoare st st' Heval HP.
  remember <{while b do c end}> as original_command eqn:Horig.
  induction Heval;
    try (inversion Horig; subst; clear Horig);
    eauto.
Qed.

(** ############################################################### **)
(**                                                                 **)
(** *             STLC: Simply Typed Lambda Calculus                **)
(**                                                                 **)
(** ############################################################### **)

(* ################################################################# *)
(** * Syntax *)

Inductive ty : Type :=
  | Ty_Arrow : ty -> ty -> ty
  | Ty_Nat  : ty
  | Ty_Sum  : ty -> ty -> ty
  | Ty_List : ty -> ty
  | Ty_Unit : ty
  | Ty_Prod : ty -> ty -> ty
.

Inductive tm : Type :=
  (* pure STLC for Ty_Arrow *)
  | tm_var : string -> tm
  | tm_app : tm -> tm -> tm
  | tm_abs : string -> ty -> tm -> tm
  (* numbers for Ty_Nat *)
  | tm_const: nat -> tm
  | tm_plus : tm -> tm -> tm
  | tm_minus : tm -> tm -> tm
  | tm_mult : tm -> tm -> tm
  | tm_if0  : tm -> tm -> tm -> tm
  (* sums for Ty_Sum *)
  | tm_inl : ty -> tm -> tm     (* tm_inl Unit (tm_const 3) : Ty_Sum Ty_Nat Unit *)
  | tm_inr : ty -> tm -> tm     (* tm_inr Unit (tm_const 3) : Ty_Sum Unit Ty_Nat *)
  | tm_case : tm -> string -> tm -> string -> tm -> tm
          (* i.e., [match t0 with | inl x1 => t1 | inr x2 => t2 end] *)
  (* lists for Ty_List *)
  | tm_nil : ty -> tm
  | tm_cons : tm -> tm -> tm
  | tm_lcase : tm -> tm -> string -> string -> tm -> tm
           (* i.e., [match t1 with | nil => t2 | x::y => t3 end] *)
  (* unit for Ty_Unit *)
  | tm_unit : tm

  (* pairs for Ty_Prod *)
  | tm_pair : tm -> tm -> tm
  | tm_fst : tm -> tm
  | tm_snd : tm -> tm

  (* let for Ty_Arrow *)
  | tm_let : string -> tm -> tm -> tm
                     
  (* fix for Ty_Arrow *)
  | tm_fix  : tm -> tm
.

Declare Custom Entry stlc.

Notation "<{{ e }}>" := e (e custom stlc at level 99).
Notation "( x )" := x (in custom stlc, x at level 99).
Notation "x" := x (in custom stlc at level 0, x constr at level 0).
Notation "S -> T" := (Ty_Arrow S T) (in custom stlc at level 50, right associativity).
Notation "x y" := (tm_app x y) (in custom stlc at level 1, left associativity).
Notation "\ x : t , y" :=
  (tm_abs x t y) (in custom stlc at level 90, x at level 99,
                     t custom stlc at level 99,
                     y custom stlc at level 99,
                     left associativity).
Coercion tm_var : string >-> tm.

Notation "{ x }" := x (in custom stlc at level 1, x constr).

Notation "'Nat'" := Ty_Nat (in custom stlc at level 0).
Notation "x + y" := (tm_plus x y) (in custom stlc at level 1,
                                      left associativity).
Notation "x - y" := (tm_minus x y) (in custom stlc at level 1,
                                      left associativity).
Notation "x * y" := (tm_mult x y) (in custom stlc at level 1,
                                      left associativity).
Notation "'if0' x 'then' y 'else' z" :=
  (tm_if0 x y z) (in custom stlc at level 89,
                    x custom stlc at level 99,
                    y custom stlc at level 99,
                    z custom stlc at level 99,
                    left associativity).
Coercion tm_const : nat >-> tm.

Notation "S :+ T" :=
  (Ty_Sum S T) (in custom stlc at level 4, left associativity).
Notation "'inl' T t" := (tm_inl T t) (in custom stlc at level 0,
                                         T custom stlc at level 0,
                                         t custom stlc at level 0).
Notation "'inr' T t" := (tm_inr T t) (in custom stlc at level 0,
                                         T custom stlc at level 0,
                                         t custom stlc at level 0).
Notation "'case' t0 'of' '|' 'inl' x1 '=>' t1 '|' 'inr' x2 '=>' t2" :=
  (tm_case t0 x1 t1 x2 t2) (in custom stlc at level 89,
                               t0 custom stlc at level 99,
                               x1 custom stlc at level 99,
                               t1 custom stlc at level 99,
                               x2 custom stlc at level 99,
                               t2 custom stlc at level 99,
                               left associativity).

Notation "X :* Y" :=
  (Ty_Prod X Y) (in custom stlc at level 2, X custom stlc, Y custom stlc at level 0).
Notation "( x ',' y )" := (tm_pair x y) (in custom stlc at level 0,
                                                x custom stlc at level 99,
                                                y custom stlc at level 99).
Notation "t '.fst'" := (tm_fst t) (in custom stlc at level 0).
Notation "t '.snd'" := (tm_snd t) (in custom stlc at level 0).

Notation "'List' T" :=
  (Ty_List T) (in custom stlc at level 4).
Notation "'nil' T" := (tm_nil T) (in custom stlc at level 0, T custom stlc at level 0).
Notation "h '::' t" := (tm_cons h t) (in custom stlc at level 2, right associativity).
Notation "'case' t1 'of' '|' 'nil' '=>' t2 '|' x '::' y '=>' t3" :=
  (tm_lcase t1 t2 x y t3) (in custom stlc at level 89,
                              t1 custom stlc at level 99,
                              t2 custom stlc at level 99,
                              x constr at level 1,
                              y constr at level 1,
                              t3 custom stlc at level 99,
                              left associativity).

Notation "'Unit'" :=
  (Ty_Unit) (in custom stlc at level 0).
Notation "'unit'" := tm_unit (in custom stlc at level 0).

Notation "'let' x '=' t1 'in' t2" :=
  (tm_let x t1 t2) (in custom stlc at level 0).

Notation "'fix' t" := (tm_fix t) (in custom stlc at level 0).

(* ################################################################# *)
(** * Evaluation Relation *)

(** *** Substitution *)

Reserved Notation "'[' x ':=' s ']' t" (in custom stlc at level 20, x constr).
Fixpoint subst (x : string) (s : tm) (t : tm) : tm :=
  match t with
  (* pure STLC *)
  | tm_var y =>
      if eqb_string x y then s else t
  | <{{\y:T, t1}}> =>
      if eqb_string x y then t else <{{\y:T, [x:=s] t1}}>
  | <{{t1 t2}}> =>
      <{{([x:=s] t1) ([x:=s] t2)}}>
  (* numbers *)
  | tm_const _ =>
    t
  | <{{t1 + t2}}> =>
      <{{([x := s] t1) + ([x := s] t2)}}>
  | <{{t1 - t2}}> =>
      <{{([x := s] t1) - ([x := s] t2)}}>
  | <{{t1 * t2}}> =>
      <{{([x := s] t1) * ([x := s] t2)}}>
  | <{{if0 t1 then t2 else t3}}> =>
      <{{if0 [x := s] t1 then [x := s] t2 else [x := s] t3}}>
  (* sums *)
  | <{{inl T2 t1}}> =>
      <{{inl T2 ( [x:=s] t1)}}>
  | <{{inr T1 t2}}> =>
      <{{inr T1 ( [x:=s] t2)}}>
  | <{{case t0 of | inl y1 => t1 | inr y2 => t2}}> =>
      <{{case ([x:=s] t0) of
         | inl y1 => { if eqb_string x y1 then t1 else <{{ [x:=s] t1 }}> }
         | inr y2 => { if eqb_string x y2 then t2 else <{{ [x:=s] t2 }}> } }}>
  (* lists *)
  | <{{nil _}}> =>
      t
  | <{{t1 :: t2}}> =>
      <{{ ([x:=s] t1) :: ([x:=s] t2) }}>
  | <{{case t1 of | nil => t2 | y1 :: y2 => t3}}> =>
      <{{case ( [x:=s] t1 ) of
        | nil => [x:=s] t2
        | y1 :: y2 =>
        {if eqb_string x y1 then
           t3
         else if eqb_string x y2 then t3
              else <{{ [x:=s] t3 }}> } }}>
  (* unit *)
  | <{{unit}}> => <{{unit}}>
  (* pairs *)
  | <{{(t1,t2)}}> => <{{ ([x:=s] t1, [x:=s]t2) }}>
  | <{{t.fst}}> => <{{([x:=s]t).fst}}>
  | <{{t.snd}}> => <{{([x:=s]t).snd}}>
  (* let *)
  | <{{let y = t1 in t2}}> =>
    <{{let y = [x:=s] t1 in ({ if eqb_string x y then t2 else <{{[x:=s] t2}}> }) }}>
  (* fix *)
  | <{{fix t}}> => <{{fix ([x:=s] t)}}>
  end

where "'[' x ':=' s ']' t" := (subst x s t) (in custom stlc).

(** *** Value *)

Inductive value : tm -> Prop :=
  (* In pure STLC, function abstractions are values: *)
  | v_abs : forall x T2 t1,
      value <{{\x:T2, t1}}>
  (* Numbers are values: *)
  | v_nat : forall n : nat,
      value <{{n}}>
  (* A tagged value is a value:  *)
  | v_inl : forall v T1,
      value v ->
      value <{{inl T1 v}}>
  | v_inr : forall v T1,
      value v ->
      value <{{inr T1 v}}>
  (* A list is a value iff its head and tail are values: *)
  | v_lnil : forall T1, value <{{nil T1}}>
  | v_lcons : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{{v1 :: v2}}>
  (* A unit is always a value *)
  | v_unit : value <{{unit}}>
  (* A pair is a value if both components are: *)
  | v_pair : forall v1 v2,
      value v1 ->
      value v2 ->
      value <{{(v1, v2)}}>.

Hint Constructors value : core.

(** *** Step *)

Reserved Notation "t '-->' t'" (at level 40).

Inductive step : tm -> tm -> Prop :=
  (* pure STLC *)
  | ST_AppAbs : forall x T2 t1 v2,
         value v2 ->
         <{{(\x:T2, t1) v2}}> --> <{{ [x:=v2]t1 }}>
  | ST_App1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 t2}}> --> <{{t1' t2}}>
  | ST_App2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 t2}}> --> <{{v1  t2'}}>
  (* numbers *)
      
  | ST_Plusconsts : forall n1 n2 : nat,
         <{{n1 + n2}}> --> <{{ {n1 + n2} }}>
  | ST_Plus1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 + t2}}> --> <{{t1' + t2}}>
  | ST_Plus2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 + t2}}> --> <{{v1 + t2'}}>
  | ST_Minusconsts : forall n1 n2 : nat,
         <{{n1 - n2}}> --> <{{ {n1 - n2} }}>
  | ST_Minus1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 - t2}}> --> <{{t1' - t2}}>
  | ST_Minus2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 - t2}}> --> <{{v1 - t2'}}>
  | ST_Mulconsts : forall n1 n2 : nat,
         <{{n1 * n2}}> --> <{{ {n1 * n2} }}>
  | ST_Mult1 : forall t1 t1' t2,
         t1 --> t1' ->
         <{{t1 * t2}}> --> <{{t1' * t2}}>
  | ST_Mult2 : forall v1 t2 t2',
         value v1 ->
         t2 --> t2' ->
         <{{v1 * t2}}> --> <{{v1 * t2'}}>
  | ST_If0 : forall t1 t1' t2 t3,
         t1 --> t1' ->
         <{{if0 t1 then t2 else t3}}> --> <{{if0 t1' then t2 else t3}}>
  | ST_If0_Zero : forall t2 t3,
         <{{if0 0 then t2 else t3}}> --> t2
  | ST_If0_Nonzero : forall n t2 t3,
         <{{if0 {S n} then t2 else t3}}> --> t3
  (* sums *)
  | ST_Inl : forall t1 t1' T2,
        t1 --> t1' ->
        <{{inl T2 t1}}> --> <{{inl T2 t1'}}>
  | ST_Inr : forall t2 t2' T1,
        t2 --> t2' ->
        <{{inr T1 t2}}> --> <{{inr T1 t2'}}>
  | ST_Case : forall t0 t0' x1 t1 x2 t2,
        t0 --> t0' ->
        <{{case t0 of | inl x1 => t1 | inr x2 => t2}}> -->
        <{{case t0' of | inl x1 => t1 | inr x2 => t2}}>
  | ST_CaseInl : forall v0 x1 t1 x2 t2 T2,
        value v0 ->
        <{{case inl T2 v0 of | inl x1 => t1 | inr x2 => t2}}> --> <{{ [x1:=v0]t1 }}>
  | ST_CaseInr : forall v0 x1 t1 x2 t2 T1,
        value v0 ->
        <{{case inr T1 v0 of | inl x1 => t1 | inr x2 => t2}}> --> <{{ [x2:=v0]t2 }}>
  (* lists *)
  | ST_Cons1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{{t1 :: t2}}> --> <{{t1' :: t2}}>
  | ST_Cons2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{{v1 :: t2}}> --> <{{v1 :: t2'}}>
  | ST_Lcase1 : forall t1 t1' t2 x1 x2 t3,
       t1 --> t1' ->
       <{{case t1 of | nil => t2 | x1 :: x2 => t3}}> -->
       <{{case t1' of | nil => t2 | x1 :: x2 => t3}}>
  | ST_LcaseNil : forall T1 t2 x1 x2 t3,
       <{{case nil T1 of | nil => t2 | x1 :: x2 => t3}}> --> t2
  | ST_LcaseCons : forall v1 vl t2 x1 x2 t3,
       value v1 ->
       value vl ->
       <{{case v1 :: vl of | nil => t2 | x1 :: x2 => t3}}>
         -->  <{{ [x2 := vl] ([x1 := v1] t3) }}>
  (* pairs *)
  | ST_Pair1 : forall t1 t1' t2,
       t1 --> t1' ->
       <{{(t1, t2)}}> --> <{{(t1',  t2)}}>
  | ST_Pair2 : forall v1 t2 t2',
       value v1 ->
       t2 --> t2' ->
       <{{(v1, t2)}}> --> <{{(v1, t2')}}>
  | ST_Fst : forall t1 t1',
       t1 --> t1' ->
       <{{t1.fst}}> --> <{{t1'.fst}}>
  | ST_FstPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{{(v1,v2).fst}}> --> <{{ v1 }}>
  | ST_Snd : forall t1 t1',
       t1 --> t1' ->
       <{{t1.snd}}> --> <{{t1'.snd}}>
  | ST_SndPair : forall v1 v2,
       value v1 ->
       value v2 ->
       <{{(v1,v2).snd}}> --> <{{ v2 }}>
  (* let *)
  | ST_Let : forall x t1 t1' t2,
       t1 --> t1' ->
       <{{let x = t1 in t2}}> --> <{{let x = t1' in t2}}>
  | ST_LetVal : forall x v1 t2,
       value v1 ->
       <{{let x = v1 in t2}}> --> <{{ [x:=v1]t2 }}>
  (* fix *)
  | ST_Fix : forall t1 t1',
       t1 --> t1' ->
       <{{fix t1}}> --> <{{fix t1'}}>
  | ST_FixAbs : forall f T t,
       <{{fix (\f:T, t)}}> --> <{{ [f := fix (\f:T, t) ] t }}>

  where "t '-->' t'" := (step t t').

Hint Constructors step : core.

(* ################################################################# *)
(** * Typing Relation *)

Definition context := partial_map ty.

(** Next we define the typing rules.  These are nearly direct
    transcriptions of the inference rules shown above. *)

Reserved Notation "Gamma '|--' t '\in' T" (at level 40, t custom stlc, T custom stlc at level 0).

Inductive has_type : context -> tm -> ty -> Prop :=
  (* pure STLC *)
  | T_Var : forall Gamma x T1,
      Gamma x = Some T1 ->
      Gamma |-- x \in T1
  | T_Abs : forall Gamma x T1 T2 t1,
      (x |-> T2 ; Gamma) |-- t1 \in T1 ->
      Gamma |-- \x:T2, t1 \in (T2 -> T1)
  | T_App : forall T1 T2 Gamma t1 t2,
      Gamma |-- t1 \in (T2 -> T1) ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- t1 t2 \in T1
  (* numbers *)
  | T_Nat : forall Gamma (n : nat),
      Gamma |-- n \in Nat
  | T_Plus : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 + t2 \in Nat
  | T_Minus : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 - t2 \in Nat
  | T_Mult : forall Gamma t1 t2,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in Nat ->
      Gamma |-- t1 * t2 \in Nat
  | T_If0 : forall Gamma t1 t2 t3 T0,
      Gamma |-- t1 \in Nat ->
      Gamma |-- t2 \in T0 ->
      Gamma |-- t3 \in T0 ->
      Gamma |-- if0 t1 then t2 else t3 \in T0
  (* sums *)
  | T_Inl : forall Gamma t1 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- (inl T2 t1) \in (T1 :+ T2)
  | T_Inr : forall Gamma t2 T1 T2,
      Gamma |-- t2 \in T2 ->
      Gamma |-- (inr T1 t2) \in (T1 :+ T2)
  | T_Case : forall Gamma t0 x1 T1 t1 x2 T2 t2 T3,
      Gamma |-- t0 \in (T1 :+ T2) ->
      (x1 |-> T1 ; Gamma) |-- t1 \in T3 ->
      (x2 |-> T2 ; Gamma) |-- t2 \in T3 ->
      Gamma |-- (case t0 of | inl x1 => t1 | inr x2 => t2) \in T3
  (* lists *)
  | T_Nil : forall Gamma T1,
      Gamma |-- (nil T1) \in (List T1)
  | T_Cons : forall Gamma t1 t2 T1,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in (List T1) ->
      Gamma |-- (t1 :: t2) \in (List T1)
  | T_Lcase : forall Gamma t1 T1 t2 x1 x2 t3 T2,
      Gamma |-- t1 \in (List T1) ->
      Gamma |-- t2 \in T2 ->
      (x1 |-> T1 ; x2 |-> <{{List T1}}> ; Gamma) |-- t3 \in T2 ->
      Gamma |-- (case t1 of | nil => t2 | x1 :: x2 => t3) \in T2
  (* unit *)
  | T_Unit : forall Gamma,
      Gamma |-- unit \in Unit

  (* pairs *)
  | T_Pair : forall Gamma t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      Gamma |-- t2 \in T2 ->
      Gamma |-- (t1,  t2) \in (T1 :* T2)
  | T_Fst : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 :* T2) ->
      Gamma |-- t.fst \in T1
  | T_Snd : forall Gamma t T1 T2,
      Gamma |-- t \in (T1 :* T2) ->
      Gamma |-- t.snd \in T2
  (* let *)
  | T_Let : forall Gamma x t1 t2 T1 T2,
      Gamma |-- t1 \in T1 ->
      (x |-> T1; Gamma) |-- t2 \in T2 ->
      Gamma |-- let x = t1 in t2 \in T2
  (* fix *)
  | T_Fix : forall Gamma t T,
      Gamma |-- t \in (T -> T) ->
      Gamma |-- fix t \in T

where "Gamma '|--' t '\in' T" := (has_type Gamma t T).

Hint Constructors has_type : core.












(** ############################################################### **)
(**                                                                 **)
(** *           Definitions and Tactics for Final Exam              **)
(**                                                                 **)
(** ############################################################### **)

Definition FILL_IN_HERE {T: Type} : T.  Admitted.

(** Important: 

    - Just leave [exact FILL_IN_HERE] for those problems that you fail to prove.
**)

(**
    - Here is the list of tactics and tacticals you have learned.

      [intros]
      [revert]
      [reflexivity]
      [simpl]
      [rewrite]
      [induction]
      [assert]
      [unfold]
      [apply] ... [with] ... [in] ...
      [destruct] ... [as] ... [eqn:] ...
      [inversion]
      [symmetry]
      [generalize dependent]
      [split]
      [exists]
      [clear]
      [subst]
      [rename] ... [into] ...
      [contradiction]
      [constructor]
      [auto]
      [repeat]
      [try]
      [remember] ... [as] ...
      [replace] ... [with] ...
      [eauto]
      [nia]
      [;]
**)

(** IMPORTANT!!

   You can use a very powerful tactic, [nia].
   [nia] can solve arithmetic problems automatically.
*)

(* ################################################################# *)
(** * hexploit *)

(* [hexploit]: A very useful tactic, developed by Gil Hur.

   Suppose we have:

     H: P1 -> ... -> Pn -> Q
     ========================
     G

   [hexploit H] turns this goal into the following (n+1) subgoals:

     H: P1 -> ... -> Pn -> Q
     =========================
     P1

     ...

     H: P1 -> ... -> Pn -> Q
     =========================
     Pn

     H: P1 -> ... -> Pn -> Q
     =========================
     Q -> G
*)

Lemma __mp__: forall P Q: Type, P -> (P -> Q) -> Q.
Proof. intuition. Defined.

Ltac hexploit H := eapply __mp__; [eapply H|].

(* ################################################################# *)
(** * Names for Variables *)

(** Defining a few variable names as notational shorthands will make
    examples easier to read: *)

Definition F : string := "F".
Definition G : string := "G".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".
Definition I : string := "I".
Definition J : string := "J".
Definition P : string := "P".
Definition T : string := "T".
Definition N : string := "N".
Definition RES : string := "RES".

(* ################################################################# *)
(** * Automation for Hoare Logic *)

Ltac hauto_vc :=
  eauto;
  unfold "->>", assn_sub, t_update, bassn;
  intros; simpl in *;
  repeat
    match goal with
    | [H: _ <> true |- _] => apply not_true_iff_false in H
    | [H: _ <> false |- _] => apply not_false_iff_true in H
    | [H: _ /\ _ |- _] => destruct H
    | [H: _ && _ = true |- _] => apply andb_true_iff in H
    | [H: _ && _ = false |- _] => apply andb_false_iff in H
    | [H: _ || _ = true |- _] => apply orb_true_iff in H
    | [H: _ || _ = false |- _] => apply orb_false_iff in H
    | [H: negb _ = true |- _] => eapply negb_true_iff in H
    | [H: negb _ = false |- _] => eapply negb_false_iff in H
    | [H: (_ =? _) = true |- _] => eapply beq_nat_true in H
    | [H: (_ =? _) = false |- _] => eapply beq_nat_false in H
    end;
  repeat (
    try rewrite -> eqb_eq in *;
    try rewrite -> leb_le in *;
    try rewrite leb_iff in *;
    try rewrite leb_iff_conv in *
  );
  try discriminate; try contradiction; eauto; try nia.

Ltac hauto_split1 :=
  try match goal with
      | [|- {{_}} skip {{_}}] =>
        first [eapply hoare_skip; fail | eapply hoare_consequence_pre; [eapply hoare_skip|]]
      | [|- {{_}} _ := _ {{_}}] =>
        first [eapply hoare_asgn;[] | eapply hoare_consequence_pre; [eapply hoare_asgn|]]
      | [|- {{_}} _; _ {{_}}] =>
        eapply hoare_seq
      | [|- {{_}} if _ then _ else _ end {{_}}] =>
        first [eapply hoare_if_wp;[|] | eapply hoare_consequence_pre; [eapply hoare_if_wp|]]
      end.

Ltac hauto :=
  match goal with
  | [|- {{_}} _ {{_}}] => repeat hauto_split1
  | _ => idtac
  end;
  try (hauto_vc; fail).

Ltac hauto_while P :=
  first[
      eapply (hoare_while P) |
      eapply hoare_consequence_post; [eapply (hoare_while P)|] |
      eapply hoare_consequence_post; [eapply hoare_consequence_pre; [eapply (hoare_while P)|]|]
    ];
  hauto.

(* ################################################################# *)
(** * Definitions and Tactics for muti-step evaluation *)

Inductive multi {X:Type} (R: relation X) : relation X :=
  | multi_refl  : forall (x y: X) (EQ: x = y), multi R x y
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Notation " t '==>*' t' " := (multi step t t') (at level 40).

Hint Constructors multi : core.

Theorem multi_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      multi R x y  ->
      multi R y z ->
      multi R x z.
Proof.
  intros. induction H; subst; eauto.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Definition step_normal_form := normal_form step.

Definition normal_form_of (t t' : tm) :=
  (t ==>* t' /\ step_normal_form t').

Definition stuck (t:tm) : Prop :=
  normal_form step t /\ ~ value t.

(** *** Tactics [normalize1] and [normalize] *)

Tactic Notation "normalize1" :=
  eapply multi_step ; [ (eauto 20 using step; fail) | (instantiate; simpl)].

Tactic Notation "normalize" := 
   repeat normalize1;
   try (apply multi_refl; repeat apply f_equal; eauto; nia).

(* ################################################################# *)
(** * Program Definitions *)

(** *** Optimize Assignment *)

Fixpoint aexp_subst (x: string) (xa: aexp) (a: aexp) : aexp :=
  match a with
  | ANum _ => a
  | AId y => if eqb_string x y then xa else a
  | APlus a1 a2 => APlus (aexp_subst x xa a1) (aexp_subst x xa a2) 
  | AMinus a1 a2 => AMinus (aexp_subst x xa a1) (aexp_subst x xa a2) 
  | AMult a1 a2 => AMult (aexp_subst x xa a1) (aexp_subst x xa a2) 
  end.

Fixpoint optimize_asgn (c: com) : com :=
  match c with
  | <{ skip }> | <{ _ := _ }> => c
  | <{ c1 ; c2 }>  =>
    match c1, c2 with
    | <{ x1 := a1 }>, <{ x2 := a2 }> => 
      if eqb_string x1 x2
      then <{ x1 := aexp_subst x1 a1 a2 }>
      else c
    | _, _ => <{ optimize_asgn c1 ; optimize_asgn c2 }>
    end
  | <{ if b then c1 else c2 end }> =>
      <{ if b then optimize_asgn c1 else optimize_asgn c2 end }>
  | <{ while b do c end }> =>
      <{ while b do optimize_asgn c end }>
  end.

(** *** Odd Sum *)

Definition odd_sum_com : com := <{
  RES := 0 ;
  I := 0 ;
  J := 1 ;
  while ~(I = N) do
    RES := RES + J;
    I := I + 1;
    J := J + 2
  end }>.

(** *** Fibonacci *)

Fixpoint fib n :=
  match n with 
  | 0 => 0
  | S n' =>
    match n' with
    | 0 => 1
    | S n'' => fib n' + fib n''         
    end
  end.

(** *** Slow Factorial *)

Definition slow_fact_com : com := <{
  RES := 1 ;
  while ~ (N = 0) do
    J := RES;
    I := 1;
    while ~ (I = N) do
      RES := RES + J;
      I := I + 1
    end;
    N := N - 1
  end }>.

Fixpoint fact n :=
  match n with 
  | 0 => 1 
  | S m => n * fact m 
  end.













(*=========== 3141592 ===========*)

(** Prove the following lemma (10 points). *)

Lemma aexp_subst_eval: forall x a1 a2 st,
  aeval st (aexp_subst x a1 a2) = aeval (x !-> aeval st a1; st) a2.
Proof.
  induction a2; intros; simpl; eauto.
  unfold t_update. destruct eqb_string; eauto.
Qed.

(*-- Check --*)

Check aexp_subst_eval: forall x a1 a2 st,
  aeval st (aexp_subst x a1 a2) = aeval (x !-> aeval st a1; st) a2.

(*=========== 3141592 ===========*)

(** Prove the correctness of [optimize_asgn] (10 points). *)

Theorem optimize_asgn_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_asgn c ]=>st').
Proof.
  intros. induction H; simpl; eauto.
  destruct c1; eauto.
  destruct c2; eauto.
  destruct (eqb_string x x0) eqn: EQN; eauto.
  apply eqb_string_true_iff in EQN. subst.
  inversion H; subst. inversion H0; subst.
  rewrite t_update_shadow.
  rewrite <-aexp_subst_eval. eauto.
Qed.

(*-- Check --*)

Check optimize_asgn_correct: forall st st' c,
  (st =[ c ]=> st') -> (st =[ optimize_asgn c ]=>st').

(*=========== 3141592 ===========*)

(** Find the weakest precondition [WP] of [X := X + Y] for postcondition [X - 2*Y < 10]

      {{ WP }} X := X + Y {{ X - 2*Y < 10 }}

    and prove it correct (10 points).
 *)

Definition WP : Assertion :=
  assert (X - Y < 10)
  .

(* You can use [hauto_vc]. *)
Theorem WP_weakest: forall P
    (PRE: {{ P }} X := X + Y {{ X - 2*Y < 10 }}),
  P ->> WP.
Proof.
  intros. unfold WP. red in PRE. red; intros.
  hexploit PRE; eauto using ceval. 
  hauto_vc.
Qed.

(*-- Check --*)

Check WP : Assertion.

Check WP_weakest: forall P
    (PRE: {{ P }} X := X + Y {{ X - 2*Y < 10 }}),
  P ->> WP.

(*=========== 3141592 ===========*)

(** *** The following is an example of an Imp program. *)

Definition slow_sub_com (m n: nat) : com :=
  <{
    X := m;
    Z := n;
    while ~(X = 0) do
      Z := Z - 1;
      X := X - 1
    end
  }>.

(** End **)

(** Write an Imp program [sort_two_com] that sorts in the increasing order
    the values in the variables 'X' and 'Y', and prove it correct (10 points).

    Avaiable Vairable Names: F, G, X, Y, Z, I, J, P, T, N, RES
 *)

Definition sort_two_com : com :=
  <{
    if X <= Y then skip else
      Z := X;
      X := Y;
      Y := Z
    end
  }>
.

Theorem sort_two_com_correct: forall n m: nat,
  {{ X = n /\ Y = m }}
     sort_two_com
  {{ X <= Y /\ ((X = n /\ Y = m) \/ (X = m /\ Y = n)) }}.
Proof.
  unfold sort_two_com. intros.
  (* You should be able to prove the goal by [hauto]
     if you wrote [sort_two_com] correctly. *)  
  hauto.
Qed.

(*-- Check --*)

Check sort_two_com : com.

Check sort_two_com_correct: forall n m: nat,
  {{ X = n /\ Y = m }}
     sort_two_com
  {{ X <= Y /\ ((X = n /\ Y = m) \/ (X = m /\ Y = n)) }}.

(*=========== 3141592 ===========*)

(** *** The following is an example of verification using hauto. *)

Lemma slow_sub_correct: forall (m n: nat),
  {{ True }} slow_sub_com m n {{ Z = n - m }}.
Proof.
  unfold slow_sub_com. intros.
  hauto.
  - hauto_while (assert (Z - X = n - m)).
  - hauto.
Qed.

(** End **)

(** Verify the [odd_sum_com] program (10 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition odd_sum_com : com := <{
  RES := 0 ;
  I := 0 ;
  J := 1 ;
  while ~(I = N) do
    RES := RES + J;
    I := I + 1;
    J := J + 2
  end }>.
*)
  
Theorem odd_sum_correct: forall (n: nat),
  {{ N = n }} 
    odd_sum_com
  {{ RES = n * n }}.
Proof.
  intros. unfold odd_sum_com.
  hauto.
  - hauto_while (assert (RES = I * I /\ J = 2*I+1 /\ N = n)).
  - hauto.
Qed.

(*-- Check --*)

Check odd_sum_correct: forall (n: nat),
  {{ N = n }} 
    odd_sum_com
  {{ RES = n * n }}.

(*=========== 3141592 ===========*)

(** Verify the [slow_fact_com] program (10 points).

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

(*
Definition slow_fact_com : com := <{
  RES := 1 ;
  while ~ (N = 0) do
    J := RES;
    I := 1;
    while ~ (I = N) do
      RES := RES + J;
      I := I + 1
    end;
    N := N - 1
  end }>.

Fixpoint fact n :=
  match n with 
  | 0 => 1 
  | S m => n * fact m 
  end.
*)

Theorem slow_fact_correct: forall (n: nat),
  {{ N = n }} 
    slow_fact_com
  {{ RES = fact n }}.
Proof.
  intros. unfold slow_fact_com.
  hauto.
  - hauto_while (fun st => st RES * fact (st N) = fact n).
    + hauto_while (fun st => st J * fact (st N) = fact n /\
                             st RES = st J * st I /\ st I >= 1).
      hauto_vc.
      destruct (st N); try nia.
      simpl in *. rewrite sub_0_r. nia.
    + hauto_vc.
    + hauto_vc.
      rewrite H0 in H. simpl in *. nia.
  - hauto_vc.
    rewrite H. nia.
Qed.

(*-- Check --*)

Check slow_fact_correct: forall (n: nat),
  {{ N = n }} 
    slow_fact_com
  {{ RES = fact n }}.

(*=========== 3141592 ===========*)

(** Write the fibonacci function in com and prove it correct (20 points).

    Avaiable Vairable Names: F, G, X, Y, Z, I, J, P, T, N, RES

    Hint: You can also use [hauto_vc] to simplify the goal.
 *)

Definition fib_com : com :=
  <{
  if N = 0 then
    RES := 0
  else
    P := 0;
    RES := 1;
    I := 1;
    while I <= N-1 do
      T := RES;
      RES := RES + P;
      P := T;
      I := I + 1
    end
  end
  }>
.

Lemma fib_unfold: forall n, fib (S (S n)) = fib (S n) + fib n.
Proof.
  intros. destruct n; eauto.
Qed.

Theorem fib_correct: forall (n: nat),
  {{ N = n }} 
    fib_com
  {{ RES = fib n }}.
Proof.
  intros. unfold fib_com.
  hauto.
  - hauto_while (fun st => st RES = fib (st I) /\ st P = fib (st I - 1)
                           /\ st I >= 1 /\ st I <= n /\ st N = n).
    + hauto_vc.
      destruct (st I); try nia.
      rewrite (plus_comm _ 1). simpl plus; simpl minus in *. rewrite sub_0_r in *.
      rewrite fib_unfold. nia.
    + hauto_vc.
      replace (st I) with n in *; nia.
  - hauto_vc.
    rewrite H.
    destruct n; simpl; repeat split; intros; eauto; try nia.
    contradiction. discriminate.
Qed.

(*-- Check --*)

Check fib_com : com.

Check fib_correct: forall (n: nat),
  {{ N = n }} 
    fib_com
  {{ RES = fib n }}.

(*-- Check --*)

Check fib_com : com.

Check fib_correct: forall (n: nat),
  {{ N = n }} 
    fib_com
  {{ RES = fib n }}.

(*=========== 3141592 ===========*)

(** *** The following is an example of a STLC program, and a test. *)

Definition tmsquare : tm := <{{ \X:Nat, X * X }}>.
  
Example tmsquare_test: <{{ tmsquare 3 }}> ==>* 9.
Proof.
  unfold tmsquare.
  normalize.
Qed.

(** End **)

(** Write a lamba term [tmfac] of type (TNat -> TNat) that computes a factorial (10 points)
    and prove it correct (10 points).

    Avaiable Vairable Names: F, G, X, Y, Z, I, J, P, T, N, RES
 *)

Definition tmfac : tm :=
  <{{
  fix (\F:Nat->Nat, \N:Nat,
    if0 N then 1 else N * (F (N-1))
  )
  }}>
.

Example tmfac_type: empty |-- tmfac \in (Nat -> Nat).
Proof.
  repeat econstructor.
Qed.

Example tmfac_ex1: <{{ tmfac 4 }}> ==>* <{{ 24 }}>.
Proof.
  unfold tmfac. normalize.
Qed.

Example tmfac_ex2: <{{ tmfac 5 }}> ==>* <{{ 120 }}>.
Proof.
  unfold tmfac. normalize.
Qed.

Example tmfac_ex3: <{{ tmfac 6 }}> ==>* <{{ 720 }}>.
Proof.
  unfold tmfac. normalize.
Qed.

(** Correctness:

   Hint: 
   Use the tactic [normalize1], which takes one-step of execution.
     (e.g.) [do 5 normalize1] takes 5 steps of execution.
   You can use the tactic [normalize], which takes steps as many as possible.

   Proving the following lemma might be useful.
   [forall (n: nat) t t', t ==>* t' -> <{{ n * t }}> ==>* <{{ n * t' }}>]
 *)

Lemma tmult_compat2: forall (n: nat) t t',
  t ==>* t' ->
  <{{ n * t }}> ==>* <{{ n * t' }}>.
Proof.
  intros; induction H; subst; eauto.
Qed.

Theorem tmfac_correct: forall (n: nat),
   <{{ tmfac n }}> ==>* (tm_const (fact n)).
Proof.
  unfold tmfac. intros.
  normalize.
  induction n.
  - normalize.
  - normalize.
    rewrite sub_0_r.
    eapply multi_trans.
    + eapply tmult_compat2. eauto.
    + normalize.
Qed.

(*-- Check --*)

Check tmfac : tm.

Check tmfac_type: empty |-- tmfac \in (Nat -> Nat).

Check tmfac_ex1: <{{ tmfac 4 }}> ==>* <{{ 24 }}>.

Check tmfac_ex2: <{{ tmfac 5 }}> ==>* <{{ 120 }}>.

Check tmfac_ex3: <{{ tmfac 6 }}> ==>* <{{ 720 }}>.

(*-- Check --*)

Check tmfac : tm.

Check tmfac_correct: forall (n: nat),
   <{{ tmfac n }}> ==>* (tm_const (fact n)).

