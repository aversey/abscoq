(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Failure Transparency Definition *)
Require Import Coq.Lists.List.

Definition ruleset (config: Type) := config -> config -> Prop.

Definition reducible {config: Type} (R: ruleset config) C C' := R C C'.
Notation "R |- C '=>' C'" := (reducible R C C') (at level 60).

Definition execution {config: Type} (R: ruleset config) C0 E := 
  hd C0 E = C0 ->
  (forall i C C', nth_error E i = Some C -> nth_error E (i+1) = Some C' ->
    R |- C => C').


Definition observablyEquivalent {config: Type} {config': Type} {observation: Type}
  (R: ruleset config) (O: config -> observation)
  (T: config' -> config -> Prop)
  (O': config' -> observation) (R': ruleset config') :=
  forall C0 C'0, T C'0 C0 ->
  forall E, execution R C0 E ->
  exists E', execution R' C'0 E' /\
  forall i C, nth_error E i = Some C ->
  exists j C', nth_error E' j = Some C' /\
  O C = O' C'.

Definition failureTransparent {config: Type} {observation: Type}
  (R: ruleset config) (F: ruleset config)
  (O: config -> observation) (K: config -> Prop) :=
  observablyEquivalent
  R O
  (fun C C' => (C = C' /\ K C))
  O (fun C C' => (R C C' /\ ~F C C')).


(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Streaming *)
Require Import Basics.
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Require Import Coq.Vectors.Vector.
Require Import Coq.Strings.String.
Require Import Coq.Bool.Bool.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Syntax *)

Parameter countOfProcessors: nat.

(* Basic Definitions *)

(* Processor ID *)
Implicit Types (p q: Fin.t countOfProcessors).

(* Stream Name *)
Implicit Types (s o r t: string).

(* Sequence Number or Length of Sequence *)
Implicit Types (n: nat).

(* Sequence Index *)
Implicit Types (i j: nat).

(* LL: Epoch Number *)
Implicit Types (e: nat).

(* Values, for now let's just use natural numbers *)
Implicit Types (v: nat).

(* Parameter MessageData: Type. *)
(* For now just instantiated for the low level *)
Inductive lldatacase := event v | border.
Definition MessageData: Type := nat * lldatacase.
Implicit Types (d: MessageData).

(* Parameter State: Type. *)
(* For now just instantiated for the low level *)
Inductive llstatecase := failed | normal e v.
Definition Archive := list nat.
Implicit Types (a: Archive).
Definition State: Type := Archive * llstatecase.
Implicit Types (sigma Sigmap: State).

(* Parameter Processor: Type. *)
(* For now just instantiated for the low level *)
Inductive Processor := lltask (f: nat * nat -> nat * nat) (ss: list string) o.
Implicit Types (pi: Processor).

Inductive Action := produce s d | consume s d.
Notation "`+" := produce (at level 1) : type_scope.
Notation "`-" := consume (at level 1) : type_scope.
Implicit Types (x: Action).

Definition Actions := list Action.
Implicit Types (X: Actions).

Inductive Message := message n s d.
Implicit Types (m: Message).

Definition Messages := list Message.
Implicit Types (M: Messages).

(* Parameter AuxiliaryData: Type. *)
(* For now just instantiated for the low level *)
Definition AuxiliaryData: Type := Messages.
Implicit Types (D: AuxiliaryData).

(* Compound Definitions *)

Definition States := Vector.t State countOfProcessors.
Implicit Types (Sigma: States).

Definition Processors := Vector.t Processor countOfProcessors.
Implicit Types (Pi: Processors).

Definition SequenceNumbers := string -> nat.
Implicit Types (Np: SequenceNumbers).
Definition AllSequenceNumbers := Vector.t SequenceNumbers countOfProcessors.
Implicit Types (N: AllSequenceNumbers).

Definition Configuration: Type := Processors * States * AllSequenceNumbers * Messages * AuxiliaryData.
Implicit Types (C: Configuration).

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Semantics *)

Reserved Notation "pi '||-' sigma '-(' X ')->l' sigma'" (at level 60).
Inductive lsteps: Processor -> State -> list Action -> State -> Prop :=
| l_event: forall f ss o a e v s w w' v',
  (w', v') = f(w, v) ->
  lltask f ss o ||- (a, normal e v) -([`- s (e, event w); `+ o (e, event w')])->l (a, normal e v')
| l_border: forall f ss o a e v s,
  lltask f ss o ||-
  (a, normal e v)
  -(List.map (fun s => `- s (e, border)) ss ++ [`+ o (e, border)])->l
  (a++[v], normal (e+1) v)
where "pi '||-' sigma '-(' X ')->l' sigma'" := (lsteps pi sigma X sigma').

Reserved Notation "pi '||-' sigma1 '-(' X ')->f' sigma2" (at level 60).
Inductive fsteps: Processor -> State -> list Action -> State -> Prop :=
| f_fail: forall pi a sigmal, pi ||- (a, sigmal) -([])->f (a, failed)
where "pi '||-' sigma '-(' X ')->f' sigma'" := (fsteps pi sigma X sigma').

Definition local pi sigma A sigma': Prop := lsteps pi sigma A sigma' \/ fsteps pi sigma A sigma'.
Notation "pi ||- sigma -( X )-> sigma'" := (local pi sigma X sigma') (at level 60).

Definition replaceNp Np s n := fun s' => if string_dec s s' then n else Np s'.

Inductive applyActions: Actions -> SequenceNumbers -> Messages -> SequenceNumbers -> Messages -> Prop :=
| apply_produce : forall s d Np M Np' M',
  applyActions [`+ s d] Np M (replaceNp Np s (Np s + 1)) (message (Np s) s d :: M')
| apply_consume : forall s d Np M Np' M',
  List.In (message (Np s) s d) M ->
  applyActions [`- s d] Np M (replaceNp Np s (Np s + 1)) M
| apply_more : forall x X Np M Np' M' Np'' M'',
  applyActions [x] Np M Np' M' ->
  applyActions X Np' M' Np'' M'' ->
  applyActions (x :: X) Np M Np'' M''
| apply_empty : forall Np M, applyActions [] Np M Np M.

Reserved Notation "C '=>s(' steps ')' C'" (at level 60).
Inductive sSteps (steps: Processor -> State -> list Action -> State -> Prop):
  Configuration -> Configuration -> Prop :=
| s_step: forall Pi Sigma N M D p X Sigmap' Np' M',
  steps (nth Pi p) (nth Sigma p) (X) (Sigmap') ->
  applyActions X (nth N p) M Np' M' ->
  (Pi, Sigma, N, M, D) =>s(steps) (Pi, replace Sigma p Sigmap', replace N p Np', M', D)
where "C '=>s(' steps ')' C'" := (sSteps steps C C').

Definition gce C: nat := match C with (Pi, Sigma, N, M, D) =>
  fold_left (fun acc sigma => match sigma with (a, sigmal) => min acc (List.length a) end) 0 Sigma
end.

Definition out C: Messages := match C with (Pi, Sigma, N, M, D) =>
  List.filter (fun m => match m with message n s (e, dd) => Nat.leb e (gce C) end) M
end.

Definition snapshotOf C: Configuration := match C with (Pi, Sigma, N, M, D) =>
  (Pi,
  Sigma,
  N,
  List.filter (fun m => match m with message n s (e, dd) => Nat.ltb (gce C) e end) M ++ out C,
  D)
end.

Reserved Notation "C '=>f' C'" (at level 60).
Inductive fSteps: Configuration -> Configuration -> Prop :=
| f_recover: forall Pi Sigma N M D p a,
  nth Sigma p = (a, failed) ->
  (Pi, Sigma, N, M, D) =>f snapshotOf (Pi, Sigma, N, M, D)
where "C '=>f' C'" := (fSteps C C').

Definition F C C': Prop := sSteps fsteps C C' \/ fSteps C C'.
Definition L C C': Prop := sSteps local C C' \/ fSteps C C'.

Definition initial C := True. (* TODO *)
Theorem failureTransparency: failureTransparent L F out initial.
Admitted.