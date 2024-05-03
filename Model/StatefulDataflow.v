(* TODO refactor, think about modules/parameters (probably there is a better way to do it) *)
From Coq Require Import String List Vector.
From Model Require Import Streaming.
Import ListNotations.

Module Type StatefulDataflowTypes.
  Parameter eventValueType: Type.
  Parameter stateValueType: Type.
End StatefulDataflowTypes.

Module StatefulDataflowParameters (T: StatefulDataflowTypes) <: Parameters.
  Import T.
  Implicit Types (w: eventValueType).
  Implicit Types (v: stateValueType).
  Implicit Types (n e: nat).
  Implicit Types (s o r t: string).

  Inductive ProcessorType := lltask (f: stateValueType * eventValueType -> stateValueType * list eventValueType) (ss: list string) o.
  Definition Processor := ProcessorType.

  Inductive llstatecase := failed | normal e v.
  Definition Archive := list stateValueType.
  Implicit Types (a: Archive).
  Definition State: Type := Archive * llstatecase.

  Inductive lldatacase := event w | border.
  Definition MessageData: Type := nat * lldatacase.
  Implicit Types (d: MessageData).

  Inductive Message := message n s d.
  Definition AuxiliaryData: Type := list Message.
End StatefulDataflowParameters.

Module StatefulDataflow (C: CountOfProcessors) (T: StatefulDataflowTypes).
Module SDP := StatefulDataflowParameters T.
Module StatefulDataflowSystem := Streaming C SDP.
Export StatefulDataflowSystem.
Export T.

Implicit Types (v: stateValueType).
Implicit Types (w: eventValueType).
Implicit Types (W: list eventValueType).
Implicit Types (p q: Fin.t countOfProcessors).
Implicit Types (s o r t: string).
Implicit Types (n e: nat).
Implicit Types (i j: nat).
Implicit Types (pi: Processor).
Implicit Types (Pi: Processors).
Implicit Types (sigma Sigmap: State).
Implicit Types (Sigma: States).
Implicit Types (d: MessageData).
Implicit Types (m: Message).
Implicit Types (M: Messages).
Implicit Types (Np: SequenceNumbers).
Implicit Types (N: AllSequenceNumbers).
Implicit Types (D: AuxiliaryData).

Reserved Notation "pi '||-' sigma '-(' X ')->l' sigma'" (at level 60).
Inductive lsteps: Processor -> State -> list Action -> State -> Prop :=
| l_event: forall f ss o a e v s w W' v',
  (v', W') = f(v, w) ->
  lltask f ss o ||- (a, normal e v) -([`- s (e, event w)] ++ List.map (fun w' => `+ o (e, event w')) W')->l (a, normal e v')
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

Definition gce (C: Configuration): nat := match C with (Pi, Sigma, N, M, D) =>
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

Definition F C C': Prop := StreamingAbsP fsteps C C' \/ fSteps C C'.
Definition L C C': Prop := StreamingAbsP local C C' \/ fSteps C C'.

End StatefulDataflow.