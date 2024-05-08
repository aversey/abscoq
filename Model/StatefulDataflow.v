From Coq Require Import String List Vector.
From Model Require Import Streaming.
Import ListNotations.
Import StreamingNotations.

Section StatefulDataflow.

Class SDParameters: Type :=
  { countOfProcessors: nat
  ; StateValue: Type
  ; EventValue: Type }.
Context { sdParametersContext: SDParameters }.

(* Values *)
Implicit Types (v: StateValue).
Implicit Types (w: EventValue).
Implicit Types (W: list EventValue).

(* Epoch Number *)
Implicit Types (e: nat).

(* Processor ID *)
Implicit Types (p q: Fin.t countOfProcessors).

(* Stream Name *)
Implicit Types (s o r t: string).

(* Sequence Number or Length of Sequence *)
Implicit Types (n: nat).

(* Sequence Index *)
Implicit Types (i j: nat).

(* Processor *)
Inductive Processor := lltask (f: StateValue * EventValue -> StateValue * list EventValue) (ss: list string) o.
Implicit Types (pi: Processor).

(* State *)
Inductive llstatecase := failed | normal e v.
Definition Archive := list StateValue.
Implicit Types (a: Archive).
Definition State: Type := Archive * llstatecase.
Implicit Types (sigma Sigmap: State).

(* Message Data *)
Inductive lldatacase := event w | border.
Definition MessageData: Type := nat * lldatacase.
Implicit Types (d: MessageData).

(* Auxiliary Data *)
Definition AuxiliaryData := list (nat * string * MessageData).

Instance sParameters: SParameters :=
  {| SCountOfProcessors := countOfProcessors
   ; SProcessor     := Processor
   ; SState         := State
   ; SMessageData   := MessageData
   ; SAuxiliaryData := AuxiliaryData |}.

Reserved Notation "pi '||-' sigma '-(' X ')->l' sigma'" (at level 60).
Inductive lsteps: Processor -> State -> list Action -> State -> Prop :=
| l_event: forall f ss o a e v s w W' v',
  (v', W') = f(v, w) ->
  lltask f ss o ||- (a, normal e v) -([`- s (e, event w)] ++ List.map (fun w' => `+ o (e, event w')) W' )->l (a, normal e v')
| l_border: forall f ss o a e v s,
  lltask f ss o ||-
  (a, normal e v)
  -(List.map (fun s => `- s (e, border)) ss ++ [produce o (e, border)])->l
  (a++[v], normal (e+1) v)
where "pi '||-' sigma '-(' X ')->l' sigma'" := (lsteps pi sigma X sigma').

Reserved Notation "pi '||-' sigma '-(' X ')->f' sigma'" (at level 60).
Inductive fsteps: Processor -> State -> list Action -> State -> Prop :=
| f_fail: forall pi a sigmal, pi ||- (a, sigmal) -([])->f (a, failed)
where "pi '||-' sigma '-(' X ')->f' sigma'" := (fsteps pi sigma X sigma').

Definition local pi sigma X sigma': Prop :=
  pi ||- sigma -(X)->l sigma' \/
  pi ||- sigma -(X)->f sigma'.
Notation "pi ||- sigma -( X )-> sigma'" := (local pi sigma X sigma') (at level 60).

Definition gce (c: Configuration): nat := match c with (Pi, Sigma, N, M, D) =>
  fold_left (fun acc sigma => match sigma with (a, sigmal) => min acc (List.length a) end) 0 Sigma
end.

Definition out c: Messages := match c with (Pi, Sigma, N, M, D) =>
  List.filter (fun m => match m with (n, s, (e, dd)) => Nat.leb e (gce c) end) M
end.

Definition onStream s M: Messages :=
  List.filter (fun m => match m with (n, s', (e, dd)) => String.eqb s' s end) M.

Definition lcs c: Configuration := match c with (Pi, Sigma, N, M, D) =>
  ( Pi
  , Vector.map (fun sigma => match sigma with (a, sigmav) =>
    ( firstn (gce c + 1) a
    , match (List.nth_error a (gce c)) with None => failed |
      Some v => normal (gce c + 1) v
    end) end) Sigma
  , Vector.map (fun Np => List.map (fun sn => match sn with (s, n) => (s, length (onStream s (out c))) end) Np) N
  , List.filter (fun m => match m with (n, s, (e, dd)) => Nat.ltb (gce c) e end) D ++ out c
  , D )
end.

Reserved Notation "c '=>f' c'" (at level 60).
Inductive fSteps: Configuration -> Configuration -> Prop :=
| f_recover: forall Pi Sigma N M D p a,
  nth Sigma p = (a, failed) ->
  (Pi, Sigma, N, M, D) =>f lcs (Pi, Sigma, N, M, D)
where "c '=>f' c'" := (fSteps c c').

Definition F c c': Prop := StreamingAbsP fsteps c c' \/ fSteps c c'.
Definition L c c': Prop := StreamingAbsP local c c' \/ fSteps c c'.

End StatefulDataflow.
