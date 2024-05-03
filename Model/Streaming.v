From Coq Require Import List Vector String.
Import ListNotations.

Module Type CountOfProcessors.
  Parameter countOfProcessors: nat.
End CountOfProcessors.

Module Type Parameters.
  Parameter Processor: Type.
  Parameter State: Type.
  Parameter MessageData: Type.
  Parameter AuxiliaryData: Type.
End Parameters.

Module Streaming (C: CountOfProcessors) (P: Parameters).
Export C.
Export P.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Syntax *)

(* Basic Definitions *)

(* Processor ID *)
Implicit Types (p q: Fin.t countOfProcessors).

(* Stream Name *)
Implicit Types (s o r t: string).

(* Sequence Number or Length of Sequence *)
Implicit Types (n: nat).

(* Sequence Index *)
Implicit Types (i j: nat).

(* Processor *)
Implicit Types (pi: Processor).

(* State *)
Implicit Types (sigma Sigmap: State).

(* Message Data *)
Implicit Types (d: MessageData).

(* Auxiliary Data *)
Implicit Types (D: AuxiliaryData).

(* Compound Definitions *)

Definition Processors := Vector.t Processor countOfProcessors.
Implicit Types (Pi: Processors).

Definition States := Vector.t State countOfProcessors.
Implicit Types (Sigma: States).

Inductive Message := message n s d.
Implicit Types (m: Message).
Definition Messages := list Message.
Implicit Types (M: Messages).

Definition SequenceNumbers := string -> nat.
Implicit Types (Np: SequenceNumbers).
Definition AllSequenceNumbers := Vector.t SequenceNumbers countOfProcessors.
Implicit Types (N: AllSequenceNumbers).

Inductive Action := produce s d | consume s d.
Notation "`+" := produce (at level 1) : type_scope.
Notation "`-" := consume (at level 1) : type_scope.
Implicit Types (x: Action).
Definition Actions := list Action.
Implicit Types (X: Actions).

(* The Configuration *)

Definition Configuration: Type := Processors * States * AllSequenceNumbers * Messages * AuxiliaryData.
Implicit Types (C: Configuration).

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Action Application *)

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

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Semantics *)

Reserved Notation "C '=(' Np , X ')(' p ')=>s(' localRules ')' C'" (at level 60).
Inductive StreamingStep (localRules: Processor -> State -> list Action -> State -> Prop):
  Configuration -> SequenceNumbers -> Actions -> Fin.t countOfProcessors -> Configuration -> Prop :=
| s_step: forall Pi Sigma N M D p X Sigmap' Np' M',
  localRules (nth Pi p) (nth Sigma p) (X) (Sigmap') ->
  applyActions X (nth N p) M Np' M' ->
  (Pi, Sigma, N, M, D) =(nth N p, X)(p)=>s(localRules) (Pi, replace Sigma p Sigmap', replace N p Np', M', D)
where "C '=(' Np , X ')(' p ')=>s(' localRules ')' C'" := (StreamingStep localRules C Np X p C').

Reserved Notation "C '=(' p ')=>s(' localRules ')' C'" (at level 60).
Inductive StreamingAbsX (localRules: Processor -> State -> list Action -> State -> Prop):
  Configuration -> Fin.t countOfProcessors -> Configuration -> Prop :=
| s_absx: forall Pi Sigma N M D Pi' Sigma' N' M' D' Np X p,
  (Pi, Sigma, N, M, D) =(Np, X)(p)=>s(localRules) (Pi', Sigma', N', M', D') ->
  (Pi, Sigma, N, M, D)        =(p)=>s(localRules) (Pi', Sigma', N', M', D')
where "C '=(' p ')=>s(' localRules ')' C'" := (StreamingAbsX localRules C p C').

Reserved Notation "C '=>s(' localRules ')' C'" (at level 60).
Inductive StreamingAbsP (localRules: Processor -> State -> list Action -> State -> Prop):
  Configuration -> Configuration -> Prop :=
| s_absp: forall Pi Sigma N M D Pi' Sigma' N' M' D' p,
  (Pi, Sigma, N, M, D) =(p)=>s(localRules) (Pi', Sigma', N', M', D') ->
  (Pi, Sigma, N, M, D)     =>s(localRules) (Pi', Sigma', N', M', D')
where "C '=>s(' localRules ')' C'" := (StreamingAbsP localRules C C').

End Streaming.
