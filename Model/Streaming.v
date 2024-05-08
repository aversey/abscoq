From Coq Require Import List Vector String.
Import ListNotations.

Section Streaming.

Class SParameters: Type :=
  { SCountOfProcessors: nat
  ; SProcessor: Type
  ; SState: Type
  ; SMessageData: Type
  ; SAuxiliaryData: Type }.
Context { sParametersContext: SParameters }.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Syntax *)

(* Basic Definitions *)

(* Processor ID *)
Implicit Types (p q: Fin.t SCountOfProcessors).

(* Stream Name *)
Implicit Types (s o r t: string).

(* Sequence Number or Length of Sequence *)
Implicit Types (n: nat).

(* Sequence Index *)
Implicit Types (i j: nat).

(* Processor *)
Implicit Types (pi: SProcessor).

(* State *)
Implicit Types (sigma Sigmap: SState).

(* Message Data *)
Implicit Types (d: SMessageData).

(* Auxiliary Data *)
Implicit Types (D: SAuxiliaryData).

(* Compound Definitions *)

Definition Processors := Vector.t SProcessor SCountOfProcessors.
Implicit Types (Pi: Processors).

Definition States := Vector.t SState SCountOfProcessors.
Implicit Types (Sigma: States).

Definition Message: Type := nat * string * SMessageData.
Implicit Types (m: Message).
Definition Messages := list Message.
Implicit Types (M: Messages).

Definition SequenceNumbers: Type := list (string * nat).
Implicit Types (Np: SequenceNumbers).
Definition AllSequenceNumbers := Vector.t SequenceNumbers SCountOfProcessors.
Implicit Types (N: AllSequenceNumbers).

Inductive Action := produce s d | consume s d.
Notation "`+" := produce (at level 1).
Notation "`-" := consume (at level 1).
Implicit Types (x: Action).
Definition Actions := list Action.
Implicit Types (X: Actions).

(* The Configuration *)

Definition Configuration: Type := Processors * States * AllSequenceNumbers * Messages * SAuxiliaryData.
Implicit Types (c: Configuration).

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Action Application *)

Definition mapOption {A B} (f: A -> B) (o: option A): option B :=
match o with
| Some a => Some (f a)
| None => None
end.
Definition getNp Np s := mapOption snd (List.find (fun np => String.eqb s (fst np)) Np).
Fixpoint replaceNp Np s n := match Np with
| [] => [(s, n)]
| np :: Np' => if String.eqb s (fst np) then (s, n) :: Np' else np :: replaceNp Np' s n
end.
Inductive applyActions: Actions -> SequenceNumbers -> Messages -> SequenceNumbers -> Messages -> Prop :=
| apply_produce : forall s d Np M Np' M' nps,
  Some nps = getNp Np s ->
  applyActions [`+ s d] Np M (replaceNp Np s (nps + 1)) ((nps, s, d) :: M')
| apply_consume : forall s d Np M Np' M' nps,
  Some nps = getNp Np s ->
  List.In (nps, s, d) M ->
  applyActions [`- s d] Np M (replaceNp Np s (nps + 1)) M
| apply_more : forall x X Np M Np' M' Np'' M'',
  applyActions [x] Np M Np' M' ->
  applyActions X Np' M' Np'' M'' ->
  applyActions (x :: X) Np M Np'' M''
| apply_empty : forall Np M, applyActions [] Np M Np M.

(* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *)
(* Semantics *)

Reserved Notation "c '=(' Np , X ')(' p ')=>s(' localRules ')' c'" (at level 60).
Inductive StreamingStep (localRules: SProcessor -> SState -> list Action -> SState -> Prop):
  Configuration -> SequenceNumbers -> Actions -> Fin.t SCountOfProcessors -> Configuration -> Prop :=
| s_step: forall Pi Sigma N M D p X Sigmap' Np' M',
  localRules (nth Pi p) (nth Sigma p) (X) (Sigmap') ->
  applyActions X (nth N p) M Np' M' ->
  (Pi, Sigma, N, M, D) =(nth N p, X)(p)=>s(localRules) (Pi, replace Sigma p Sigmap', replace N p Np', M', D)
where "c '=(' Np , X ')(' p ')=>s(' localRules ')' c'" := (StreamingStep localRules c Np X p c').

Reserved Notation "c '=(' p ')=>s(' localRules ')' c'" (at level 60).
Inductive StreamingAbsX (localRules: SProcessor -> SState -> list Action -> SState -> Prop):
  Configuration -> Fin.t SCountOfProcessors -> Configuration -> Prop :=
| s_absx: forall Pi Sigma N M D Pi' Sigma' N' M' D' Np X p,
  (Pi, Sigma, N, M, D) =(Np, X)(p)=>s(localRules) (Pi', Sigma', N', M', D') ->
  (Pi, Sigma, N, M, D)        =(p)=>s(localRules) (Pi', Sigma', N', M', D')
where "c '=(' p ')=>s(' localRules ')' c'" := (StreamingAbsX localRules c p c').

Reserved Notation "c '=>s(' localRules ')' c'" (at level 60).
Inductive StreamingAbsP (localRules: SProcessor -> SState -> list Action -> SState -> Prop):
  Configuration -> Configuration -> Prop :=
| s_absp: forall Pi Sigma N M D Pi' Sigma' N' M' D' p,
  (Pi, Sigma, N, M, D) =(p)=>s(localRules) (Pi', Sigma', N', M', D') ->
  (Pi, Sigma, N, M, D)     =>s(localRules) (Pi', Sigma', N', M', D')
where "c '=>s(' localRules ')' c'" := (StreamingAbsP localRules c c').

End Streaming.

Module StreamingNotations.

Notation "`+" := produce (at level 1).
Notation "`-" := consume (at level 1).
Notation "c '=(' Np , X ')(' p ')=>s(' localRules ')' c'" := (StreamingStep localRules c Np X p c') (at level 60).
Notation "c '=(' p ')=>s(' localRules ')' c'" := (StreamingAbsX localRules c p c') (at level 60).
Notation "c '=>s(' localRules ')' c'" := (StreamingAbsP localRules c c') (at level 60).

End StreamingNotations.