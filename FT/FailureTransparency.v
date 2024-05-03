From Coq Require Import List.
From FT Require Import Execution ObservationalExplainability.

Definition failureTransparency {config: Type} {observation: Type}
  (R: ruleset config) (O: config -> observation) (K: config -> Prop) (F: ruleset config) :=
  R `[O]\=(fun c c' => (c = c' /\ K c))=\[O] (fun c c' => (R c c' /\ ~F c c')).
Notation "R \\ O K F" := (failureTransparency R O K F) (at level 50).
