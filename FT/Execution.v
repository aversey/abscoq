From Coq Require Import List.
Import ListNotations.

Definition ruleset (config: Type) := config -> config -> Prop.

Definition executionStep {config: Type} (R: ruleset config) C C' := R C C'.
Notation "R |- C '=>' C'" := (executionStep R C C') (at level 60).

(** C is an execution in R *)
Fixpoint execution {config: Type} C (R: ruleset config): Prop :=
match C  with [] => True | c  :: C' =>
match C' with [] => True | c' :: _  =>
  R |- c => c' /\ execution C' R
end end.