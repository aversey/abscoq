From Coq Require Import List.
From FT Require Import Execution.

Definition observationalExplanation {config: Type} {config': Type} {observation: Type}
  (C: list config) (O: config -> observation)
  (O': config' -> observation) (C': list config') :=
  forall n' Cn', nth_error C n' = Some Cn' ->
  exists m' C'm', nth_error C' m' = Some C'm' /\
  O Cn' = O' C'm'.
Notation "C `[ O ]\=\[ O' ] C'" := (observationalExplanation C O O' C') (at level 50).

Definition observationalExplainability {config: Type} {config': Type} {observation: Type}
  (R: ruleset config) (O: config -> observation)
  (T: config' -> config -> Prop)
  (O': config' -> observation) (R': ruleset config') :=
  forall c c', T c' c ->
  forall C, execution C R /\ (hd c C) = c ->
  exists C', execution C' R' /\ (hd c' C') = c' /\
  C `[O]\=\[O'] C'.
Notation "R `[ O ]\= T =\[ O' ] R'" := (observationalExplainability R O T O' R') (at level 50).

Lemma ReflexivityOfObservationalExplainability {config: Type} {observation: Type}:
  forall R: ruleset config, forall O: config -> observation,
  R `[O]\=eq=\[O] R.
Admitted. (* TODO *)

Definition compose {A B C: Type} (T': C -> B -> Prop) (T: B -> A -> Prop) :=
  fun c a => exists b, T' c b /\ T b a.
Lemma TransitivityOfObservationalExplainability
  {config: Type} {config': Type} {config'': Type} {observation: Type}:
  forall R: ruleset config, forall O: config -> observation,
  forall T: config' -> config -> Prop,
  forall O': config' -> observation, forall R': ruleset config',
  forall T': config'' -> config' -> Prop,
  forall O'': config'' -> observation, forall R'': ruleset config'',
  R `[O]\=T=\[O'] R' /\ R' `[O']\=T'=\[O''] R'' -> R `[O]\=(compose T' T)=\[O''] R''.
Admitted. (* TODO *)

Definition composeFn {A B C: Type} (f: B -> C) (g: A -> B) := fun c => f (g c).
Lemma CompositionOfObservabilities
  {config: Type} {config': Type} {observation: Type} {observation': Type}:
  forall R: ruleset config, forall O: config -> observation,
  forall T: config' -> config -> Prop,
  forall O': config' -> observation, forall R': ruleset config',
  forall O'': observation -> observation',
  R `[O]\=T=\[O'] R' -> R `[composeFn O'' O]\=T=\[composeFn O'' O'] R'.
Admitted. (* TODO *)