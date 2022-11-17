/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# Important : the definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes.

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : ¬ true → false :=
begin
  intro h,
  apply h,
  triv,
end

example : false → ¬ true :=
begin
  intro h,
  intro h_1,
  exact h,
end

example : ¬ false → true :=
begin
  intro h_0,
  triv,
end

example : true → ¬ false :=
begin
  intro h,
  intro h_1,
  exact h_1,
end

example : false → ¬ P :=
begin
  triv,
end

example : P → ¬ P → false :=
begin
  intro p,
  intro h_1,
  apply h_1,
  exact p,
end

example : P → ¬ (¬ P) :=
begin
  intro p,
  intro h_0,
  apply h_0,
  exact p,
  
end

example : (P → Q) → (¬ Q → ¬ P) :=
begin
  intro pq,
  intro h_0,
  intro p,
  have q := pq(p),
  triv,
end

example : ¬ ¬ false → false :=
begin
  intro h_0,
  by_contra h_0,
  triv,
end

example : ¬ ¬ P → P :=
begin
  intro h_0,
  by_contra h_0,
  triv,
end

example : (¬ Q → ¬ P) → (P → Q) :=
begin
  intro h,
  change ( Q → false ) → ( P → false ) at h,
  intro hP,
  by_contra hnQ,
  have h_1 := h(hnQ),
  have h_2 := h_1(hP),
  exact h_2,

end