/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.

variables (P Q R : Prop)

example : P ∧ Q → P :=
begin
  intro h,
  exact h.left, 


end

example : P ∧ Q → Q :=
begin
  intro h,
  exact h.right,
end

example : (P → Q → R) → (P ∧ Q → R) :=
begin
  intro h,
  intro h_1,
  have h_2 := h(h_1.left),
  apply h_2,
  exact h_1.right,
end

example : P → Q → P ∧ Q :=
begin
  intro hp,
  intro hq,
  split,
  { exact hp,},
  { exact hq,}
end

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P :=
begin
  intro h,
  split,
  exact h.right,
  exact h.left,
end

example : P → P ∧ true :=
begin
  intro h,
  split,
  exact h,
  triv,
end

example : false → P ∧ false :=
begin
  triv,
end

/-- `∧` is transitive -/
example : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  intro h,
  intro h_1,
  split,
  exact h.left,
  exact h_1.right,
end

example : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intro h,
  intro hp,
  intro hq,
  apply h,
  split,
  exact hp,
  exact hq,
end



