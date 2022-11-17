/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/

variables (P Q R S : Prop)

example : P ↔ P :=
begin
  refl,
end

example : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  split,
  intro hq,
  have p := h.2(hq),
  exact p,
  intro hp,
  apply h.1,
  exact hp,

end

example : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  intro h,
  split,
  intro hq,
  apply h.2,
  exact hq,
  intro hp,
  apply h.1,
  exact hp,
  tauto!,


end

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intro hpq,
  intro hqr,
  split,
  intro hp,
  apply hqr.1,
  apply hpq.1,
  exact hp,
  intro hr,
  exact hpq.2(hqr.2(hr)),


end

example : P ∧ Q ↔ Q ∧ P :=
begin
  split,
  intro hpq,
  split,
  exact hpq.right,
  exact hpq.left,
  intro hqp,
  split,
  exact hqp.right,
  exact hqp.left,

end

example : ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  intro h,
  split,
  exact h.left.left,
  split,
  exact h.left.right,
  exact h.right,
  intro h,
  split,
  split,
  exact h.left,
  exact h.right.left,
  exact h.right.right,

end

example : P ↔ (P ∧ true) :=
begin
  split,
  intro hp,
  split,
  exact hp,
  triv,
  intro h,
  exact h.left,
end

example : false ↔ (P ∧ false) :=
begin
  split,
  intro hf,
  split,
  exfalso, 
  exact hf,
  exact hf,
  intro hpf,
  exact hpf.right,
end

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
begin
  intro hpq,
  intro hrs,
  split,
  intro hpr,
  split,
  exact hpq.1(hpr.left),
  exact hrs.1(hpr.right),
  intro hqs,
  split,
  tauto!,
  tauto!,

end

example : ¬ (P ↔ ¬ P) :=
begin
  intro h,
  cases h with f b,
  by_cases P,
  have h_1 := f(h),
  apply h_1,
  exact h,

  apply h,


  

end
