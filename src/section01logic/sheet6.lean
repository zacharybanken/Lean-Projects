/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/

-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.

variables (P Q R S : Prop)

example : P → P ∨ Q :=
begin
  intro p,
  left,
  exact p,
end

example : Q → P ∨ Q :=
begin
  intro h,
  right,
  exact h,
end

example : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros h0 h1 h2,
  cases h0 with p q,
 
  {exact h1 p,},

  {exact h2 q,}


end

-- symmetry of `or`
example : P ∨ Q → Q ∨ P :=
begin
  intro h,
  cases h with p q,
  right,
  exact p,
  left,
  exact q,
end

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  intro h,
  cases h with hpq hr,
  cases hpq with hp hq,
  left,
  exact hp,
  right,
  left,
  exact hq,
  right,
  right,
  exact hr,
  intro h,
  cases h with hp hqr,
  left, left,
  exact hp,
  cases hqr with hq hr,
  left, right,
  exact hq,
  right,
  exact hr,

end

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  intros hpr hqs hpq,
  cases hpq,
  left,
  apply hpr,
  exact hpq,
  right,
  apply hqs,
  exact hpq,
end

example : (P → Q) → P ∨ R → Q ∨ R :=
begin
  intros hpq hpr,
  cases hpr,
  left,
  apply hpq,
  exact hpr,
  right,
  exact hpr,
end

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  intros hpr hqs,
  split,
  intro hpq,
  cases hpq,
  left,
  apply hpr.1,
  exact hpq,
  right,
  apply hqs.1,
  exact hpq,
  intro hrs,
  cases hrs with r s,
  left,
  exact hpr.2(r),
  right,
  exact hqs.2(s),

end

-- de Morgan's laws
example : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
begin
  -- split,
  -- intro hnpq,
  -- split,
  -- intro p,
  -- apply hnpq,
  -- left,
  -- exact p,
  -- intro q,
  -- apply hnpq,
  -- right,
  -- exact q,
  -- intro hpaq,
  -- intro hpoq,
  -- cases hpoq with p q,
  -- have h := hpaq.1,
  -- apply h,
  -- exact p,
  -- have h := hpaq.2,
  -- triv,

  
end

example : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
begin
  split, {
    intro j,
    by_cases P,
    right,
    intro q,
    apply j,
    split, {
      exact h,
    }, {
      exact q,
    },

    left,
    exact h,
  }, {
    intro h,
    intro j,
    cases h with np nq, {
      apply np,
      exact j.1,
    }, {
      apply nq,
      exact j.2,
    }, 
  }


end
--open classical
example : ¬ (P ∧ Q) → ¬ P ∨ ¬ Q :=
(λ h, 
or.elim (classical.em P)
(λ hp, or.inr(λ (hq : Q), h(⟨hp,hq⟩)))
(λ hnp, or.inl hnp))

