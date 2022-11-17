/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 1 : ∪ ∩ ⊆ and all that

Lean doesn't have "abstract" sets, it only has *subsets* of a type. If `X : Type` is a type
then the type of subsets of `X` is called `set X`. A term `A : set X`
can be thought of in three ways:

1) A set of elements of `X` (i.e. a set of elements all of which have type `X`);
2) A subset of `X`;
3) An element of the power set of `X`;
4) A function from `X` to `Prop` (sending the elements of `A` to `true` and the other ones to `false`)

So `set X` could have been called `subset X` or `powerset X`; I guess they chose `set X`
because it was the shortest.

Note that `X` is a type, but `A` is a term; the type of `A` is `set X`. This means
that `a : A` doesn't make sense. What we say instead is `a : X` and `a ∈ A`. 
Of course `a ∈ A` is a true-false statement, so `a ∈ A : Prop`. 

All the sets `A`, `B`, `C` etc we consider will be subsets of `X`. 
If `x : X` then `x` may or may not be an element of `A`, `B`, `C`,
but it will always be a term of type `X`.

-/

-- set up variables
variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D : set X) -- A,B,C are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

/-

# subset (`⊆`), union (`∪`) and intersection (`∩`)

Here are some mathematical facts:

`A ⊆ B` is equivalent to `∀ x, x ∈ A → x ∈ B`;
`x ∈ A ∪ B` is equivalent to `x ∈ A ∨ x ∈ B`;
`x ∈ A ∩ B` is equivalent to `x ∈ A ∧ x ∈ B`. 

All of these things are true *by definition* in Lean. Let's
check this.

-/

lemma subset_def : A ⊆ B ↔ ∀ x, x ∈ A → x ∈ B :=
begin
  -- ↔ is reflexive so `refl` works because LHS is defined to be equal to RHS
  refl,
end

lemma mem_union_iff : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B :=
begin
  refl,
end

lemma mem_inter_iff : x ∈ A ∩ B ↔ x ∈ A ∧ x ∈ B :=
iff.rfl -- you don't even have to go into tactic mode to prove this

/-

So now to change one side of these `↔`s to the other, you can
`rw` the appropriate lemma, or you can just use `change`. Or
you can ask yourself whether you need to do this at all.

Let's prove some theorems.

-/

example : A ⊆ A :=
begin
  refl,
end

example : A ⊆ B → B ⊆ C → A ⊆ C :=
begin
  intro h,
  intro j,
  rw subset_def at h,
  rw subset_def at j,
  rw subset_def,
  intro x,
  specialize h x,
  specialize j x,
  intro k,
  apply j,
  apply h,
  exact k,
end

example : A ⊆ A ∪ B :=
begin
  rw subset_def,
  intro x,
  intro h,
  rw mem_union_iff,
  left,
  exact h,
end

example : A ∩ B ⊆ A :=
begin
  rw subset_def,
  intro x,
  intro h,
  rw mem_inter_iff at h,
  exact h.1,
end

example : A ⊆ B → A ⊆ C → A ⊆ (B ∩ C) :=
begin
  intro h,
  intro j,
  intro x,
  intro k,
  specialize j k,
  specialize h k,
  split,
  exact h,
  exact j,
end

example : B ⊆ A → C ⊆ A → B ∪ C ⊆ A :=
begin
  intro h,
  intro j,
  intro x,
  intro k,
  cases k,
  apply h,
  exact k,
  apply j,
  exact k,
end

example : A ⊆ B → C ⊆ D → A ∪ C ⊆ B ∪ D :=
begin
  intro h,
  intro j,
  intro x,
  intro k,
  cases k,
  specialize h k,
  left,
  exact h,
  specialize j k,
  right,
  exact j,
end

example : A ⊆ B → C ⊆ D → A ∩ C ⊆ B ∩ D :=
begin
  intro h,
  intro j,
  intro x,
  intro k,
  split,
  apply h,
  exact k.1,
  apply j,
  exact k.2,
end