/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Functions in Lean.

In this sheet we'll learn how to manipulate the concepts of 
injectivity and surjectivity in Lean. 

The notation for functions is the usual one in mathematics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of all functions from `X` to `Y`, and `f : X → Y`
means that `f` is a term of type `X → Y`, i.e., a function
from `X` to `Y`.

One thing worth mentioning is that the simplest kind of function
evaluation, where you have `x : X` and `f : X → Y`, doesn't need
brackets: you can just write `f x` instead of `f(x)`. You only
need it when evaluating a function at a more complex object;
for example if we also had `g : Y → Z` then we can't write
`g f x` for `g(f(x))`, we have to write `g(f x)` otherwise
`g` would eat `f` and get confused. Without brackets,
a function just eats the next term greedily.

## The API we'll be using

Lean has the predicates `function.injective` and `function.surjective` on functions.
In other words, if `f : X → Y` is a function, then `function.injective f`
and `function.surjective f` are true-false statements. 

-/

-- Typing `function.` gets old quite quickly, so let's open the function namespace
open function

-- Now we can just write `injective f` and `surjective f`.

 -- Our functions will go between these sets, or Types as Lean calls them
variables (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.

theorem injective_def (f : X → Y) : 
  injective f ↔ ∀ (a b : X), f a = f b → a = b :=
begin
  refl, -- this proof works, because `injective f` 
       -- means ∀ a b, f a = f b → a = b *by definition*
       -- so the proof is "it's reflexivity of `↔`"
end

-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : 
  surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
begin
  refl,
end

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) :
  id x = x :=
begin
  refl,
end

-- Function composition is `∘` in Lean (find out how to type it by putting your cursor on it). 
-- The *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) :
  (g ∘ f) x = g (f x) :=
begin
  refl,
end

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.

example : injective (id : X → X) :=
begin
  -- you can start with `rw injective_def` if you like,
  -- and later you can `rw id_eval`, although remember that `rw` doesn't
  -- work under binders like `∀`, so use `intro` first.
  rw injective_def,
  intros a b,
  rw [id_eval, id_eval],
  intro h,
  exact h,

end

example : surjective (id : X → X) :=
begin
  rw surjective_def,
  intro y,
  use y,
  rw id_eval,
end

example (f : X → Y) (g : Y → Z) (hf : injective f) (hg : injective g) :
  injective (g ∘ f) :=
begin
  rw injective_def at hf,
  rw injective_def at hg,
  rw injective_def,
  intros a b,
  repeat {rw comp_eval},
  intro h,
  specialize hg (f a) (f b),
  have j := hg(h),
  specialize hf a b,
  have k := hf(j),
  exact k,
end

example (f : X → Y) (g : Y → Z) (hf : surjective f) (hg : surjective g) :
  surjective (g ∘ f) :=
begin
  rw surjective_def at hf, 
  rw surjective_def at hg,
  rw surjective_def,
  intro z,
  specialize hg z,
  cases hg with y hy,
  specialize hf y,
  cases hf with x hx,
  rw ← hx at hy,
  use x,
  rw comp_eval,
  exact hy,
  
end

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet
example (f : X → Y) (g : Y → Z) : 
  injective (g ∘ f) → injective f :=
begin
  intro h,
  rw injective_def at h,
  rw injective_def,
  intros a b,
  intro j,
  specialize h a b,
  repeat {rw comp_eval at h},
  rw j at h,
  apply h,
  refl,
end

-- This is another one
example (f : X → Y) (g : Y → Z) : 
  surjective (g ∘ f) → surjective g :=
begin
  intro h,
  rw surjective_def at h,
  rw surjective_def,
  intro z,
  specialize h z,
  cases h with x hx,
  rw comp_eval at hx,
  use f x,
  exact hx,
end
