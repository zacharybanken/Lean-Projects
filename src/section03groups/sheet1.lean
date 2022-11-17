/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Group theory in Lean

Lean has groups. But let's make our own anyway. In this sheet we will
learn about the `class` command, which is one of the ways to make
a theory of groups in Lean (and indeed the way it's done in `mathlib`)

We will also learn about `simp`, a tactic which does long series of
rewrites automatically. We'll even learn how to train it to solve a
certain kind of problem.

## Definition of a group

`group G` is already defined in `mathlib`, so let's define a new
type `mygroup G`. Here `G : Type` is a type, and `mygroup G` is the type of
group structures on `G`.

-/

/-- `mygroup G` is the type of group structures on the type `G`. -/
class mygroup (G : Type)
  extends has_one G, has_mul G, has_inv G : Type :=
(mul_assoc : ∀ a b c : G, (a * b) * c = a * (b * c))
(one_mul : ∀ a : G, 1 * a = a)
(mul_one : ∀ a : G, a * 1 = a)
(inv_mul_self : ∀ a : G, a⁻¹ * a = 1)
(mul_inv_self : ∀ a : G, a * a⁻¹ = 1)

/-

Right now the axioms are called `mygroup.mul_assoc`, `mygroup.one_mul` etc.
Furthermore we want to build some lemmas called things like `mygroup.one_inv`
and stuff. The fix? Let's move into the `mygroup` namespace, where they're
just caled `mul_assoc`, `one_inv` etc.

-/

namespace mygroup

-- tag all the axioms for groups with the `@[simp]` attribute.
-- Note that we can drop the `mygroup` prefix now as we're in the namespace.

attribute [simp] mul_assoc one_mul mul_one inv_mul_self mul_inv_self 

-- Throughout our work in this namespace, let `G` be a group and let
-- `a`, `b` and `c` be elements of `G`.
variables {G : Type} [mygroup G] (a b c : G)

/-

Five of the next seven lemmas are tagged with `@[simp]` as well.
See if you can prove all seven using (for the most part) the `rw` tactic.

-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b :=
begin
  rw ← mul_assoc,
  rw inv_mul_self,
  rw one_mul,
end

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b :=
begin
  rw ← mul_assoc,
  rw mul_inv_self,
  rw one_mul,

end

lemma left_inv_eq_right_inv {a b c : G} (h1 : b * a = 1) (h2 : a * c = 1) : 
  b = c :=
begin
  -- hint for this one : establish the auxiliary fact
  -- that `b * (a * c) = (b * a) * c` with the `have` tactic.
  have j : b * (a * c) = (b * a) * c, {
    rw mul_assoc,
  }, {
    rw h2 at j,
    rw h1 at j,
    rw one_mul at j,
    rw mul_one at j,
    exact j,
  }
end

lemma mul_eq_one_iff_eq_inv : a * b = 1 ↔ a⁻¹ = b :=
begin
  split, {
    intro h,
    have j : a⁻¹ * a * b = a⁻¹, {
      rw mul_assoc,
      rw h,
      rw mul_one,
    }, {
      rw inv_mul_self at j,
      rw one_mul at j,
      symmetry,
      exact j,
    },
  }, {
    intro h,
    have j : a * a⁻¹ *  b = a⁻¹, {
      rw mul_inv_self,
      rw one_mul,
      symmetry,
      exact h,
    }, {
      rw mul_inv_self at j,
      rw one_mul at j,
      rw j,
      rw mul_inv_self,
    }
  }
end

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  have j : 1 * 1 = 1, {
    ring,
  }, {
    have k :  (1 : G)⁻¹ * 1 = 1, {
        rw inv_mul_self,
    }, 
    rw mul_one at k,
    exact k,
  }
end

@[simp] lemma inv_inv : (a⁻¹)⁻¹ = a :=
begin
  have j : (a⁻¹)⁻¹ * a⁻¹ = a * (a⁻¹), {
    rw inv_mul_self,
    rw mul_inv_self,
  },
  have k : (a⁻¹)⁻¹ * a⁻¹ * a = a * (a⁻¹) * a, {
    rw j,
  },
  rw mul_assoc at k,
  rw mul_assoc at k,
  repeat {rw inv_mul_self at k},
  repeat {rw mul_one at k},
  exact k,
end

@[simp] lemma mul_inv_rev : (a * b)⁻¹ = b⁻¹ * a⁻¹ := 
begin
  have j : (a * b)⁻¹ * (a * b) = 1, {
    rw inv_mul_self (a * b),
  }, 
  have k : (a * b)⁻¹ * (a * b) = b⁻¹ * a⁻¹ * (a * b), {
    rw j,
    rw mul_assoc,
    rw ← mul_assoc a⁻¹ a b,
    rw inv_mul_self,
    rw one_mul,
    rw inv_mul_self,
  }
end

/-

Remember the `ring` tactic which didn't look at hypotheses but which could
prove hypothesis-free identities in commutative rings? A theorem of Knuth
and Bendix says that we have just trained Lean's simplifier to prove
arbitrary true hypothesis-free identities in groups; those ten lemmas
we tagged with `@[simp]` are all you need. We've made a Noetherian
confluent rewrite system for group theory!

-/
-- example of Knuth-Bendix theorem
example (G : Type) [mygroup G] (a b : G) : 
  (b⁻¹ * a⁻¹)⁻¹ * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp

-- bonus puzzle : if g^2=1 for all g in G, then G is abelian
example (G : Type) [mygroup G] (h : ∀ g : G, g * g = 1) :
  ∀ g h : G, g * h = h * g :=
begin
  intro g,
  intro k,
  
  have h2 : ∀ g : G, g * g = 1 := by exact h,
  have h4 : ∀ g : G, g * g = 1 := by exact h,
  have h5 : ∀ g : G, g * g = 1 := by exact h,
  have h6 : ∀ g : G, g * g = 1 := by exact h,

  specialize h (g * k),
  specialize h6 (g * k),
  specialize h2 (k * g),
  specialize h4 g,
  specialize h5 k,

  rw ← h2 at h,
  have h3 : g * k * (g * k) * (g * k) = k * g * (k * g) * (g * k), {
    rw h,
  },
  rw mul_assoc (k * g)  (k * g)  (g * k) at h3,
  rw mul_assoc k  g  (g * k) at h3,
  rw ← mul_assoc g g k at h3,
  rw h4 at h3,
  rw one_mul at h3,
  rw h5 at h3,
  rw mul_one at h3,
  rw h6 at h3,
  rw one_mul at h3,
  exact h3,
  
end

end mygroup
