/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Making ℤ from ℕ²

You can define `ℤ` as ℕ² / ≈, where (a,b) ≈ (c,d) ↔ a + d = b + c.
This sheet goes through this (definition, commutative ring structure) with very few hints.
All the techniques are things we've seen in the earlier sheets.

Hint: if the tactic state is

h : a + d = b + c
⊢ c + b = d + a

you can close the goal with `linarith`. If things get nonlinear (multiplication,
I'm looking at you), there's always `nlinarith`.

-/

/-

# Warm-up: how products work in Lean

-/

-- constructor for ℕ × ℕ 

example : ℕ × ℕ := (3,4)

-- eliminators

def foo : ℕ × ℕ := (37, 53)

example : foo.1 = 37 := 
begin
  refl,
end

example : foo.2 = 53 := 
begin
  refl
end

-- warning : constructor on eliminators isn't refl
example (a : ℕ × ℕ) : a = (a.1, a.2) :=
begin
  -- refl fails
  cases a with x y, -- a term of type ℕ × ℕ is a pair; `cases` takes it apart.
  -- now refl works
  refl,
end

def R (ab cd : ℕ × ℕ) : Prop :=
ab.1 + cd.2 = ab.2 + cd.1

lemma R_def (ab cd : ℕ × ℕ) :
R ab cd ↔ ab.1 + cd.2 = ab.2 + cd.1 := 
begin
  split, {
    intro h,
    cases ab with a b,
    cases cd with c d,
    simp,
    rw R at h,
    simp at h,
    exact h,
  }, {
    cases ab with a b,
    cases cd with c d,
    intro h,
    simp * at *,
    rw R,
    simp,
    assumption,
  }
end

lemma R_def' (a b c d : ℕ) :
R (a, b) (c, d) ↔ a + d = b + c :=
begin
  split, {
    intro h,
    rw R at h,
    exact h,
  }, {
    intro h,
    rw R,
    exact h,
  }
end 


lemma R_refl : reflexive R :=
begin
  unfold reflexive,
  rintros ⟨x,y⟩,
  rw R,
  simp [add_comm],
end

lemma R_symm : symmetric R :=
begin
  unfold symmetric,
  rintros ⟨x,y⟩ ⟨w,z⟩,
  intro h,
  rw R at *,
  simp [*, add_comm],
end

lemma R_trans : transitive R :=
begin
  unfold transitive,
  rintros ⟨x1, x2⟩ ⟨y1,y2⟩ ⟨z1, z2⟩,
  intros h j,
  simp [*, R] at *,
  linarith,
end

instance s : setoid (ℕ × ℕ) :=
{ r := R,
  iseqv := ⟨R_refl, R_symm, R_trans⟩ }

@[simp] lemma equiv_def (a b c d : ℕ) :
  (a, b) ≈ (c, d) ↔ a + d = b + c :=
begin
  refl,
end

notation `myint` := quotient s

-- Amusingly, we can't now make a myint namespace unless
-- we do some weird quote thing (Lean unfolds the notation otherwise)
namespace «myint»

instance : has_zero myint :=
{ zero := ⟦(0,0)⟧ }

@[simp] lemma zero_def : (0 : myint) = ⟦(0, 0)⟧ :=
begin
  refl,
end

def neg : myint → myint :=
quotient.map (λ ab, (ab.2, ab.1)) begin
  rintros ⟨a1, a2⟩ ⟨b1, b2⟩,
  intro h,
  simp,
  rw equiv_def at h,
  exact h.symm,
end

instance : has_neg myint :=
{ neg := neg }

@[simp] lemma neg_def (a b : ℕ) : 
  -⟦(a, b)⟧ = ⟦(b, a)⟧ :=
begin
  refl,
end

def add : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 + cd.1, ab.2 + cd.2)) begin
  rintros ⟨a, b⟩ ⟨c, d⟩,
  intro h,
  rintros ⟨e,f⟩ ⟨g,k⟩,
  intro l,
  simp [equiv_def, *, add_assoc] at *,
  linarith,
end

instance : has_add myint :=
{ add := add }

@[simp] lemma add_def (a b c d : ℕ) :
  ⟦(a, b)⟧ + ⟦(c, d)⟧ = ⟦(a + c, b + d)⟧ :=
begin
  refl,
end

instance add_comm_group : add_comm_group myint :=
{ add := (+),
  add_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    rintros ⟨a1, a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩,
    simp,
    linarith,
    
  end,
  zero := 0,
  zero_add := begin
    intro a,
    apply quotient.induction_on a,
    rintros ⟨a1, a2⟩,
    simp,
    linarith,
  end,
  add_zero := begin
    intro a,
    apply quotient.induction_on a,
    rintros ⟨ a1, a2⟩,
    simp,
    linarith,
  end,
  neg := has_neg.neg,
  add_left_neg := begin
    intro a,
    apply quotient.induction_on a,
    rintro ⟨ a1, a2 ⟩,
    simp,
    linarith,
    
  end,
  add_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b,
    rintro ⟨ a1, a2 ⟩ ⟨ b1, b2⟩,
    simp,
    linarith,
  end }

-- our model is that the equivalence class ⟦(a, b)⟧
-- represents the integer a - b
instance : has_one myint :=
{ one := ⟦(1, 0)⟧}

@[simp] lemma one_def : (1 : myint) = ⟦(1, 0)⟧ :=
begin
  refl,
end

-- (a-b)*(c-d)=(ac+bd)-(ad+bc)
def mul : myint → myint → myint :=
quotient.map₂ (λ ab cd, (ab.1 * cd.1 + ab.2 * cd.2, ab.1 * cd.2 + ab.2 * cd.1)) begin
  rintros ⟨a, b⟩ ⟨c,d⟩ k ⟨e, f⟩ ⟨g, h⟩ l,
  simp,
  rw equiv_def at *,
  nlinarith!,
end

instance : has_mul myint :=
{ mul := mul }

@[simp] lemma mul_def (a b c d : ℕ) :
  ⟦(a, b)⟧ * ⟦(c, d)⟧ = ⟦(a * c + b * d, a * d + b * c)⟧ :=
begin
  refl,
end

instance : comm_ring myint :=
{ add := (+),
  zero := 0,
  mul := (*),
  mul_assoc := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    rintros ⟨a1,a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩,
    simp,
    nlinarith,
  end,
  one := 1,
  one_mul := begin
    intro a,
    apply quotient.induction_on a,
    rintros ⟨a1,a2⟩,
    simp,
    nlinarith,
  end,
  mul_one := begin
    intro a,
    apply quotient.induction_on a,
    rintros ⟨a1,a2⟩,
    simp,
    nlinarith,
  end,
  left_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    rintros ⟨a1,a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩,
    simp,
    nlinarith,
  end,
  right_distrib := begin
    intros a b c,
    apply quotient.induction_on₃ a b c,
    rintros ⟨a1,a2⟩ ⟨b1, b2⟩ ⟨c1, c2⟩,
    simp,
    nlinarith,
  end,
  mul_comm := begin
    intros a b,
    apply quotient.induction_on₂ a b,
    rintros ⟨a1,a2⟩ ⟨b1, b2⟩,
    simp,
    nlinarith,
  end,
  ..myint.add_comm_group }

end «myint»

