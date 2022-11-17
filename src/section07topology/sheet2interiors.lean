/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
-- the next import will be enough for this sheet
import topology.basic

/-!

# Topology : making the API for `interior`.

(I'll assume you know the mathematics behind the interior of a subset of a topological space
in this sheet). 

The way to make a type `X` into a topological space is to 
tell the type class inference system that you'd like it to
keep track of a topological space structure on `X`. So it's

`variables (X : Type) [topological_space X]`

Lean has interiors of topological spaces, but let's
make our own, as warm-up.

-/

-- Here's the notation we'll use in this sheet
variables {X : Type} [topological_space X] (S : set X)

/-

## The API for topological spaces

`is_open S : Prop` is the predicate that `S : set X` is open.

Now here's some standard facts from topology. I'll tell you the names
of the proofs, you can guess what they're proofs of
(and then check with `#check`, which tells you the type of a term, so
if you give it a theorem proof it will tell you the theorem statement). 
-/
#check is_open_univ
#check is_open_Union -- is_open_bUnion, is_open_sUnion --(note the capital U)
#check is_open.inter --(note the small i) (and the dot to enable dot notation)
/-
-/

/-

## Interiors

Lean has interior of a set, but let's make them ourselves
because it's a nice exercise.

-/

-- Got to call it `interior'` with a dash, because Lean already has `interior`
-- The following would work for the definition -- a "bUnion".
def interior' (S : set X) : set X := ⋃ (U ∈ {V : set X | is_open V ∧ V ⊆ S}), U

-- useful for rewrites; saves you having to unfold `interior'` (a good Lean
-- proof should never use `unfold` unless you're making API).
lemma mem_interior' (x : X) : x ∈ interior' S ↔ ∃ (U : set X) (hU : is_open U) (hUS : U ⊆ S), x ∈ U :=
begin
  unfold interior',
  rw set.mem_bUnion_iff,
  finish,
end



/-
Two alternative definitions: a Union of a Union, Union of a Union of a Union, or a sUnion.

-- Union of Union
def interior'' (S : set X) : set X := ⋃ (U : set X) (h : is_open U ∧ U ⊆ S), U

-- Union of Union of Union
def interior'' (S : set X) : set X := ⋃ (U : set X) (hU : is_open U) (hUS : U ⊆ S), U

-- sUnion
def interior''' (S : set X) : set X := ⋃₀ ({V : set X | is_open V ∧ V ⊆ S})

You can try one of those if you'd rather. Then in the above proof you might end up
rewriting set.mem_Union_iff or set.mem_sUnion_iff.
-/

-- Lean has `is_open_Union` and `is_open_bUnion` and `is_open_sUnion`.
-- Because our definition is a `bUnion`, we could start with `apply is_open_bUnion`,
-- the "correct form" of the assertion that an arbitrary 

lemma interior'_open : is_open (interior' S) := 
begin
  apply is_open_bUnion,
  intros i h,
  finish,
end

lemma interior'_subset : interior' S ⊆ S :=
begin
  rw set.subset_def,
  intros x hx,
  rw mem_interior' at hx,
  cases hx with u h,
  cases h with hU h,
  cases h with hUS x,
  exact hUS(x),
end

-- Lean can work out S from hUS so let's make S a {} input for this one

variable {S}

lemma subset_interior' {U : set X} (hU : is_open U) (hUS : U ⊆ S) : U ⊆ interior' S :=
begin
  intros x hx,
  simp [mem_interior' S],
  use U,
  exact ⟨hU, hUS, hx⟩,
end


-- Similarly here I put S and T in squiggly brackets because Lean can figure them out
-- when it sees hST
lemma interior'_mono {S T : set X} (hST : S ⊆ T) : interior' S ⊆ interior' T :=
begin
  have j := interior'_subset(S),
  intros x hx,
  simp [mem_interior'],
  use interior' S,
  have hi : interior' S ⊆ T,
  intros y hy, 
  exact hST(j(hy)),
  exact ⟨interior'_open S, hi, hx⟩,

end

-- instead of starting this with `ext`, you could `apply set.subset.antisymm`,
-- which is the statement that if S ⊆ T and T ⊆ S then S = T.
lemma interior'_interior' : interior' (interior' S) = interior' S :=
begin
  apply set.subset.antisymm, {
    exact interior'_subset (interior' S),
  }, {
    intros x hx,
    rw mem_interior' at *,
    cases hx with U hx,
    cases hx with hU hx,
    cases hx with hUS hx,
    use U,
    split, exact hU,
    use subset_interior' hU hUS,
    exact hx,

  }
end

-- Some examples of interiors
lemma interior'_empty : interior' (∅ : set X) = ∅ :=
begin
  apply set.subset.antisymm, {
    intros x hx,
    rw set.mem_empty_eq,
    rw mem_interior' at hx,
    cases hx with m hm, cases hm with w hw, cases hw with y hy,
    specialize y(hy),
    cases y,
  }, {
    intros x hx,
    cases hx,
  }
end

lemma interior'_univ : interior' (set.univ : set X) = set.univ :=
begin
  ext,
  split, {
    intro h,
    triv,
  }, {
    intro h,
    rw mem_interior',
    use set.univ,
    split, {
      exact is_open_univ,
    }, {
      finish,
    }
  }
end

lemma interior'_inter (S T : set X) : interior' (S ∩ T) = interior' S ∩ interior' T :=
begin
  ext,
  split, {
    intro hx,
    rw mem_interior' at hx,
    cases hx with U hUS,
    cases hUS with hU hUS,
    cases hUS with hU2 hx,
    split, {
      rw mem_interior',
      finish,
    }, {
      rw mem_interior',
      finish,
    }
  }, {
    intro hx,
    rw mem_interior' at *,
    cases hx with hs ht,
    rw mem_interior' at *,
    cases hs with U hUS,
    cases ht with V hVS,
    cases hUS with hU hU2,
    cases hVS with hV hV2,
    cases hU2 with hut hxu,
    cases hV2 with hvt hxv,
    use U ∩ V,
    split, {
      exact is_open.inter hU hV,
    }, {
      norm_num,
      split, {
        split, {
          intro y,
          intro hy,
          exact hut (hy.1),
        }, {
          intros y hy,
          exact hvt (hy.2),
        }
      }, {
        finish,
      }
    }
  }
end
