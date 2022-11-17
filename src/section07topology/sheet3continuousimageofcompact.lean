/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets

/-!

# Topology : continuous image of compact is compact

Useful API for this proof:

* `continuous.is_open_preimage` : preimage of open under continuous map is open


-/

-- let X & Y be topological spaces
variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 

-- If f is continuous and S is compact, then the image f(S) is also compact.
theorem continuous_image_of_compact_compact (hf : continuous f) (hS : is_compact S) : is_compact (f '' S) :=
begin
  -- Figure out the maths proof first, and then see if you can 
  -- formalise it in Lean.

  -- since f is continuous, f⁻¹(Uᵢ) open in X. ⋃ f⁻¹ (Uᵢ) is cover of X. Since S is compact, we can cover S
  --  with a finite union of f⁻¹(Uᵢ). Then there is a finite subcover of Y given by union of Uᵢ  

  rw is_compact_iff_finite_subcover at hS ⊢, -- might be a good first line
  intros ι U hι hfS,

  have k : (∀ i : ι, is_open (f⁻¹' (U i))),
  { intro i,
  specialize hι i,
  exact continuous_def.mp hf (U i) hι,},
  
  have l : (S ⊆ ⋃ (i : ι), f⁻¹'(U i)),
  {intros x hx,
  simp [set.mem_bUnion],
  have j : f(x) ∈ f '' S,
  exact set.mem_image_of_mem f hx,
  specialize hfS (j),
  exact set.mem_Union.mp hfS,},

  finish,
  
end

lemma close_subspace_compact ( Y : set X) :
is_compact (set.univ : set X) ∧ is_closed Y → is_compact Y :=
begin
  rintros ⟨h1, h2⟩,
  rw is_compact_univ_iff at h1,
  rw is_compact_iff_finite_subcover,
  intro l,
  intro f,
  intro hf,
  intro hy,
end

#print continuous_image_of_compact_compact