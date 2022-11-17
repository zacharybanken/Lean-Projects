/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/

open set

variables
  (X : Type) -- Everything will be a subset of `X`
  (A B C D E : set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : A ∪ A = A :=
begin
  ext,
  split, {
    intro h,
    cases h, {
      exact h,
    }, {
      exact h,
    },
  }, {
    intro h,
    left,
    exact h,
  }
end

example : A ∩ A = A :=
begin
  ext,
  split, {
    intro h,
    use h.1,
  }, {
    intro h,
    split, {
      exact h,
    }, {
      exact h,
    }

  }
end

example : A ∩ ∅ = ∅ :=
begin
  ext,
  split, {
    intro h,
    exact h.2,
  }, {
    intro h,
    cases h,
  }
end

example : A ∪ univ = univ :=
begin
  ext,
  split, {
    intro h,
    cases h,
    triv,
    exact h,
  }, {
    intro h,
    right,
    exact h,
  }
end

example : A ⊆ B → B ⊆ A → A = B :=
begin
  intro h,
  intro j,
  ext,
  split, {
    intro k,
    specialize h k,
    exact h,
  }, {
    intro k,
    specialize j k,
    exact j,
  }
end

example : A ∩ B = B ∩ A :=
begin
  ext,
  split, {
    intro h,
    split, {
      exact h.2,
    }, {
      exact h.1,
    },
  }, {
    intro h,
    split, {
      exact h.2,
    }, {
      exact h.1,
    }
  }
end

example : A ∩ (B ∩ C) = (A ∩ B) ∩ C :=
begin
  ext, 
  split, {
    intro h,
    split, {
      split, {
        use h.1,
      }, {
        use h.2.1,
      }
    }, {
      use h.2.2,
    }
  }, {
    intro h,
    split, {
       use h.1.1,
    }, {
      split, {
        use h.1.2,
      }, {
        use h.2,
      }
    }
  }

  
  
end

example : A ∪ (B ∪ C) = (A ∪ B) ∪ C :=
begin
  ext,
  split, {
    intro h,
    cases h,
    left,
    left,
    exact h,
    cases h,
    left,
    right,
    exact h,
    right,
    exact h,
  }, {
    intro h,
    cases h,
    cases h,
    left,
    exact h,
    right,
    left,
    exact h,
    right,
    right,
    exact h,
  }
end

example : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) :=
begin
  ext,
  split, {
    intro h,
    cases h,
    split, {
      left,
      exact h,
    }, {
      left,
      exact h,
    }, {
      split, {
        right,
        exact h.1,
      }, {
        right,
        exact h.2,
      }
    }
  }, {
    intro h,
    have j := h.1,
    have k := h.2,
    cases j, {
      left,
      exact j,
    }, {
      cases k, {
        left,
        exact k,
      }, {
        right,
        split, {
          exact j,
        }, {
          exact k,
        }
      }
    }

  }
end

example : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) :=
begin
  ext, 
  split, {
    intro h,
    have j := h.1,
    have k := h.2,
    cases k, {
      left,
      split, {
        exact j,
      }, {
        exact k,
      }
    }, {
      right,
      split, {
        exact j,
      }, {
        exact k,
      }
    }
  }, {
    intro h,
    cases h, {
      split, {
        use h.1,
      }, {
        left,
        use h.2,
      }
    }, {
      split, {
        use h.1,
      }, {  
        right,
        use h.2,
      }

    }
  }
end

