/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics

/-!

# Lists

An example of a list of naturals is [1,5,8,1]. More generally, given a
type `X`, a term of type `mylist X` is a finite list of terms of type `X`,
with repeats allowed.

## The definition of a list

The empty list is traditionally called `nil`, and the constructor which
takes a list and adds an element to the beginning is called `cons`,
so `cons 3 [1,5,4] = [3,1,5,4]`. 

We don't set up the `[a,b,c]` notation in this file.

-/

/-- `mylist X` is the type of (finite) lists of elements of `X`. -/
inductive mylist (X : Type) : Type
| nil : mylist -- empty list
| cons (x : X) (l : mylist) : mylist -- "put `(x : X)` at the beginning of `(l : mylist X)`"

namespace mylist

variables (a b c : ℕ)

-- list [a,b,c] of naturals
example : mylist ℕ := cons a (cons b (cons c nil))

variable {X : Type} -- make X implicit

-- joining lists together: [1,5,4] + [2,1] = [1,5,4,2,1]. Defined 
-- by induction on the left list.

/-- Addition of lists. Often called `append` in the literature. -/
def add : mylist X → mylist X → mylist X
| nil l := l
| (cons x m) l := cons x (add m l)

-- Enable `+` notation for addition of lists.
instance : has_add (mylist X) := 
{ add := add }

@[simp] lemma nil_add (a : mylist X) : nil + a = a :=
begin
  refl,
end

@[simp] lemma cons_add (x : X) (m l) : cons x m + l = cons x (m + l) :=
begin
  refl,
end

-- You might want to start this one with `induction a with h t IH`,
@[simp] lemma add_nil (a : mylist X) : a + nil = a :=
begin
  induction a with h t IH,
  refl,
  rw cons_add,
  rw IH,
end

lemma add_assoc (a b c : mylist X) : (a + b) + c = a + (b + c) :=
begin
  induction a with x hx,
  rw nil_add, rw nil_add,
  rw cons_add,
  rw cons_add,
  rw a_ih,
  rwa cons_add,
end

-- singleton list
def singleton (x : X) : mylist X := cons x nil

@[simp] lemma singleton_def (x : X) : singleton x = cons x nil :=
begin
  refl,
end

/-- The reverse of a list. -/
def reverse : mylist X → mylist X
| nil := nil
| (cons x m) := (reverse m) + (singleton x)

-- surprisingly difficult question. Geometrically obvious, but so
-- is a + b = b + a for naturals, and this takes some preliminary work.
-- Don't just jump in! Prove things like `reverse_add` and even more basic things first
-- (and consider tagging them with `@[simp]` if you want to train Lean's
-- simplifier to do the work)

lemma reverse_add_singleton (l : mylist X) (x : X) : l.reverse + singleton x = (singleton x + l).reverse :=
begin
  cases l,
  rw reverse,
  simp,
  rw reverse,
  rw reverse,
  simp,
  rw reverse,
  simp,
  rw reverse,
  rw reverse,
  simp,
end



-- reverse(a b c) + (d e) = ((a b c) + (d)) + (e) = reverse(d a b c) + (e) = reverse( e d a b c) = (c b a d e) 
-- = reverse( reverse(d e) + (a b c))

-- l + (x m) = (l + (x m)) = reverse(m (x l))

lemma add_cons (x : X) (m l) : l + cons x m = l + singleton(x) + m :=
begin
  cases l with y l,
  {
    simp,
  }, {
    rw cons_add,
    rw singleton_def,
    rw cons_add,
    simp [cons_add, add_assoc],
  }
  
end

lemma singleton_add (x : X) (l : mylist X) : singleton x + l = cons x l :=
begin
  rw singleton_def,
  refl,
end

lemma reverse_cons (x : X) (l : mylist X) : (cons x l).reverse = l.reverse + singleton x :=
begin
  rw singleton_def,
  rw reverse,
  refl,
end

lemma reverse_add_cons (x : X) (m l : mylist X) : l.reverse + cons x m = (cons x l).reverse + m :=
begin
  rw reverse_cons,
  rw add_assoc,
  rw singleton_add,
end

-- reverse((a b) + (c d)) = d c b a = (d c) + (b a) = reverse(c d) + reverse(a b)

lemma reverse_sum (l m : mylist X) : (l + m).reverse = m.reverse + l.reverse :=
begin
cases l,
simp,
rw reverse,
rw add_nil,
rw reverse_cons,
simp,
rw reverse_cons,
simp,
sorry,

end

--(x c b a) = (a b c + x).reverse

-- lemma cons_reverse (l : mylist X) (x : X) : cons x l.reverse = (l + singleton x).reverse :=
-- begin
--   cases l,
--   simpa,
--   rw reverse_cons,
--   rw cons_add,
--   rw reverse_cons,
--   simp,
--   sorry,
-- end

lemma reverse_singleton (x : X) : (singleton x).reverse = singleton x :=
begin 
rw singleton_def,
rw reverse,
refl,
end

-- reverse(a b c) + (e d) = (c b a) + (e d) = reverse((d e) + (a b c)) = (c b a e d)

lemma reverse_add (l m : mylist X): l.reverse + m = (m.reverse + l).reverse :=
begin
  cases m,{ 
    simp,
    reflexivity,
  }, {
   
    
  }
  
end




theorem reverse_reverse (l : mylist X) : reverse (reverse l) = l :=
begin
  induction l with x l,
  --cases l with x l,
  -- refl,
  -- rw reverse,
  -- rw reverse_add_singleton,
  -- rw ← reverse_singleton,
  -- rw ← reverse_add,
  -- rw ← reverse_add,
  -- rw reverse_singleton,
  -- refl,
end

end mylist
