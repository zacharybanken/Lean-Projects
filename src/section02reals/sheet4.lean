/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers

/-

# Figuring out how to use the reals

## The `library_search` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `library_search` tactic tells you the names of all these lemmas. 
See where it says "try this" -- click there and Lean will replace
`library_search` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.

The `linarith` tactic is a tactic which can solve some equalities and inequalities
in ordered structures like the naturals or reals. Unlike `ring`, `linarith`
does look at hypotheses in the tactic state. For example if you have
hypotheses `h1 : a < b` and `h2 : b ≤ c` then `linarith` would prove
a goal of `⊢ a < c`.

However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `library_search` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |(-x)| = |x| :=
begin
  exact abs_neg x,
end

example (x y : ℝ) : |x - y| = |y - x| :=
begin
  exact abs_sub_comm x y,
end 

example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C :=
begin
  exact max_le_iff,
end

example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y :=
begin
  exact abs_lt,
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 :=
begin
  linarith,
end

example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y :=
begin
  linarith,
end

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 :=
begin
  linarith,
end

example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) :
  a + b + c + d < x + y :=
begin
  linarith,
end
