/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/

import tactic -- imports all the Lean tactics
import data.real.basic -- imports the real numbers
import solutions.section02reals.sheet5 -- import a bunch of previous stuff

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in a solutions video,
so if you like you can try some of them and then watch me
solving them.

Good luck! 
-/


/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsto_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : tendsto a t) :
  tendsto (λ n, 37 * a n) (37 * t) :=
begin
  -- intros ε hε,
  -- obtain ⟨X, hX⟩ := h (ε/37) (by linarith),
  rw tendsto_def at *,
  intro ε,
  specialize h (ε/37),
  intro hε,
  have hε2 :  0 < ε/37 := by linarith,
  specialize  h hε2,
  cases h with n hn,
  use n,
  intro m,
  specialize hn m,
  intro k,
  specialize hn k,
  have i : 37 * |a m - t| < ε := by linarith,
  rw [← mul_sub, abs_mul, abs_of_nonneg],
  exact i,
  linarith,
  

end

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : 0 < c) : tendsto (λ n, c * a n) (c * t) :=
begin
  rw tendsto_def at *,
  intro ε,
  specialize h (ε/c),
  intro hε,
  have hεc : 0 < ε/c := div_pos hε hc,
  specialize h hεc,
  cases h with n hn,
  use n,
  intro m,
  specialize hn m,
  intro k,
  specialize hn k,
  have i : c * |a m - t| < ε := (lt_div_iff' hc).mp hn,
  rw [← mul_sub, abs_mul, abs_of_nonneg],
  exact i,
  linarith,
end

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsto_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : tendsto a t)
  {c : ℝ} (hc : c < 0) : tendsto (λ n, c * a n) (c * t) :=
begin
  unfold tendsto at *,
  have hc' : 0 < -c := neg_pos.mpr hc,
  intros ε hε,
  obtain ⟨N, hN⟩ := h (ε/(-c)) (div_pos hε hc'), 
  existsi N,
  intros n hn,
  rw [←mul_sub, abs_mul, abs_of_neg hc],
  exact (lt_div_iff' hc').mp (hN n hn),
end



/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsto_const_mul (a : ℕ → ℝ) (t : ℝ) (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, c * a n) (c * t) :=
begin
  obtain (hl | rfl | hg) := lt_trichotomy c 0, 
    { exact tendsto_neg_const_mul h hl,},
    { simpa using tendsto_const 0 },
    { exact tendsto_pos_const_mul h hg }
end

#print tendsto_const_mul

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsto_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : tendsto a t) :
  tendsto (λ n, a n * c) (t * c) :=
begin
  convert tendsto_const_mul a t c h using 1,
  ext n,
  rw mul_comm (a n) c,
  linarith,
end

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tendsto_neg' {a : ℕ → ℝ} {t : ℝ} (ha : tendsto a t) :
  tendsto (λ n, - a n) (-t) :=
begin
  convert tendsto_const_mul (-1) ha, -- read about `convert` on the community web pages
  { ext, simp }, -- ext is a generic extensionality tactic. Here it's being
                 -- used to deduce that two functions are the same if they take
                 -- the same values everywhere
  { simp },
end

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsto_of_tendsto_sub {a b : ℕ → ℝ} {t u : ℝ}
  (h1 : tendsto (λ n, a n - b n) t) (h2 : tendsto b u) :
  tendsto a (t+u) :=
begin
  convert tendsto_add h1 h2,
  simp,
  
end

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsto_sub_lim_iff {a : ℕ → ℝ} {t : ℝ}
   : (tendsto a t)  ↔ tendsto (λ n, a n - t) 0 :=
begin
  split, {
    intro h,
    have j := tendsto_sub h (tendsto_const t) ,
    simp at j,
    assumption,
  }, {
    intro h,
    have j := tendsto_const t,
    simpa using tendsto_of_tendsto_sub h j,
  }
  
end

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsto_zero_mul_tendsto_zero
  {a b : ℕ → ℝ} (ha : tendsto a 0) (hb : tendsto b 0) :
  tendsto (λ n, a n * b n) 0 :=
begin
  intros ε hε,
  have k : ((1 : ℝ) > (0 : ℝ)) := by norm_num,
  specialize ha 1 k,
  specialize hb ε hε,
  cases ha with N1 hN1,
  cases hb with N2 hN2,
  use max N1 N2,
  intro n,
  specialize hN1 n, specialize hN2 n,
  intro hN,
  have l := le_max_left N1 N2,
  have i := le_max_right N1 N2,
  specialize hN1 (le_trans l hN),
  specialize hN2 (le_trans i hN),
  simp at *,
  rw abs_mul,
  simpa using mul_lt_mul'' hN1 hN2 _ _,
  simpa using abs_nonneg _,
  simpa using abs_nonneg _,
end

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsto_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : tendsto a t)
  (hb : tendsto b u) : tendsto (λ n, a n * b n) (t * u) :=
begin
  --intros ε hε,
  rw tendsto_sub_lim_iff,
  have ht := tendsto_const t,
  have hu := tendsto_const u,
  have ha2 := tendsto_sub ha ht,
  have hb2 := tendsto_sub hb hu,
  simp at *,
  have hab := tendsto_zero_mul_tendsto_zero ha2 hb2,
  simp at *,
  have h : (∀ n, a n * b n - t * u = (a n - t) * (b n - u) + u * (a n - t) + t * (b n - u)),
  { intro n, ring,},
  simp [h],
  rw (show (0 : ℝ) = 0 + u * 0 + t * 0, by simp),
  apply tendsto_add, {
    apply tendsto_add,
    exact hab,
    exact tendsto_const_mul (λ (n : ℕ), a n - t) 0 u ha2,

  }, {
    exact tendsto_const_mul (λ (n : ℕ), b n - u) 0 t hb2,

  }, 
  
  

end

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsto_unique (a : ℕ → ℝ) (s t : ℝ)
  (hs : tendsto a s) (ht : tendsto a t) : s = t :=
begin
  by_contra h,
  wlog h2 : s < t,
  {exact ne.lt_or_lt h},
  set ε := t - s with hε,
  have hε : 0 < ε := sub_pos.mpr h2,
  obtain ⟨X, hX⟩ := hs (ε/2) (by linarith),
  obtain ⟨Y, hY⟩ := ht (ε/2) (by linarith),
  specialize hX (max X Y) (le_max_left X Y),
  specialize hY (max X Y) (le_max_right X Y),
  rw abs_lt at hX hY,
  linarith,
end

