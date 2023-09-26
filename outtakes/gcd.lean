import tactic
import data.nat.gcd
import data.int.gcd
import data.int.basic
import data.nat.modeq
import data.nat.prime
import number_theory.divisors
import algebra.big_operators.basic
--import geom_sum


lemma gcd_le_sum (m n : ℕ) (h_m_pos : m > 0) (h_n_pos : n > 0) :  m.gcd n ≤ m + n :=
begin
  have hl := nat.gcd_le_left n h_m_pos,
  have hr := nat.gcd_le_right n h_n_pos,
  exact le_add_right hl,
end

lemma gcd_le_sum' (m n : ℤ) (h_m_pos : m > 0) (h_n_pos : n > 0) :  ↑(m.gcd n) ≤ m + n :=
begin
  library_search,
end

-- lemma pow_gcd_sub_one_dvd_pow_right_sub_one (a m n : ℕ) (h_m_pos : m > 0) (h_n_pos : n > 0) (ha : a ≠ 1) (h_a_pos : a > 0)
--       : (a^(nat.gcd m n) - 1) ∣ (a^m - 1) :=
-- begin
--     --nth_rewrite 1 hs,
--   --   rw pow_mul' a s (nat.gcd m n),
--   sorry,
-- end

-- lemma pow_gcd_sub_one_dvd_pow_left_sub_one (a m n : ℕ) (h_m_pos : m > 0) (h_n_pos : n > 0) (ha : a ≠ 1) (h_a_pos : a > 0)
--       : (a^(nat.gcd m n) - 1) ∣ (a^m - 1) :=
-- begin
--     --nth_rewrite 1 hs,
--   --   rw pow_mul' a s (nat.gcd m n),
--   sorry,
-- end

-- lemma pow_gcd_minus_one_dvd_pow_left_minus_one_times_pow_right_sub_one (a m n : ℕ) (h_m_pos : m > 0) (h_n_pos : n > 0) (ha : a ≠ 1) (h_a_pos : a > 0)
--       : (a^(nat.gcd m n) - 1) ∣ (a^m - 1) :=
-- begin
--   -- exact nat.dvd_gcd (pow_gcd_sub_one_dvd_pow_left_sub_one a m n h_m_pos h_n_pos ha h_a_pos)
--   --                   (pow_gcd_sub_one_dvd_pow_right_sub_one a m n h_m_pos h_n_pos ha h_a_pos),
--   sorry,
-- end




-- theorem gcd_pows_minus_one (a m n : ℕ) (ha : a ≠ 1) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
--                           : (nat.gcd (a^m - 1) (a^n - 1)) = a^(nat.gcd m n) - 1 :=
-- begin
--   -- have d : ℕ := (nat.gcd m n ),
--   -- have hd : d = (nat.gcd m n ) := by refl, --why doesn't this work??
  
--   have hm : (nat.gcd m n ) ∣ m := nat.gcd_dvd_left m n,
--   have hn : (nat.gcd m n ) ∣ n := nat.gcd_dvd_right m n,
--   have hm2 := dvd_iff_exists_eq_mul_left.mp hm,
--   have hn2 := dvd_iff_exists_eq_mul_left.mp hn,
--   cases hm2 with s hs,
--   cases hn2 with t ht,

--   -- show a^gcd(mn,) - 1 ∣ (a^m -1, a^n - 1)
  
--   have hamn : (a^(nat.gcd m n) - 1) ∣ (nat.gcd (a^m - 1) (a^n -1)),
--   { exact nat.dvd_gcd ham han, },



-- -- show gcd_a and gcd_b hav opposite signs, assume wlog y ≤ 0

--   have hxy := int.gcd_eq_gcd_ab m n,
--   have h_xy_signs : ( (int.of_nat(m)).gcd_a(int.of_nat(n)) ≤ 0 ∧ (int.of_nat(m)).gcd_b (int.of_nat(n)) > 0 ) ∨ 
--                     ( (int.of_nat(m)).gcd_a(int.of_nat(n)) > 0 ∧ (int.of_nat(m)).gcd_b (int.of_nat(n)) ≤ 0 ),
--   { simp,
--     by_contra, push_neg at h,
--     have gcd_nonneg : nat.gcd m n ≥ 0,
--     { exact zero_le (nat.gcd m n), },
--     have gcd_le_sum := gcd_le_sum m n h_m_pos h_n_pos,
    
--     sorry,
  
--   },

--   -- r = (a^m -1, a^n - 1)
--   -- r ∣ (a^(mx)- 1) and t ∣ (a^(-ny) - 1)
--   -- r ∣ a^gcd(mn,) - 1
--   -- expressions dvd each other -> they are equal

--   simp only [gt_iff_lt, int.of_nat_eq_coe] at h_xy_signs,
  
--   have hr1 : (nat.gcd (a^m - 1) (a^n - 1)) ∣ (a^(m * int.to_nat((int.of_nat(m)).gcd_a( int.of_nat(n) )) - 1)),
--   {
--     sorry,

    
--   },
--   have hr2 : (nat.gcd (a^m - 1) (a^n - 1)) ∣ (a^(int.to_nat(-int.of_nat(n)) * int.to_nat((int.of_nat(m)).gcd_b( int.of_nat(n) )) - 1)),
--   {simp only [int.of_nat_eq_coe], 
--   sorry,

--   },

--   have hr : (nat.gcd (a^m - 1) (a^n - 1)) ∣ a^(nat.gcd m n) - 1,
--   {
--     have hr3 : (nat.gcd (a^m - 1) (a^n - 1)) ∣ 
--       (a^(m * int.to_nat((int.of_nat(m)).gcd_a( int.of_nat(n) )) - 1)) 
--       * (a^(int.to_nat(-int.of_nat(n)) * int.to_nat((int.of_nat(m)).gcd_b( int.of_nat(n) )) - 1)) := 
--       dvd_mul_of_dvd_left hr1 (a ^ ((-int.of_nat n).to_nat * ((int.of_nat m).gcd_b (int.of_nat n)).to_nat - 1)),

--       simp only [int.of_nat_eq_coe] at hr3,

--       nth_rewrite 0 hs at hr3,
--       nth_rewrite 1 ht at hr3,
      
--       simp at hr3,
--       sorry,
      

--   },

--   exact nat.dvd_antisymm ht hamn,

-- end


lemma self_eq_self_sub_1_plus_1 (a : ℕ) (h_a_pos : a > 0) : (a = a - 1 + 1) :=
begin
  zify at *,
  simp,
end


lemma useful_lemma (a d e : ℕ) (h_a_pos : a > 0) : ((a^d)^e - 1 ≡ 0 [MOD a^d - 1]) :=
begin
  have h1 : a^d ≡ 1 [MOD a^d - 1],
  {
    have hz := nat.modeq_zero_iff.mpr (show (a^d - 1) = (a^d - 1), by refl),
    have hr : 1 ≡ 1 [MOD a^d - 1]  := nat.modeq.rfl,
    have hzr : (a ^ d - 1) + 1 ≡ 0 + 1 [MOD a ^ d - 1] := nat.add_modeq_left,
    have hl : a^d = a^d - 1 + 1,

    { have h_ad_pos : a^d > 0 := pow_pos h_a_pos d,
      exact self_eq_self_sub_1_plus_1 (a^d) h_ad_pos},
    rwa [← hl, zero_add] at hzr,
  },
  have h2 : (a^d)^e ≡ 1 [MOD a^d - 1],
  {
    have hp := nat.modeq.pow e h1,
    rwa one_pow e at hp,
  },
  have hge1 : (a ^ d) ^ e ≥ 1,
  {
    have h_a_ge_1 : a ≥ 1 := nat.succ_le_iff.mpr h_a_pos,
    have h_a_d_ge_1 : a^d ≥ 1^d := pow_le_pow_of_le_left' h_a_ge_1 d,
    simpa using pow_le_pow_of_le_left' h_a_d_ge_1 e,
  },
  suffices h : ((a ^ d) ^ e) - 1 + 1 ≡ 0 + 1 [MOD a ^ d - 1],
  exact nat.modeq.add_right_cancel' 1 h,
  simp,
  
  have h_ade_pos : (a^d)^e > 0 := pow_pos (pow_pos h_a_pos d) e,
  have k := self_eq_self_sub_1_plus_1 ((a^d)^e) h_ade_pos,
  rwa k at h2,
  
end

lemma dvd_prod {d a k : ℕ} (hd : d ∣ a) : (d ∣ k * a) :=
begin
  exact dvd_mul_of_dvd_right hd k,
end

/-

proof based on:

https://math.stackexchange.com/questions/11567/gcdbx-1-by-1-b-z-1-dots-b-gcdx-y-z-dots-1-/

lemma gcd_linear_combo_signs {m n : ℕ} (h_m_pos : m > 0) (h_n_pos : n > 0) 
                            : (m.gcd_a n ≤ 0 ∧ m.gcd_b n > 0) ∨ (m.gcd_a n > 0 ∧ m.gcd_b n ≤ 0) :=
begin
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  have hxy : ↑(m.gcd n) = ↑m * x + ↑n * y := nat.gcd_eq_gcd_ab m n,

  by_contra, push_neg at h,
  have gcd_pos : nat.gcd m n > 0 := nat.gcd_pos_of_pos_left n h_m_pos,
  have gcd_le_sum := gcd_le_sum m n h_m_pos h_n_pos,
  zify at gcd_pos,
  zify at h_m_pos,
  zify at h_n_pos,
  have hx : (x ≤ 0 ∨ x >0) := le_or_lt x 0,
  cases hx with hx_nonpos hx_pos,
  { have hy_nonpos := h.1(hx_nonpos),
    have hmx : ↑m * x ≤ 0 := linarith.mul_nonpos hx_nonpos h_m_pos,
    have hny : ↑n * y ≤ 0 := linarith.mul_nonpos hy_nonpos h_n_pos,
    have h_combo : ↑m * x + ↑n * y ≤ 0 := add_nonpos hmx hny,
    rw ← hxy at h_combo,
    linarith,
  },
  { 
    have hy_pos := h.2(hx_pos),
    have hcm : ↑m * x  > ↑m :=  sorry,
    have hcn : ↑n * y  > ↑n :=  sorry,
    have hcmn : ↑m * x + ↑n * y > ↑m + ↑n := add_lt_add hcm hcn,
    rw ← hxy at hcmn,
    linarith,
  },
end

lemma gcd_linear_combo_signs' {m n : ℤ} (h_m_pos : m > 0) (h_n_pos : n > 0) 
                            : (m.gcd_a n ≤ 0 ∧ m.gcd_b n > 0) ∨ (m.gcd_a n > 0 ∧ m.gcd_b n ≤ 0) :=
begin
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  have hxy : ↑(m.gcd n) = m * x + n * y := (int.gcd_eq_gcd_ab m n),

  by_contra, push_neg at h,
  have gcd_pos : int.gcd m n > 0 := sorry,
  have gcd_le_sum := 
  zify at gcd_pos,
  zify at h_m_pos,
  zify at h_n_pos,
  have hx : (x ≤ 0 ∨ x >0) := le_or_lt x 0,
  cases hx with hx_nonpos hx_pos,
  { have hy_nonpos := h.1(hx_nonpos),
    have hmx : ↑m * x ≤ 0 := linarith.mul_nonpos hx_nonpos h_m_pos,
    have hny : ↑n * y ≤ 0 := linarith.mul_nonpos hy_nonpos h_n_pos,
    have h_combo : ↑m * x + ↑n * y ≤ 0 := add_nonpos hmx hny,
    rw ← hxy at h_combo,
    linarith,
  },
  { 
    
    have hcn : ↑n * y  > ↑n :=  sorry,
    have hcmn : ↑m * x + ↑n * y > ↑m + ↑n := add_lt_add hcm hcn,
    rw ← hxy at hcmn,
    linarith,
  },
end

lemma h_a_pow {a : ℕ} (h_a_pos : a > 0) (n : ℕ) : 1 ≤ a^n :=
begin
  exact nat.one_le_pow n a h_a_pos,
end

lemma gcd_pow {a m n : ℕ} (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
              : 1 ≡ a^((nat.gcd m n)) [MOD (nat.gcd (a^m - 1) (a^n - 1))] :=
begin
  set d := (nat.gcd (a^m - 1) (a^n - 1)),
  have h_xy_signs := gcd_linear_combo_signs h_m_pos h_n_pos,
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  
  cases h_xy_signs with hl hr,
  {

    -- g = gcd(m n); g = mx + ny; wlog y ≤ 0
    -- d = gcd(a^m - 1, a^n -1)
    -- d ∣ a^(mx) - 1 ; d ∣ a^(-ny) - 1 ; d ∣ -a^g (a^-ny - 1)
    -- d ∣ -a^g (a^-ny - 1) + a^(mx) - 1
    -- d ∣ a^g - a^(g-ny) + a^(mx) - 1 = a^g - 1

    set g := (nat.gcd m n),

    have hx : -x ≥ 0 := by linarith,
    have hmx : m * int.to_nat(-x) ≥ 0 := zero_le (m * (-x).to_nat),

    have hd1 : d ∣ a^m - 1 := (a ^ m - 1).gcd_dvd_left (a ^ n - 1),


    have hd1_mod : 1 ≡ a^m [MOD d] := (nat.modeq_iff_dvd' (h_a_pow h_a_pos m)).mpr hd1,

    have hd1x : 1^(int.to_nat(-x)) ≡ (a^m)^(int.to_nat(-x)) [MOD d] := nat.modeq.pow (-x).to_nat hd1_mod,
    simp only [one_pow] at hd1x,
    rw ← pow_mul at hd1x,

    have hd2 : d ∣ a^n - 1 := (a ^ m - 1).gcd_dvd_right (a ^ n - 1),
    have hd2_mod : 1 ≡ a^n [MOD d] := (nat.modeq_iff_dvd' (h_a_pow h_a_pos n)).mpr hd2,

    have hd2y : 1^(int.to_nat(y)) ≡ (a^n)^(int.to_nat(y)) [MOD d] := nat.modeq.pow (y).to_nat hd2_mod,
    simp only [one_pow] at hd2y,
    rw ← pow_mul at hd2y,

    have hd2y_dvd : d ∣ a ^ (n * y.to_nat) - 1 := (nat.modeq_iff_dvd' (h_a_pow h_a_pos (n * y.to_nat) )).mp hd2y,
    have hd1x_dvd : d ∣ a ^ (m * (-x).to_nat) - 1 := (nat.modeq_iff_dvd' (h_a_pow h_a_pos (m * (-x).to_nat) )).mp hd1x,

    have hd2y_dvd_mul1 : ↑d ∣ ↑(a ^ (m * (-x).to_nat) - 1) := int.coe_nat_dvd.mpr hd1x_dvd,
    have hd2y_dvd_mul2 : ↑d ∣ -↑(a^g) * ↑(a ^ (m * (-x).to_nat) - 1) := dvd_mul_of_dvd_right hd2y_dvd_mul1 (-int.of_nat(a^g)),
 
    have hg : ↑(g) = ↑m * x + ↑n * y := nat.gcd_eq_gcd_ab m n,
    apply_fun int.to_nat at hg,
    simp only [int.to_nat_coe_nat] at hg,
    rw (show ↑m * x = -↑m * (-x), by linarith) at hg,


     -- ^(0_0)^ ???
   
    
    },
  {
    sorry,
    },

end


lemma gcd_pow' {a : ℕ} {m n : ℤ} (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
              : 1 ≡ a^((int.gcd m n)) [MOD (int.gcd (a^(m.to_nat) - 1) (a^(n.to_nat) - 1))] :=
begin
  set d := (nat.gcd (a^m.to_nat - 1) (a^n.to_nat - 1)),
  have h_xy_signs := gcd_linear_combo_signs h_m_pos h_n_pos,
  set x := m.gcd_a n,
  set y := m.gcd_b n,
  
  cases h_xy_signs with hl hr,
  {

    -- g = gcd(m n); g = mx + ny; wlog y ≤ 0
    -- d = gcd(a^m - 1, a^n -1)
    -- d ∣ a^(mx) - 1 ; d ∣ a^(-ny) - 1 ; d ∣ -a^g (a^-ny - 1)
    -- d ∣ -a^g (a^-ny - 1) + a^(mx) - 1
    -- d ∣ a^g - a^(g-ny) + a^(mx) - 1 = a^g - 1

    set g := (nat.gcd m n),

   
    
    },
  {
    sorry,
    },

end



theorem gcd_pows_minus_one (a m n : ℕ) (ha : a ≠ 1) (h_a_pos : a > 0) (h_m_pos : m > 0) (h_n_pos : n > 0) 
                        : (nat.gcd (a^m - 1) (a^n - 1)) = a^(nat.gcd m n) - 1 :=
begin

have left_dvd_right : (nat.gcd (a^m - 1) (a^n - 1)) ∣ a^(nat.gcd m n) - 1,
{ 
  -- use modular arithmetic to show 1 ≡ a^m , 1 ≡ a^n -> 1 ≡ a^(mx + ny) [mod d]

  set d := (nat.gcd (a^m - 1) (a^n - 1)),
  have hd1 : d ∣ (a^m - 1) := (a ^ m - 1).gcd_dvd_left (a ^ n - 1),
  have hd2 : d ∣ (a^n - 1) := (a ^ m - 1).gcd_dvd_right (a ^ n - 1),
  rw ← nat.modeq_iff_dvd' at hd1, rw ← nat.modeq_iff_dvd' at hd2,
  {
    
    have h_gcd_pow := gcd_pow h_a_pos h_m_pos h_n_pos,
    set d := (nat.gcd (a^m - 1) (a^n - 1)),
    
    have hk : 1 ≤ a ^ m.gcd n := (nat.gcd m n).one_le_pow a h_a_pos,
    exact (nat.modeq_iff_dvd' hk).mp h_gcd_pow,
  },

  -- inequalities are satisfied for hd1 and hd2
  { exact nat.one_le_pow n a h_a_pos,},
  { exact nat.one_le_pow m a h_a_pos,}

},
have right_dvd_left : a^(nat.gcd m n) - 1 ∣ (nat.gcd (a^m - 1) (a^n - 1)),
{ 
  have h1 : nat.gcd m n ∣ n := nat.gcd_dvd_right m n,
  have h2 : nat.gcd m n ∣ m := nat.gcd_dvd_left m n,

  have h1_d := dvd_iff_exists_eq_mul_left.mp h1,
  have h2_d := dvd_iff_exists_eq_mul_left.mp h2,

  cases h1_d with e he,
  cases h2_d with f hf,

  have h3 : a^n - 1 = (a^(m.gcd n))^e - 1,
  {
    nth_rewrite 0 he,
    rw mul_comm e (m.gcd n),
    suffices h : a ^ (m.gcd n * e) = (a ^ m.gcd n) ^ e,
    rw h,
    exact pow_mul a (nat.gcd m n) e,
  },
  have h4 : a^m - 1 = (a^(m.gcd n))^f - 1,
  {nth_rewrite 0 hf,
    rw mul_comm f (m.gcd n),
    suffices h : a ^ (m.gcd n * f) = (a ^ m.gcd n) ^ f,
    rw h,
    exact pow_mul a (nat.gcd m n) f,},

  have h5 := nat.modeq.symm( useful_lemma a (m.gcd n) e h_a_pos),
  have h6 := nat.modeq.symm( useful_lemma a (m.gcd n) f h_a_pos),
  
  rw ← h3 at h5,
  rw ← h4 at h6,

  rw nat.modeq_iff_dvd' at h5, simp only [tsub_zero] at h5,
  rw nat.modeq_iff_dvd' at h6, simp only [tsub_zero] at h6,
  exact nat.dvd_gcd h6 h5,

  --show inequalities are satisfied
  {suffices h : 1 ≤ a^m,
  linarith,
  exact nat.one_le_pow m a h_a_pos,},
  {suffices h : 1 ≤ a^n,
  linarith,
  exact nat.one_le_pow n a h_a_pos,},

},

exact nat.dvd_antisymm left_dvd_right right_dvd_left,

end
