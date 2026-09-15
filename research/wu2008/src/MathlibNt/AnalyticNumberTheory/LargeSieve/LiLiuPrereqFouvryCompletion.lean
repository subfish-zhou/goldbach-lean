import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Finite Fourier completion of the reciprocal sum

The modulus is any positive natural number, including one. Neither frequency
is assumed coprime to it. These are finite identities and bounds, not an
assertion of the complete Kloosterman square-root estimate.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {q : ℕ} [NeZero q]

def reciprocalPhase (q : ℕ) [NeZero q] (d : ℤ) (u : ZMod q) : ℂ :=
  if IsUnit u then ZMod.stdAddChar ((d : ZMod q) * u⁻¹) else 0

def completeKloosterman (q : ℕ) [NeZero q] (m : ZMod q) (d : ℤ) : ℂ :=
  ∑ u : ZMod q, ZMod.stdAddChar (m * u) * reciprocalPhase q d u

/-- The integers in the interval are `A, A+1, ..., A+L-1`. -/
def incompleteReciprocal (q : ℕ) [NeZero q] (d A : ℤ) (L : ℕ) : ℂ :=
  ∑ j ∈ range L, reciprocalPhase q d ((A : ZMod q) + (j : ZMod q))

def intervalFourier (q : ℕ) [NeZero q] (A : ℤ) (L : ℕ) (m : ZMod q) : ℂ :=
  ∑ j ∈ range L, ZMod.stdAddChar (m * ((A : ZMod q) + (j : ZMod q)))

theorem completeKloosterman_eq (m : ZMod q) (d : ℤ) :
    completeKloosterman q m d =
      ∑ u : ZMod q, if IsUnit u then
        ZMod.stdAddChar (m * u + (d : ZMod q) * u⁻¹) else 0 := by
  classical
  simp only [completeKloosterman, reciprocalPhase, AddChar.map_add_eq_mul]
  apply sum_congr rfl
  intro u _
  split_ifs <;> simp

theorem dft_reciprocalPhase (d : ℤ) (m : ZMod q) :
    ZMod.dft (reciprocalPhase q d) m = completeKloosterman q (-m) d := by
  simp only [ZMod.dft_apply, completeKloosterman, smul_eq_mul, neg_mul]
  congr 1 with u
  rw [mul_comm u m]

theorem reciprocalPhase_fourier (d : ℤ) (u : ZMod q) :
    reciprocalPhase q d u = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, ZMod.stdAddChar (m * u) * completeKloosterman q (-m) d := by
  have h := congrFun (ZMod.dft.symm_apply_apply (reciprocalPhase q d)) u
  simpa only [ZMod.invDFT_apply, smul_eq_mul, dft_reciprocalPhase] using h.symm

/-- Exact completion, even for intervals longer than a period. -/
theorem incompleteReciprocal_completion (d A : ℤ) (L : ℕ) :
    incompleteReciprocal q d A L = (q : ℂ)⁻¹ *
      ∑ m : ZMod q, intervalFourier q A L m * completeKloosterman q (-m) d := by
  unfold incompleteReciprocal
  simp_rw [reciprocalPhase_fourier]
  rw [← mul_sum, sum_comm]
  simp_rw [← sum_mul]
  rfl

theorem stdAddChar_norm (u : ZMod q) : ‖ZMod.stdAddChar u‖ = 1 := by
  exact Circle.norm_coe (ZMod.toCircle u)

theorem intervalFourier_zero (A : ℤ) (L : ℕ) :
    intervalFourier q A L 0 = L := by
  simp [intervalFourier]

theorem intervalFourier_norm_le_length (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ ≤ L := by
  unfold intervalFourier
  simpa only [stdAddChar_norm, sum_const, card_range, nsmul_eq_mul, mul_one] using
    norm_sum_le (range L) (fun j ↦ ZMod.stdAddChar
      (m * ((A : ZMod q) + (j : ZMod q))))

theorem intervalFourier_eq_geom (A : ℤ) (L : ℕ) (m : ZMod q) :
    intervalFourier q A L m =
      ZMod.stdAddChar (m * (A : ZMod q)) *
        ∑ j ∈ range L, (ZMod.stdAddChar m) ^ j := by
  simp only [intervalFourier, mul_add, AddChar.map_add_eq_mul, mul_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_comm m (j : ZMod q), ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

theorem intervalFourier_norm_mul (A : ℤ) (L : ℕ) (m : ZMod q) :
    ‖intervalFourier q A L m‖ * ‖ZMod.stdAddChar m - 1‖ ≤ 2 := by
  rw [intervalFourier_eq_geom, norm_mul, stdAddChar_norm, one_mul, ← norm_mul,
    geom_sum_mul]
  calc
    ‖ZMod.stdAddChar m ^ L - 1‖ ≤ ‖ZMod.stdAddChar m ^ L‖ + ‖(1 : ℂ)‖ :=
      norm_sub_le _ _
    _ = 2 := by rw [norm_pow, stdAddChar_norm]; norm_num

theorem incompleteReciprocal_norm_le_completion (d A : ℤ) (L : ℕ) (B : ℝ)
    (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤
      (q : ℝ)⁻¹ * (∑ m : ZMod q, ‖intervalFourier q A L m‖) * B := by
  rw [incompleteReciprocal_completion, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    (q : ℝ)⁻¹ * ‖∑ m : ZMod q,
        intervalFourier q A L m * completeKloosterman q (-m) d‖
      ≤ (q : ℝ)⁻¹ * ∑ m : ZMod q,
        ‖intervalFourier q A L m‖ * B := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          refine (norm_sum_le _ _).trans (sum_le_sum fun m _ ↦ ?_)
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hB (-m)) (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

theorem completeKloosterman_modulus_one (m : ZMod 1) (d : ℤ) :
    completeKloosterman 1 m d = 1 := by
  have hu (u : ZMod 1) : IsUnit u := by
    rw [Subsingleton.elim u 1]; exact isUnit_one
  have he (u : ZMod 1) : ZMod.stdAddChar u = 1 := by
    rw [Subsingleton.elim u 0]; simp
  rw [completeKloosterman_eq]
  simp only [hu, if_true, he, sum_const, card_univ, ZMod.card, nsmul_eq_mul,
    Nat.cast_one, one_mul]

theorem incompleteReciprocal_modulus_one (d A : ℤ) (L : ℕ) :
    incompleteReciprocal 1 d A L = L := by
  have h (u : ZMod 1) : reciprocalPhase 1 d u = 1 := by
    simp [reciprocalPhase, Subsingleton.elim u 1,
      Subsingleton.elim (d : ZMod 1) 0]
  simp [incompleteReciprocal, h]

theorem incompleteReciprocal_zero_frequency (A : ℤ) (L : ℕ) :
    incompleteReciprocal q 0 A L =
      (((range L).filter (fun j : ℕ ↦
        IsUnit ((A : ZMod q) + (j : ZMod q)))).card : ℂ) := by
  classical
  simp [incompleteReciprocal, reciprocalPhase, sum_boole]

private theorem sin_pi_mul_lower {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    2 * min t (1 - t) ≤ Real.sin (Real.pi * t) := by
  have half (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) :
      2 * s ≤ Real.sin (Real.pi * s) := by
    have h := Real.mul_le_sin (mul_nonneg Real.pi_pos.le hs0)
      (show Real.pi * s ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
    convert h using 1
    field_simp
  by_cases ht : t ≤ 1 / 2
  · rw [min_eq_left (by linarith)]
    exact half t h0 ht
  · rw [min_eq_right (by linarith)]
    have h := half (1 - t) (by linarith) (by linarith)
    simpa only [mul_sub, mul_one, Real.sin_pi_sub] using h

theorem stdAddChar_sub_one_lower (k : ℕ) (hk : k ≤ q) :
    4 * min (k : ℝ) ((q : ℝ) - k) ≤
      (q : ℝ) * ‖ZMod.stdAddChar (k : ZMod q) - 1‖ := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hkR : (k : ℝ) ≤ q := by exact_mod_cast hk
  have ht0 : 0 ≤ (k : ℝ) / q := by positivity
  have ht1 : (k : ℝ) / q ≤ 1 := (div_le_one hq).2 hkR
  have hs := sin_pi_mul_lower ht0 ht1
  have hs0 : 0 ≤ Real.sin (Real.pi * ((k : ℝ) / q)) :=
    (mul_nonneg (by norm_num) (le_min ht0 (by linarith))).trans hs
  have he : ZMod.stdAddChar (k : ZMod q) =
      Complex.exp (Complex.I * ((2 * Real.pi * ((k : ℝ) / q) : ℝ) : ℂ)) := by
    rw [← Int.cast_natCast k, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show 2 * Real.pi * ((k : ℝ) / q) / 2 =
    Real.pi * ((k : ℝ) / q) by ring]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by norm_num) hs0)]
  have hmin : min ((k : ℝ) / q) (1 - (k : ℝ) / q) =
      min (k : ℝ) ((q : ℝ) - k) / q := by
    rw [← min_div_div_right hq.le, sub_div, div_self hq.ne']
  rw [hmin] at hs
  have hh := mul_le_mul_of_nonneg_left hs hq.le
  field_simp at hh
  rw [show Real.pi * ((k : ℝ) / q) = (k : ℝ) * Real.pi / q by ring]
  nlinarith

theorem intervalFourier_norm_le_reciprocals (A : ℤ) (L k : ℕ)
    (hk0 : 0 < k) (hkq : k < q) :
    ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) := by
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hk : (0 : ℝ) < k := by exact_mod_cast hk0
  have hqk : (0 : ℝ) < (q : ℝ) - k := sub_pos.mpr (by exact_mod_cast hkq)
  have hlow := stdAddChar_sub_one_lower k hkq.le
  have hu := intervalFourier_norm_mul A L (k : ZMod q)
  have hm := mul_le_mul_of_nonneg_left hlow
    (norm_nonneg (intervalFourier q A L (k : ZMod q)))
  have huq := mul_le_mul_of_nonneg_left hu hq.le
  rw [Nat.cast_sub hkq.le]
  by_cases hhalf : (k : ℝ) ≤ (q : ℝ) - k
  · rw [min_eq_left hhalf] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / k := by
      apply (le_div_iff₀ hk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_right (by positivity))
  · rw [min_eq_right (le_of_not_ge hhalf)] at hm
    have hb : ‖intervalFourier q A L (k : ZMod q)‖ ≤ (q : ℝ) / ((q : ℝ) - k) := by
      apply (le_div_iff₀ hqk).2
      nlinarith
    exact hb.trans (by
      rw [div_eq_mul_inv, mul_add]
      exact le_add_of_nonneg_left (by positivity))

private theorem sum_zmod_eq_range (f : ZMod q → ℝ) :
    ∑ u : ZMod q, f u = ∑ k ∈ range q, f (k : ZMod q) := by
  symm
  refine sum_bij (fun k _ ↦ (k : ZMod q)) (by simp) ?_ ?_ (by simp)
  · intro a ha b hb hab
    have h := congrArg ZMod.val hab
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp ha),
      ZMod.val_natCast_of_lt (mem_range.mp hb)] using h
  · intro u _
    exact ⟨u.val, mem_range.mpr (ZMod.val_lt u), ZMod.natCast_zmod_val u⟩

/-- The normalized interval Fourier L1 norm costs only one logarithm. -/
theorem intervalFourier_lone (A : ℤ) (L : ℕ) (hL : L ≤ q) :
    ∑ m : ZMod q, ‖intervalFourier q A L m‖ ≤
      (q : ℝ) * (3 + 2 * Real.log q) := by
  have hq : 0 < q := NeZero.pos q
  rw [sum_zmod_eq_range, sum_range_eq_add_Ico _ hq]
  have hs : ∑ k ∈ Ico 1 q, ‖intervalFourier q A L (k : ZMod q)‖ ≤
      (q : ℝ) * (2 * (harmonic q : ℝ)) := by
    calc
      _ ≤ ∑ k ∈ Ico 1 q,
          (q : ℝ) * ((k : ℝ)⁻¹ + ((q - k : ℕ) : ℝ)⁻¹) :=
        sum_le_sum fun k hk ↦ intervalFourier_norm_le_reciprocals A L k
          (mem_Ico.mp hk).1 (mem_Ico.mp hk).2
      _ = (q : ℝ) * (2 * ∑ k ∈ Ico 1 q, (k : ℝ)⁻¹) := by
        rw [← mul_sum, sum_add_distrib,
          sum_Ico_reflect (fun n : ℕ ↦ (n : ℝ)⁻¹) 1 (m := q) (n := q) (by omega)]
        simp only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right]
        ring
      _ ≤ _ := by
        gcongr
        rw [harmonic_eq_sum_Icc, Rat.cast_sum]
        simp only [Rat.cast_inv, Rat.cast_natCast]
        exact sum_le_sum_of_subset_of_nonneg
          (fun k hk ↦ mem_Icc.mpr ⟨(mem_Ico.mp hk).1, (mem_Ico.mp hk).2.le⟩)
          (fun _ _ _ ↦ by positivity)
  have hzero : ‖intervalFourier q A L (0 : ZMod q)‖ ≤ (q : ℝ) :=
    (intervalFourier_norm_le_length A L 0).trans (by exact_mod_cast hL)
  have hh := harmonic_le_one_add_log q
  have hp := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ q by positivity)
  simp only [Nat.cast_zero]
  nlinarith

theorem incompleteReciprocal_norm_le_log (d A : ℤ) (L : ℕ) (hL : L ≤ q)
    (B : ℝ) (hB : ∀ m : ZMod q, ‖completeKloosterman q m d‖ ≤ B) :
    ‖incompleteReciprocal q d A L‖ ≤ (3 + 2 * Real.log q) * B := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hq : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  refine (incompleteReciprocal_norm_le_completion d A L B hB).trans ?_
  calc
    _ ≤ (q : ℝ)⁻¹ * ((q : ℝ) * (3 + 2 * Real.log q)) * B := by
      gcongr
      exact intervalFourier_lone A L hL
    _ = _ := by field_simp

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
