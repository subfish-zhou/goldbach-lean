import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalizationMonomials

/-!
# Square-root payment of both section-length contributions

The second term is kept even when span/q exceeds D'. No lower bound such
as H*s≥n is used. The local k is cancelled under the square root only
after multiplication by the original reciprocal amplitude.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Square-root frequency normalization, with the remaining local denominator. -/
theorem directNormalization_sqrt_frequency {A H B : ℝ}
    (hA : 0 < A) (hHB : H ≤ A * B) :
    A⁻¹ * Real.sqrt H ≤ Real.sqrt B / Real.sqrt A := by
  calc
    _ ≤ A⁻¹ * Real.sqrt (A * B) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hHB) (inv_nonneg.mpr hA.le)
    _ = _ := by
      rw [Real.sqrt_mul hA.le]
      have hs := (Real.sqrt_pos.2 hA).ne'
      have hsq := Real.sq_sqrt hA.le
      field_simp
      rw [hsq]

/-- Two distinct section-length monomials after square-root normalization. -/
theorem directNormalization_sqrt_length
    {D Dprime k r s q span H B : ℝ}
    (hD : 0 < D) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s) (hq : 0 < q)
    (hDp : 0 ≤ Dprime) (hspan : 0 ≤ span)
    (hH : H ≤ D * k * r * s * B) (hspanK : span ≤ 2 * k) :
    (D * k * r * s)⁻¹ * Real.sqrt H * Real.sqrt (Dprime + span / q) ≤
      Real.sqrt B * (Real.sqrt Dprime / Real.sqrt (D * k * r * s) +
        Real.sqrt 2 / Real.sqrt (D * r * s * q)) := by
  have hA : 0 < D * k * r * s := by positivity
  have hsum : Real.sqrt (Dprime + span / q) ≤
      Real.sqrt Dprime + Real.sqrt (2 * k / q) := by
    have hh := directNormalization_sqrt_three hDp (div_nonneg hspan hq.le) (le_refl (0 : ℝ))
    simp only [add_zero, Real.sqrt_zero] at hh
    exact hh.trans (add_le_add le_rfl
      (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hspanK hq.le)))
  calc
    _ ≤ (Real.sqrt B / Real.sqrt (D * k * r * s)) *
        (Real.sqrt Dprime + Real.sqrt (2 * k / q)) :=
      mul_le_mul (directNormalization_sqrt_frequency hA hH) hsum
        (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by
      rw [Real.sqrt_div (by positivity : 0 ≤ 2 * k),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
        Real.sqrt_mul (by positivity : 0 ≤ D * k * r),
        Real.sqrt_mul (by positivity : 0 ≤ D * k), Real.sqrt_mul hD.le,
        Real.sqrt_mul (by positivity : 0 ≤ D * r * s),
        Real.sqrt_mul (by positivity : 0 ≤ D * r), Real.sqrt_mul hD.le]
      have hkd := (Real.sqrt_pos.2 hk).ne'
      field_simp

/-- The two-term root payment at the actual retained floor frequency.
The free Gram label only supplies its original positive modulus and span;
its phase/gcd/remaining energy factors are not asserted to be bounded here. -/
theorem directNormalization_floor_sqrt_length
    {M T x Z : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive)
    (cap : Fin 5 → ℕ) (L : WGramLabel) (hq : 0 < wGramModulus L) :
    wBlockAmplitude K j * Real.sqrt ((2 : ℝ) ^ j 0) *
        Real.sqrt ((K.D' : ℝ) + (wGramSpan R S M Z K j cap L : ℝ) /
          (wGramModulus L : ℝ)) ≤
      Real.sqrt (32 * Z * T / x) *
        (Real.sqrt (K.D' : ℝ) /
          Real.sqrt ((K.D : ℝ) * 2 ^ j 1 * 2 ^ j 3 * 2 ^ j 4) +
          Real.sqrt 2 /
            Real.sqrt ((K.D : ℝ) * 2 ^ j 3 * 2 ^ j 4 * (wGramModulus L : ℝ))) := by
  have hD : (0 : ℝ) < K.D := by
    exact_mod_cast (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hqr : (0 : ℝ) < wGramModulus L := by exact_mod_cast hq
  have hx0 : 0 < x := by rw [hx]; positivity
  have hf := directLocalScale_floor_frequency_le hM hZ hN hQ ht
  rw [directLocalScale_frequency_change_variables hM.ne' hT.ne' hx] at hf
  apply directNormalization_sqrt_length hD (by positivity) (by positivity) (by positivity)
    hqr (by positivity) (by positivity) _
    (directNormalization_span_le R S M Z K j cap L)
  convert hf using 1
  ring

/-- A fully connected full-level corollary: first pay the local reciprocal,
then enlarge only the resulting nonnegative coordinate exponents. -/
theorem directNormalization_floor_fullLevel_monomial
    {M T x Z L R S : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {a : ℤ} {P : WOriginalTuple → Prop} {ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N (Ioc 0 ⌊L⌋₊)
        a P R S ξ b K) j positive)
    (p u v w : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hu : 0 ≤ p + u - 1) (hv : 0 ≤ p + v - 1) (hw : 0 ≤ p + w - 1) :
    wBlockAmplitude K j * ((2 : ℝ) ^ j 0) ^ p * ((2 : ℝ) ^ j 1) ^ u *
        ((2 : ℝ) ^ j 3) ^ v * ((2 : ℝ) ^ j 4) ^ w ≤
      (32 * Z * T / x) ^ p * L ^ (p + u - 1) * R ^ (p + v - 1) * S ^ (p + w - 1) := by
  have hQ : ∀ q ∈ Ioc 0 ⌊L⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hD := (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hx0 : 0 < x := by rw [hx]; positivity
  have hB : 0 ≤ 32 * Z * T / x := by positivity
  obtain ⟨hkL, hrR, hsS⟩ := directLocalScale_fullLevel_coordinates hN hL hR hS ht
  have hh := (directNormalization_floor_monomial hM hT hZ hx hN hQ ht p u v w hp).trans
    (directNormalization_global_monomial hB (Nat.cast_nonneg _) (by positivity)
      (by positivity) (by positivity) hkL hrR hsS hu hv hw)
  apply hh.trans
  have hk := mul_le_mul_of_nonneg_left
    (directNormalization_key_nonpositive_power K hD hp1) (Real.rpow_nonneg hB p)
  have hk' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hk (Real.rpow_nonneg hL (p + u - 1)))
      (Real.rpow_nonneg hR (p + v - 1))) (Real.rpow_nonneg hS (p + w - 1))
  simpa only [mul_one] using hk'

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
