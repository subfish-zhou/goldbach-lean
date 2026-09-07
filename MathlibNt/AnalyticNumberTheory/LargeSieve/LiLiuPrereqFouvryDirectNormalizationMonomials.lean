import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryDirectNormalization

/-!
# Local monomials after reciprocal payment

These are algebraic normalization tools, not asserted producers of main
or secondary energy. Exponents are arbitrary and are only enlarged to
global scales when their post-payment values are nonnegative.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- The small key costs at most Y^3 in D and Y^5 in D'. -/
theorem directLocalScale_key_bounds {Y : ℝ} (hY : 0 ≤ Y)
    {K : WExtractedKey} (hK : K ∈ wExtractedKeyBox Y) :
    (K.D : ℝ) ≤ Y ^ 3 ∧ (K.D' : ℝ) ≤ Y ^ 5 := by
  have hk := mem_wExtractedKeyBox_iff.mp hK
  have hh {n : ℕ} (hn : n ≤ ⌊Y⌋₊) : (n : ℝ) ≤ Y :=
    (Nat.cast_le.mpr hn).trans (Nat.floor_le hY)
  have hD : (K.D : ℝ) ≤ Y ^ 3 := by
    unfold WExtractedKey.D
    push_cast
    calc
      _ ≤ Y * Y * Y := by
        exact mul_le_mul (mul_le_mul (hh hk.2.2.1) (hh hk.2.2.2.1)
          (Nat.cast_nonneg _) hY) (hh hk.2.2.2.2.1) (Nat.cast_nonneg _) (mul_nonneg hY hY)
      _ = _ := by ring
  refine ⟨hD, ?_⟩
  unfold WExtractedKey.D'
  push_cast
  calc
    _ ≤ Y * Y * Y ^ 3 := by
      exact mul_le_mul (mul_le_mul (hh hk.1) (hh hk.2.1)
        (Nat.cast_nonneg _) hY) hD (Nat.cast_nonneg _) (mul_nonneg hY hY)
    _ = _ := by ring

/-- Global upper coordinates are consequences of an actual full-level member.
This theorem does not itself replace any local scale in a denominator. -/
theorem directLocalScale_fullLevel_coordinates
    {H : ℕ → ℕ → ℕ} {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {L R S : ℝ} (hL : 0 ≤ L) (hR : 0 ≤ R) (hS : 0 ≤ S)
    {a : ℤ} {P : WOriginalTuple → Prop} {ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber H N (Ioc 0 ⌊L⌋₊) a P R S ξ b K) j positive) :
    (2 : ℝ) ^ j 1 ≤ L ∧ (2 : ℝ) ^ j 3 ≤ R ∧ (2 : ℝ) ^ j 4 ≤ S := by
  have hQ : ∀ q ∈ Ioc 0 ⌊L⌋₊, 0 < q := fun _ hq => (mem_Ioc.mp hq).1
  have hf := (mem_filter.mp ht).1
  have hz := (mem_wExtractedFrequencies_iff.mp
    (mem_filter.mp (mem_wExtractedKeyFiber_iff.mp hf).1).1).1
  have hv := (wExtractedOriginal_valid hN hQ hz).1
  have hm := mem_wFactorExtractionTuples_iff.mp hz
  have hq := (mem_filter.mp (wExtractedOriginal_reducedModuli hz).1).1
  have hk : (wGCDTuple (wExtractedOriginal t.1)).k₁ ≤ ⌊L⌋₊ :=
    (Nat.le_of_dvd (hQ _ hq) hv.k₁_dvd).trans (mem_Ioc.mp hq).2
  have hb := wAnalyticDyadicBlock_bounds hN hQ ht
  exact ⟨(hb 1).1.trans ((Nat.cast_le.mpr hk).trans (Nat.floor_le hL)),
    (hb 3).1.trans ((Nat.cast_le.mpr (mem_Ioc.mp hm.2.2.1).2).trans (Nat.floor_le hR)),
    (hb 4).1.trans ((Nat.cast_le.mpr (mem_Ioc.mp hm.2.2.2.1).2).trans (Nat.floor_le hS))⟩

/-- Exact exponents after multiplying the local reciprocal and using H≤Dkrs B. -/
theorem directNormalization_monomial
    {D k r s H B p u v w : ℝ}
    (hD : 0 < D) (hk : 0 < k) (hr : 0 < r) (hs : 0 < s)
    (hH : 0 ≤ H) (hB : 0 ≤ B) (hp : 0 ≤ p)
    (hHB : H ≤ D * k * r * s * B) :
    (D * k * r * s)⁻¹ * H ^ p * k ^ u * r ^ v * s ^ w ≤
      B ^ p * D ^ (p - 1) * k ^ (p + u - 1) * r ^ (p + v - 1) * s ^ (p + w - 1) := by
  have hh := directNormalization_rpow_payment (by positivity : 0 < D * k * r * s)
    hH hB hp hHB
  calc
    _ ≤ (D * k * r * s) ^ (p - 1) * B ^ p * k ^ u * r ^ v * s ^ w := by
      gcongr
    _ = _ := by
      rw [show p + u - 1 = (p - 1) + u by ring,
        show p + v - 1 = (p - 1) + v by ring,
        show p + w - 1 = (p - 1) + w by ring,
        Real.rpow_add hk, Real.rpow_add hr, Real.rpow_add hs]
      rw [Real.mul_rpow (by positivity : 0 ≤ D * k * r) hs.le,
        Real.mul_rpow (by positivity : 0 ≤ D * k) hr.le,
        Real.mul_rpow hD.le hk.le]
      ring

/-- The preceding scalar rule instantiated with the proved actual floor cutoff. -/
theorem directNormalization_floor_monomial
    {M T x Z : ℝ} (hM : 0 < M) (hT : 0 < T) (hZ : 0 ≤ Z)
    (hx : x = 4 * M * T) {N Q : Finset ℕ}
    (hN : ∀ n ∈ N, 0 < n) (hQ : ∀ q ∈ Q, 0 < q)
    {a : ℤ} {P : WOriginalTuple → Prop} {R S ξ : ℝ} {b : ℕ}
    {K : WExtractedKey} {j : Fin 5 → ℕ} {positive : Bool}
    {t : WExtractedTuple × ℤ}
    (ht : t ∈ wAnalyticDyadicBlock
      (wExtractedKeyFiber (wFloorCutoff M Z) N Q a P R S ξ b K) j positive)
    (p u v w : ℝ) (hp : 0 ≤ p) :
    wBlockAmplitude K j * ((2 : ℝ) ^ j 0) ^ p * ((2 : ℝ) ^ j 1) ^ u *
        ((2 : ℝ) ^ j 3) ^ v * ((2 : ℝ) ^ j 4) ^ w ≤
      (32 * Z * T / x) ^ p * (K.D : ℝ) ^ (p - 1) *
        ((2 : ℝ) ^ j 1) ^ (p + u - 1) *
        ((2 : ℝ) ^ j 3) ^ (p + v - 1) * ((2 : ℝ) ^ j 4) ^ (p + w - 1) := by
  have hD : (0 : ℝ) < K.D := by
    exact_mod_cast (wExtractedKeyFiber_positive hN hQ (mem_filter.mp ht).1).1
  have hx0 : 0 < x := by rw [hx]; positivity
  have hf := directLocalScale_floor_frequency_le hM hZ hN hQ ht
  rw [directLocalScale_frequency_change_variables hM.ne' hT.ne' hx] at hf
  apply directNormalization_monomial hD (by positivity) (by positivity) (by positivity)
    (by positivity) (by positivity) hp
  convert hf using 1
  ring

/-- An explicit expansion of the only frequency loss; no exponent is silently absorbed. -/
theorem directNormalization_frequency_power {Z T x : ℝ}
    (hZ : 0 ≤ Z) (hT : 0 ≤ T) (hx : 0 ≤ x) (p : ℝ) :
    (32 * Z * T / x) ^ p = (32 : ℝ) ^ p * Z ^ p * T ^ p / x ^ p := by
  rw [Real.div_rpow (by positivity) hx,
    Real.mul_rpow (by positivity : 0 ≤ 32 * Z) hT,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 32) hZ]

/-- Only nonnegative exponents after reciprocal payment may be globally enlarged. -/
theorem directNormalization_global_monomial
    {B D k r s L R S p u v w : ℝ}
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hk : 0 ≤ k) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hkL : k ≤ L) (hrR : r ≤ R) (hsS : s ≤ S)
    (hu : 0 ≤ p + u - 1) (hv : 0 ≤ p + v - 1) (hw : 0 ≤ p + w - 1) :
    B ^ p * D ^ (p - 1) * k ^ (p + u - 1) * r ^ (p + v - 1) * s ^ (p + w - 1) ≤
      B ^ p * D ^ (p - 1) * L ^ (p + u - 1) * R ^ (p + v - 1) * S ^ (p + w - 1) := by
  have hL := hk.trans hkL
  have hR := hr.trans hrR
  have hS := hs.trans hsS
  have hkl := Real.rpow_le_rpow hk hkL hu
  have hrr := Real.rpow_le_rpow hr hrR hv
  have hss := Real.rpow_le_rpow hs hsS hw
  gcongr

/-- At p≤1 the positive integer key denominator helps, rather than costing Y. -/
theorem directNormalization_key_nonpositive_power (K : WExtractedKey)
    (hD : 0 < K.D) {p : ℝ} (hp : p ≤ 1) : (K.D : ℝ) ^ (p - 1) ≤ 1 := by
  have hd : (1 : ℝ) ≤ K.D := by exact_mod_cast hD
  calc
    _ ≤ (K.D : ℝ) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hd (by linarith)
    _ = 1 := Real.rpow_zero _

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
