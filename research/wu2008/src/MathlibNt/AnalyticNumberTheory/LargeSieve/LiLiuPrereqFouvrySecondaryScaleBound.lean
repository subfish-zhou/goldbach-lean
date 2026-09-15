import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryGcdBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvrySecondaryRatioCarrier

/-!
# An explicit envelope for the remaining secondary base sum

This coarse envelope uses `gcd(s,|A|) <= s`; the sharper occupied mean
remains separately available. Divisor coefficients are paid by a proved
uniform power bound, not an assumed arithmetic-error estimate.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def wGramSecondaryNumeratorMax (a : ℤ) (K : WExtractedKey) (F : ℕ)
    (j : Fin 5 → ℕ) : ℕ :=
  a.natAbs * K.1.2.1 * 2 ^ (j 0 + 1) * (F / K.1.1)

def wGramSecondaryBaseCountBound (K : WExtractedKey) (F : ℕ) (j : Fin 5 → ℕ) : ℝ :=
  (2 ^ j 2 : ℕ) * (F / K.1.1 : ℕ) ^ 2 *
    (4 * (2 ^ (j 0 + 1) : ℕ) * (2 ^ j 4 : ℕ) *
      (1 + Real.log (2 ^ (j 0 + 1) : ℕ)))

def wGramSecondaryScaleEnvelope (ε δ C Cτ : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) : ℝ :=
  (C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ)) *
    (2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) ^ (1 / 2 + ε : ℝ)) *
    ((2 ^ (j 3 + 1) - 1 : ℕ) * Real.sqrt
      ((2 ^ (j 2 + 1) * 2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) *
        (Cτ * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ)))

theorem wGramSecondaryScaleEnvelope_nonneg {C : ℝ} (hC : 0 ≤ C)
    (ε δ Cτ : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey) (F : ℕ) (j cap : Fin 5 → ℕ) :
    0 ≤ wGramSecondaryScaleEnvelope ε δ C Cτ a R S K F j cap := by
  unfold wGramSecondaryScaleEnvelope
  positivity

theorem wGramSecondaryBases_numerator_le
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {v : WGramSecondaryBase}
    (hv : v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c))) :
    (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a v.2.1.2.2).natAbs ≤
      wGramSecondaryNumeratorMax a K F j := by
  obtain ⟨_, hm, hm', _, _, hh, _⟩ :=
    wGramSecondaryBases_scale_data hN hNF hR hS hM hZ hv
  have hhbound : v.2.1.2.2.natAbs ≤ 2 ^ (j 0 + 1) := by
    obtain ⟨n, hn, he⟩ := mem_image.mp hh
    rw [← he]
    cases positive <;> simpa using (mem_Ico.mp hn).2.le
  have hdiff := Int.natAbs_coe_sub_coe_le_of_le (mem_Ioc.mp hm').2 (mem_Ioc.mp hm).2
  simp only [iv3SecondaryNumerator, Int.natAbs_mul, Int.natAbs_natCast]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hhbound) hdiff

/-- The power-bound constant precedes all residue, coefficient, support and
dyadic choices. The nonzero divisor argument is derived from occupation. -/
theorem wGramSecondaryBases_mean_le_scaleEnvelope {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cτ : ℝ, 0 < Cτ ∧
    ∀ (ε C : ℝ) (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)),
      0 ≤ ε → 0 ≤ C → (∀ n ∈ N, 0 < n) → (∀ n ∈ N, n ≤ F) →
      0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      ∀ v ∈ wGramSecondaryBases (wGramSecondaryLabels K a (wCoprimeFiber x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c)),
        wGramSecondaryGcdDyadicMean ε C a R S K j cap v ≤
          wGramSecondaryScaleEnvelope ε δ C Cτ a R S K F j cap := by
  obtain ⟨Cτ, hCτ, hτ⟩ := fouvryTau_le_const_rpow (k := 2) (by decide) hδ
  refine ⟨Cτ, hCτ, ?_⟩
  intro ε C N F a x η R S M Z K b j cap positive c hε hC hN hNF hR hS hM hZ v hv
  obtain ⟨hn, _, _, hs, hs', _, _⟩ :=
    wGramSecondaryBases_scale_data hN hNF hR hS hM hZ hv
  obtain ⟨_, hspos, _, hsec, hl⟩ := wGramSecondaryBases_data hN hv
  let A := (iv3SecondaryNumerator K.1.2.1 v.2.1.1 v.2.2.1 a v.2.1.2.2).natAbs
  have hA : 0 < A :=
    Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr (iv3SecondaryNumerator_ne_zero hsec hl))
  have hAmax : (A : ℝ) ≤ wGramSecondaryNumeratorMax a K F j := by
    exact_mod_cast wGramSecondaryBases_numerator_le hN hNF hR hS hM hZ hv
  have hτA : (A.divisors.card : ℝ) ≤ Cτ * (wGramSecondaryNumeratorMax a K F j : ℝ) ^ δ := by
    have htau : (A.divisors.card : ℝ) ≤ Cτ * (A : ℝ) ^ δ := by
      simpa only [fouvryTau_two] using hτ A hA
    exact htau.trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hAmax hδ.le) hCτ.le)
  have hqlo :
      (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ) ≤
      v.1 * 2 ^ j 3 * v.2.1.2.1 * v.2.2.2.1 :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ (mem_Ico.mp hn).1)
      (mem_Ico.mp hs).1) (mem_Ico.mp hs').1
  have hqhi :
      v.1 * (2 ^ (j 3 + 1) - 1) * v.2.1.2.1 * v.2.2.2.1 ≤
      2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) * 2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_right _ (mem_Ico.mp hn).2.le)
      (mem_Ico.mp hs).2.le) (mem_Ico.mp hs').2.le
  have hsqrt : v.1 * v.2.2.2.1 * v.2.1.2.1 ≤
      2 ^ (j 2 + 1) * 2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (mem_Ico.mp hn).2.le (mem_Ico.mp hs').2.le)
      (mem_Ico.mp hs).2.le
  apply (wGramSecondaryGcdDyadicMean_le_old hC ε a R S K j cap v hspos).trans
  unfold wGramSecondaryDyadicMean wGramSecondaryScaleEnvelope
  apply mul_le_mul
  · apply mul_le_mul
    · apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply add_le_add le_rfl
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by exact_mod_cast hqlo)
    · exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hqhi) (by linarith)
    · positivity
    · positivity
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    change ((v.1 * v.2.2.2.1 * v.2.1.2.1 * A.divisors.card : ℕ) : ℝ) ≤ _
    rw [Nat.cast_mul]
    exact mul_le_mul (by exact_mod_cast hsqrt) hτA (by positivity) (by positivity)
  · positivity
  · positivity

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
