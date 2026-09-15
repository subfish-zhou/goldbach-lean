import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryMainJointCarrier

/-! # Fully summed main cost on the actual Gram carrier

The local denominator is retained before taking the arithmetic mean. In
particular neither the D' term nor span/q is discarded. No joint-arithmetic
bound is assumed: its constants come from the proved restricted mean.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- Local analytic factor, with both completion terms and the dyadic modulus. -/
def wGramDirectMainCostFactor (κ C : ℝ) (a : ℤ) (R S : ℝ)
    (K : WExtractedKey) (j cap : Fin 5 → ℕ) : ℝ :=
  C * (a.natAbs.divisors.card : ℝ) *
    ((K.D' : ℝ) + ((wKSectionGridUpper R S K j cap + 1 : ℕ) : ℝ) /
      (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ)) *
    (2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
      2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) ^ (1 / 2 + κ : ℝ)

theorem wGramDirectMainCostFactor_nonneg {C : ℝ} (hC : 0 ≤ C)
    (κ : ℝ) (a : ℤ) (R S : ℝ) (K : WExtractedKey) (j cap : Fin 5 → ℕ) :
    0 ≤ wGramDirectMainCostFactor κ C a R S K j cap := by
  unfold wGramDirectMainCostFactor
  positivity

/-- Pointwise cost extraction uses actual occupied dyadic coordinates. -/
theorem wGramDirectMain_cost_le
    {κ C : ℝ} (hκ : 0 ≤ κ) (hC : 0 ≤ C)
    {N : Finset ℕ} (hN : ∀ n ∈ N, 0 < n)
    {F : ℕ} (hNF : ∀ n ∈ N, n ≤ F)
    {a : ℤ} {x η R S M Z : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S)
    (hM : 0 < M) (hZ : 0 < Z) {K : WExtractedKey} {b : ℕ}
    {j cap : Fin 5 → ℕ} {positive : Bool} {c : Finset (ℕ × ℕ)}
    {L : WGramLabel}
    (hL : L ∈ wGramLabels (wCoprimeFiber x N S
      (wGramPrefix N a x η R S M Z K b j cap positive) c)) :
    wGramFouvryCost κ C a R S M Z K j cap L ≤
      wGramDirectMainCostFactor κ C a R S K j cap *
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ) := by
  obtain ⟨hn, _, _, hs, hs', _, _⟩ :=
    wGramMainJointCarrier_scale_data hN hNF hR hS hM hZ hL
  have hr := mem_Ioc.mp (wGramLabels_r_mem_dyadic hN hL)
  have hrlo : 2 ^ j 3 ≤ L.1.1 := by
    have : 0 < (2 : ℕ) ^ j 3 := by positivity
    omega
  have hqlo : (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ) ≤
      wGramModulus L :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (mem_Ico.mp hn).1 hrlo)
      (mem_Ico.mp hs).1) (mem_Ico.mp hs').1
  have hqhi : wGramModulus L ≤
      2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) * 2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (mem_Ico.mp hn).2.le hr.2)
      (mem_Ico.mp hs).2.le) (mem_Ico.mp hs').2.le
  have hspan : (wGramSpan R S M Z K j cap L : ℝ) ≤
      (wKSectionGridUpper R S K j cap + 1 : ℕ) := by
    exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ _) 1
  have hd := div_le_div₀ (by positivity) hspan
    (show (0 : ℝ) < (2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ) by positivity)
    (show ((2 ^ j 2 * 2 ^ j 3 * 2 ^ j 4 * 2 ^ j 4 : ℕ) : ℝ) ≤
      wGramModulus L by exact_mod_cast hqlo)
  have he := Real.rpow_le_rpow (Nat.cast_nonneg (wGramModulus L))
    (show (wGramModulus L : ℝ) ≤
      (2 ^ (j 2 + 1) * (2 ^ (j 3 + 1) - 1) *
        2 ^ (j 4 + 1) * 2 ^ (j 4 + 1) : ℕ) by exact_mod_cast hqhi)
    (by linarith : 0 ≤ 1 / 2 + κ)
  unfold wGramFouvryCost wGramDirectMainCostFactor
  calc
    _ = (C * (a.natAbs.divisors.card : ℝ) *
        ((K.D' : ℝ) + (wGramSpan R S M Z K j cap L : ℝ) / (wGramModulus L : ℝ)) *
        (wGramModulus L : ℝ) ^ (1 / 2 + κ : ℝ)) *
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hd) (by positivity))
        he (by positivity) (by positivity)) (Real.sqrt_nonneg _)

/-- All main labels, including both ordered beta and frequency coordinates,
are summed. Constants precede the coefficient family and all scales. -/
theorem wGramDirectMain_weighted_cost_sum {δ : ℝ} (hδ : 0 < δ) :
    ∃ Cτ Cjoint : ℝ, 0 < Cτ ∧ 0 < Cjoint ∧
    ∀ (κ C : ℝ) (N : Finset ℕ) (F : ℕ) (a : ℤ) (x η R S M Z T : ℝ)
      (K : WExtractedKey) (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      0 ≤ κ → 0 ≤ C → a ≠ 0 → (∀ n ∈ N, 0 < n) → (∀ n ∈ N, n ≤ F) →
      0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → x ^ η < T →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      (∑ L ∈ wGramMainLabels K a (wCoprimeFiber x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c),
        |wGramWeight K β ζ L| * wGramFouvryCost κ C a R S M Z K j cap L) ≤
          ((Bβ * Bζ) ^ 2 * wGramDirectMainCostFactor κ C a R S K j cap) *
            wGramMainJointMean δ Cτ Cjoint a K F j := by
  obtain ⟨Cτ, Cjoint, hCτ, hCjoint, hmean⟩ := wGramMainJointCarrier_sqrt_sum hδ
  refine ⟨Cτ, Cjoint, hCτ, hCjoint, ?_⟩
  intro κ C N F a x η R S M Z T K b j cap positive c β ζ Bβ Bζ
    hκ hC ha hN hNF hR hS hM hZ hNT hgap hBβ hBζ hβ hζ
  let G := wGramMainLabels K a (wCoprimeFiber x N S
    (wGramPrefix N a x η R S M Z K b j cap positive) c)
  let A := (Bβ * Bζ) ^ 2 * wGramDirectMainCostFactor κ C a R S K j cap
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg _)
    (wGramDirectMainCostFactor_nonneg hC κ a R S K j cap)
  calc
    _ ≤ ∑ L ∈ G, A *
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ) := by
      apply sum_le_sum
      intro L hL
      have hlabel := (mem_filter.mp hL).1
      have hw := wGramWeight_abs_le_of_support hN hR hS hM hZ
        (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c)
        β ζ hBβ hBζ hβ hζ hlabel
      have hc := wGramDirectMain_cost_le hκ hC hN hNF hR hS hM hZ hlabel
      simpa only [A, mul_assoc] using mul_le_mul hw hc
        (wGramFouvryCost_nonneg hC κ a R S M Z K j cap L) (sq_nonneg _)
    _ = A * ∑ L ∈ G,
        Real.sqrt ((wGramModulus L).gcd (wGramNumerator K a L).natAbs : ℝ) :=
      (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hmean N F a x η R S M Z T K b j cap positive c
        ha hN hNF hR hS hM hZ hNT hgap) hA

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
