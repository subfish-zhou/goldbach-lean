import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryGramResonanceBound

/-!
# Consuming the occupied resonance count in the original whole energy

These endpoints retain the original full-level prefix, both paid floor
cutoffs, the common first beta coordinate and every ordered-pair multiplicity.
The nonzero-numerator Fouvry sum is unchanged. No weak-Weil estimate is used
on zero numerators, and no cancellation of the small-root product is asserted.

The support gap is proved from `x>1`, `eta<epsilonSupport` and
`x^epsilonSupport≤T`; positivity of the beta carrier is also derived.
The remaining base sum and nonzero sum still require analytic aggregation.
This is not the complete C.2 estimate.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

private theorem beta_positive
    {N : Finset ℕ} {x εSupport T : ℝ} (hx : 1 < x)
    (hSupport : x ^ εSupport ≤ T) (hNT : ∀ n ∈ N, T ≤ (n : ℝ)) :
    ∀ n ∈ N, 0 < n := by
  intro n hn
  have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hx) εSupport
  have hnreal := hp.trans_le (hSupport.trans (hNT n hn))
  exact_mod_cast hnreal

/-- Coefficient-dependent divisor majorant for the actual whole energy,
without any assumptions on the size of beta or zeta. -/
theorem wSeparatedCorrelationEnergy_resonance_divisors {κ : ℝ} (hκ : 0 < κ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z T εSupport : ℝ) (K : WExtractedKey)
      (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → 1 < x → η < εSupport → x ^ εSupport ≤ T →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c K β ζ a ≤
        (2 ^ j 1 : ℕ) *
          (∑ v ∈ wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
              (wGramPrefix N a x η R S M Z K b j cap positive) c)),
            wGramResonanceDivisorMass K β ζ v) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| * wGramFouvryCost κ C a R S M Z K j cap L := by
  obtain ⟨C, hC, henergy⟩ := wSeparatedCorrelationEnergy_fouvry hκ
  refine ⟨C, hC, ?_⟩
  intro N a x η R S M Z T εSupport K b j cap positive c β ζ
    ha hR hS hM hZ hNT hx hη hSupport
  have hN := beta_positive hx hSupport hNT
  have hT := iv3_resonance_support_gap hx hη hSupport
  have hzero := wGramZeroLabels_sum_le_divisor_mass hN ha hR hS hM hZ hNT hT
    (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c)
    j cap positive c β ζ
  exact (henergy N a x η R S M Z K b j cap positive c β ζ hN ha hR hS hM hZ).trans
    (add_le_add hzero le_rfl)

/-- Uniform quantitative consumption of the proved occupied fiber count.
The zero mass is `(Bbeta*Bzeta)^2 * 2^(j 1) * Czero * sum A^(2ε) B^ε`,
with the exact local `A=|h*n₂'*s'|`, `B=d₁*n₁+A`. -/
theorem wSeparatedCorrelationEnergy_resonance_local
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ Czero Cnonzero : ℝ, 0 < Czero ∧ 0 < Cnonzero ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x η R S M Z T εSupport : ℝ) (K : WExtractedKey)
      (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → 1 < x → η < εSupport → x ^ εSupport ≤ T →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x η R S M Z K b j cap positive) c K β ζ a ≤
        (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
          (∑ v ∈ wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
              (wGramPrefix N a x η R S M Z K b j cap positive) c)),
            wGramResonanceScale K ε v) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x η R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L := by
  obtain ⟨Czero, hCzero, hzero⟩ := wGramZeroLabels_sum_le_local_scales hε
  obtain ⟨Cnonzero, hCnonzero, henergy⟩ := wSeparatedCorrelationEnergy_fouvry hκ
  refine ⟨Czero, Cnonzero, hCzero, hCnonzero, ?_⟩
  intro N a x η R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hx hη hSupport hBβ hBζ hβ hζ
  have hN := beta_positive hx hSupport hNT
  have hT := iv3_resonance_support_gap hx hη hSupport
  have hz := hzero N a x η R S M Z T K b j cap positive c
    (wCoprimeFiber x N S (wGramPrefix N a x η R S M Z K b j cap positive) c)
    β ζ Bβ Bζ hN ha hR hS hM hZ hNT hT
    (wGramCoprimePrefix_subset N a x η R S M Z K b j cap positive c)
    hBβ hBζ hβ hζ
  exact (henergy N a x η R S M Z K b j cap positive c β ζ hN ha hR hS hM hZ).trans
    (add_le_add hz le_rfl)

/-- A concrete internal choice of the five-small exponent. No separate
support-gap premise remains when the support exponent is positive. -/
theorem wSeparatedCorrelationEnergy_resonance_half_support
    {ε κ : ℝ} (hε : 0 < ε) (hκ : 0 < κ) :
    ∃ Czero Cnonzero : ℝ, 0 < Czero ∧ 0 < Cnonzero ∧
    ∀ (N : Finset ℕ) (a : ℤ) (x R S M Z T εSupport : ℝ) (K : WExtractedKey)
      (b : ℕ) (j cap : Fin 5 → ℕ) (positive : Bool)
      (c : Finset (ℕ × ℕ)) (β ζ : ℕ → ℝ) (Bβ Bζ : ℝ),
      a ≠ 0 → 0 ≤ R → 0 ≤ S → 0 < M → 0 < Z →
      (∀ n ∈ N, T ≤ (n : ℝ)) → 1 < x → 0 < εSupport → x ^ εSupport ≤ T →
      0 ≤ Bβ → 0 ≤ Bζ →
      (∀ n ∈ N, |β n| ≤ Bβ) → (∀ s ∈ Ioc 0 ⌊S⌋₊, |ζ s| ≤ Bζ) →
      wSeparatedCorrelationEnergy x N S
        (wGramPrefix N a x (εSupport / 2) R S M Z K b j cap positive) c K β ζ a ≤
        (Bβ * Bζ) ^ 2 * (2 ^ j 1 : ℕ) * Czero *
          (∑ v ∈ wGramResonanceBases (wGramZeroLabels K a (wCoprimeFiber x N S
              (wGramPrefix N a x (εSupport / 2) R S M Z K b j cap positive) c)),
            wGramResonanceScale K ε v) +
        ∑ L ∈ (wGramLabels (wCoprimeFiber x N S
            (wGramPrefix N a x (εSupport / 2) R S M Z K b j cap positive) c)).filter
              (fun L => wGramNumerator K a L ≠ 0),
          |wGramWeight K β ζ L| *
            wGramFouvryCost κ Cnonzero a R S M Z K j cap L := by
  obtain ⟨Czero, Cnonzero, hCzero, hCnonzero, hbound⟩ :=
    wSeparatedCorrelationEnergy_resonance_local hε hκ
  refine ⟨Czero, Cnonzero, hCzero, hCnonzero, ?_⟩
  intro N a x R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hx hSupportPos hSupport hBβ hBζ hβ hζ
  exact hbound N a x (εSupport / 2) R S M Z T εSupport K b j cap positive c β ζ Bβ Bζ
    ha hR hS hM hZ hNT hx (by linarith) hSupport hBβ hBζ hβ hζ

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
