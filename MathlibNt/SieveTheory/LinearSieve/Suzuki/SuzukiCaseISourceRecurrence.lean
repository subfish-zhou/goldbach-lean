import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIEndpointBridge

open scoped Classical BigOperators
open Finset

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

/-- A source layer can be extended from its literal outer carrier to every
supported outer prime when the odd cubic cutoff is known pointwise.  Terms
failing the lower cutoff vanish by source support, so no global `z^n ≤ D`
condition is needed. -/
theorem suzukiSourceV_eq_recurrence_of_supported_cube
    (S : BoundingSieve) {n D z : ℕ} (hn : 2 ≤ n)
    (hcube : Odd n → ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D) :
    suzukiSourceV S n D z =
      ∑ p ∈ suzukiSupportedBelow S z,
        S.nu p * suzukiSourceV S (n - 1) (D ⌈/⌉ p) p := by
  classical
  have hpred : 0 < n - 1 := by omega
  have hnrepr : n - 1 + 1 = n := by omega
  rw [← hnrepr, suzukiSourceV_succ_of_pos S hpred]
  apply sum_subset
  · intro p hp
    exact (mem_filter.mp hp).1
  · intro p hpfull hpsource
    have hpP : p ∈ S.prodPrimes.primeFactors := (mem_filter.mp hpfull).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpP
    have hp0 : 0 < p := hpprime.pos
    have hnotPred : ¬ (D ≤ p ^ ((n - 1 + 1) + 2) ∧
        (Odd (n - 1 + 1) → p ^ 3 < D)) := by
      intro hpreds
      apply hpsource
      exact mem_filter.mpr ⟨hpfull, hpreds⟩
    have hlowerFail : ¬ D ≤ p ^ (n + 2) := by
      intro hlower
      apply hnotPred
      refine ⟨?_, ?_⟩
      · simpa [hnrepr] using hlower
      · intro hnodd
        exact hcube (by simpa [hnrepr] using hnodd) p hpfull
    have hzero : suzukiSourceV S (n - 1) (D ⌈/⌉ p) p = 0 := by
      apply suzukiSourceV_inner_eq_zero_of_outer_lower_fails S (by omega) hp0
      simpa [show n - 1 + 3 = n + 2 by omega] using hlowerFail
    rw [hzero, mul_zero]

/-- For odd `N`, the selected source indices are the base index one together
with successors of all predecessor-parity indices. -/
theorem sourceParityIndices_odd_eq_insert_image_pred
    {N : ℕ} (hN : Odd N) :
    sourceParityIndices N =
      insert 1 ((sourceParityIndices (N - 1)).image (fun m => m + 1)) := by
  classical
  ext n
  simp only [sourceParityIndices, mem_filter, mem_Icc, mem_insert, mem_image]
  have hN1 : 1 ≤ N := by
    obtain ⟨k, rfl⟩ := hN
    omega
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hpar⟩
    by_cases hn : n = 1
    · exact Or.inl hn
    · right
      refine ⟨n - 1, ?_, by omega⟩
      constructor
      · constructor <;> omega
      · have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
        omega
  · rintro (rfl | ⟨m, ⟨⟨hm1, hmN⟩, hmpar⟩, rfl⟩)
    · exact ⟨⟨le_rfl, hN1⟩, by simpa using (Nat.odd_iff.mp hN).symm⟩
    · constructor
      · constructor <;> omega
      · have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
        omega

/-- Direct source-faithful parity recurrence at an odd endpoint.  It expands
`suzukiSourceV` itself and retains source layers on the right; it never passes
through `section14ExtendedT`. -/
theorem suzukiSourceParitySum_recurrence_of_odd_of_supported_cube
    (S : BoundingSieve) {N D z : ℕ} (hN : Odd N)
    (hcube : ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      ∑ p ∈ suzukiSupportedBelow S z, S.nu p *
        (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p) := by
  classical
  rw [sourceParityIndices_odd_eq_insert_image_pred hN, sum_insert]
  · have hbase : suzukiSourceV S 1 D z = 0 := by
      rw [suzukiSourceV_one]
      apply sum_eq_zero
      intro p hp
      have hpfull : p ∈ suzukiSupportedBelow S z := (mem_filter.mp hp).1
      exact False.elim ((Nat.not_lt_of_ge (mem_filter.mp hp).2) (hcube p hpfull))
    rw [hbase, zero_add]
    rw [sum_image]
    · apply Eq.trans (sum_congr rfl (fun n hn =>
        suzukiSourceV_eq_recurrence_of_supported_cube S (by
          simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
          omega) (fun _ p hp => hcube p hp)))
      rw [sum_comm]
      simp_rw [mul_sum, Nat.add_sub_cancel]
    · intro a ha b hb hab
      exact Nat.add_right_cancel hab
  · simp only [mem_image]
    rintro ⟨m, hm, h⟩
    simp only [sourceParityIndices, mem_filter, mem_Icc] at hm
    omega

/-- At an even endpoint there is no exceptional base index: every selected
source index is the successor of a uniquely selected predecessor index. -/
theorem sourceParityIndices_even_eq_image_pred
    {N : ℕ} (hN : Even N) (hN2 : 2 ≤ N) :
    sourceParityIndices N =
      (sourceParityIndices (N - 1)).image (fun m => m + 1) := by
  classical
  ext n
  simp only [sourceParityIndices, mem_filter, mem_Icc, mem_image]
  have hNeven : N % 2 = 0 := Nat.even_iff.mp hN
  constructor
  · rintro ⟨⟨hn1, hnN⟩, hpar⟩
    have hn2 : 2 ≤ n := by omega
    refine ⟨n - 1, ?_, by omega⟩
    constructor
    · constructor <;> omega
    · omega
  · rintro ⟨m, ⟨⟨hm1, hmN⟩, hmpar⟩, rfl⟩
    constructor
    · constructor <;> omega
    · omega

/-- Direct source-faithful parity recurrence at an even endpoint.  All selected
layers have even index, so neither the odd cubic side condition nor a base
layer condition is needed. -/
theorem suzukiSourceParitySum_recurrence_of_even
    (S : BoundingSieve) {N D z : ℕ} (hN : Even N) (hN2 : 2 ≤ N) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      ∑ p ∈ suzukiSupportedBelow S z, S.nu p *
        (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p) := by
  classical
  rw [sourceParityIndices_even_eq_image_pred hN hN2, sum_image]
  · apply Eq.trans (sum_congr rfl (fun n hn =>
      suzukiSourceV_eq_recurrence_of_supported_cube S (by
        simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
        omega) (by
          intro hnodd
          simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
          have hNeven : N % 2 = 0 := Nat.even_iff.mp hN
          have hnEven : (n + 1) % 2 = 0 := by omega
          exact False.elim ((Nat.not_even_iff_odd.mpr hnodd)
            (Nat.even_iff.mpr hnEven)))))
    rw [sum_comm]
    simp_rw [mul_sum, Nat.add_sub_cancel]
  · intro a ha b hb hab
    exact Nat.add_right_cancel hab

/-- The exact Case-I recurrence for either parity.  `hbase` is required only
when the parity domain contains the exceptional source layer `V₁`; `hcube` is
required only for odd non-base layers.  Thus even endpoints carry no artificial
cubic or base hypothesis. -/
theorem suzukiSourceParitySum_recurrence
    (S : BoundingSieve) {N D z : ℕ} (hN2 : 2 ≤ N)
    (hbase : Odd N → suzukiSourceV S 1 D z = 0)
    (hcube : ∀ n ∈ sourceParityIndices N, 2 ≤ n → Odd n →
      ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      ∑ p ∈ suzukiSupportedBelow S z, S.nu p *
        (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p) := by
  rcases Nat.even_or_odd N with hN | hN
  · exact suzukiSourceParitySum_recurrence_of_even S hN hN2
  · classical
    rw [sourceParityIndices_odd_eq_insert_image_pred hN, sum_insert]
    · rw [hbase hN, zero_add, sum_image]
      · apply Eq.trans (sum_congr rfl (fun n hn =>
          suzukiSourceV_eq_recurrence_of_supported_cube S (by
            simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
            omega) (by
              intro _ p hp
              apply hcube (n + 1)
              · simp only [sourceParityIndices, mem_filter, mem_Icc] at hn ⊢
                have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
                omega
              · simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
                omega
              · exact Nat.odd_iff.mpr (by
                  simp only [sourceParityIndices, mem_filter, mem_Icc] at hn
                  have hNodd : N % 2 = 1 := Nat.odd_iff.mp hN
                  omega)
              · exact hp)))
        rw [sum_comm]
        simp_rw [mul_sum, Nat.add_sub_cancel]
      · intro a ha b hb hab
        exact Nat.add_right_cancel hab
    · simp only [mem_image]
      rintro ⟨m, hm, h⟩
      simp only [sourceParityIndices, mem_filter, mem_Icc] at hm
      omega

/-- The source-reviewed Case-I value
`τ = max(s, (1 - log 2 / log D)⁻¹)`. -/
noncomputable def caseITau (D s : ℝ) : ℝ :=
  max s (1 - Real.log 2 / Real.log D)⁻¹

/-- Exact real cutoff data used in the three-range Case-I split.  Besides the
ordering needed for a partition, this records the source identity
`D^(1/τ) = min(z,D/2)` rather than replacing real cutoffs by rounded naturals. -/
structure CaseIThreeRangeDomain (D z : ℕ) (σ s : ℝ) : Prop where
  sigmaCut_le_tauCut :
    (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / caseITau (D : ℝ) s)
  tauCut_eq_min :
    (D : ℝ) ^ (1 / caseITau (D : ℝ) s) =
      min (z : ℝ) ((D : ℝ) / 2)

/-- Any sum on the supported natural-prime carrier splits exactly into the
three source ranges `Σ₀`, `Σ₁`, `Σ₂`.  The inequalities are predicates in
`ℝ`; no floor/ceiling surrogate is introduced. -/
theorem sum_supported_eq_caseI_three_ranges
    (S : BoundingSieve) {D z : ℕ} {σ s : ℝ}
    (hdom : CaseIThreeRangeDomain D z σ s) (f : ℕ → ℝ) :
    (∑ p ∈ suzukiSupportedBelow S z, f p) =
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)), f p) +
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
            (p : ℝ) < (D : ℝ) ^ (1 / caseITau (D : ℝ) s)), f p) +
      ∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / caseITau (D : ℝ) s) ≤ (p : ℝ)), f p := by
  classical
  let a : ℝ := (D : ℝ) ^ (1 / σ)
  let b : ℝ := (D : ℝ) ^ (1 / caseITau (D : ℝ) s)
  have hab : a ≤ b := hdom.sigmaCut_le_tauCut
  let P := suzukiSupportedBelow S z
  have houter :
      P.filter (fun p : ℕ => ¬ (p : ℝ) < b) =
        P.filter (fun p : ℕ => b ≤ (p : ℝ)) := by
    ext p
    simp only [mem_filter, not_lt]
  have hleft :
      (P.filter (fun p : ℕ => (p : ℝ) < b)).filter
          (fun p : ℕ => (p : ℝ) < a) =
        P.filter (fun p : ℕ => (p : ℝ) < a) := by
    ext p
    simp only [mem_filter]
    constructor
    · rintro ⟨⟨hpP, _⟩, hpa⟩
      exact ⟨hpP, hpa⟩
    · rintro ⟨hpP, hpa⟩
      exact ⟨⟨hpP, lt_of_lt_of_le hpa hab⟩, hpa⟩
  have hmiddle :
      (P.filter (fun p : ℕ => (p : ℝ) < b)).filter
          (fun p : ℕ => ¬ (p : ℝ) < a) =
        P.filter (fun p : ℕ => a ≤ (p : ℝ) ∧ (p : ℝ) < b) := by
    ext p
    simp only [mem_filter, not_lt]
    tauto
  change (∑ p ∈ P, f p) = _
  rw [← sum_filter_add_sum_filter_not P (fun p : ℕ => (p : ℝ) < b), houter]
  rw [← sum_filter_add_sum_filter_not
    (P.filter (fun p : ℕ => (p : ℝ) < b)) (fun p : ℕ => (p : ℝ) < a),
    hleft, hmiddle]

/-- Source-faithful Case-I recurrence followed by the exact `Σ₀+Σ₁+Σ₂`
partition at the real cutoffs from pages 85--86. -/
theorem suzukiSourceParitySum_recurrence_three_ranges
    (S : BoundingSieve) {N D z : ℕ} {σ s : ℝ} (hN2 : 2 ≤ N)
    (hbase : Odd N → suzukiSourceV S 1 D z = 0)
    (hcube : ∀ n ∈ sourceParityIndices N, 2 ≤ n → Odd n →
      ∀ p ∈ suzukiSupportedBelow S z, p ^ 3 < D)
    (hdom : CaseIThreeRangeDomain D z σ s) :
    (∑ n ∈ sourceParityIndices N, suzukiSourceV S n D z) =
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (p : ℝ) < (D : ℝ) ^ (1 / σ)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) +
      (∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) ∧
            (p : ℝ) < (D : ℝ) ^ (1 / caseITau (D : ℝ) s)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p)) +
      ∑ p ∈ (suzukiSupportedBelow S z).filter
          (fun p : ℕ => (D : ℝ) ^ (1 / caseITau (D : ℝ) s) ≤ (p : ℝ)),
        S.nu p * (∑ m ∈ sourceParityIndices (N - 1),
          suzukiSourceV S m (D ⌈/⌉ p) p) := by
  rw [suzukiSourceParitySum_recurrence S hN2 hbase hcube]
  exact sum_supported_eq_caseI_three_ranges S hdom _


end MathlibNt.SieveTheory
