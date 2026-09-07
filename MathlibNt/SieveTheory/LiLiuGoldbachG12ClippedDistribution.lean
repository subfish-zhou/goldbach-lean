import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedGeometry
noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

def residual (N : ℕ) (g L U : ℕ → ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
    g m *
      (((primesInAP ⌊U m⌋₊ d (natInvMod d m * b % d) : ℝ) -
          (primesInAP ⌊L m⌋₊ d (natInvMod d m * b % d) : ℝ)) -
        (PanPrincipal.primeCount ⌊U m⌋₊ -
          PanPrincipal.primeCount ⌊L m⌋₊) / (d.totient : ℝ))

theorem residual_eq_prefix_sub {N : ℕ}
    (hN : 2 ≤ N) {ε : ℝ} {g L U : ℕ → ℝ}
    (h : Admissible N ε g L U) (d b : ℕ) :
    residual N g L U d b =
      primeCenteredAPSum (goldbachG12ActiveProductSupport N)
        (g) (U) d b -
      primeCenteredAPSum (goldbachG12ActiveProductSupport N)
        (g) (L) d b := by
  have hpos : ∀ m ∈ goldbachG12ActiveProductSupport N, 0 < m := by
    intro m hm
    exact (goldbachG12ActiveProductSupport_data hm).1
  have hlo := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    (endpoint_nonneg hN h hm).1
  have hhi := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    (endpoint_nonneg hN h hm).2
  rw [primeCenteredAPSum_eq_inverse _ _ _ _ _ hpos hhi,
    primeCenteredAPSum_eq_inverse _ _ _ _ _ hpos hlo]
  simp only [residual, sum_filter, realPrimeCount,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  by_cases hmd : m.Coprime d
  · simp only [if_pos hmd]
    ring
  · simp only [if_neg hmd, sub_zero]

/-- A single source witness pays for both complete prefixes, uniformly in epsilon. -/
theorem residual_weighted (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (g L U : ℕ → ℝ) (ε : ℝ) (Q : ℕ) (b : ℕ → ℕ),
      Admissible N ε g L U →
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |residual N g L U d (b d)|) ≤
          C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, M, hsource⟩ :=
    balanced_common_profile_primeCentered_natural A (4 / 53) 1 hA
      (by norm_num) (by norm_num)
  have hgrowth : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (4 / 53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hgrowth
  refine ⟨B, 2 * C, hB, by positivity, max 4 (max M K), le_max_left _ _, ?_⟩
  intro N hN g L U ε Q b had hQ hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hNM : M ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hz := hK N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hS := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    goldbachG12Linked_balanced_support hm
  have hprofiles := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    goldbachG12Linked_profiles_and_coefficient (ε := ε) hN2 hz hm
  have hf : ∀ m ∈ goldbachG12ActiveProductSupport N, |g m| ≤ 1 := by
    intro m hm
    rw [abs_of_nonneg (had m hm).1.1]
    exact (had m hm).1.2.trans (goldbachG12NormalizedCoefficient_bounds N m).2
  have hrL : ∀ m ∈ goldbachG12ActiveProductSupport N,
      2 ≤ L m ∧ (m : ℝ) * L m ≤ N := by
    intro m hm
    exact ⟨(hprofiles m hm).2.1.1.trans (had m hm).2.1,
      (mul_le_mul_of_nonneg_left ((had m hm).2.2.1.trans (had m hm).2.2.2)
        (Nat.cast_nonneg m)).trans (hprofiles m hm).1.2⟩
  have hrU : ∀ m ∈ goldbachG12ActiveProductSupport N,
      2 ≤ U m ∧ (m : ℝ) * U m ≤ N := by
    intro m hm
    exact ⟨(hrL m hm).1.trans (had m hm).2.2.1,
      (mul_le_mul_of_nonneg_left (had m hm).2.2.2
        (Nat.cast_nonneg m)).trans (hprofiles m hm).1.2⟩
  have hhi := hsource N hNM Q (goldbachG12ActiveProductSupport N)
    g U b hQ hS hf hrU hb
  have hlo := hsource N hNM Q (goldbachG12ActiveProductSupport N)
    g L b hQ hS hf hrL hb
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (|primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (g) (U) d (b d)| +
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (g) (L) d (b d)|) := by
      apply sum_le_sum
      intro d _
      rw [residual_eq_prefix_sub hN2 had]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (wuModulusWeight_nonneg d)
    _ = (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (g) (U) d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (g) (L) d (b d)| := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ C * N / Real.log (N : ℝ) ^ A + C * N / Real.log (N : ℝ) ^ A :=
      add_le_add hhi hlo
    _ = (2 * C) * N / Real.log (N : ℝ) ^ A := by ring

/-- Unweighting is restricted to squarefree moduli; the on-carrier residue stays N. -/
theorem residual_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (g L U : ℕ → ℝ) (ε : ℝ) (Q : ℕ),
      Admissible N ε g L U →
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q,
        |residual N g L U d N|) ≤
          C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hN₀, hbound⟩ :=
    residual_weighted A hA
  refine ⟨B, C, hB, hC, N₀, hN₀, ?_⟩
  intro N hN g L U ε Q had hQ
  have h := hbound N hN g L U ε Q (goldbachG11LinkedCompletedResidue N) had hQ
    (fun d _ => goldbachG11LinkedCompletedResidue_coprime N d)
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q, wuModulusWeight d *
        |residual N g L U d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_, hsq, hcop⟩ := mem_filter.mp hd
      rw [goldbachG11LinkedCompletedResidue_eq hcop]
      exact le_mul_of_one_le_left (abs_nonneg _) (goldbachG11Linked_one_le_weight hsq)
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |residual N g L U d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro d _ _
        exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ C * N / Real.log (N : ℝ) ^ A := h

end G12ClippedWindow
