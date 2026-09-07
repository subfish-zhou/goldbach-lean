import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve Wu2004MeanValue
noncomputable section

theorem goldbachG12Linked_balanced_support {N m : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (N : ℝ)^(4/53 : ℝ) ≤ (m : ℝ) ∧ (m : ℝ) ≤ (N : ℝ)^(1-(4/53 : ℝ)) := by
  have h := goldbachG12ActiveProductSupport_data hm
  exact ⟨h.2.2.2.1,by convert h.2.2.2.2.1 using 1; norm_num⟩

theorem goldbachG12Linked_profiles_and_coefficient {N m : ℕ} {ε : ℝ}
    (hN : 2 ≤ N) (hz : 2 ≤ (N : ℝ)^(4/53 : ℝ))
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (2 ≤ goldbachG11PiLiHi N m ∧ (m : ℝ)*goldbachG11PiLiHi N m ≤ N) ∧
    (2 ≤ goldbachG11PiLiLo N ε m ∧ (m : ℝ)*goldbachG11PiLiLo N ε m ≤ N) ∧
    |goldbachG12NormalizedCoefficient N m| ≤ 1 := by
  obtain ⟨hlo,horder,hhi⟩ := goldbachG12PiLiEndpoints_bounds hN hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (goldbachG12ActiveProductSupport_data hm).1
  have hh : (m : ℝ)*goldbachG11PiLiHi N m ≤ N := by
    simpa only [mul_comm] using (le_div_iff₀ hm0).mp hhi
  have hl : (m : ℝ)*goldbachG11PiLiLo N ε m ≤ N := by
    simpa only [mul_comm] using (le_div_iff₀ hm0).mp (horder.trans hhi)
  have ha := goldbachG12NormalizedCoefficient_bounds N m
  exact ⟨⟨hz.trans (hlo.trans horder),hh⟩,⟨hz.trans hlo,hl⟩,
    by rw [abs_of_nonneg ha.1]; exact ha.2⟩

def goldbachG12LinkedWindowResidual (N : ℕ) (ε : ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
    goldbachG12NormalizedCoefficient N m *
      (((primesInAP ⌊goldbachG11PiLiHi N m⌋₊ d (natInvMod d m * b % d) : ℝ) -
          (primesInAP ⌊goldbachG11PiLiLo N ε m⌋₊ d (natInvMod d m * b % d) : ℝ)) -
        (PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
          PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊) / (d.totient : ℝ))

theorem goldbachG12LinkedWindowResidual_eq_prefix_sub {N : ℕ}
    (hN : 2 ≤ N) (ε : ℝ) (d b : ℕ) :
    goldbachG12LinkedWindowResidual N ε d b =
      primeCenteredAPSum (goldbachG12ActiveProductSupport N)
        (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiHi N) d b -
      primeCenteredAPSum (goldbachG12ActiveProductSupport N)
        (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiLo N ε) d b := by
  have hpos : ∀ m ∈ goldbachG12ActiveProductSupport N, 0 < m := by
    intro m hm
    exact (goldbachG12ActiveProductSupport_data hm).1
  have hlo : ∀ m ∈ goldbachG12ActiveProductSupport N,
      0 ≤ goldbachG11PiLiLo N ε m := by
    intro m hm
    exact (Real.rpow_nonneg (Nat.cast_nonneg N) _).trans
      (goldbachG12PiLiEndpoints_bounds hN hm).1
  have hhi : ∀ m ∈ goldbachG12ActiveProductSupport N,
      0 ≤ goldbachG11PiLiHi N m := by
    intro m hm
    exact (hlo m hm).trans (goldbachG12PiLiEndpoints_bounds hN hm).2.1
  rw [primeCenteredAPSum_eq_inverse _ _ _ _ _ hpos hhi,
    primeCenteredAPSum_eq_inverse _ _ _ _ _ hpos hlo]
  simp only [goldbachG12LinkedWindowResidual, sum_filter, realPrimeCount,
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  by_cases hmd : m.Coprime d
  · simp only [if_pos hmd]
    ring
  · simp only [if_neg hmd, sub_zero]

/-- A single source witness pays for both complete prefixes, uniformly in epsilon. -/
theorem goldbachG12LinkedWindowResidual_weighted (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |goldbachG12LinkedWindowResidual N ε d (b d)|) ≤
          C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, M, hsource⟩ :=
    balanced_common_profile_primeCentered_natural A (4 / 53) 1 hA
      (by norm_num) (by norm_num)
  have hgrowth : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ (4 / 53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hgrowth
  refine ⟨B, 2 * C, hB, by positivity, max 4 (max M K), le_max_left _ _, ?_⟩
  intro N hN ε Q b hQ hb
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hNM : M ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hz := hK N ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hS := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    goldbachG12Linked_balanced_support hm
  have hprofiles := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    goldbachG12Linked_profiles_and_coefficient (ε := ε) hN2 hz hm
  have hf := fun m (hm : m ∈ goldbachG12ActiveProductSupport N) =>
    (hprofiles m hm).2.2
  have hhi := hsource N hNM Q (goldbachG12ActiveProductSupport N)
    (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiHi N) b
    hQ hS hf (fun m hm => (hprofiles m hm).1) hb
  have hlo := hsource N hNM Q (goldbachG12ActiveProductSupport N)
    (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiLo N ε) b
    hQ hS hf (fun m hm => (hprofiles m hm).2.1) hb
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (|primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiHi N) d (b d)| +
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiLo N ε) d (b d)|) := by
      apply sum_le_sum
      intro d _
      rw [goldbachG12LinkedWindowResidual_eq_prefix_sub hN2]
      exact mul_le_mul_of_nonneg_left (abs_sub _ _) (wuModulusWeight_nonneg d)
    _ = (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiHi N) d (b d)|) +
        ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |primeCenteredAPSum (goldbachG12ActiveProductSupport N)
          (goldbachG12NormalizedCoefficient N) (goldbachG11PiLiLo N ε) d (b d)| := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ C * N / Real.log (N : ℝ) ^ A + C * N / Real.log (N : ℝ) ^ A :=
      add_le_add hhi hlo
    _ = (2 * C) * N / Real.log (N : ℝ) ^ A := by ring

/-- Unweighting is restricted to squarefree moduli; the on-carrier residue stays N. -/
theorem goldbachG12LinkedWindowResidual_squarefree (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q,
        |goldbachG12LinkedWindowResidual N ε d N|) ≤
          C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hN₀, hbound⟩ :=
    goldbachG12LinkedWindowResidual_weighted A hA
  refine ⟨B, C, hB, hC, N₀, hN₀, ?_⟩
  intro N hN ε Q hQ
  have h := hbound N hN ε Q (goldbachG11LinkedCompletedResidue N) hQ
    (fun d _ => goldbachG11LinkedCompletedResidue_coprime N d)
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q, wuModulusWeight d *
        |goldbachG12LinkedWindowResidual N ε d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_, hsq, hcop⟩ := mem_filter.mp hd
      rw [goldbachG11LinkedCompletedResidue_eq hcop]
      exact le_mul_of_one_le_left (abs_nonneg _) (goldbachG11Linked_one_le_weight hsq)
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |goldbachG12LinkedWindowResidual N ε d (goldbachG11LinkedCompletedResidue N d)| := by
      apply sum_le_sum_of_subset_of_nonneg
      · exact filter_subset _ _
      · intro d _ _
        exact mul_nonneg (wuModulusWeight_nonneg d) (abs_nonneg _)
    _ ≤ C * N / Real.log (N : ℝ) ^ A := h

theorem goldbachG12LinkedWindowResidual_epsilon_one (N d b : ℕ) :
    goldbachG12LinkedWindowResidual N 1 d b = 0 := by
  simp only [goldbachG12LinkedWindowResidual, goldbachG11PiLiLo_one, sub_self,
    zero_div, mul_zero, sum_const_zero]

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig