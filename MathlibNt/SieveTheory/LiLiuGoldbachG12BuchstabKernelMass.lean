import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG12BuchstabUpperMass

open Finset Set LiLiuPrereqBuchstab
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

theorem goldbachG12PrimeKernel_buchstabGeometry {N : ℕ} (hN : 4 ≤ N)
    {v : GoldbachG11Label}
    (hv : v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) :
    Real.log ((N : ℝ)/goldbachG11LabelProd v)/Real.log (v.2.2.2 : ℝ) ∈
      Icc (3 : ℝ) (1141/132) := by
  rcases v with ⟨t,s,r,q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ)) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ)^(4/53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG12Labels, Finset.mem_sigma] using hv
  exact goldbachG12_canonical_logQuotient_bounds (by omega) hm.1 hm.2.1 hm.2.2.1 hm.2.2.2

/-- Only the raw pointwise Buchstab bound is supplied by the caller. -/
theorem goldbachG12BuchstabUpperMass_le_primeKernel
    {N : ℕ} (hN : 4 ≤ N) (η W : ℝ) (_hη : 0 ≤ η)
    (hW : ∀ u ∈ Icc (3 : ℝ) (1141/132), buchstab u ≤ W) :
    (Real.log (N : ℝ) / N) * goldbachG12BuchstabUpperMass N η ≤
      (W + η) * goldbachG12PrimeKernel (fun _ => 1) N := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  unfold goldbachG12BuchstabUpperMass goldbachG12PrimeKernel
  rw [mul_sum, mul_sum]
  apply sum_le_sum
  intro v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN hv
  have hprod : (goldbachG11LabelProd v : ℝ) ≠ 0 := by
    exact_mod_cast (goldbachG11LabelProd_pos (goldbachG12Labels_subset_goldbachG11Labels _ _ _ _ hv)).ne'
  have hterm :
      Real.log (N : ℝ) / N *
          (goldbachG11BuchstabMass ((N : ℝ) / goldbachG11LabelProd v) v.2.2.2 +
            η * ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ)) =
        (buchstab (Real.log ((N : ℝ) / goldbachG11LabelProd v) /
          Real.log (v.2.2.2 : ℝ)) + η) *
          (Real.log (N : ℝ) / ((goldbachG11LabelProd v : ℝ) *
            Real.log (v.2.2.2 : ℝ))) := by
    unfold goldbachG11BuchstabMass
    field_simp
  rw [hterm, one_mul]
  exact mul_le_mul_of_nonneg_right (add_le_add (hW _ (goldbachG12PrimeKernel_buchstabGeometry hN hv)) le_rfl)
    (div_nonneg hlogN (mul_nonneg (Nat.cast_nonneg _) hg.2.le))

theorem goldbachG12BuchstabUpperMass_eventually_nonneg (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, 0 ≤ goldbachG12BuchstabUpperMass N η := by
  obtain ⟨N₀,hN₀,hh⟩ := goldbachG12FullRoughMass_le_buchstabUpper η hη
  refine ⟨N₀,hN₀,fun N hN => ?_⟩
  exact (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)).trans (hh N hN)

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
