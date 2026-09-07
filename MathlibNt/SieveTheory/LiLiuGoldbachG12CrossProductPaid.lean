import MathlibNt.SieveTheory.LiLiuGoldbachG12CrossProduct
import MathlibNt.SieveTheory.LiLiuGoldbachQuadrupleExceptionBudget

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Exact good cross count after grouping by its true product coefficient. -/
noncomputable def goldbachG12ProductPrimeTotal (N : ℕ) (ε z b c : ℝ) : ℤ :=
  ∑ m ∈ goldbachG12ProductSupport N z b c,
    (goldbachG12ProductCoefficient N z b c m : ℤ) *
      (goldbachG11ProductFirstPrimeFiber N ε z m).card

/-- An additional, explicitly paid exception budget for the good-body switch.
Only the bad part is enlarged; the surviving product sum remains on the cross. -/
theorem goldbachG12_roughSum_le_productPrime_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ ε : ℝ, 0 ≤ ε → ∀ b c : ℝ,
      ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
          goldbachG11RoughCount N ε v : ℤ) : ℝ) ≤
        (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) +
          δ*(SingularSeries.liuSingularSeries N*(N : ℝ)/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀,hN₀,hn⟩ := goldbachQuadruple_exceptions_normalized δ hδ
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε hε b c
  have hb := hn N hN ε hε c
  rw [Int.cast_add] at hb
  have hR : 0 ≤ ((∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
      goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v : ℤ) : ℝ) := by
    exact_mod_cast (Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _) :
      (0 : ℤ) ≤ ∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
        goldbachG11RSquareCount (goldbachDifferenceCarrier N ε) v)
  have hbad : (goldbachG12BadCrossTotal N ε ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) ≤
      ((∑ v ∈ goldbachG11Labels N ((N : ℝ)^(4/53 : ℝ)) c,
        goldbachG11NCount (goldbachDifferenceCarrier N ε) N v : ℤ) : ℝ) := by
    exact_mod_cast goldbachG12BadCrossTotal_le_NCount_sum N ε _ b c hε
  have hsplit := goldbachG12RoughSum_eq_good_add_bad N ε ((N : ℝ)^(4/53 : ℝ)) b c
  rw [goldbachG12GoodCrossTotal_eq_product_sum] at hsplit
  have heq : ((∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ)) b c,
      goldbachG11RoughCount N ε v : ℤ) : ℝ) =
      (goldbachG12ProductPrimeTotal N ε ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) +
      (goldbachG12BadCrossTotal N ε ((N : ℝ)^(4/53 : ℝ)) b c : ℝ) := by
    rw [← Int.cast_add]
    exact congrArg (fun n : ℤ => (n : ℝ)) hsplit
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
