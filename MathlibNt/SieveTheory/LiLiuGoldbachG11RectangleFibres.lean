import MathlibNt.SieveTheory.LiLiuGoldbachG11RectangleCount
import MathlibNt.SieveTheory.LiLiuFouvryG9ProductFibreActual
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryZeroModeBound
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryTauPointwise

open Finset
open scoped BigOperators Classical
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Reuse the stronger order-one bound; this weaker order-two form fits the
already proved arbitrary weighted-fibre interface, including m=0. -/
theorem goldbachG11NormalizedProductCoefficient_le_tau_two (N m : ℕ) :
    0 ≤ goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m ∧
    goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
      ((N : ℝ)^(4/33 : ℝ)) m ≤ (fouvryTau 2 m : ℝ) := by
  refine ⟨goldbachG11NormalizedProductCoefficient_nonneg N m _ _,?_⟩
  have ha := (le_abs_self _).trans (goldbachG11NormalizedProductCoefficient_le_fouvryTau N m)
  by_cases hm : m = 0
  · subst m
    simpa only [fouvryTau, ArithmeticFunction.map_zero, Nat.cast_zero] using ha
  · rw [fouvryTau_order_one hm, Nat.cast_one] at ha
    exact ha.trans (by exact_mod_cast one_le_fouvryTau_succ 1 hm)

/-- Original labelled G11 multiplicities on the absolute-difference fibre.
Repeated factors, the zero output, and the overhanging negative side all remain. -/
theorem goldbachG11Rectangle_natAbs_fibre_le (N r : ℕ) (U V : Finset ℕ) :
    (∑ v ∈ U ×ˢ V, if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs = r then
      goldbachG11RectangleWeight N v else 0) ≤
      400*((fouvryTau 3 (N+r) : ℝ)+(fouvryTau 3 (N-r) : ℝ)) := by
  let α := goldbachG11NormalizedProductCoefficient N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ))
  let β := fun p => if p.Coprime N then primeSWBeta p else 0
  have h := fouvryG9_weighted_natAbs_fibre_le U V α β N r
    (fun m _ => goldbachG11NormalizedProductCoefficient_le_tau_two N m)
    (fun p _ => fouvryG9_prime_copN_beta_bounds N p)
  calc
    _ = 400*(∑ v ∈ U ×ˢ V, if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs = r then
        α v.1*β v.2 else 0) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro v _
      split_ifs
      · dsimp [goldbachG11RectangleWeight,α,β]
        rw [← goldbachG11NormalizedProductCoefficient_mul_four_hundred N v.1 _ _]
        ring
      · simp
    _ ≤ _ := mul_le_mul_of_nonneg_left h (by norm_num)

/-- Fixed subpower fibre bound, uniform over all finite rectangles of original G11 weights. -/
theorem goldbachG11Rectangle_fibres_subpower {κ : ℝ} (hκ : 0 < κ) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (N : ℕ) (U V : Finset ℕ) (r : ℕ), r ≤ 4*N →
      (∑ v ∈ U ×ˢ V, if ((N : ℤ)-(v.1 : ℤ)*v.2).natAbs = r then
        goldbachG11RectangleWeight N v else 0) ≤ 800*C₀*(5*(N : ℝ))^κ := by
  obtain ⟨C₀,hC₀,hτ⟩ := fouvryTau_le_const_rpow (k := 3) (by norm_num) hκ
  refine ⟨C₀,hC₀,?_⟩
  intro N U V r hr
  have hv : ∀ v : ℕ, v ≤ 5*N → (fouvryTau 3 v : ℝ) ≤ C₀*(5*(N : ℝ))^κ := by
    intro v hv
    by_cases hz : v = 0
    · subst v
      simp only [fouvryTau, ArithmeticFunction.map_zero, Nat.cast_zero]
      positivity
    · exact (hτ v (Nat.pos_of_ne_zero hz)).trans
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg v) (by exact_mod_cast hv) hκ.le) hC₀.le)
  have h1 := hv (N+r) (by omega)
  have h2 := hv (N-r) (by omega)
  have hf := goldbachG11Rectangle_natAbs_fibre_le N r U V
  nlinarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig