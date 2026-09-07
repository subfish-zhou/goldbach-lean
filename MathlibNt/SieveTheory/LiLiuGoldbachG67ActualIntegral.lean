import MathlibNt.SieveTheory.LiLiuGoldbachIdealPairKernel
import MathlibNt.SieveTheory.LiLiuGoldbachG67KernelQuadrature

open scoped BigOperators Interval NNReal
open Finset
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open LiLiuGoldbachIdealPairKernel
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle

noncomputable def goldbachG67JRIntegral (τ : ℝ) : ℝ :=
  (1/2 : ℝ)*(∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/53 : ℝ)..(4/33 : ℝ),
    kernel τ (u,v)/(u*v)) +
  (∫ u in (4/53 : ℝ)..(4/33 : ℝ), ∫ v in (4/33 : ℝ)..(3/11 : ℝ), kernel τ (u,v)/(u*v))

noncomputable def goldbachG67LogRectangleMass : ℝ :=
  (1/2 : ℝ)*logarithmicRectangleMass (4/53) (4/33) (4/53) (4/33) +
    logarithmicRectangleMass (4/53) (4/33) (4/33) (3/11)

noncomputable def goldbachG67IntegralConstant : ℝ :=
  (53/(2*Real.exp Real.eulerMascheroniConstant))*goldbachG67JRIntegral 0

theorem goldbachJRKernel_symmetric (τ u v : ℝ) : kernel τ (u,v) = kernel τ (v,u) := by
  unfold kernel
  rw [show (1/2 : ℝ)-u-v = 1/2-v-u by ring]

/-- Pointwise passage keeps the actual totient, including its square diagonal. -/
theorem goldbachPairKernelSum_le_ideal (N : ℕ) (τ : ℝ) (T : Finset (ℕ × ℕ))
    (hT : ∀ p ∈ T, 0 < p.1 ∧ 0 < p.2) :
    goldbachPairKernelSum N (kernel τ) T ≤ goldbachPairIdealSum N τ T := by
  apply Finset.sum_le_sum
  intro p hp
  exact kernel_div_product_le N τ (hT p hp).1 (hT p hp).2

/-- Actual JR kernel and actual original pair sums, with a common threshold. -/
theorem goldbachG67JRIntegral_lower (τ η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG67JRIntegral τ - η ≤
        goldbachPairIdealSum N τ (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
        goldbachPairIdealSum N τ (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) := by
  obtain ⟨N₀,hN₀,hn⟩ := exists_goldbachG67_kernel_integral_lower
    (a := 4/53) (b := 4/33) (c := 3/11) (by norm_num) (by norm_num) (by norm_num)
    (kernel_lipschitz τ) (kernel_nonneg τ) (goldbachJRKernel_symmetric τ) hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  apply (hn N hN).trans
  apply add_le_add
  · apply goldbachPairKernelSum_le_ideal
    intro p hp
    obtain ⟨hs,hr⟩ := mem_goldbachG6Pairs_iff.mp hp
    exact ⟨(mem_goldbachClosedPrimes_iff.mp hr).1.pos,(mem_goldbachClosedPrimes_iff.mp hs).1.pos⟩
  · apply goldbachPairKernelSum_le_ideal
    intro p hp
    obtain ⟨hr,hs⟩ := Finset.mem_product.mp hp
    exact ⟨(mem_goldbachClosedPrimes_iff.mp hr).1.pos,(mem_goldbachClosedPrimes_iff.mp hs).1.pos⟩

theorem goldbachG67JRIntegral_truncation {τ : ℝ} (hτ : 0 ≤ τ) :
    goldbachG67JRIntegral 0 - τ*goldbachG67LogRectangleMass ≤ goldbachG67JRIntegral τ := by
  have h6 := integral_truncation_loss (a := 4/53) (b := 4/33) (c := 4/53) (d := 4/33)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hτ
  have h7 := integral_truncation_loss (a := 4/53) (b := 4/33) (c := 4/33) (d := 3/11)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hτ
  unfold goldbachG67JRIntegral goldbachG67LogRectangleMass
  linarith

theorem goldbachG67IdealSum_integral_lower (τ η : ℝ) (hτ : 0 ≤ τ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachG67JRIntegral 0 - τ*goldbachG67LogRectangleMass - η ≤
        goldbachPairIdealSum N τ (goldbachG6Pairs N ((N : ℝ)^(4/53 : ℝ)) ((N : ℝ)^(4/33 : ℝ))) +
        goldbachPairIdealSum N τ (goldbachG7Pairs N ((N : ℝ)^(4/53 : ℝ))
          ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ))) := by
  obtain ⟨N₀,hN₀,hn⟩ := goldbachG67JRIntegral_lower τ η hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN
  have h := hn N hN
  have ht := goldbachG67JRIntegral_truncation hτ
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
