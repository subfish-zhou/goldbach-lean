import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanConvolutionAPCount
import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanWangDingSource

open scoped BigOperators
open Finset
namespace MathlibNt.SieveTheory.LiuWeight

/-- Identification with the counting component of the actual production sum.
The main function, its argument N/a in real arithmetic, and its normalization
are left literally unchanged. -/
theorem liuMainPanCoprimeIntervalSum_eq_count_sub_main
    (main : ℝ → ℝ) (N z y A₁ A₂ q l : ℕ) :
    liuMainPanCoprimeIntervalSum main N A₁ A₂ q l (liuWeight N z y) =
      liuCoprimeIntervalCount N z y A₁ A₂ q l -
        ∑ a ∈ Ioc A₁ A₂, if a.Coprime q then
          liuWeight N z y a * (main ((N : ℝ) / a) / Nat.totient q) else 0 := by
  unfold liuMainPanCoprimeIntervalSum liuCoprimeIntervalCount liuScaledAPError
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> ring


end MathlibNt.SieveTheory.LiuWeight