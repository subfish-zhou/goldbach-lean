import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindowAP

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
open _root_.AnalyticNumberTheory.LargeSieve

/-- An inadmissible cofactor contributes no actual output divisible by d. -/
theorem goldbachG12Linked_outputDivisors_empty {N m d : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hNd : N.Coprime d) (hmd : ¬ m.Coprime d) :
    (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  obtain ⟨hr, hd⟩ := mem_filter.mp hr
  have hgout : Nat.gcd m d ∣ N-r*m := dvd_trans (Nat.gcd_dvd_right m d) hd
  have hgrm : Nat.gcd m d ∣ r*m := dvd_mul_of_dvd_right (Nat.gcd_dvd_left m d) r
  have hgN := Nat.dvd_add hgout hgrm
  rw [Nat.sub_add_cancel (goldbachG12LinkedPrimeWindow_product_le hm hr)] at hgN
  have hg := Nat.dvd_gcd hgN (Nat.gcd_dvd_right m d)
  rw [hNd.gcd_eq_one] at hg
  exact hmd (Nat.dvd_one.mp hg)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig