import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.Sieve _root_.AnalyticNumberTheory.LargeSieve Wu2004MeanValue
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


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig