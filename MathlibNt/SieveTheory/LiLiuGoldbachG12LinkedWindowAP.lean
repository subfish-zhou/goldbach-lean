import MathlibNt.SieveTheory.LiLiuGoldbachG12LinkedWindow
import MathlibNt.SieveTheory.FiniteRealWindows
import MathlibNt.Wu2004MeanValue.RealEndpoints


namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve


theorem goldbachG12LinkedPrimeWindow_product_le {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε m) : r*m ≤ N := by
  have hs := goldbachG12ActiveProductSupport_mem_full hm
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast (goldbachG11ProductSupport_data hs).1
  have hhi := (Finset.mem_filter.mp hr).2.2.2
  have hn := (le_div_iff₀ hmR).mp ((min_le_right _ _).trans' hhi)
  exact_mod_cast hn

/-- On the geometric mother, the actual output is positive, not truncated to zero. -/
theorem goldbachG12LinkedPrimeWindow_output_pos {N m r : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hr : r ∈ goldbachG11LinkedPrimeWindow N ε m) : 0 < N-r*m := by
  have hs := goldbachG12ActiveProductSupport_mem_full hm
  exact Nat.sub_pos_of_lt ((goldbachG11_product_upper_cutoff_iff hs r).mpr
    (goldbachG12LinkedPrimeWindow_product_le hm hr))


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig