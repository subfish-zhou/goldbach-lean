import MathlibNt.SieveTheory.LiLiuGoldbachG11ProductGrouping
import MathlibNt.SieveTheory.LiLiuGoldbachG11ActiveProductGeometry

open scoped BigOperators
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11_product_active_bounds {N m r : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ)))
    (hr : r ∈ goldbachG11ProductFirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) m) :
    ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ) := by
  obtain ⟨u, hu, heq⟩ := mem_goldbachG11ProductSupport_iff.mp hm
  have huB := (mem_goldbachG11GoodSwitchedBodies_iff.mp hu).1
  have hr' : r ∈ goldbachG11FirstPrimeFiber N ε ((N : ℝ)^(4 / 53 : ℝ)) u := by
    rwa [goldbachG11FirstPrimeFiber_eq_product huB, heq]
  simpa only [heq] using goldbachG11_active_product_bounds hN huB hr'

/-- A purely geometric envelope; no output-prime condition is inserted into coefficients. -/
noncomputable def goldbachG11EffectiveProductSupport (N : ℕ) (ε : ℝ) : Finset ℕ := by
  classical
  exact (goldbachG11ProductSupport N ((N : ℝ)^(4 / 53 : ℝ)) ((N : ℝ)^(4 / 33 : ℝ))).filter
    fun m => ε * (N : ℝ)^(29 / 33 : ℝ) < (m : ℝ) ∧ (m : ℝ) < (N : ℝ)^(49 / 53 : ℝ)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig