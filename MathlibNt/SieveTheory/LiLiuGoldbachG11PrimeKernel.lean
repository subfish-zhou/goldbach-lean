import MathlibNt.SieveTheory.LiLiuGoldbachG11MainMassTransport
import MathlibNt.SieveTheory.LiLiuGoldbachG11BuchstabEndpointMass
import MathlibNt.SieveTheory.LiuPrimePairLogKernel


open Finset Set LiLiuPrereqBuchstab
open scoped BigOperators Interval

noncomputable section

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

def goldbachG11PrimeKernel (h : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (4 / 33 : ℝ)),
    h (Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ)) * Real.log (N : ℝ) /
      ((goldbachG11LabelProd v : ℝ) * Real.log (v.2.2.2 : ℝ))

def goldbachG11PrimeIntegral (h : ℝ → ℝ) : ℝ :=
  ∫ r in (4 / 53 : ℝ)..(4 / 33), ∫ q in r..(4 / 33),
    ∫ s in q..(4 / 33), ∫ t in s..(4 / 33), h r / (r * q ^ 2 * s * t)


theorem goldbachG11PrimeKernel_logGeometry {N : ℕ} (hN : 4 ≤ N)
    {v : GoldbachG11Label}
    (hv : v ∈ goldbachG11Labels N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (4 / 33 : ℝ))) :
    Real.log (v.2.2.1 : ℝ) / Real.log (N : ℝ) ∈ Icc (4 / 53 : ℝ) (4 / 33) ∧
      0 < Real.log (v.2.2.2 : ℝ) ∧
      Real.log ((N : ℝ) / goldbachG11LabelProd v) / Real.log (v.2.2.2 : ℝ) ∈
        Icc (17 / 4 : ℝ) (37 / 4) := by
  rcases v with ⟨t, s, r, q⟩
  have hm : t ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (4 / 33 : ℝ)) ∧
      s ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) (t : ℝ) ∧
      r ∈ goldbachClosedPrimes N ((N : ℝ) ^ (4 / 53 : ℝ)) (s : ℝ) ∧
      q ∈ goldbachClosedPrimes N (r : ℝ) (s : ℝ) := by
    simpa only [goldbachG11Labels, Finset.mem_sigma] using hv
  obtain ⟨ht, hs, hr, hq⟩ := hm
  have ht' := mem_goldbachClosedPrimes_iff.mp ht
  have hs' := mem_goldbachClosedPrimes_iff.mp hs
  have hr' := mem_goldbachClosedPrimes_iff.mp hr
  have hq' := mem_goldbachClosedPrimes_iff.mp hq
  exact ⟨goldbachG11_logPrimeExponent_mem (by omega) hr'.1 hr'.2.2.1
    (hr'.2.2.2.trans (hs'.2.2.2.trans ht'.2.2.2)),
    Real.log_pos (by exact_mod_cast hq'.1.one_lt),
    goldbachG11_canonical_logQuotient_bounds (by omega) ht hs hr hq⟩


/-- The minimum encodes the matching two branches without a discontinuity. -/
def goldbachG11AuthorWeight (r : ℝ) : ℝ :=
  36 / (5 * (1 - min r (1 / 10)))

theorem goldbachG11AuthorWeight_global_upper (r : ℝ) : goldbachG11AuthorWeight r ≤ 8 := by
  have hm := min_le_right r (1/10 : ℝ)
  unfold goldbachG11AuthorWeight
  apply (div_le_iff₀ (by linarith : 0 < 5*(1-min r (1/10)))).2
  linarith

theorem goldbachG11AuthorWeight_eq_low {r : ℝ} (hr : r ≤ 1 / 10) :
    goldbachG11AuthorWeight r = 36 / (5 * (1 - r)) := by
  simp only [goldbachG11AuthorWeight, min_eq_left hr]

theorem goldbachG11AuthorWeight_eq_high {r : ℝ} (hr : 1 / 10 ≤ r) :
    goldbachG11AuthorWeight r = 8 := by
  norm_num [goldbachG11AuthorWeight, min_eq_right hr]


theorem goldbachG11AuthorWeight_nonneg (r : ℝ) :
    0 ≤ goldbachG11AuthorWeight r := by
  have hm := min_le_right r (1 / 10 : ℝ)
  unfold goldbachG11AuthorWeight
  exact div_nonneg (by norm_num) (by linarith)

theorem continuous_goldbachG11AuthorWeight : Continuous goldbachG11AuthorWeight := by
  unfold goldbachG11AuthorWeight
  apply Continuous.div continuous_const
    (continuous_const.mul (continuous_const.sub (continuous_id.min continuous_const)))
  intro r
  have hm := min_le_right r (1 / 10 : ℝ)
  dsimp
  nlinarith

theorem continuousOn_goldbachG11AuthorWeight :
    ContinuousOn goldbachG11AuthorWeight (Icc (4 / 53 : ℝ) (4 / 33)) :=
  continuous_goldbachG11AuthorWeight.continuousOn

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig