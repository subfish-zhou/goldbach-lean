import WR2XiSixthContinuousPanel
import WR2XiSixthDensityPanel
import WR2XiSixthContinuousMonotone

noncomputable section
namespace WuPaper.R2Xi.SixthContinuous
open Real Set MeasureTheory WuTarget.W01Continuous WuSource.SrcSixthGain Finset
open scoped Classical Interval

/-- Rational endpoint payments bound the actual continuous source gain. -/
theorem quadrature_le_amount {n : ℕ} {x : ℕ → ℝ}
    (h0 : x 0 = 2) (hn : x n = endpoint)
    (hx : ∀ i ≤ n, x i ∈ Set.Icc 2 endpoint)
    (hstep : ∀ i < n, x i ≤ x (i+1)) :
    (∑ i ∈ range n, 8*(x (i+1)-x i)*
      (densityLower (x i) (x (i+1))*pointLower (x (i+1)))) ≤ SourceSixth.amount := by
  apply le_trans _ candidate_gain_le_amount
  rw [continuous_density_integral RationalCandidate.lowerH_nonneg,← h0,← hn]
  have hi (i : ℕ) (hin : i < n) : IntervalIntegrable
      (fun s => density s*hContinuous RationalCandidate.lowerH s) volume (x i) (x (i+1)) := by
    apply (gain_integrand_integrable RationalCandidate.lowerH).mono_set
    rw [uIcc_of_le (hstep i hin),uIcc_of_le scalar_interval]
    exact Icc_subset_Icc (hx i (by omega)).1 (hx (i+1) (by omega)).2
  rw [← intervalIntegral.sum_integral_adjacent_intervals hi,Finset.mul_sum]
  apply sum_le_sum
  intro i him
  have hin := mem_range.mp him
  have ha := (hx i (by omega)).1
  have hb := (hx (i+1) (by omega)).2
  have hp := panel_integral_lower ha (hstep i hin) hb
    (densityLower_nonneg ha (hstep i hin) hb)
    (fun s hs => densityLower_le ha hb hs)
  have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 8)
  simpa only [mul_assoc] using hm

/-- Certificates may round each panel down independently to keep arithmetic small. -/
theorem certificate {n : ℕ} {x q : ℕ → ℝ} {target : ℝ}
    (h0 : x 0 = 2) (hn : x n = endpoint)
    (hx : ∀ i ≤ n, x i ∈ Set.Icc 2 endpoint)
    (hstep : ∀ i < n, x i ≤ x (i+1))
    (hq : ∀ i < n, q i ≤ 8*(x (i+1)-x i)*
      (densityLower (x i) (x (i+1))*pointLower (x (i+1))))
    (ht : target ≤ ∑ i ∈ range n, q i) : target ≤ SourceSixth.amount := by
  exact ht.trans ((sum_le_sum (fun i hi => hq i (mem_range.mp hi))).trans
    (quadrature_le_amount h0 hn hx hstep))

end WuPaper.R2Xi.SixthContinuous
#print axioms WuPaper.R2Xi.SixthContinuous.certificate
