import Hf4TargetLinearBlocks

noncomputable section
namespace Hf4Target
open Real Set MeasureTheory NodeExtension
open scoped Interval BigOperators

/-- Bound the actual paid remainder, using its already proved FTC and no new cuts. -/
theorem new_density_cap {t : ℝ} (ht : 1 ≤ t) :
    Hf4Continue.newDensity t ≤ 1/100800 := by
  have ht0 : 0 < t := by linarith
  have hm : 0 ≤ t-1 := by linarith
  have hp : (t-1)^9 ≤ t*(t+1)^8*(t+2) := by
    calc
      (t-1)^9 = (t-1)*(t-1)^8 := by ring
      _ ≤ t*(t+1)^8 := by gcongr <;> linarith
      _ ≤ t*(t+1)^8*(t+2) := by
        exact le_mul_of_one_le_right (by positivity) (by linarith)
  unfold Hf4Continue.newDensity
  apply (div_le_iff₀ (by positivity : 0 < 100800*t*(t+1)^8*(t+2))).mpr
  nlinarith only [hp]

theorem new_cell_cap {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Hf4Continue.newCellPayment a b ≤ (b-a)/100800 := by
  rw [← Hf4Continue.newDensity_integral ha hab]
  have h := intervalIntegral.integral_mono_on hab
    (Hf4Continue.newDensity_continuous ha hab).intervalIntegrable
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/100800 : ℝ)) volume a b)
    (fun t ht => new_density_cap (ha.trans ht.1))
  simpa [div_eq_mul_inv] using h

theorem new_variation_cap :
    Hf4Continue.newVariation NineFeedbackStrength.originalH < (1/1000000 : ℝ) := by
  have h : Hf4Continue.newVariation NineFeedbackStrength.originalH ≤
      ∑ k : Fin 9, NineFeedbackStrength.originalH k * ((upperNode k-upperLeft k)/100800) := by
    apply Finset.sum_le_sum
    intro k _
    obtain ⟨ha,hab,_⟩ := SigmaEndpointPayment.original_cell_bounds k
    exact mul_le_mul_of_nonneg_left (new_cell_cap ha hab)
      (CoupledIntegralRecovery.originalH_nonneg k)
  apply h.trans_lt
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  dsimp [NineFeedbackStrength.originalH]
  norm_num [upperNode, upperLeft]

end Hf4Target
