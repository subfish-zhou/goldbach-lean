import MathlibNt.Wu2004MeanValue.ManuscriptPairs
import MathlibNt.SieveTheory.Liu.Weights.LiuWeightMainSum

/-!
# The true logarithmic integral in the manuscript masses

The normalization is exactly `wuLi = integral from 2`, not `x / log x`.
The sharp upper estimate consumes the frozen real-endpoint remainder theorem
in `LiuWeightMainSum`, with additive normalization zero.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.LiuWeight
open scoped Topology

theorem wuLi_nonneg {x : ℝ} (hx : 2 ≤ x) : 0 ≤ wuLi x :=
  liuLogarithmicIntegral_nonneg 0 le_rfl hx

theorem wuLi_mono {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    wuLi x ≤ wuLi y := by
  have hi := liuLogarithmicIntegrand_intervalIntegrable hx
  have hj := liuLogarithmicIntegrand_intervalIntegrable_of_two_le hx hxy
  have heq := intervalIntegral.integral_add_adjacent_intervals hi hj
  have hn := intervalIntegral.integral_nonneg (μ := MeasureTheory.volume) hxy
    (fun t ht => liuLogarithmicIntegrand_nonneg (hx.trans ht.1))
  simp only [wuLi, liuLogarithmicIntegral, zero_add]
  linarith

/-- Uniformly at all sufficiently large real arguments, the true li has the
sharp proxy upper bound, with any prescribed positive relative slack. -/
theorem eventually_wuLi_le_one_add_mul (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, wuLi x ≤ (1 + δ) * (x / Real.log x) := by
  obtain ⟨C, hC, hrem⟩ := eventually_abs_liuLogarithmicIntegralRemainder_le 0
  have hlog : ∀ᶠ x : ℝ in atTop, C / δ ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hrem, hlog, eventually_ge_atTop (2 : ℝ)] with x hr hl hx
  have hx0 : 0 ≤ x := by linarith
  have hl0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hCδ : C ≤ δ * Real.log x := by
    have := (div_le_iff₀ hδ).mp hl
    nlinarith
  have hpay : C * x / Real.log x ^ 2 ≤ δ * (x / Real.log x) := by
    apply (div_le_iff₀ (sq_pos_of_pos hl0)).mpr
    calc
      C * x ≤ (δ * Real.log x) * x := mul_le_mul_of_nonneg_right hCδ hx0
      _ = δ * (x / Real.log x) * Real.log x ^ 2 := by
        field_simp
  have he := (le_abs_self (liuLogarithmicIntegralRemainder 0 x)).trans (hr hx)
  change wuLi x - x / Real.log x ≤ _ at he
  nlinarith

/-- Nonnegativity of the whole literal tail mass, including its lower li
endpoint, after the fixed-eta domain threshold. -/
theorem tailMass_nonneg {N : ℕ} {c τ η : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hN : (2 / η) ^ 2 ≤ (N : ℝ)) :
    0 ≤ tailMass N c τ η := by
  unfold tailMass intervalMass
  apply Finset.sum_nonneg
  intro m hm
  have hs := mem_tailSource.mp hm
  have hd := tail_prime_endpoint_domain N η hη hη1 hN m hs.1.pos hs.2.2.2
  apply sub_nonneg.mpr
  apply wuLi_mono hd.1
  exact div_le_div_of_nonneg_right
    (mul_le_of_le_one_left (Nat.cast_nonneg N) hη1) (Nat.cast_nonneg m)

end Wu2004MeanValue
