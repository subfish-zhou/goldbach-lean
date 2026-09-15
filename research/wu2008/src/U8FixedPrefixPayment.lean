import U8TwoLogDenominator
import U8OptimalPrefix

/-! The original closed small-product prefix is paid with one fixed cutoff.
The true two-log denominator and the true optimal CRT bound are both consumed. -/
noncomputable section
open Filter
namespace U8Literal.SmallProduct
open TwoDimensional MathlibNt.SieveTheory MathlibNt.SieveTheory.LiuWeight

/-- The cutoff is fixed before the common threshold; it does not depend on N. -/
theorem smallPrefix_sigma_payment (σ : ℝ) (hσ : 0 < σ) :
    ∃ e : ℝ, 0 < e ∧ e ≤ 1/2 ∧ ∃ N0 : ℕ, ∀ N ≥ N0, Even N →
      ((smallPrefix N e).card : ℝ) ≤
        σ * SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log N)^2 := by
  let β : ℝ := originalAlpha/2
  have hβ : 0 < β := by norm_num [β, originalAlpha]
  have hβα : β < originalAlpha := by norm_num [β, originalAlpha]
  have hβsmall : β < 1/15 := by norm_num [β, originalAlpha]
  obtain ⟨C,hC,hupper⟩ := smallPrefix_optimal_eventually_upper
  let K : ℝ := C*64/β^2
  have hK : 0 < K := by dsimp [K]; positivity
  let e : ℝ := min (1/2) (σ/(2*K))
  have he : 0 < e := lt_min (by norm_num) (by positivity)
  have hehalf : e ≤ 1/2 := min_le_left _ _
  have hKe : K*e ≤ σ/2 := by
    have hh := (le_div_iff₀ (show 0 < 2*K by positivity)).mp
      (min_le_right (1/2 : ℝ) (σ/(2*K)))
    change e*(2*K) ≤ σ at hh
    nlinarith
  have hU := hupper e β he.le hehalf hβ hβα
  have hD := eventually_denominator_two_log hβ
  have hS0 := SingularSeries.liuUniversalProduct_pos
  have hE := (polynomial_remainder_littleO hβ hβsmall).def
    (show 0 < (σ/2)*SingularSeries.liuUniversalProduct by positivity)
  have hall : ∀ᶠ N : ℕ in atTop, Even N →
      ((smallPrefix N e).card : ℝ) ≤
        σ * SingularSeries.liuSingularSeries N * (N : ℝ) / (Real.log N)^2 := by
    filter_upwards [hU,hD,hE,eventually_ge_atTop (2 : ℕ)] with N hUN hDN hEN hN
    intro hEven
    have hNtwo : 1 < N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hNtwo)
    have hS : 0 < SingularSeries.liuSingularSeries N := SingularSeries.liuSingularSeries_pos N
    have hden := hDN hEven _ (power_cutoff_legal hNtwo hβ hβα).2.2
    have hbase : 0 < (β^2/64)*(Real.log N)^2/SingularSeries.liuSingularSeries N := by positivity
    have hmain : C*e*(N : ℝ)/denominator N ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^β) ≤
        (σ/2)*(SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2) := by
      calc
        _ = (C*e*(N : ℝ))*(1/denominator N ((N : ℝ)^(1/3 : ℝ)) ((N : ℝ)^β)) := by ring
        _ ≤ (C*e*(N : ℝ))*(1/((β^2/64)*(Real.log N)^2/SingularSeries.liuSingularSeries N)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hbase hden) (by positivity)
        _ = (K*e)*(SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2) := by
          dsimp [K]
          field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_right hKe (by positivity)
    have hrem : 8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4 ≤
        (σ/2)*(SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2) := by
      have hn0 : 0 ≤ (N : ℝ)/(Real.log N)^2 := by positivity
      have hr0 : 0 ≤ 8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^β+1)^2*((N : ℝ)^β)^4 := by positivity
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hr0, abs_of_nonneg hn0] at hEN
      calc
        _ ≤ ((σ/2)*SingularSeries.liuUniversalProduct)*((N : ℝ)/(Real.log N)^2) := hEN
        _ ≤ ((σ/2)*SingularSeries.liuSingularSeries N)*((N : ℝ)/(Real.log N)^2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) (by positivity)) hn0
        _ = _ := by ring
    calc
      _ ≤ _ := hUN hEven
      _ ≤ (σ/2)*(SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2) +
          (σ/2)*(SingularSeries.liuSingularSeries N*(N : ℝ)/(Real.log N)^2) := add_le_add hmain hrem
      _ = _ := by ring
  obtain ⟨N0,hN0⟩ := eventually_atTop.1 hall
  exact ⟨e,he,hehalf,N0,hN0⟩

end U8Literal.SmallProduct
