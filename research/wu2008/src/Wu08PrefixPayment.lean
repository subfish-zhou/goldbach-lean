import Wu08PrefixActual
import U8CanonicalMother

noncomputable section
open Finset Real Filter
open scoped Classical Topology
open Wu2008DoubleSieve
open U8Literal.SmallProduct U8Literal.SmallProduct.TwoDimensional
open MathlibNt.SieveTheory
namespace Wu08FirstPrimeFour.Prefix

def exponent : ℝ := truncatedSixthLowerAlpha/2
def prefixConstant : ℝ := multiplicity*64/exponent^2

theorem multiplicity_pos : 0 < multiplicity := by
  norm_num [multiplicity,truncatedSixthLowerAlpha]
theorem exponent_pos : 0 < exponent := by norm_num [exponent,truncatedSixthLowerAlpha]
theorem prefixConstant_pos : 0 < prefixConstant := by
  unfold prefixConstant
  exact div_pos (mul_pos multiplicity_pos (by norm_num)) (pow_pos exponent_pos 2)

/-- Fixed xi has a proportional loss, not an error that disappears by taking N
large. One threshold works for every e, retaining the same original-N scale. -/
theorem smallPrefix_proportional {ξ κ : ℝ} (hξ : 0 ≤ ξ) (hξu : ξ ≤ 1/2)
    (hκ : 0 < κ) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ e : Bool,
      ((smallPrefix N e ξ).card : ℝ) ≤
        (prefixConstant*ξ+κ) * (wuSingularSeries N*N/log N^2) := by
  have hb := exponent_pos
  have hsmall : exponent < 1/15 := by norm_num [exponent,truncatedSixthLowerAlpha]
  have hden := eventually_denominator_two_log hb
  have hE := (polynomial_remainder_littleO hb hsmall).def
    (show 0 < (κ/multiplicity)*SingularSeries.liuUniversalProduct by
      exact mul_pos (div_pos hκ multiplicity_pos) SingularSeries.liuUniversalProduct_pos)
  have hall : ∀ᶠ N : ℕ in atTop, Even N → ∀ e : Bool,
      ((smallPrefix N e ξ).card : ℝ) ≤
        (prefixConstant*ξ+κ) * (wuSingularSeries N*N/log N^2) := by
    filter_upwards [hden,hE,eventually_ge_atTop (4 : ℕ)] with N hDN hEN hN
    intro he e
    have hN1 : 1 < N := by omega
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN1)
    have hS : 0 < SingularSeries.liuSingularSeries N := SingularSeries.liuSingularSeries_pos N
    have hZ : (N : ℝ)^exponent < LastPrimeFour.z N := by
      apply rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hN1)
      norm_num [exponent,truncatedSixthLowerAlpha]
    have hzout : LastPrimeFour.z N ≤ (1-ξ)*N := by
      apply le_trans (b := (N : ℝ)^(1/3 : ℝ))
      · apply rpow_le_rpow_of_exponent_le hN1r
        norm_num [LastPrimeFour.z,truncatedSixthLowerAlpha]
      · exact cubeRoot_le_output_floor hN hξu
    have hR := one_le_rpow hN1r hb.le
    have hD := hDN he _ hZ
    have hbase : 0 < (exponent^2/64)*(log N)^2/SingularSeries.liuSingularSeries N := by
      exact div_pos (mul_pos (div_pos (pow_pos hb 2) (by norm_num)) (pow_pos hlog 2)) hS
    have hmain : multiplicity*(ξ*N/denominator N (LastPrimeFour.z N) ((N : ℝ)^exponent)) ≤
        (prefixConstant*ξ)*(SingularSeries.liuSingularSeries N*N/log N^2) := by
      calc
        _ = (multiplicity*ξ*N)*(1/denominator N (LastPrimeFour.z N) ((N : ℝ)^exponent)) := by ring
        _ ≤ (multiplicity*ξ*N)*(1/((exponent^2/64)*(log N)^2/SingularSeries.liuSingularSeries N)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hbase hD)
            (mul_nonneg (mul_nonneg multiplicity_pos.le hξ) hNp.le)
        _ = _ := by unfold prefixConstant; field_simp
    have hdom : 2*((N : ℝ)^exponent+1)^2*((N : ℝ)^exponent)^4 ≤
        8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^exponent+1)^2*((N : ℝ)^exponent)^4 := by
      have hp : 1 ≤ (N : ℝ)^(3/5 : ℝ) := one_le_rpow hN1r (by norm_num)
      gcongr
      linarith
    have hrem : multiplicity*(2*((N : ℝ)^exponent+1)^2*((N : ℝ)^exponent)^4) ≤
        κ*(SingularSeries.liuSingularSeries N*N/log N^2) := by
      have hn0 : 0 ≤ (N : ℝ)/(log N)^2 := by positivity
      have hr0 : 0 ≤ 8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^exponent+1)^2*((N : ℝ)^exponent)^4 := by positivity
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hr0,abs_of_nonneg hn0] at hEN
      calc
        _ ≤ multiplicity*(8*(N : ℝ)^(3/5 : ℝ)*((N : ℝ)^exponent+1)^2*((N : ℝ)^exponent)^4) :=
          mul_le_mul_of_nonneg_left hdom multiplicity_pos.le
        _ ≤ multiplicity*(((κ/multiplicity)*SingularSeries.liuUniversalProduct)*(N/log N^2)) :=
          mul_le_mul_of_nonneg_left hEN multiplicity_pos.le
        _ ≤ multiplicity*(((κ/multiplicity)*SingularSeries.liuSingularSeries N)*(N/log N^2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (SingularSeries.liuUniversalProduct_le_liuSingularSeries N)
              (div_nonneg hκ.le multiplicity_pos.le)) hn0) multiplicity_pos.le
        _ = _ := by field_simp [multiplicity_pos.ne']
    have hh := smallPrefix_selberg_upper (e := e) hN1 he hξ hR le_rfl hzout
    rw [mul_add] at hh
    have hs : wuSingularSeries N*N/log N^2 =
        SingularSeries.liuSingularSeries N*N/log N^2 :=
      U8CanonicalMother.scale_eq_liu (by omega)
    rw [hs]
    calc
      _ ≤ _ := hh
      _ ≤ (prefixConstant*ξ)*(SingularSeries.liuSingularSeries N*N/log N^2)+
          κ*(SingularSeries.liuSingularSeries N*N/log N^2) := add_le_add hmain hrem
      _ = _ := by ring
  obtain ⟨T,hT⟩ := eventually_atTop.mp hall
  exact ⟨max T 4,le_max_right _ _,fun N hN => hT N ((le_max_left _ _).trans hN)⟩

/-- xi is selected before N, with any prescribed positive ceiling and one
threshold for both e. This is the actual two-prefix payment on properPairCore. -/
theorem smallPrefix_pair_payment {σ ξmax : ℝ} (hσ : 0 < σ) (hmax : 0 < ξmax) :
    ∃ ξ : ℝ, 0 < ξ ∧ ξ ≤ min ξmax (1/2) ∧ ∃ T : ℕ, 4 ≤ T ∧
      ∀ N : ℕ, T ≤ N → Even N →
        ((smallPrefix N false ξ).card : ℝ)+(smallPrefix N true ξ).card ≤
          σ*(wuSingularSeries N*N/log N^2) := by
  let ξ := min (min ξmax (1/2)) (σ/(4*prefixConstant))
  have hξ : 0 < ξ := lt_min (lt_min hmax (by norm_num))
    (div_pos hσ (mul_pos (by norm_num) prefixConstant_pos))
  have hξu : ξ ≤ min ξmax (1/2) := min_le_left _ _
  have hp : prefixConstant*ξ ≤ σ/4 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) prefixConstant_pos)).mp
      (min_le_right (min ξmax (1/2)) (σ/(4*prefixConstant)))
    change ξ*(4*prefixConstant) ≤ σ at hh
    linarith
  obtain ⟨T,hT,hu⟩ := smallPrefix_proportional hξ.le (hξu.trans (min_le_right _ _))
    (show 0 < σ/4 by positivity)
  refine ⟨ξ,hξ,hξu,T,hT,?_⟩
  intro N hN he
  have hscale : 0 ≤ wuSingularSeries N*N/log N^2 := by
    exact div_nonneg (mul_nonneg (wuSingularSeries_pos N (by omega)).le (Nat.cast_nonneg N)) (sq_nonneg _)
  have h0 := hu N hN he false
  have h1 := hu N hN he true
  have hpay := mul_le_mul_of_nonneg_right hp hscale
  nlinarith only [h0,h1,hpay]

#print axioms smallPrefix_proportional
#print axioms smallPrefix_pair_payment
end Wu08FirstPrimeFour.Prefix
