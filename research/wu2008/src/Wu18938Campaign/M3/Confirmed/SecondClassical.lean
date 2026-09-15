import Wu18938Campaign.M3.Confirmed.G2Slack
import Wu18938Campaign.M3.Confirmed.TableBounds

noncomputable section

namespace Wu18938Campaign.M3.Confirmed.SecondClassical

open Real Set MeasureTheory Wu2008DoubleSieve Wu08OriginalFirstSteps

def logPolynomial (x : ℝ) : ℝ := x - x^2/2 + x^3/3 - x^4/4
def kernelPolynomial (x : ℝ) : ℝ := x/2 - x^2/2 + 5*x^3/12 - x^4/3
def innerPolynomial (x : ℝ) : ℝ := x^2/4 - x^3/6 + 5*x^4/48 - x^5/15
def inversePolynomial (x : ℝ) : ℝ := 1/3 - x/9 + x^2/27 - x^3/81
def outerPrimitive (x : ℝ) : ℝ :=
  x^3/36 - x^4/48 + x^5/80 - 31*x^6/4320 +
    259*x^7/136080 - 73*x^8/155520 + x^9/10935

theorem log_polynomial_lower {x : ℝ} (hx : 0 ≤ x) :
    logPolynomial x ≤ log (1+x) := by
  have hd (t : ℝ) (ht : 0 ≤ t) :
      HasDerivAt (fun t => log (1+t)-logPolynomial t) (t^4/(1+t)) t := by
    have hn : 1+t ≠ 0 := by linarith
    have hp := (((hasDerivAt_id t).sub (((hasDerivAt_id t).pow 2).div_const 2)).add
      (((hasDerivAt_id t).pow 3).div_const 3)).sub
      (((hasDerivAt_id t).pow 4).div_const 4)
    have hh := ((((hasDerivAt_id t).const_add 1).log hn).sub hp)
    convert hh using 1 <;> first | rfl | (dsimp; field_simp; ring)
  have hm : MonotoneOn (fun t => log (1+t)-logPolynomial t) (Ici 0) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => div_nonneg (pow_nonneg (interior_subset ht) 4) (by
        have h : 0 ≤ t := interior_subset ht
        linarith))
  have h := hm (by simp) hx hx
  norm_num [logPolynomial] at h
  unfold logPolynomial
  linarith

theorem kernel_lower {u : ℝ} (hu : 2 ≤ u) :
    kernelPolynomial (u-2) ≤ log (u-1)/u := by
  have hl := log_polynomial_lower (show 0 ≤ u-2 by linarith)
  have hp : u * kernelPolynomial (u-2) =
      logPolynomial (u-2) - (u-2)^5/3 := by
    unfold kernelPolynomial logPolynomial
    ring
  apply (le_div_iff₀ (by linarith : 0 < u)).mpr
  rw [mul_comm, hp]
  norm_num only [show (1 : ℝ)+(u-2)=u-1 by ring] at hl
  linarith [pow_nonneg (show 0 ≤ u-2 by linarith) 5]

theorem inner_derivative (x : ℝ) :
    HasDerivAt innerPolynomial (kernelPolynomial x) x := by
  have h := (((((hasDerivAt_id x).pow 2).div_const 4).sub
    (((hasDerivAt_id x).pow 3).div_const 6)).add
      ((((hasDerivAt_id x).pow 4).const_mul 5).div_const 48)).sub
        (((hasDerivAt_id x).pow 5).div_const 15)
  convert h using 1 <;> first | rfl | (dsimp [kernelPolynomial]; ring)

theorem inner_lower {t : ℝ} (ht : 3 ≤ t) :
    innerPolynomial (t-3) ≤ B t := by
  have he : (∫ u in (2:ℝ)..(t-1), kernelPolynomial (u-2)) =
      innerPolynomial (t-3) := by
    have hd (u : ℝ) :
        HasDerivAt (fun u => innerPolynomial (u-2)) (kernelPolynomial (u-2)) u := by
      convert! (inner_derivative (u-2)).comp u ((hasDerivAt_id u).sub_const 2) using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      ((by unfold kernelPolynomial; fun_prop :
        Continuous (fun u : ℝ => kernelPolynomial (u-2))).intervalIntegrable _ _)]
    norm_num [show (t-1:ℝ)-2=t-3 by ring, innerPolynomial]
  rw [← he]
  apply intervalIntegral.integral_mono_on (show (2:ℝ) ≤ t-1 by linarith)
    ((by unfold kernelPolynomial; fun_prop :
      Continuous (fun u : ℝ => kernelPolynomial (u-2))).intervalIntegrable _ _)
    (k_continuous.intervalIntegrable (μ := volume) _ _)
  intro u hu
  rw [k_literal hu.1]
  exact kernel_lower hu.1

theorem inverse_bounds {x : ℝ} (hx : x ∈ Icc 0 (3/25)) :
    0 ≤ inversePolynomial x ∧ inversePolynomial x ≤ 1/(3+x) := by
  have h2 : x^2 ≤ (3/25:ℝ)^2 := pow_le_pow_left₀ hx.1 hx.2 2
  have h3 : x^3 ≤ (3/25:ℝ)^3 := pow_le_pow_left₀ hx.1 hx.2 3
  constructor
  · unfold inversePolynomial
    nlinarith [sq_nonneg x]
  · apply (le_div_iff₀ (by linarith [hx.1] : 0 < 3+x)).mpr
    have he : inversePolynomial x * (3+x) = 1-x^4/81 := by
      unfold inversePolynomial
      ring
    rw [he]
    linarith [pow_nonneg hx.1 4]

theorem outer_derivative (x : ℝ) :
    HasDerivAt outerPrimitive (innerPolynomial x * inversePolynomial x) x := by
  have h := ((((((((hasDerivAt_id x).pow 3).div_const 36).sub
    (((hasDerivAt_id x).pow 4).div_const 48)).add
      (((hasDerivAt_id x).pow 5).div_const 80)).sub
        ((((hasDerivAt_id x).pow 6).const_mul 31).div_const 4320)).add
          ((((hasDerivAt_id x).pow 7).const_mul 259).div_const 136080)).sub
            ((((hasDerivAt_id x).pow 8).const_mul 73).div_const 155520)).add
              (((hasDerivAt_id x).pow 9).div_const 10935)
  convert h using 1 <;> first | rfl | (dsimp [innerPolynomial, inversePolynomial]; ring)

theorem recurrence_lower :
    (107349304377 / 2441406250000000 : ℝ) ≤ C (103/25) := by
  have hi : IntervalIntegrable
      (fun t : ℝ => innerPolynomial (t-3)*inversePolynomial (t-3))
      volume 3 (78/25) :=
    (by unfold innerPolynomial inversePolynomial; fun_prop :
      Continuous (fun t : ℝ => innerPolynomial (t-3)*inversePolynomial (t-3))).intervalIntegrable _ _
  have he : (∫ t in (3:ℝ)..(78/25), innerPolynomial (t-3)*inversePolynomial (t-3)) =
      (107349304377 / 2441406250000000 : ℝ) := by
    have hd (t : ℝ) : HasDerivAt (fun t => outerPrimitive (t-3))
        (innerPolynomial (t-3)*inversePolynomial (t-3)) t := by
      convert! (outer_derivative (t-3)).comp t ((hasDerivAt_id t).sub_const 3) using 1
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi]
    norm_num [outerPrimitive]
  rw [← he]
  change _ ≤ ∫ t in (3:ℝ)..(103/25-1), B t/max 1 t
  norm_num only [show (103/25:ℝ)-1=78/25 by norm_num]
  apply intervalIntegral.integral_mono_on (by norm_num) hi
    ((div_continuous B_continuous).intervalIntegrable (μ := volume) _ _)
  intro t ht
  rw [max_eq_right (by linarith [ht.1] : (1:ℝ) ≤ t)]
  have hb := inverse_bounds (show t-3 ∈ Icc 0 (3/25) by
    constructor <;> linarith [ht.1, ht.2])
  have hpos : 0 ≤ B t := by
    change 0 ≤ ∫ u in (2:ℝ)..(t-1), k u
    apply intervalIntegral.integral_nonneg (by linarith [ht.1])
    intro u hu
    rw [k_literal hu.1]
    exact div_nonneg (log_nonneg (by linarith [hu.1])) (by linarith [hu.1])
  calc
    _ ≤ B t * inversePolynomial (t-3) :=
      mul_le_mul_of_nonneg_right (inner_lower ht.1) hb.1
    _ ≤ B t * (1/(3+(t-3))) := mul_le_mul_of_nonneg_left hb.2 hpos
    _ = _ := by ring

theorem second_main_lower :
    (9103015/1000000 : ℝ) ≤ Wu08TerminalAlignment.secondMain := by
  have hl := TableBounds.logLower_le (by norm_num : (1:ℝ) ≤ 78/25)
  have hr := recurrence_lower
  have hpay : (9103015/1000000 : ℝ) ≤
      8*(TableBounds.logLower (78/25)+107349304377/2441406250000000) := by
    norm_num [TableBounds.logLower, Finset.sum_range_succ]
  rw [Wu08TerminalAlignment.second_exact]
  linarith only [hl, hr, hpay]

theorem second_actual_count {ε : ℝ} (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((9103015/1000000:ℝ)-ε)*truncatedSixthMassScale N ≤
        (sieveCount N 1 N ((N:ℝ)^truncatedSixthLowerBeta) : ℝ) := by
  obtain ⟨T,hT,hc⟩ := BaseLowerCounts.actual_count_lower
    (κ := truncatedSixthLowerBeta)
    (by norm_num [truncatedSixthLowerBeta]) (by norm_num [truncatedSixthLowerBeta]) he
  refine ⟨T,hT,fun N hN hEven => ?_⟩
  have hs := truncatedSixthClosure_scale_nonneg (hT.trans hN)
  have hnum := mul_le_mul_of_nonneg_right (sub_le_sub_right second_main_lower ε) hs
  have hcN := hc N hN hEven
  have hcN' : (Wu08TerminalAlignment.secondMain-ε)*truncatedSixthMassScale N ≤
      (sieveCount N 1 N ((N:ℝ)^truncatedSixthLowerBeta) : ℝ) := by
    simpa only [Wu08TerminalAlignment.secondMain, truncatedSixthMassScale,
      mul_div_assoc, mul_assoc] using hcN
  exact hnum.trans hcN'

end Wu18938Campaign.M3.Confirmed.SecondClassical
