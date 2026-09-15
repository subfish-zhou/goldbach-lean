import OriginalBoundaryConsumer

noncomputable section
open MeasureTheory Set Filter Finset
open scoped Interval Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
namespace OriginalU8.Weighted

/-- Continuous endpoint conventions are identified only after the discrete cover
has retained every closed atom. No prime sum is altered by this equality. -/
theorem low_eq_closed_iterated {a : ℝ} (hab : a ≤ 1/10) :
    low a = ∫ x in Icc a (1/10 : ℝ),
      ∫ y in Icc (1/3 : ℝ) ((1-x)/2), fouvryG9WeightedIntegrand (x,y) := by
  rw [low_eq_iteratedSetIntegral hab, integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x _
  exact integral_Icc_eq_integral_Ioc.symm

theorem inner_integrable {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) (1/3)) :
    IntervalIntegrable (fun v => 1/(u*v*(1-u-v)*(1-u))) volume (1/3) ((1-u)/2) := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith [hu.2] : (1/3 : ℝ) ≤ (1-u)/2)]
  apply ContinuousOn.div continuousOn_const (by fun_prop)
  intro v hv
  have hp : 0 < u*v*(1-u-v)*(1-u) := by
    have hv0 : 0 < v := by linarith [hv.1]
    have hgap : 0 < 1-u-v := by linarith [hu.2, hv.2]
    have hu1 : 0 < 1-u := by linarith [hu.2]
    exact mul_pos (mul_pos (mul_pos hu.1 hv0) hgap) hu1
  exact hp.ne'

theorem outer_integrable {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/10) :
    IntervalIntegrable (fun u => ∫ v in (1/3 : ℝ)..((1-u)/2),
      1/(u*v*(1-u-v)*(1-u))) volume a (1/10) := by
  have hc : ContinuousOn (fun u : ℝ => Real.log (2-3*u)/(u*(1-u)^2)) (Icc a (1/10)) := by
    apply ContinuousOn.div
      ((continuousOn_const.sub (continuousOn_const.mul continuousOn_id)).log
        (fun u hu => by change 2-3*u ≠ 0; linarith [hu.2]))
      (continuousOn_id.mul ((continuousOn_const.sub continuousOn_id).pow 2))
    intro u hu
    change u*(1-u)^2 ≠ 0
    exact mul_ne_zero (by linarith [hu.1]) (pow_ne_zero 2 (by linarith [hu.2]))
  have hi : IntervalIntegrable (fun u : ℝ => Real.log (2-3*u)/(u*(1-u)^2))
      volume a (1/10) := hc.intervalIntegrable_of_Icc hab
  apply hi.congr
  intro u hu
  rw [uIoc_of_le hab] at hu
  exact (inner_weighted_eq ⟨ha.trans hu.1, by linarith [hu.2]⟩).symm

theorem original_kernel_nonneg {N : ℕ} {ρ δ : ℝ} (hN : 2 ≤ N)
    (hρ : 1 < ρ) (hδ : δ ≤ 1/8) : 0 ≤ relaxedPairKernel N ρ δ := by
  unfold relaxedPairKernel
  apply Finset.sum_nonneg
  intro rs hrs
  obtain ⟨_,hu,hv,hcurve⟩ := original_log_geometry hN hρ hrs
  have hg : 0 ≤ 1+3*Real.log ρ/Real.log (N : ℝ)-
      primeLogExponent N rs.1-primeLogExponent N rs.2 := by linarith
  have hd : 0 ≤ (5/9 : ℝ)*(1-primeLogExponent N rs.1)-δ := by linarith
  change 0 ≤ 1/((rs.1 : ℝ)*rs.2*(1+3*Real.log ρ/Real.log (N : ℝ)-
    primeLogExponent N rs.1-primeLogExponent N rs.2)*((5/9 : ℝ)*(1-primeLogExponent N rs.1)-δ))
  exact one_div_nonneg.mpr (mul_nonneg (mul_nonneg (by positivity) hg) hd)

/-- Literal limsup of the original kernel, with rho fixed before N. -/
theorem original_kernel_limsup (ρ δ : ℝ) (hρ : 1 < ρ) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1/8) :
    Filter.limsup (fun N : ℕ => relaxedPairKernel N ρ δ) atTop ≤
      (1+6*δ)*((9/5 : ℝ)*low (100/1327)) := by
  have hnn : ∀ᶠ N : ℕ in atTop, 0 ≤ relaxedPairKernel N ρ δ := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact original_kernel_nonneg hN hρ hδ
  have hcb := isCoboundedUnder_le_of_eventually_le atTop hnn
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨N₀,hN₀⟩ := original_kernel_fixed ρ δ ε hρ hδ0 hδ hε
  exact limsup_le_of_le hcb (eventually_atTop.mpr ⟨N₀,hN₀⟩)

end OriginalU8.Weighted
