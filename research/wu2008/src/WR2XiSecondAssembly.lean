import WR2XiEquation65

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem Xi2_kernel_assembly {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    {t : ℝ} (ht : t ∈ Icc 1 3)
    (ht4 : t ≠ alpha4 p) (ht8 : t ≠ alpha8 p)
    (hQ : p.S - 1 - t ≠ 0) (hD : p.kappa2 * p.S - p.S - p.kappa2 * t ≠ 0) :
    5 * Xi2 p t = K65 p t + K66 p t + K67 p t + K68 p t := by
  rcases second_parameter_bounds hp with ⟨_, hS, _, hk1, hk2, _⟩
  have ha := second_alpha_bounds hp
  have h14 := ha.2.1.le
  have h42 := ha.2.2.2.2.1
  have h68 := ha.2.2.2.2.2.1
  have h84 := ha.2.2.2.2.2.2
  have hsplit1 := closed_indicator_split h14 h42 ht4
  have hsplit2 := closed_indicator_split h68 h84 ht8
  have hsplit3 := closed_indicator_split h84 h42 ht4
  have hk11 : p.kappa1 - 1 ≠ 0 := by linarith
  have hk21 : p.kappa2 - 1 ≠ 0 := by linarith
  have hS0 : p.S ≠ 0 := by linarith
  have ht1 : t + 1 ≠ 0 := by linarith [ht.1]
  dsimp only [Xi2, K65, K66, K67, K68]
  simp_rw [hsplit1, hsplit2, hsplit3]
  simp only [
    log_div (pow_ne_zero 2 ht1) (mul_ne_zero hk11 hk21), log_pow,
    log_mul hk11 hk21, log_div ht1 hk11, log_div ht1 hk21,
    log_div ht1 (mul_ne_zero hk21 hQ), log_mul hk21 hQ,
    log_div hS0 hD, log_div (mul_ne_zero hQ hD) hS0, log_mul hQ hD]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem Xi2_kernel_assembly_ae {p : SecondFunctionalParameters}
    (hp : PropositionFourGeometry p) :
    ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (1 : ℝ) 3 →
      5 * Xi2 p t = K65 p t + K66 p t + K67 p t + K68 p t := by
  have hex (a : ℝ) : ∀ᵐ t : ℝ ∂volume, t ≠ a := by rw [ae_iff]; simp
  filter_upwards [hex (alpha4 p), hex (alpha8 p), hex (p.S - 1),
    hex (p.S - p.S / p.kappa2)] with t h4 h8 hQ hD ht
  have hm := uIoc_subset_uIcc ht
  rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at hm
  have hk2 : p.kappa2 ≠ 0 := by
    have h := (second_parameter_bounds hp).2.2.2.2.1
    linarith
  apply Xi2_kernel_assembly hp hm h4 h8 (by intro he; apply hQ; linarith)
  intro he
  apply hD
  have hm := div_mul_cancel₀ p.S hk2
  apply (mul_right_cancel₀ hk2)
  nlinarith

theorem Xi2_integral_assembly {f : ℝ → ℝ}
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    (h65 : IntervalIntegrable (fun t => f t * K65 p t) volume 1 3)
    (h66 : IntervalIntegrable (fun t => f t * K66 p t) volume 1 3)
    (h67 : IntervalIntegrable (fun t => f t * K67 p t) volume 1 3)
    (h68 : IntervalIntegrable (fun t => f t * K68 p t) volume 1 3) :
    IntervalIntegrable (fun t => f t * Xi2 p t) volume 1 3 ∧
    (∫ t in (1 : ℝ)..3, f t * Xi2 p t) =
      ((∫ t in (1 : ℝ)..3, f t * K65 p t) +
       (∫ t in (1 : ℝ)..3, f t * K66 p t) +
       (∫ t in (1 : ℝ)..3, f t * K67 p t) +
       (∫ t in (1 : ℝ)..3, f t * K68 p t)) / 5 := by
  have he : ∀ᵐ t : ℝ ∂volume, t ∈ uIoc (1 : ℝ) 3 →
      f t * Xi2 p t =
        (f t * K65 p t + f t * K66 p t + f t * K67 p t + f t * K68 p t) / 5 := by
    filter_upwards [Xi2_kernel_assembly_ae hp] with t ht hm
    have h := congrArg (fun x => f t * x / 5) (ht hm)
    linarith
  have hi := (((h65.add h66).add h67).add h68).div_const 5
  refine ⟨hi.congr_ae ?_, ?_⟩
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
    filter_upwards [he] with t ht
    exact fun hm => (ht hm).symm
  · rw [intervalIntegral.integral_congr_ae he, intervalIntegral.integral_div,
      intervalIntegral.integral_add ((h65.add h66).add h67) h68,
      intervalIntegral.integral_add (h65.add h66) h67,
      intervalIntegral.integral_add h65 h66]

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
