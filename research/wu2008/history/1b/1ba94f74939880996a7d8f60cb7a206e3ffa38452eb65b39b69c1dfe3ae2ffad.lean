import R2XiFullRegularity

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix WuPaper.RMapMSigma
open scoped Interval

def originalJ (f : ℝ → ℝ) (r S : ℝ) : ℝ :=
  ∫ u in (1 - 1 / r)..(1 - 1 / S), gProfile f (S * u) / (u * (1 - u))

def original66 (f : ℝ → ℝ) (p : SecondFunctionalParameters) : ℝ :=
  ∫ x in (1 / p.S)..(1 / p.kappa2),
    (∫ u in x..(1 / p.kappa2),
      f (p.S - p.S * x - p.S * u) / (u * (1 - x - u))) / x

def original67 (f : ℝ → ℝ) (p : SecondFunctionalParameters) : ℝ :=
  ∫ x in (1 / p.S)..(1 / p.kappa1),
    (∫ u in (1 / p.kappa2)..(1 / p.kappa3),
      f (p.S - p.S * x - p.S * u) / (u * (1 - x - u))) / x

def original68 (f : ℝ → ℝ) (p : SecondFunctionalParameters) : ℝ :=
  ∫ x in (1 / p.S)..(1 / p.kappa1),
    (∫ u in x..(1 / p.kappa2), f ((1 - x - u) / x) / (u * (1 - x - u))) / x

theorem originalJ_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {r S : ℝ} (hr : 2 ≤ r) (hS : 3 ≤ S) (hS5 : S ≤ 5)
    (hrS : r < S) (hrr : 2 ≤ S - S / r) :
    originalJ f r S = source63RHS f (1 - 1 / r) (1 - 1 / S) S := by
  have hg := J_endpoints hr hS hS5 hrS hrr
  have hj := gProfile_weighted_formula hf hg.1 hg.2.1 hg.2.2.1
    hg.2.2.2.1 hg.2.2.2.2
  unfold originalJ
  rw [rationalWeight_rescale hg.1 hg.2.1 hg.2.2.1 (by linarith : 0 < S), hj.2]

theorem Xi2_original_identity {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 : ℝ)..3, f t * Xi2 p t) =
      (originalJ f p.s p.S + originalJ f p.kappa2 p.S + originalJ f p.kappa3 p.S +
        4 * eProfile f p.S + eProfile f p.kappa1 +
        original66 f p + original67 f p + original68 f p) / 5 := by
  have hi := Xi2_integral_assembly hp (K65_integral_identity hf hp).1
    (K66_integrable hf hp) (K67_integrable hf hp) (K68_integrable hf hp)
  rw [hi.2, (K65_integral_identity hf hp).2, ← equation66 hf hp,
    ← equation67 hf hp, ← equation68 hf hp]
  rcases second_parameter_bounds hp with ⟨hs, hS, hS5, _, hk2, hk3, hsS, h2S, h3S, hr2, hr3⟩
  have hr := hp.2.2.2.2.2.2.2.2.1
  rw [originalJ_identity hf hs hS hS5 hsS hr,
    originalJ_identity hf hk2 hS hS5 h2S hr2,
    originalJ_identity hf hk3 hS hS5 h3S hr3]
  rfl

def actualLowerJ (δ r S : ℝ) : ℝ :=
  ∫ u in (1 - 1 / r)..(1 - 1 / S),
    wuImprovementLimit false δ (S * u) / (u * (1 - u))

def originalSecondFeedback (δ : ℝ) (p : SecondFunctionalParameters) : ℝ :=
  (actualLowerJ δ p.s p.S + actualLowerJ δ p.kappa2 p.S + actualLowerJ δ p.kappa3 p.S +
    4 * wuImprovementLimit true δ p.S + wuImprovementLimit true δ p.kappa1 +
    original66 (wuImprovementLimit true δ) p +
    original67 (wuImprovementLimit true δ) p +
    original68 (wuImprovementLimit true δ) p) / 5

theorem Xi2_actual_feedback {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi2 p t) ≤
      originalSecondFeedback δ p := by
  have hf := wuImprovementLimit_intervalIntegrable true hd (by linarith : δ < 1 / 2)
    (a := 1) (b := 3) (by norm_num) (by norm_num) (by norm_num)
  have hi := Xi2_integral_assembly hp (K65_integral_identity hf hp).1
    (K66_integrable hf hp) (K67_integrable hf hp) (K68_integrable hf hp)
  rw [hi.2, ← equation66 hf hp, ← equation67 hf hp, ← equation68 hf hp]
  have h65 := equation65_actual hd hdhi hp
  unfold originalSecondFeedback actualLowerJ original66 original67 original68
  linarith

theorem original_four_rows_integral_identity (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 1 3) (i : Fin 4) :
    let p := ActualNineFeedback.coupledRow i
    (∫ t in (1 : ℝ)..3, f t * Xi2 p t) =
      (originalJ f p.s p.S + originalJ f p.kappa2 p.S + originalJ f p.kappa3 p.S +
        4 * eProfile f p.S + eProfile f p.kappa1 +
        original66 f p + original67 f p + original68 f p) / 5 :=
  Xi2_original_identity hf (original_four_rows_qualified i)

theorem original_four_rows_actual_feedback {δ : ℝ} (hd : 0 < δ) (hdhi : δ ≤ 1 / 10)
    (i : Fin 4) :
    (∫ t in (1 : ℝ)..3, wuImprovementLimit true δ t * Xi2 (ActualNineFeedback.coupledRow i) t) ≤
      originalSecondFeedback δ (ActualNineFeedback.coupledRow i) :=
  Xi2_actual_feedback hd hdhi (original_four_rows_qualified i)

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
