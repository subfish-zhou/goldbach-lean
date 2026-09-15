import WR2XiFirstActual

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix WuPaper.RMapMSigma
open scoped Interval

def K65 (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  (Icc (alpha2 p) 3).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) ^ 5 / ((p.s - 1) * (p.S - 1) * (p.kappa1 - 1) *
      (p.kappa2 - 1) * (p.kappa3 - 1))) +
  sigma0 t / t * log (1024 / ((p.s - 1) * (p.S - 1) * (p.kappa1 - 1) *
      (p.kappa2 - 1) * (p.kappa3 - 1))) +
  (Icc (alpha5 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((p.kappa3 - 1) * (p.S - 1 - t))) +
  (Icc (alpha4 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((p.kappa2 - 1) * (p.S - 1 - t))) +
  (Icc (alpha3 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((p.s - 1) * (p.S - 1 - t))) +
  (Icc (alpha1 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / (p.kappa1 - 1))

def K66 (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  (Icc (alpha6 p) (alpha4 p)).indicator (fun _ => (1 : ℝ)) t /
    (t * (1 - t / p.S)) * log (p.S / (p.kappa2 * p.S - p.S - p.kappa2 * t)) +
  (Icc (alpha4 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t /
    (t * (1 - t / p.S)) * log (p.S - 1 - t)

def K67 (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  (Icc (alpha7 p) (alpha5 p)).indicator (fun _ => (1 : ℝ)) t /
    (t * (1 - t / p.S)) *
    log (p.S ^ 2 / ((p.kappa1 * p.S - p.S - p.kappa1 * t) *
      (p.kappa3 * p.S - p.S - p.kappa3 * t))) +
  (Icc (alpha5 p) (alpha8 p)).indicator (fun _ => (1 : ℝ)) t /
    (t * (1 - t / p.S)) *
    log (p.S * (p.S - 1 - t) / (p.kappa1 * p.S - p.S - p.kappa1 * t)) +
  (Icc (alpha8 p) (alpha4 p)).indicator (fun _ => (1 : ℝ)) t /
    (t * (1 - t / p.S)) *
    log ((p.S - 1 - t) * (p.kappa2 * p.S - p.S - p.kappa2 * t) / p.S)

def K68 (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  (Icc (alpha9 p) (alpha1 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - t))) +
  (Icc (alpha1 p) (alpha4 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log ((t + 1) / (p.kappa2 - 1)) +
  (Icc (alpha4 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / t *
    log (p.S - 1 - t)

def Xi2 (p : SecondFunctionalParameters) (t : ℝ) : ℝ :=
  sigma0 t / (5 * t) *
    log (1024 / ((p.s - 1) * (p.S - 1) * (p.kappa1 - 1) *
      (p.kappa2 - 1) * (p.kappa3 - 1))) +
  (Icc (alpha2 p) 3).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
    log ((t + 1) ^ 5 / ((p.s - 1) * (p.S - 1) * (p.kappa1 - 1) *
      (p.kappa2 - 1) * (p.kappa3 - 1))) +
  (Icc (alpha9 p) (alpha1 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
    log ((t + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - t))) +
  (Icc (alpha5 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
    log ((t + 1) / ((p.kappa3 - 1) * (p.S - 1 - t))) +
  (Icc (alpha3 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
    log ((t + 1) / ((p.s - 1) * (p.S - 1 - t))) +
  (Icc (alpha1 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t / (5 * t) *
    log ((t + 1) ^ 2 / ((p.kappa1 - 1) * (p.kappa2 - 1))) +
  (Icc (alpha7 p) (alpha5 p)).indicator (fun _ => (1 : ℝ)) t /
    (5 * t * (1 - t / p.S)) *
    log (p.S ^ 2 / ((p.kappa1 * p.S - p.S - p.kappa1 * t) *
      (p.kappa3 * p.S - p.S - p.kappa3 * t))) +
  (Icc (alpha5 p) (alpha8 p)).indicator (fun _ => (1 : ℝ)) t /
    (5 * t * (1 - t / p.S)) *
    log (p.S * (p.S - 1 - t) / (p.kappa1 * p.S - p.S - p.kappa1 * t)) +
  (Icc (alpha6 p) (alpha8 p)).indicator (fun _ => (1 : ℝ)) t /
    (5 * t * (1 - t / p.S)) *
    log (p.S / (p.kappa2 * p.S - p.S - p.kappa2 * t)) +
  (Icc (alpha8 p) (alpha2 p)).indicator (fun _ => (1 : ℝ)) t /
    (5 * t * (1 - t / p.S)) * log (p.S - 1 - t)

theorem second_parameter_bounds {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    2 ≤ p.s ∧ 3 ≤ p.S ∧ p.S ≤ 5 ∧ 3 ≤ p.kappa1 ∧
    2 ≤ p.kappa2 ∧ 2 ≤ p.kappa3 ∧ p.s < p.S ∧
    p.kappa2 < p.S ∧ p.kappa3 < p.S ∧
    2 ≤ p.S - p.S / p.kappa2 ∧ 2 ≤ p.S - p.S / p.kappa3 := by
  rcases hp with ⟨hs, _, hS, hS5, hs3, h32, h21, h1S, _, ha, _⟩
  have ha1 := (ha 0).1
  have ha4 := (ha 3).1
  have ha5 := (ha 4).1
  change 1 ≤ p.kappa1 - 2 at ha1
  change 1 ≤ p.S - p.S / p.kappa2 - 1 at ha4
  change 1 ≤ p.S - p.S / p.kappa3 - 1 at ha5
  exact ⟨hs, hS, hS5, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem second_alpha_bounds {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∀ i, sourceAlphas p i ∈ Icc 1 3) ∧
    alpha1 p < alpha4 p ∧ alpha5 p < alpha8 p ∧
    alpha1 p ≤ alpha2 p ∧ alpha4 p ≤ alpha2 p ∧
    alpha6 p ≤ alpha8 p ∧ alpha8 p ≤ alpha4 p := by
  rcases hp with ⟨hs, _, hS, _, hs3, h32, h21, h1S, _, ha, h14, h58⟩
  have hk1 : 0 < p.kappa1 := by linarith
  have hk2 : 0 < p.kappa2 := by linarith
  have hS0 : 0 ≤ p.S := by linarith
  have hdiv := div_le_div_of_nonneg_left hS0 hk2 h21.le
  have hdiv1 := (one_le_div hk1).mpr h1S
  refine ⟨ha, h14, h58, ?_, alpha4_le_alpha2 hk2 (by linarith), ?_, ?_⟩
  · dsimp [alpha1, alpha2]
    linarith
  · dsimp [alpha6, alpha8]
    rw [mul_div_assoc]
    linarith
  · dsimp [alpha8, alpha4]
    linarith

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
