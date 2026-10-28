import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticConditionalAnnularLogDerivative
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedRightTailQuantitative
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirichLTwistedSmoothedPsiClose

open Set Function Filter Complex Real MeasureTheory

namespace AnalyticNumberTheory.LargeSieve

open DirichletLGlobalConductorLogDerivativeBound

/-- The quadratic contour uses the full conditional cross-zero width and a
quarter-width extension into the absolutely convergent half-plane. -/
noncomputable def dirichletLTwistedSmoothedQuadraticConditionalLeft
    (A c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  1 - dirichletLQuadraticConditionalCrossZeroWidth A c η q T

noncomputable def dirichletLTwistedSmoothedQuadraticConditionalDelta
    (A c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  dirichletLQuadraticConditionalCrossZeroWidth A c η q T / 4

noncomputable def dirichletLTwistedSmoothedQuadraticConditionalRight
    (A c η : ℝ) (q : ℕ) (T : ℝ) : ℝ :=
  1 + dirichletLTwistedSmoothedQuadraticConditionalDelta A c η q T

/-- The finite quadratic Perron rectangle. -/
def dirichletLTwistedSmoothedQuadraticConditionalRectangle
    (A c η : ℝ) (q : ℕ) (T : ℝ) : Set ℂ :=
  ((dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T : ℂ) - I * T).Rectangle
    (dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T + I * T)

/-- The whole-band estimate pays the complete left edge of the quadratic
Perron rectangle.  This is the quantitative edge needed by the later Bochner
integral estimate; no nonquadratic hypothesis occurs. -/
theorem norm_logDerivative_le_on_quadraticConditionalPerronLeft
    (Z : ℝ) (hZ : 0 < Z)
    (hzeta : ∀ (x u : ℝ), 0 < x → x ≤ 1 → u ≠ 0 →
      ‖riemannZeta (1 + x + I * u)‖ ≤
        Z * (1 + Real.log (|u| + 2) + 1 / |u|))
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hquad : χ ^ 2 = 1) (hχ : χ ≠ 1)
    {A c η T t : ℝ}
    (hA : 0 < A) (hAc : A ≤ c / 256) (hAhalf : A ≤ 1 / 2)
    (hAsmall : A ≤ 1 / (16 * Z * 192 ^ 4))
    (hc : 0 < c) (hη : 0 < η) (hT : 0 < T)
    (hSiegel : c * (q : ℝ) ^ (-η) ≤ (χ.LFunction 1).re)
    (hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T)
    (ht : |t| ≤ T) :
    ‖deriv χ.LFunction
        (dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T + I * t) /
      χ.LFunction
        (dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T + I * t)‖ ≤
      (128 * dirichletLQuadraticConditionalCentralH q T ^ 2) /
          (c * (q : ℝ) ^ (-η)) +
        dirichletLQuadraticConditionalFixedH q
            (dirichletLQuadraticConditionalCentralHeight c η q T) T ^ 12 /
          (A * (q : ℝ) ^ (-2 * η)) := by
  apply norm_logDerivative_le_on_quadraticConditionalWholeBand
    Z hZ hzeta χ hquad hχ hA hAc hAhalf hAsmall hc hη hT hSiegel
  · rfl
  · dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft]
    linarith
  · exact ht

/-- A zero-free quadratic cross-zero rectangle gives a holomorphic Perron
integrand on the narrower variable-right rectangle. -/
theorem twistedSmoothedPerronIntegrand_holomorphicOn_quadraticConditionalRectangle
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {A A₀ c η T : ℝ} (_hAA₀ : A ≤ A₀) (_hA : 0 < A)
    (_hc : 0 < c) (_hη : 0 < η) (hT : 0 < T) (hχ : χ ≠ 1)
    (hw : 0 < dirichletLQuadraticConditionalCrossZeroWidth A c η q T)
    (hw2 : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤ 1 / 2)
    (hwidthle : dirichletLQuadraticConditionalCrossZeroWidth A c η q T ≤
      dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T)
    (hzero : ∀ s ∈ dirichletLQuadraticConditionalCrossZeroRectangle A₀ c η q T,
      χ.LFunction s ≠ 0)
    {ν : ℝ → ℝ} (diffν : ContDiff ℝ 1 ν)
    (νpos : ∀ x > 0, 0 ≤ ν x)
    (suppν : support ν ⊆ Icc (1 / 2) 2)
    (mass_one : ∫ x in Ioi (0 : ℝ), ν x / x = 1)
    {X ε : ℝ} (hX : 0 < X) (hε : 0 < ε) (hε1 : ε < 1) :
    HolomorphicOn (DirichletCharacter.twistedSmoothedPerronIntegrand χ ν ε X)
      (dirichletLTwistedSmoothedQuadraticConditionalRectangle A c η q T) := by
  have hleftRight : dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T ≤
      dirichletLTwistedSmoothedQuadraticConditionalRight A c η q T := by
    dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft,
      dirichletLTwistedSmoothedQuadraticConditionalRight,
      dirichletLTwistedSmoothedQuadraticConditionalDelta]
    linarith only [hw]
  have hsub : dirichletLTwistedSmoothedQuadraticConditionalRectangle A c η q T ⊆
      dirichletLQuadraticConditionalCrossZeroRectangle A₀ c η q T := by
    intro s hs
    rw [dirichletLTwistedSmoothedQuadraticConditionalRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    rw [Set.uIcc_of_le hleftRight, Set.uIcc_of_le (by linarith : -T ≤ T)] at hs
    simp only [mem_Icc] at hs
    rw [dirichletLQuadraticConditionalCrossZeroRectangle, Complex.Rectangle,
      Complex.mem_reProdIm]
    norm_num
    have hcross : 1 - dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T ≤ 2 := by
      have hw0 : 0 ≤ dirichletLQuadraticConditionalCrossZeroWidth A₀ c η q T :=
        hwidthle.trans' hw.le
      linarith
    rw [Set.uIcc_of_le hcross, Set.uIcc_of_le (by linarith : -T ≤ T)]
    refine ⟨⟨?_, ?_⟩, hs.2⟩
    · dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft] at hs
      linarith
    · dsimp only [dirichletLTwistedSmoothedQuadraticConditionalRight,
        dirichletLTwistedSmoothedQuadraticConditionalDelta] at hs
      linarith
  have hlog : HolomorphicOn (fun s => -deriv χ.LFunction s / χ.LFunction s)
      (dirichletLTwistedSmoothedQuadraticConditionalRectangle A c η q T) := by
    have hL : Differentiable ℂ χ.LFunction :=
      DirichletCharacter.differentiable_LFunction hχ
    exact hL.deriv.differentiableOn.neg.div hL.differentiableOn
      (fun s hs => hzero s (hsub hs))
  apply DifferentiableOn.mul
  · apply DifferentiableOn.mul hlog
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply Smooth1MellinDifferentiable diffν suppν ⟨hε, hε1⟩ νpos mass_one
    rw [dirichletLTwistedSmoothedQuadraticConditionalRectangle, Complex.Rectangle,
      Complex.mem_reProdIm] at hs
    norm_num at hs
    have hedge : 0 < dirichletLTwistedSmoothedQuadraticConditionalLeft A c η q T := by
      dsimp only [dirichletLTwistedSmoothedQuadraticConditionalLeft]
      linarith
    rw [Set.uIcc_of_le hleftRight] at hs
    linarith [hs.1.1]
  · intro s _
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_cpow (by fun_prop)
    left
    norm_cast
    exact ne_of_gt hX


end AnalyticNumberTheory.LargeSieve
