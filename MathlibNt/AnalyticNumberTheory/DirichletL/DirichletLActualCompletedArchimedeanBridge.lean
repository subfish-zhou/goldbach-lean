import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLQuadraticTatuzawaZeroContribution
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# The actual symmetrically completed Dirichlet L-function

This module removes the abstract `hgammaBridge` input from the Tatuzawa zero
contribution layer.  Mathlib's `DirichletCharacter.completedLFunction` contains
the Deligne gamma factor but not the symmetric conductor factor.  We therefore
adjoin `q ^ (s / 2)` and prove its exact logarithmic-derivative identity.
-/

open Complex

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

/-- The standard symmetric completion
`q^(s/2) Γℝ(s+a) L(s,χ)`, using Mathlib's completed L-function. -/
def symmetricCompletedLFunction {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  (q : ℂ) ^ (s / 2) * χ.completedLFunction s

/-- Its explicit conductor/gamma logarithmic derivative. -/
def conductorGammaTerm {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  log (q : ℂ) / 2 + logDeriv χ.gammaFactor s

lemma differentiable_symmetricCompletedLFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    Differentiable ℂ (symmetricCompletedLFunction χ) := by
  apply Differentiable.mul
  · fun_prop (disch := exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  · exact DirichletCharacter.differentiable_completedLFunction hχ

lemma gammaFactor_ne_zero_of_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 0 < σ) : χ.gammaFactor σ ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simpa using hσ)
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos (by simpa using add_pos_of_pos_of_nonneg hσ zero_le_one)

lemma differentiableAt_gammaFactor_of_pos {q : ℕ} (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : 0 < σ) : DifferentiableAt ℂ χ.gammaFactor σ := by
  -- Recover differentiability from the entire reciprocal away from its zeros.
  have hΓ {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
    simpa only [Pi.inv_def, inv_inv] using
      (differentiable_Gammaℝ_inv s).inv (inv_ne_zero (Gammaℝ_ne_zero_of_re_pos hs))
  rcases χ.even_or_odd with hχ | hχ
  · rw [show χ.gammaFactor = Gammaℝ from funext hχ.gammaFactor_def]
    exact hΓ (by simpa using hσ)
  · rw [show χ.gammaFactor = fun s ↦ Gammaℝ (s + 1) from funext hχ.gammaFactor_def]
    exact (hΓ (by simpa using add_pos_of_pos_of_nonneg hσ zero_le_one)).comp
      (σ : ℂ) (by fun_prop)

lemma logDeriv_conductorFactor {q : ℕ} [NeZero q] (σ : ℂ) :
    logDeriv (fun s : ℂ ↦ (q : ℂ) ^ (s / 2)) σ = log (q : ℂ) / 2 := by
  rw [logDeriv_apply, Complex.deriv_const_cpow (by fun_prop)]
  simp only [deriv_div_const, deriv_id'', one_div]
  field_simp [Nat.cast_ne_zero.mpr (NeZero.ne q)]

/-- Exact character-specific archimedean bridge.  Unlike the former abstract
`hgammaBridge`, every function here is the actual Dirichlet L-function,
its actual symmetric completion, or the explicit conductor/gamma term. -/
theorem negLogDerivative_eq_conductorGamma_sub_completed
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 0 < σ) (hL : χ.LFunction σ ≠ 0) :
    -logDeriv χ.LFunction σ =
      conductorGammaTerm χ σ - logDeriv (symmetricCompletedLFunction χ) σ := by
  have hq : q ≠ 1 := fun hq ↦ hχ (DirichletCharacter.level_one' χ hq)
  have hfun : χ.LFunction = fun s ↦ χ.completedLFunction s / χ.gammaFactor s := by
    funext s
    exact DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (Or.inr hq)
  have hγ0 := gammaFactor_ne_zero_of_pos χ hσ
  have hγd := differentiableAt_gammaFactor_of_pos χ hσ
  have hΛd := (DirichletCharacter.differentiable_completedLFunction hχ) σ
  have hΛ0 : χ.completedLFunction σ ≠ 0 := by
    intro h
    apply hL
    rw [hfun]
    simp [h]
  have hqpow0 : (q : ℂ) ^ ((σ : ℂ) / 2) ≠ 0 :=
    by simp [cpow_eq_zero_iff, Nat.cast_ne_zero.mpr (NeZero.ne q)]
  have hcpowd : DifferentiableAt ℂ (fun s : ℂ ↦ (q : ℂ) ^ (s / 2)) σ := by
    fun_prop (disch := exact Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))
  have hLlog : logDeriv χ.LFunction σ =
      logDeriv χ.completedLFunction σ - logDeriv χ.gammaFactor σ := by
    rw [hfun]
    exact logDeriv_div (σ : ℂ) hΛ0 hγ0 hΛd hγd
  have hsymlog : logDeriv (symmetricCompletedLFunction χ) σ =
      log (q : ℂ) / 2 + logDeriv χ.completedLFunction σ := by
    change logDeriv (fun s : ℂ ↦
      (q : ℂ) ^ (s / 2) * χ.completedLFunction s) σ = _
    rw [logDeriv_mul (σ : ℂ) hqpow0 hΛ0 hcpowd hΛd,
      logDeriv_conductorFactor]
  rw [conductorGammaTerm, hLlog, hsymlog]
  ring

/-- Real-part form used on the real strip in zero-repulsion arguments. -/
theorem negLogDerivative_re_eq_conductorGamma_sub_completed
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {σ : ℝ} (hσ : 0 < σ) (hL : χ.LFunction σ ≠ 0) :
    (-deriv χ.LFunction σ / χ.LFunction σ).re =
      (conductorGammaTerm χ σ).re -
        (deriv (symmetricCompletedLFunction χ) σ /
          symmetricCompletedLFunction χ σ).re := by
  have h := congrArg re
    (negLogDerivative_eq_conductorGamma_sub_completed χ hχ hσ hL)
  simpa only [logDeriv_apply, neg_div, sub_re, neg_re] using h

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
