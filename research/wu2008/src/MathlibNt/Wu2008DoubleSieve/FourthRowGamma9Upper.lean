import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import MathlibNt.Wu2008DoubleSieve.OmegaSwitchedIntegral

/-!
# Small Gamma9: the actual upper with its original envelope

The literal ordered domain is 25/89 ≤ t ≤ u ≤ v ≤ 2/5. The supremum
stays outside the integral and ranges over every phi ≥ 2. The fixed-delta
loss is retained. Only the original source box is required by the upper.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter Set
open scoped Classical Topology

noncomputable def fourthRowGamma9Integral (φ : ℝ) : ℝ :=
  ∫ t in (25 / 89 : ℝ)..(2 / 5), ∫ u in t..(2 / 5), ∫ v in u..(2 / 5),
    LiLiuPrereqBuchstab.buchstab ((φ - t - u - v) / u) / (t * u ^ 2 * v)

noncomputable def fourthRowGamma9I : ℝ := omega3XIntegralEnvelope (5 / 2) (89 / 25)

theorem fourthRowGamma9Integral_eq (φ : ℝ) :
    fourthRowGamma9Integral φ = omega3XIntegral (5 / 2) (89 / 25) φ := by
  norm_num [fourthRowGamma9Integral, omega3XIntegral, omega3XIntegralKernel]

theorem fourthRowGamma9I_eq_envelope :
    fourthRowGamma9I = omega3XIntegralEnvelope (5 / 2) (89 / 25) := rfl

theorem fourthRowGamma9I_eq_sSup :
    fourthRowGamma9I = sSup (fourthRowGamma9Integral '' Ici 2) := by
  simp only [fourthRowGamma9I, omega3XIntegralEnvelope, fourthRowGamma9Integral_eq]

theorem fourthRowGamma9Integral_bddAbove :
    BddAbove (fourthRowGamma9Integral '' Ici 2) := by
  simpa only [fourthRowGamma9Integral_eq] using
    (omega3XIntegral_bddAbove (s := 5 / 2) (t := 89 / 25)
      (by norm_num) (by norm_num) (by norm_num))

theorem fourthRowGamma9I_bounds :
    0 ≤ fourthRowGamma9I ∧ fourthRowGamma9I ≤ 10000 * (2 / 5 - 25 / 89) ^ 3 := by
  have h := omega3XIntegralEnvelope_bounds (s := 5 / 2) (t := 89 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  norm_num only [fourthRowGamma9I, one_div_div] at h ⊢
  exact h

/-- Actual Omega3, not an upper extracted backwards from a mixed inequality.
The two analytic errors and the fixed coefficient slack each cost epsilon/3. -/
theorem fourthRowGamma9_actual_upper (k : ℕ) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        wuOmega3Sum N δ (5 / 2) (89 / 25) (convolutionWuWindows N Δ V) ≤
          (2 / (1 - 2 * δ) * fourthRowGamma9I + ε) *
            boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  let f : ℝ → ℝ := fun ρ =>
    (1 + ρ) * ((1 + ρ) * (1 + ρ * exp (-eulerMascheroniConstant)) *
      (8 / (1 - 2 * δ))) / 4 * fourthRowGamma9I
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hf0 : f 0 = 2 / (1 - 2 * δ) * fourthRowGamma9I := by dsimp [f]; ring
  have hlim := hf.tendsto.mono_left (nhdsWithin_le_nhds :
    𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  rw [hf0] at hlim
  have hsmall := hlim.eventually (gt_mem_nhds
    (show 2 / (1 - 2 * δ) * fourthRowGamma9I <
      2 / (1 - 2 * δ) * fourthRowGamma9I + ε / 3 by linarith))
  have hpos : ∀ᶠ ρ : ℝ in 𝓝[>] (0 : ℝ), 0 < ρ := self_mem_nhdsWithin
  obtain ⟨ρ, hρ, hslack⟩ := (hpos.and hsmall).exists
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨TS, hTS4, hTS⟩ := wu04_54 k hδ hδhi hε3
  obtain ⟨TX, _, hTX⟩ := omega3_switched_upper_envelope k hδ hδhi hρ hρ hε3
  refine ⟨max TS TX, hTS4.trans (le_max_left _ _), ?_⟩
  intro N hN hEven i Δ V hb
  have hNS : TS ≤ N := (le_max_left _ _).trans hN
  have hNX : TX ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := hTS4.trans hNS
  have hs := hTS N hNS N le_rfl hEven i Δ V hb (5 / 2) (89 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  have hx := hTX N hNX hEven i Δ V hb (5 / 2) (89 / 25)
    (by norm_num) (by norm_num) (by norm_num)
  have hC := (wuSingularSeries_pos N (by omega)).le
  have hmass : 0 ≤ boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) :=
    sum_nonneg fun _ _ => by positivity
  have hθ : 0 ≤ boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) :=
    (show 0 ≤ 2 * wuSingularSeries N * (N : ℝ) / log N ^ 2 *
      boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) by positivity).trans
      (omega3_source_theta_lower_singular hN4 hδ hδhi hb)
  have hcoef := mul_le_mul_of_nonneg_right hslack.le hθ
  change f ρ * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) ≤ _ at hcoef
  dsimp only [f, fourthRowGamma9I] at hx hcoef ⊢
  linarith only [hs, hx, hcoef]

/-- The fixed-delta excess over 2I9 is explicit, not an asymptotic error. -/
theorem fourthRowGamma9_fixed_delta_loss {δ : ℝ} (hδhi : δ < 1 / 2) :
    2 / (1 - 2 * δ) * fourthRowGamma9I - 2 * fourthRowGamma9I =
      4 * δ / (1 - 2 * δ) * fourthRowGamma9I := by
  have hd : 1 - 2 * δ ≠ 0 := by linarith
  field_simp
  ring

end Wu2008DoubleSieve
