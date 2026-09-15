import Hf4NextTerminal

noncomputable section
namespace Hf4Refine
open Real Set MeasureTheory Wu2008DoubleSieve SharpLogRecurrence

def coefficientPart (t v : ℝ) : ℝ :=
  (SigmaJEndpoint.coefficient ((t+1)/(v-1))-SigmaInnerEndpointRecovery.beta t)*
    (upperLog ((t+1)/(v-1))-lowerLog ((t+1)/(v-1)))

theorem variation_split (t v : ℝ) : CorrectionSigmaVariable.variation t v =
    coefficientPart t v + F1LowerResidual.payment ((t+1)/(v-1)) := rfl

theorem coefficient_difference {x B : ℝ} (hx : 0 < x) (hB : 0 < B) :
    SigmaJEndpoint.coefficient x - SigmaJEndpoint.coefficient B =
      6*(B-x)*(B*x-1)/((x^2+8*x+1)*(B^2+8*B+1)) := by
  have hd : 0 < x^2+8*x+1 := by positivity
  have he : 0 < B^2+8*B+1 := by positivity
  unfold SigmaJEndpoint.coefficient
  field_simp
  ring

theorem coefficient_rescale {t v : ℝ} (ht : 1 ≤ t) (hv : 3 ≤ v) :
    coefficientPart t v/v =
    ((v-1)-2)*((t+1)^2-2*(v-1))*((t+1)-(v-1))^5 /
      ((v-1)*((t+1)+(v-1))^3*((t+1)^2+8*(t+1)*(v-1)+(v-1)^2)*
        ((t+1)^2+16*(t+1)+4)*v) := by
  have hs : 0 < t+1 := by linarith
  have hu : 0 < v-1 := by linarith
  have hx : 0 < (t+1)/(v-1) := div_pos hs hu
  unfold coefficientPart SigmaInnerEndpointRecovery.beta
  rw [coefficient_difference hx (by positivity), OriginalFirstErrorRecovery.envelope_gap hx]
  field_simp
  ring

theorem coefficient_denom_upper {s u : ℝ} (hu : 2 ≤ u) (hus : u ≤ s) :
    u*(s+u)^3*(s^2+8*s*u+u^2)*(s^2+16*s+4)*(u+1) ≤ 800*s^8*(s+1) := by
  have hs : 2 ≤ s := hu.trans hus
  have hu0 : 0 ≤ u := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hq : s^2+8*s*u+u^2 ≤ 10*s^2 := by
    calc
      _ ≤ s^2+8*s*s+s^2 := by gcongr
      _ = _ := by ring
  have hb : s^2+16*s+4 ≤ 10*s^2 := by
    nlinarith only [sq_nonneg (s-2), hs]
  calc
    _ ≤ s*(2*s)^3*(10*s^2)*(10*s^2)*(s+1) := by gcongr; linarith
    _ = _ := by ring

theorem coefficient_density_lower {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    (7/2:ℝ)*Hf4Next.coupledCellFactor t*(t-1)*(v-3)*(t+2-v)^5 ≤ coefficientPart t v/v := by
  let s := t+1
  let u := v-1
  have hu : 2 ≤ u := by dsimp [u]; linarith [hv.1]
  have hus : u ≤ s := by dsimp [s,u]; linarith [hv.2]
  have hs : 2 ≤ s := hu.trans hus
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hn : 0 ≤ (u-2)*(s*(s-2))*(s-u)^5 := by positivity
  have hd : 0 < u*(s+u)^3*(s^2+8*s*u+u^2)*(s^2+16*s+4)*(u+1) := by positivity
  have hnum : (u-2)*(s*(s-2))*(s-u)^5 ≤ (u-2)*(s^2-2*u)*(s-u)^5 := by
    gcongr
    nlinarith only [hus]
  calc
    _ = ((u-2)*(s*(s-2))*(s-u)^5)/(800*s^8*(s+1)) := by
      dsimp [Hf4Next.coupledCellFactor,s,u]
      field_simp
      ring
    _ ≤ ((u-2)*(s*(s-2))*(s-u)^5)/
        (u*(s+u)^3*(s^2+8*s*u+u^2)*(s^2+16*s+4)*(u+1)) :=
      div_le_div_of_nonneg_left hn hd (coefficient_denom_upper hu hus)
    _ ≤ ((u-2)*(s^2-2*u)*(s-u)^5)/
        (u*(s+u)^3*(s^2+8*s*u+u^2)*(s^2+16*s+4)*(u+1)) :=
      div_le_div_of_nonneg_right hnum hd.le
    _ = coefficientPart t v/v := by rw [coefficient_rescale ht hv.1]; dsimp [s,u]; ring

/-- A thin recombination of the frozen coupled estimates, now for the residual alone. -/
theorem residual_density_lower {t v : ℝ} (ht : 1 ≤ t) (hv : v ∈ Icc 3 (t+2)) :
    Hf4Next.coupledCellFactor t*(t+2-v)^7 ≤ F1LowerResidual.payment ((t+1)/(v-1))/v := by
  let s := t+1
  let u := v-1
  have hu : 2 ≤ u := by dsimp [u]; linarith [hv.1]
  have hus : u ≤ s := by dsimp [s,u]; linarith [hv.2]
  have hs : 2 ≤ s := hu.trans hus
  have hu0 : 0 < u := by linarith
  have hs0 : 0 < s := by linarith
  have hp : 0 ≤ (s-u)^7 := pow_nonneg (sub_nonneg.mpr hus) _
  have hd : 0 < s^2*(s+u)^4*(s^2+8*s*u+u^2) := by positivity
  calc
    _ = ((s-u)^7/(210*(160*s^8)))*(12*s/(s+1)) := by
      dsimp [Hf4Next.coupledCellFactor,s,u]
      field_simp
      ring
    _ ≤ ((s-u)^7/(210*(s^2*(s+u)^4*(s^2+8*s*u+u^2))))*((5*s+7*u)/(u+1)) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_left hp (by positivity) (by
          exact mul_le_mul_of_nonneg_left (Hf4Next.coupled_denom_upper hu0.le hus) (by norm_num)))
        (Hf4Next.coupled_ratio_lower hu hus) (by positivity) (by positivity)
    _ = _ := by
      rw [show (t+1)/(v-1) = s/u from rfl, Hf4Next.residual_rescale hu0.ne']
      dsimp [s,u]
      ring

/-- Both summands are paid separately, then combined exactly once. -/
theorem combined_density_lower {t b v : ℝ} (ht : 1 ≤ t) (htb : t ≤ b)
    (hv : v ∈ Icc 3 (t+2)) :
    Hf4Next.coupledCellFactor b*((t+2-v)^7+(7/2:ℝ)*(t-1)*(v-3)*(t+2-v)^5) ≤
      CorrectionSigmaVariable.variation t v/v := by
  have hc := Hf4Next.coupledCellFactor_antitone ht htb
  have h1 := residual_density_lower ht hv
  have h2 := coefficient_density_lower ht hv
  have hn : 0 ≤ (t+2-v)^7+(7/2:ℝ)*(t-1)*(v-3)*(t+2-v)^5 := by
    have h3 : 0 ≤ v-3 := by linarith [hv.1]
    have h4 : 0 ≤ t+2-v := by linarith [hv.2]
    positivity
  have h := mul_le_mul_of_nonneg_right hc hn
  rw [variation_split, add_div]
  nlinarith only [h,h1,h2]

end Hf4Refine
