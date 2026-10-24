import MathlibNt.Wu2004MeanValue.GammaFiveLossBudgetGeneral
import MathlibNt.Wu2004MeanValue.GammaFiveLossSections

/-! Exact logarithmic loss from imposing the Gamma₅ legal section cutoff.
These pointwise identities are independent of the weight H. Applications to
counting still require the full and legal integral transport identities. -/

namespace Wu2004MeanValue.GammaFiveLossBudget
open Real

noncomputable def sectionLog (W L U : ℝ) : ℝ :=
  if L < U then log (U*(W-L)/(L*(W-U))) else 0

/-- The symmetric full section has a single logarithmic ratio. -/
theorem sectionLog_half {W B : ℝ} (hL : 0 < W-B) (hB : W/2 ≤ B) :
    sectionLog W (W-B) (W/2) = log (B/(W-B)) := by
  have hW : 0 < W := by linarith
  by_cases h : W-B < W/2
  · rw [sectionLog, if_pos h]
    congr 1
    field_simp
    ring
  · have he : B = W/2 := by linarith
    have hr : B/(W-B) = 1 := by
      apply (div_eq_one_iff_eq hL.ne').mpr
      linarith
    simp only [sectionLog, if_neg h, hr, log_one]

/-- Removing the legal cutoff gives the two branches of the loss logarithm. -/
theorem sectionLog_difference {W B r : ℝ} (hL : 0 < W-B)
    (hB : W/2 ≤ B) (hr : 0 < r) (hrW : r ≤ W/2) :
    sectionLog W (W-B) (W/2) - sectionLog W (W-B) r =
      if r ≤ W-B then log (B/(W-B)) else log ((W-r)/r) := by
  rw [sectionLog_half hL hB]
  by_cases h : r ≤ W-B
  · simp only [sectionLog, if_neg (not_lt.mpr h), if_pos h, sub_zero]
  · have hBr : W-B < r := lt_of_not_ge h
    have hB0 : 0 < B := by linarith
    have hWr : 0 < W-r := by linarith
    have hx : B/(W-B) ≠ 0 := (div_pos hB0 hL).ne'
    have hy : r*(W-(W-B))/((W-B)*(W-r)) ≠ 0 := by
      apply ne_of_gt
      apply div_pos
      · apply mul_pos hr
        linarith
      · exact mul_pos hL hWr
    rw [if_neg h, sectionLog, if_pos hBr, ← log_div hx hy]
    congr 1
    field_simp [hB0.ne', hr.ne', hL.ne', hWr.ne']
    ring

/-- On the loss interval, the full-minus-legal logarithmic section is exactly
five times the scalar loss kernel. The integral count uses the prefactor on
the left; `generalKernel` already includes the factor one fifth. -/
theorem sectionLog_loss_identity {S B v : ℝ}
    (hS : 0 < S) (hBhi : B < 1/2) (hA : 5/4 ≤ S*(1-2*B))
    (hv : S*(1-2*B) ≤ v ∧ v ≤ S/3) :
    (1/(v*(1-v/S))) *
      (sectionLog (1-v/S) (1-v/S-B) ((1-v/S)/2) -
        sectionLog (1-v/S) (1-v/S-B) (v/S)) = 5*generalKernel S B v := by
  have hv0 : 0 < v := by linarith [hv.1]
  have hr0 : 0 < v/S := div_pos hv0 hS
  have hr : v/S ≤ 1/3 := (div_le_iff₀ hS).mpr (by linarith [hv.2])
  have hrlo : 1-2*B ≤ v/S := (le_div_iff₀ hS).mpr (by nlinarith [hv.1])
  have hL : 0 < 1-v/S-B := by linarith
  have hB : (1-v/S)/2 ≤ B := by linarith
  have hrW : v/S ≤ (1-v/S)/2 := by linarith
  rw [sectionLog_difference hL hB hr0 hrW]
  have hcut : v/S ≤ 1-v/S-B ↔ v ≤ S*(1-B)/2 := by
    have he : v/S*S = v := div_mul_cancel₀ v hS.ne'
    constructor
    · intro h
      have hm := mul_nonneg (by linarith : 0 ≤ 1-B-2*(v/S)) hS.le
      nlinarith
    · intro h
      have hh : v/S ≤ (1-B)/2 := (div_le_iff₀ hS).mpr (by nlinarith)
      linarith
  by_cases hc : v ≤ S*(1-B)/2
  · rw [if_pos (hcut.mpr hc), generalKernel, if_pos ⟨hv.1,hc⟩]
    ring
  · have hn : ¬(S*(1-2*B) ≤ v ∧ v ≤ S*(1-B)/2) := fun h => hc h.2
    rw [if_neg (fun h => hc (hcut.mp h)), generalKernel, if_neg hn]
    have heq : (1-v/S-v/S)/(v/S) = (S-2*v)/v := by
      field_simp
      ring
    rw [heq]
    by_cases he : v < S/3
    · rw [if_pos ⟨lt_of_not_ge hc,he⟩]
      ring
    · have hvE : v = S/3 := le_antisymm hv.2 (le_of_not_gt he)
      have hnE : ¬(S*(1-B)/2 < v ∧ v < S/3) := fun h => he h.2
      have hratio : (S-2*v)/v = 1 := by
        apply (div_eq_one_iff_eq hv0.ne').mpr
        linarith
      rw [if_neg hnE, hratio, log_one, mul_zero, mul_zero]

/-- Full logarithmic section before imposing t ≤ v/S. -/
noncomputable def fullSectionLog (S B v : ℝ) : ℝ :=
  sectionLog (1-v/S)
    (max (1/S) (max (1-v/S-B) (1-v/S-1/2)))
    (min B (min (1-v/S-1/S) ((1-v/S)/2)))

/-- Legal logarithmic section, with the additional upper cutoff t ≤ v/S. -/
noncomputable def legalSectionLog (S B v : ℝ) : ℝ :=
  sectionLog (1-v/S)
    (max (1/S) (max (1-v/S-B) (1-v/S-1/2)))
    (min B (min (1-v/S-1/S) (min ((1-v/S)/2) (v/S))))

/-- The parameterized loss kernel is the full-minus-legal section on all of ℝ. -/
theorem full_sub_legal_kernel {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (v : ℝ) :
    (1/(v*(1-v/S))) * (fullSectionLog S B v - legalSectionLog S B v) =
      5*generalKernel S B v := by
  by_cases hleft : S*(1-2*B) ≤ v
  · by_cases hright : v ≤ S/3
    · obtain ⟨hL,hF,hU⟩ := loss_section_endpoints hS hB hBhi hA ⟨hleft,hright⟩
      simp only [fullSectionLog, legalSectionLog, hL, hF, hU]
      exact sectionLog_loss_identity hS hBhi hA ⟨hleft,hright⟩
    · have hU := legal_upper_eq_full_above (B := B) hS (le_of_not_ge hright)
      have hg : generalKernel S B v = 0 := by
        by_contra hn
        exact hright (generalKernel_support hS hB hBhi hn).2
      simp only [fullSectionLog, legalSectionLog, hU, sub_self, mul_zero, hg]
  · have hF := full_section_empty_below (B := B) hS (le_of_not_ge hleft)
    have hU : min B (min (1-v/S-1/S) (min ((1-v/S)/2) (v/S))) ≤
        min B (min (1-v/S-1/S) ((1-v/S)/2)) :=
      min_le_min_left _ (min_le_min_left _ (min_le_left _ _))
    have hg : generalKernel S B v = 0 := by
      by_contra hn
      exact hleft (generalKernel_support hS hB hBhi hn).1.le
    simp only [fullSectionLog, legalSectionLog, sectionLog, if_neg (not_lt.mpr hF),
      if_neg (not_lt.mpr (hU.trans hF)), sub_self, mul_zero, hg]

/-- Weighted form of the exact loss identity, without extra integrability
hypotheses: multiplication by the constant commutes with the interval integral. -/
theorem weighted_section_loss_identity {S B : ℝ}
    (hS : 0 < S) (hB : 1/3 ≤ B) (hBhi : B < 1/2)
    (hA : 5/4 ≤ S*(1-2*B)) (H : ℝ → ℝ) (a b : ℝ) :
    (∫ v in a..b, H v * (1/(v*(1-v/S))) *
      (fullSectionLog S B v - legalSectionLog S B v)) =
      5 * (∫ v in a..b, H v * generalKernel S B v) := by
  calc
    _ = ∫ v in a..b, 5 * (H v * generalKernel S B v) := by
      apply intervalIntegral.integral_congr
      intro v _
      dsimp only
      rw [mul_assoc, full_sub_legal_kernel hS hB hBhi hA]
      ring
    _ = _ := intervalIntegral.integral_const_mul _ _

end Wu2004MeanValue.GammaFiveLossBudget
