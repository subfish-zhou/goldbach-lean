import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralEnvelope
import MathlibNt.Wu2008DoubleSieve.FourSeventhsBuchstab
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Wu2008DoubleSieve.HighSixPhase5
open Real Set MeasureTheory
noncomputable section

/-- The fixed source geometry covers every phi in the original unbounded envelope. -/
theorem argument_lower {φ a b c : ℝ} (hφ : 2 ≤ φ)
    (ha : 50/179 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 5/13) :
    11/5 ≤ (φ-a-b-c)/b := by
  have hb : 0 < b := by linarith
  apply (le_div_iff₀ hb).2
  linarith

/-- A single reciprocal chord suffices; the other three factors use their left endpoint. -/
theorem kernel_chord {φ a b c : ℝ} (hφ : 2 ≤ φ)
    (ha : 50/179 ≤ a) (hab : a ≤ b) (hbc : b ≤ c) (hc : c ≤ 5/13) :
    omega3XIntegralKernel φ a b c ≤
      (4/7 : ℝ)*(179/50)^3*(179/50+13/5-(179/50)*(13/5)*c) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hc0 : 0 < c := by linarith
  have hω := SecondFunctionalFourSevenths.buchstab_le_four_sevenths
    (u := (φ-a-b-c)/b) (by linarith [argument_lower hφ ha hab hbc hc])
  have hA : 1/a ≤ (179/50 : ℝ) := (div_le_iff₀ ha0).2 (by linarith)
  have hB : 1/b ≤ (179/50 : ℝ) := (div_le_iff₀ hb0).2 (by linarith)
  have hC := SecondFunctionalFourSevenths.reciprocal_chord
    (a := (50/179 : ℝ)) (b := 5/13) (x := c) (by norm_num) (by norm_num)
    ⟨by linarith, hc⟩
  have hC' : 1/c ≤ 179/50+13/5-(179/50)*(13/5)*c := by
    convert hC using 1; ring
  calc
    _ ≤ (4/7)/(a*b^2*c) := div_le_div_of_nonneg_right hω (by positivity)
    _ = (4/7)*(1/a)*(1/b)^2*(1/c) := by field_simp
    _ ≤ (4/7)*(179/50)*(179/50)^2*(179/50+13/5-(179/50)*(13/5)*c) := by
      gcongr
    _ = _ := by ring

/-- The affine majorant and its successive exact polynomial primitives. -/
def chord (c : ℝ) : ℝ :=
  (4/7 : ℝ)*(179/50)^3*(179/50+13/5-(179/50)*(13/5)*c)
def chordPrimitive (c : ℝ) : ℝ :=
  (4/7 : ℝ)*(179/50)^3*((179/50+13/5)*c-(179/50)*(13/5)*c^2/2)
def innerChord (b : ℝ) : ℝ := chordPrimitive (5/13)-chordPrimitive b
def innerPrimitive (b : ℝ) : ℝ :=
  chordPrimitive (5/13)*b-(4/7 : ℝ)*(179/50)^3*
    ((179/50+13/5)*b^2/2-(179/50)*(13/5)*b^3/6)
def middleChord (a : ℝ) : ℝ := innerPrimitive (5/13)-innerPrimitive a
def middlePrimitive (a : ℝ) : ℝ :=
  innerPrimitive (5/13)*a-chordPrimitive (5/13)*a^2/2+
    (4/7 : ℝ)*(179/50)^3*((179/50+13/5)*a^3/6-(179/50)*(13/5)*a^4/24)

theorem chord_integral (b : ℝ) : (∫ c in b..(5/13 : ℝ), chord c) = innerChord b := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := chordPrimitive)
  · intro x _
    convert (((hasDerivAt_id x).const_mul (179/50+13/5)).sub
      ((((hasDerivAt_id x).pow 2).const_mul ((179/50)*(13/5))).div_const 2)).const_mul
      ((4/7)*(179/50)^3) using 1 <;> first | rfl | (dsimp [chord]; ring)
  · exact (by unfold chord; fun_prop : Continuous chord).intervalIntegrable _ _

theorem inner_integral (a : ℝ) : (∫ b in a..(5/13 : ℝ), innerChord b) = middleChord a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := innerPrimitive)
  · intro x _
    have hd := (((((hasDerivAt_id x).pow 2).const_mul (179/50+13/5)).div_const 2).sub
      ((((hasDerivAt_id x).pow 3).const_mul ((179/50)*(13/5))).div_const 6)).const_mul ((4/7)*(179/50)^3)
    convert ((hasDerivAt_id x).const_mul (chordPrimitive (5/13))).sub hd using 1 <;> first | rfl | (dsimp [innerChord, chordPrimitive]; ring)
  · exact (by unfold innerChord chordPrimitive; fun_prop : Continuous innerChord).intervalIntegrable _ _

theorem middle_integral : (∫ a in (50/179 : ℝ)..(5/13), middleChord a) = 9563183/659100000 := by
  have h : (∫ a in (50/179 : ℝ)..(5/13), middleChord a) =
      middlePrimitive (5/13)-middlePrimitive (50/179) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt (f := middlePrimitive)
    · intro x _
      have hd := (((((hasDerivAt_id x).pow 3).const_mul (179/50+13/5)).div_const 6).sub
        ((((hasDerivAt_id x).pow 4).const_mul ((179/50)*(13/5))).div_const 24)).const_mul ((4/7)*(179/50)^3)
      convert (((hasDerivAt_id x).const_mul (innerPrimitive (5/13))).sub
        ((((hasDerivAt_id x).pow 2).const_mul (chordPrimitive (5/13))).div_const 2)).add hd using 1 <;> first | rfl | (dsimp [middleChord, innerPrimitive, chordPrimitive]; ring)
    · exact (by unfold middleChord innerPrimitive chordPrimitive; fun_prop : Continuous middleChord).intervalIntegrable _ _
  rw [h]
  norm_num [middlePrimitive, innerPrimitive, chordPrimitive]

/-- A uniform upper bound for the actual ordered Buchstab integral. -/
theorem integral_upper {φ : ℝ} (hφ : 2 ≤ φ) :
    omega3XIntegral (13/5) (179/50) φ ≤ 9563183/659100000 := by
  have hinner (a b : ℝ) (ha : 50/179 ≤ a) (hab : a ≤ b) (hb : b ≤ 5/13) :
      (∫ c in b..(5/13 : ℝ), omega3XIntegralKernel φ a b c) ≤ innerChord b := by
    rw [← chord_integral]
    apply intervalIntegral.integral_mono_on hb
      (omega3XIntegralKernel_intervalIntegrable (by linarith) (by linarith) hb)
      ((by unfold chord; fun_prop : Continuous chord).intervalIntegrable _ _)
    intro c hc
    exact kernel_chord hφ ha hab hc.1 hc.2
  have hmiddle (a : ℝ) (ha : a ∈ Icc (50/179 : ℝ) (5/13)) :
      (∫ b in a..(5/13 : ℝ), ∫ c in b..(5/13 : ℝ), omega3XIntegralKernel φ a b c) ≤ middleChord a := by
    rw [← inner_integral]
    exact intervalIntegral.integral_mono_on ha.2
      (omega3XIntegral_inner_intervalIntegrable (by linarith [ha.1]) ha.2)
      ((by unfold innerChord chordPrimitive; fun_prop : Continuous innerChord).intervalIntegrable _ _)
      (fun b hb => hinner a b ha.1 hb.1 hb.2)
  rw [← middle_integral]
  change (∫ a in (1/(179/50) : ℝ)..(1/(13/5)), ∫ b in a..(1/(13/5)),
    ∫ c in b..(1/(13/5)), omega3XIntegralKernel φ a b c) ≤ _
  norm_num only [one_div_div]
  exact intervalIntegral.integral_mono_on (by norm_num)
    (omega3XIntegral_middle_intervalIntegrable (by norm_num) (by norm_num))
    ((by unfold middleChord innerPrimitive chordPrimitive; fun_prop : Continuous middleChord).intervalIntegrable _ _) hmiddle

/-- The full phi >= 2 supremum is paid, without assuming attainment. -/
theorem envelope_upper : omega3XIntegralEnvelope (13/5) (179/50) ≤ 9563183/659100000 := by
  apply csSup_le
  · exact ⟨omega3XIntegral (13/5) (179/50) 2, mem_image_of_mem _ (show (2 : ℝ) ∈ Ici 2 by simp)⟩
  · rintro y ⟨φ, hφ, rfl⟩
    exact integral_upper hφ

end
end Wu2008DoubleSieve.HighSixPhase5
