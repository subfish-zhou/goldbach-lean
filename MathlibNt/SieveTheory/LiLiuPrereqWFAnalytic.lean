import MathlibNt.SieveTheory.LiLiuPrereqWFParameters
import MathlibNt.SieveTheory.JurkatRichert1965Section13HatSource
import MathlibNt.SieveTheory.SuzukiLemma132SlackFinal
import MathlibNt.SieveTheory.SuzukiLemma144LiteralAllDepthUniformInS

/-!
# Exponential control from the constructed JR hat producer

The factor `s` is cancelled against the denominator of the actual hat formula.
The all-depth theorem is used only in its moving range and at its rounded
natural cutoff. Constants are selected before the sieve, density, and depth.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne
open scoped Classical

namespace JR
export JurkatRichert1965ChenGammaOneQOne
  (jr1965DelayConstant jr1965F jr1965f jr1965HatPlus jr1965HatMinus
    jr1965Section13HatLayers jr1965Section13HatSourceContract
    jr1965HatPlus_eq jr1965HatMinus_eq
    abs_jr1965F_sub_one_le_exp abs_jr1965f_sub_one_le_exp)
end JR

noncomputable def jrHatDecayConstant : ℝ := Real.exp 2 * (1 + Real.exp 1)

theorem jrHatDecayConstant_pos : 0 < jrHatDecayConstant := by
  unfold jrHatDecayConstant
  positivity

private theorem shift_difference_bound (g h : ℝ → ℝ)
    (hg : ∀ t : ℝ, 1 ≤ t →
      |g t - 1| ≤ JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-t))
    (hh : ∀ t : ℝ, 1 ≤ t →
      |h t - 1| ≤ JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-t))
    {s : ℝ} (hs : 2 ≤ s) :
    g s - h (s - 1) ≤
      JR.jr1965DelayConstant * (jrHatDecayConstant * Real.exp (-s)) := by
  have hg' := (abs_le.mp (hg s (by linarith))).2
  have hh' := (abs_le.mp (hh (s - 1) (by linarith))).1
  have he : JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-s) +
      JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-(s - 1)) =
        JR.jr1965DelayConstant * (jrHatDecayConstant * Real.exp (-s)) := by
    rw [show -(s - 1) = -s + 1 by ring, Real.exp_add]
    unfold jrHatDecayConstant
    ring
  linarith

theorem jr_hat_mul_coordinate_le_exp (sign : ErrorSign) {s : ℝ} (hs : 2 ≤ s) :
    s * JR.jr1965Section13HatLayers.T sign s ≤
      jrHatDecayConstant * Real.exp (-s) := by
  have hc : 0 < JR.jr1965DelayConstant := by
    unfold JR.jr1965DelayConstant
    positivity
  have hs0 : 0 < s := by linarith
  have hplus := shift_difference_bound JR.jr1965F JR.jr1965f
    (fun _ ht => JR.abs_jr1965F_sub_one_le_exp ht)
    (fun _ ht => JR.abs_jr1965f_sub_one_le_exp ht) hs
  cases sign with
  | plus =>
      change s * JR.jr1965HatPlus s ≤ _
      rw [JR.jr1965HatPlus_eq (by linarith)]
      have heq : s * ((JR.jr1965F s - JR.jr1965f (s - 1)) /
          (JR.jr1965DelayConstant * s)) =
          (JR.jr1965F s - JR.jr1965f (s - 1)) / JR.jr1965DelayConstant := by
        field_simp
      rw [heq]
      exact (div_le_iff₀ hc).mpr (hplus.trans_eq (mul_comm _ _))
  | minus =>
      change s * JR.jr1965HatMinus s ≤ _
      rw [JR.jr1965HatMinus_eq hs]
      have hF := (abs_le.mp (JR.abs_jr1965F_sub_one_le_exp
        (show 1 ≤ s - 1 by linarith))).2
      have hf := (abs_le.mp (JR.abs_jr1965f_sub_one_le_exp
        (show 1 ≤ s by linarith))).1
      have hn : JR.jr1965F (s - 1) - JR.jr1965f s ≤
          JR.jr1965DelayConstant * (jrHatDecayConstant * Real.exp (-s)) := by
        have he : JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-(s - 1)) +
            JR.jr1965DelayConstant * Real.exp 2 * Real.exp (-s) =
              JR.jr1965DelayConstant * (jrHatDecayConstant * Real.exp (-s)) := by
          rw [show -(s - 1) = -s + 1 by ring, Real.exp_add]
          unfold jrHatDecayConstant
          ring
        linarith
      have heq : s * ((JR.jr1965F (s - 1) - JR.jr1965f s) /
          (JR.jr1965DelayConstant * s)) =
          (JR.jr1965F (s - 1) - JR.jr1965f s) / JR.jr1965DelayConstant := by
        field_simp
      rw [heq]
      exact (div_le_iff₀ hc).mpr (hn.trans_eq (mul_comm _ _))

theorem jr_errorEnvelope_le_exp (N : ℕ) {R s : ℝ}
    (hs : 2 ≤ s) (hbudget : s ^ 13 ≤ Real.log R) :
    errorEnvelope JR.jr1965Section13HatLayers N R 12 s ≤
      Real.exp 1 * (jrHatDecayConstant * Real.exp (-s)) := by
  have ht : 0 ≤ s * JR.jr1965Section13HatLayers.T (ErrorSign.ofDepth N) s :=
    mul_nonneg (by linarith)
      (JR.jr1965Section13HatSourceContract.positive _ _ (by linarith)).le
  have he := moving_envelope_le_exp_one (by linarith : 0 < s) hbudget
  have hh := jr_hat_mul_coordinate_le_exp (ErrorSign.ofDepth N) hs
  unfold errorEnvelope Section13HatLayers.kappaHat
  norm_num only [sub_self, zero_add, Real.rpow_one]
  rw [show s ^ (12 : ℝ) = s ^ (12 : ℕ) from Real.rpow_natCast s 12, mul_assoc]
  exact (mul_le_mul_of_nonneg_right he ht).trans
    (mul_le_mul_of_nonneg_left hh (Real.exp_pos 1).le)

theorem exists_jr_finiteSourceLayer_exp_bound :
    ∃ A : ℝ, 0 < A ∧ ∀ (N : ℕ) (s : ℝ), 1 ≤ N → 2 ≤ s →
      s ∈ KappaOneModel.parityDomain 2 N →
      finiteSourceLayer 1 2 N s ≤ A * Real.exp (-s) := by
  obtain ⟨C, hC, h⟩ := finiteSourceLayer_le_uniform_mul_hat
    (lemma132_finiteLayerHatUniform_slack JR.jr1965Section13HatSourceContract)
  refine ⟨C * jrHatDecayConstant, mul_pos (by linarith) jrHatDecayConstant_pos, ?_⟩
  intro N s hN hs hdom
  exact (h N s hN (by linarith) hdom).trans
    ((mul_le_mul_of_nonneg_left (jr_hat_mul_coordinate_le_exp _ hs)
      (by linarith : 0 ≤ C)).trans_eq (by ring))

theorem sourceParameters_twelve_third_five :
    SuzukiClaim145SourceParameters 12 (1 / 3) 5 := by
  constructor <;> norm_num

/-- Genuine all-depth exponential estimate, from the constructed source
producer. The numerical budget implies, rather than removes, its moving range. -/
theorem exists_actualT_exp_bound :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (S : BoundingSieve) (K : ℝ) (N R : ℕ) (s : ℝ),
        2 ≤ K → HasDimensionOneLocalProductBound S K →
        1 ≤ N → 2 ≤ R → 2 ≤ s →
        s ∈ KappaOneModel.parityDomain 2 N →
        s ^ 13 ≤ Real.log (R : ℝ) →
        Real.exp 1 ≤ Real.log (R : ℝ) →
        2 ≤ ⌈(R : ℝ) ^ (1 / s)⌉₊ →
        suzukiActualT S N R ⌈(R : ℝ) ^ (1 / s)⌉₊ ≤
          suzukiVProduct S (⌈(R : ℝ) ^ (1 / s)⌉₊ : ℝ) *
            (A * Real.exp (-s) +
              B * Real.exp (Real.sqrt K) * Real.exp (-s) *
                (Real.log (R : ℝ)) ^ (-(1 / 3 : ℝ))) := by
  obtain ⟨Cmin, _hmin, hsource⟩ :=
    exists_lemma14_4_movingRange_rounded_allDepth_uniform_in_S_of_source
      JR.jr1965Section13HatLayers JR.jr1965Section13HatSourceContract
      sourceParameters_twelve_third_five
  obtain ⟨_C145, _Clow, C, _h145, _hlow, hC, hsource⟩ := hsource Cmin le_rfl
  obtain ⟨A, hA, hlayer⟩ := exists_jr_finiteSourceLayer_exp_bound
  refine ⟨A, C * Real.exp 1 * jrHatDecayConstant, hA,
    mul_pos (mul_pos (by linarith) (Real.exp_pos 1)) jrHatDecayConstant_pos, ?_⟩
  intro S K N R s hK hlocal hN hR hs hdom hbudget hlog hz
  have hR0 : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
  have hsSigma : s ≤ sourceSigma (R : ℝ) 12 := by
    exact moving_range_of_power_budget hR0 (by linarith) hbudget hlog
  have hraw := hsource S K hK hlocal N hN R hR hR s hdom hsSigma hz
  have henv := jr_errorEnvelope_le_exp N hs hbudget
  have hlog0 : 0 ≤ (Real.log (R : ℝ)) ^ (-(1 / 3 : ℝ)) :=
    Real.rpow_nonneg (lt_of_lt_of_le (Real.exp_pos 1) hlog).le _
  apply hraw.trans
  apply mul_le_mul_of_nonneg_left _ (suzukiVProduct_nonneg S _)
  apply add_le_add (hlayer N s hN hs hdom)
  calc
    C * Real.exp (Real.sqrt K) *
        errorEnvelope JR.jr1965Section13HatLayers N (R : ℝ) 12 s *
        (Real.log (R : ℝ)) ^ (-(1 / 3 : ℝ)) ≤
      C * Real.exp (Real.sqrt K) *
        (Real.exp 1 * (jrHatDecayConstant * Real.exp (-s))) *
        (Real.log (R : ℝ)) ^ (-(1 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left henv
          (mul_nonneg (by linarith) (Real.exp_pos _).le)) hlog0
    _ = _ := by ring

#check jr_hat_mul_coordinate_le_exp
#check jr_errorEnvelope_le_exp
#check exists_jr_finiteSourceLayer_exp_bound
#check sourceParameters_twelve_third_five
#check exists_actualT_exp_bound
#print axioms jr_hat_mul_coordinate_le_exp
#print axioms jr_errorEnvelope_le_exp
#print axioms exists_jr_finiteSourceLayer_exp_bound
#print axioms sourceParameters_twelve_third_five
#print axioms exists_actualT_exp_bound

end MathlibNt.SieveTheory.LiLiuPrereqWF.SmallRosser
