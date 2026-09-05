import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZeroSpecialized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma1017GlobalPropagation
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiDDEUnitShiftRatioSanitized

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace BridgeAssembly

open Section10Lemma1017Comparison

/-- A global continuous extension which does not alter a Section-13 function on
`[2,∞)`. -/
def clampTwo (R : ℝ → ℝ) (s : ℝ) : ℝ := R (max s 2)

lemma clampTwo_continuous {R : ℝ → ℝ} (hR : ContinuousOn R (Ioi 0)) :
    Continuous (clampTwo R) := by
  change Continuous (R ∘ fun s : ℝ => max s 2)
  exact hR.comp_continuous (continuous_id.max continuous_const)
    (fun s => lt_of_lt_of_le (by norm_num) (le_max_right s 2))

lemma clampTwo_eq {R : ℝ → ℝ} {s : ℝ} (hs : 2 ≤ s) : clampTwo R s = R s := by
  simp [clampTwo, max_eq_left hs]

lemma movingWindow_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun s => ∫ t in s - 1..s, f t) := by
  let A : ℝ → ℝ := fun s => ∫ t in 0..s, f t
  have hA : Continuous A :=
    intervalIntegral.continuous_primitive (μ := volume)
      (fun a b => hf.intervalIntegrable a b) 0
  have heq : (fun s => ∫ t in s - 1..s, f t) =
      fun s => A s - A (s - 1) := by
    funext s
    have h := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (hf.intervalIntegrable 0 (s - 1)) (hf.intervalIntegrable (s - 1) s)
    dsimp [A]
    linarith
  rw [heq]
  exact hA.sub (hA.comp (continuous_id.sub continuous_const))

lemma signedPairing_continuous {b : ℝ} {R q : ℝ → ℝ}
    (hR : Continuous R) (hq : Continuous q) :
    Continuous (section10SignedPairing b R q) := by
  have hf : Continuous (fun t => q (t + 1) * R t) :=
    (hq.comp (continuous_id.add continuous_const)).mul hR
  change Continuous (fun s => s * q s * R s -
    b * ∫ t in s - 1..s, q (t + 1) * R t)
  exact ((continuous_id.mul hq).mul hR).sub
    (continuous_const.mul (movingWindow_continuous hf))

lemma continuous_zero_at_three {F : ℝ → ℝ} (hF : Continuous F)
    (hz : ∀ s, 3 < s → F s = 0) : F 3 = 0 := by
  have hlimF : Tendsto F (𝓝[Ioi (3 : ℝ)] 3) (𝓝 (F 3)) :=
    hF.continuousAt.mono_left inf_le_left
  have hlim0 : Tendsto F (𝓝[Ioi (3 : ℝ)] 3) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hz s hs).symm
  exact tendsto_nhds_unique hlimF hlim0

lemma pairing_clampTwo {b s : ℝ} {R q : ℝ → ℝ} (hs : 3 ≤ s) :
    section10SignedPairing b (clampTwo R) q s = section10SignedPairing b R q s := by
  have hs2 : 2 ≤ s := by linarith
  simp only [section10SignedPairing, clampTwo_eq hs2]
  have hi : (∫ t in s - 1..s, q (t + 1) * clampTwo R t) =
      ∫ t in s - 1..s, q (t + 1) * R t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc (s - 1) s := by
      simpa [uIcc_of_le (by linarith : s - 1 ≤ s)] using ht
    change q (t + 1) * clampTwo R t = q (t + 1) * R t
    rw [clampTwo_eq (by linarith [ht'.1] : 2 ≤ t)]
  rw [hi]

lemma clampTwo_hasDerivAt_P {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 3 < s) :
    HasDerivAt (clampTwo (section13Phat H))
      (-(2 * clampTwo (section13Phat H) s - clampTwo (section13Phat H) (s - 1)) / s) s := by
  have hev : clampTwo (section13Phat H) =ᶠ[𝓝 s] section13Phat H := by
    filter_upwards [eventually_gt_nhds (by linarith : 2 < s)] with z hz
    exact clampTwo_eq hz.le
  have hd := (section13Phat_dde hH.toSection13HatContract hs).congr_of_eventuallyEq hev
  apply hd.congr_deriv
  rw [clampTwo_eq (by linarith : 2 ≤ s), clampTwo_eq (by linarith : 2 ≤ s - 1)]

lemma clampTwo_hasDerivAt_Q {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 3 < s) :
    HasDerivAt (clampTwo (section13Qhat H))
      (-(2 * clampTwo (section13Qhat H) s + clampTwo (section13Qhat H) (s - 1)) / s) s := by
  have hev : clampTwo (section13Qhat H) =ᶠ[𝓝 s] section13Qhat H := by
    filter_upwards [eventually_gt_nhds (by linarith : 2 < s)] with z hz
    exact clampTwo_eq hz.le
  have hd := (section13Qhat_dde hH.toSection13HatContract hs).congr_of_eventuallyEq hev
  apply hd.congr_deriv
  rw [clampTwo_eq (by linarith : 2 ≤ s), clampTwo_eq (by linarith : 2 ≤ s - 1)]

/-- The actual globally continuous `SignedPQData` required by Lemma 10.17.
No comparison or pairing premise is used: the pairings come from Section 13. -/
theorem section13_signedPQData {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    SignedPQData (clampTwo (section13Phat H)) (clampTwo (section13Qhat H)) := by
  let P := clampTwo (section13Phat H)
  let Q := clampTwo (section13Qhat H)
  have hPc : Continuous P := clampTwo_continuous
    ((hH.continuous .plus).sub (hH.continuous .minus))
  have hQc : Continuous Q := clampTwo_continuous (section13Qhat_continuousOn hH.toSection13HatContract)
  refine ⟨hPc, hQc, ?_, ?_, ?_, ?_, ?_⟩
  · intro s _
    change 0 < section13Qhat H (max s 2)
    exact section13Qhat_pos hH.toSection13HatContract
      (lt_of_lt_of_le (by norm_num) (le_max_right s 2))
  · intro s hs
    exact clampTwo_hasDerivAt_P hH hs
  · intro s hs
    exact clampTwo_hasDerivAt_Q hH hs
  · intro s hs
    have hz : ∀ u, 3 < u →
        section10SignedPairing (-1) P adjointMinus u = 0 := by
      intro u hu
      rw [pairing_clampTwo hu.le]
      change section10SignedPairing (-1) (section13Phat H) section13AdjointMinus u = 0
      exact section13Phat_pairing_zero hH hu
    have hzero : section10SignedPairing (-1) P adjointMinus 3 = 0 :=
      continuous_zero_at_three (signedPairing_continuous hPc continuous_const) hz
    have hall : section10SignedPairing (-1) P adjointMinus s = 0 := by
      rcases hs.eq_or_lt with rfl | hslt
      · exact hzero
      · exact hz s hslt
    simpa [section10SignedPairing] using hall
  · intro s hs
    have hqcont : Continuous adjointPlus :=
      (continuous_id.pow 2).sub (continuous_const.mul continuous_id) |>.add continuous_const
    have hz : ∀ u, 3 < u → section10SignedPairing 1 Q adjointPlus u = 0 := by
      intro u hu
      rw [pairing_clampTwo hu.le]
      change section10SignedPairing 1 (section13Qhat H) section13AdjointPlus u = 0
      exact section13Qhat_pairing_zero hH hu
    have hzero : section10SignedPairing 1 Q adjointPlus 3 = 0 :=
      continuous_zero_at_three (signedPairing_continuous hQc hqcont) hz
    have hall : section10SignedPairing 1 Q adjointPlus s = 0 := by
      rcases hs.eq_or_lt with rfl | hslt
      · exact hzero
      · exact hz s hslt
    simpa [section10SignedPairing] using hall

/-- Global Lemma 10.17 coefficient assembled from the source contract alone. -/
theorem section13_global_uniform_eta {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ s, 3 ≤ s →
      |section13Phat H s| ≤ η * section13Qhat H s := by
  let Tp := clampTwo (H.T .plus)
  let Tm := clampTwo (H.T .minus)
  let P := clampTwo (section13Phat H)
  let Q := clampTwo (section13Qhat H)
  have hP : P = fun s => Tp s - Tm s := by
    funext s
    simp [P, Tp, Tm, clampTwo, section13Phat]
  have hQ : Q = fun s => Tp s + Tm s := by
    funext s
    simp [Q, Tp, Tm, clampTwo, section13Qhat]
  obtain ⟨η, hη, hη1, hbound⟩ :=
    lemma10_17_global_uniform_eta (section13_signedPQData hH) hP hQ
      (fun s _ => hH.positive .plus (max s 2) (by
        exact lt_of_lt_of_le (by norm_num) (le_max_right s 2)))
      (fun s _ => hH.positive .minus (max s 2) (by
        exact lt_of_lt_of_le (by norm_num) (le_max_right s 2)))
  refine ⟨η, hη, hη1, ?_⟩
  intro s hs
  simpa [P, Q, clampTwo_eq (by linarith : 2 ≤ s)] using hbound s hs

/-- A corrected sign-independent Section-10 bridge on the actual scalar-DDE
range `s ≥ 3`.  This records exactly what the pairing + Lemma 10.17 assembly
proves for both signs. -/
structure Section13HatSection10BridgeAtThree (H : Section13HatLayers) (sign : ErrorSign) where
  Qhat : ℝ → ℝ
  dde : Section10DDEApparatus Qhat 3
  K : ℝ
  one_le_K : 1 ≤ K
  hat_le : ∀ s, 3 ≤ s → H.T sign s ≤ K * Qhat s
  Q_le : ∀ s, 3 ≤ s → Qhat s ≤ K * H.T sign s

noncomputable def section13_bridgeAtThree {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) (sign : ErrorSign) :
    Section13HatSection10BridgeAtThree H sign := by
  let hex := section13_global_uniform_eta hH
  let η := Classical.choose hex
  have hspec := Classical.choose_spec hex
  have hη : 0 < η := hspec.1
  have hη1 : η < 1 := hspec.2.1
  have hbound : ∀ s, 3 ≤ s →
      |section13Phat H s| ≤ η * section13Qhat H s := hspec.2.2
  let K : ℝ := 2 / (1 - η)
  have hden : 0 < 1 - η := by linarith
  have hK1 : 1 ≤ K := by dsimp [K]; apply (le_div_iff₀ hden).2; linarith
  have hcmp := fun s (hs : 3 ≤ s) => section13_comparison_of_P_abs_le hη.le hη1 (hbound s hs)
  refine ⟨section13Qhat H, ?_, K, hK1, ?_, ?_⟩
  · refine ⟨section13AdjointPlus, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (section13Qhat_continuousOn hH.toSection13HatContract).mono
        (by intro s hs; norm_num at hs ⊢; linarith)
    · intro s hs; exact section13Qhat_pos hH.toSection13HatContract (by linarith)
    · intro s hs; dsimp [section13AdjointPlus]; nlinarith [sq_nonneg (s - 1)]
    · intro s hs; exact section13Qhat_dde hH.toSection13HatContract hs
    · intro s _; exact section13AdjointPlus_dde s
    · intro s hs
      simpa [section10Pairing, section10SignedPairing] using section13Qhat_pairing_zero hH hs
  · intro s hs
    have hc := hcmp s hs
    have hupperK : (1 + η) / 2 ≤ 2 / (1 - η) := by
      apply (le_div_iff₀ hden).2
      nlinarith [sq_nonneg η]
    cases sign with
    | plus =>
        have hQ := section13Qhat_pos hH.toSection13HatContract (by linarith : 0 < s)
        have hu := hc.2.1
        dsimp [K]
        apply hu.trans
        apply mul_le_mul_of_nonneg_right _ hQ.le
        exact hupperK
    | minus =>
        have hQ := section13Qhat_pos hH.toSection13HatContract (by linarith : 0 < s)
        have hu := hc.2.2.2
        dsimp [K]
        apply hu.trans
        apply mul_le_mul_of_nonneg_right _ hQ.le
        exact hupperK
  · intro s hs
    have hc := hcmp s hs
    cases sign with
    | plus =>
        have hl := hc.1
        dsimp [K]
        have := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / (1 - η))
        field_simp [ne_of_gt hden] at this ⊢
        nlinarith
    | minus =>
        have hl := hc.2.2.1
        dsimp [K]
        have := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 / (1 - η))
        field_simp [ne_of_gt hden] at this ⊢
        nlinarith

/-- The positive sign has `2 + ε₊ = 3`, so the corrected common bridge is
literally the requested production `Section13HatSection10Bridge`. -/
noncomputable def section13_plus_section10Bridge {H : Section13HatLayers}
    (hH : Section13HatSourceContract H) :
    Section13HatSection10Bridge H ErrorSign.plus := by
  let B := section13_bridgeAtThree hH ErrorSign.plus
  refine ⟨B.Qhat, ?_, B.K, B.one_le_K, ?_, ?_⟩
  · have heq : (2 : ℝ) + ErrorSign.epsilon ErrorSign.plus = 3 := by
      norm_num [ErrorSign.epsilon]
    rw [heq]
    exact B.dde
  · intro s hs
    apply B.hat_le s
    norm_num [ErrorSign.epsilon] at hs ⊢
    exact hs
  · intro s hs
    apply B.Q_le s
    norm_num [ErrorSign.epsilon] at hs ⊢
    exact hs

/-- Audit lemma exposing why the production record cannot be assembled for the
negative sign from the stated source contract: it asks for the scalar `Q̂` DDE
already on `s > 1`, whereas `section13Qhat_dde` is available only on `s > 3`.
This is an interface-strength mismatch, not a missing comparison or pairing. -/
theorem production_minus_bridge_requires_early_scalar_dde
    {H : Section13HatLayers} (B : Section13HatSection10Bridge H ErrorSign.minus) :
    ∀ s, 2 < s →
      HasDerivAt B.Qhat (-(2 * B.Qhat s + B.Qhat (s - 1)) / s) s := by
  intro s hs
  apply B.dde.original_dde s
  norm_num [ErrorSign.epsilon] at hs ⊢
  exact hs

end BridgeAssembly


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
