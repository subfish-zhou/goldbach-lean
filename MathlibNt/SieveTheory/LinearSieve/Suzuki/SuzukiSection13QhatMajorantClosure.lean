import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCutoffClaim146iiiSanitized
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiQuantitativeDerivatives

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral
open MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 1200000

open BridgeAssembly CutoffCorrectedRatio
open Section10Lemma1028
open Section10Lemma1028FirstCrossing
open Section10CanonicalXi

namespace Section13QhatMajorantClosure

/-- The remaining source estimate, with all quantifiers exposed.  It excludes
the scalar equation (10.53) only for a genuine earliest-crossing candidate:
the last implication explicitly carries the strict history before `s`.  Thus
this is not the withdrawn arbitrary-stationary exclusion, and it is not a
majorant, delayed/current ratio, asymptotic certificate, or Claim statement. -/
def UniformQhatStationaryExclusion
    (H : Section13HatLayers) : Prop :=
  ∃ s₀ C : ℝ, 4 ≤ s₀ ∧ 1 ≤ C ∧
    ∀ c : ℝ, C ≤ c →
      (∀ u ∈ Icc (4 : ℝ) s₀,
        normalizedMinusBase (section13Qhat H) xi u < c) →
      ∀ s : ℝ, s₀ ≤ s →
        (∀ u : ℝ, s₀ ≤ u → u < s →
          normalizedMinusBase (section13Qhat H) xi u < c) →
        normalizedMinusBase (section13Qhat H) xi s = c → False

lemma canonical_log_lt_xi {s : ℝ} (hs : Real.exp 1 ≤ s) :
    Real.log s < xi s := by
  exact Section10CanonicalXi.log_lt_xi hs

/-- The eventual logarithmic lower bound required by the sanitized Lemma 10.28
record, derived from the canonical inverse rather than assumed. -/
theorem canonicalXi_eventual_log_lower (c : ℝ) :
    ∃ S A : ℝ, 3 ≤ S ∧ 1 ≤ A ∧ ∀ s, S ≤ s →
      (1 / A) * Real.log (Real.exp 1 * s) ≤ xi s - c - 2 / s := by
  let L : ℝ := max (Real.log 4) (max 2 (2 * c + 5))
  let S : ℝ := Real.exp L
  refine ⟨S, 2, ?_, by norm_num, ?_⟩
  · have hlog4 : Real.log 4 ≤ L := le_max_left _ _
    have h4pos : (0 : ℝ) < 4 := by norm_num
    have h4S : (4 : ℝ) ≤ S := by
      dsimp [S]
      rw [← Real.exp_log h4pos]
      exact Real.exp_le_exp.mpr hlog4
    linarith
  · intro s hs
    have h2L : (2 : ℝ) ≤ L :=
      (le_max_left (2 : ℝ) (2 * c + 5)).trans (le_max_right _ _)
    have hLc : 2 * c + 5 ≤ L :=
      (le_max_right (2 : ℝ) (2 * c + 5)).trans (le_max_right _ _)
    have hSpos : 0 < S := Real.exp_pos L
    have hspos : 0 < s := hSpos.trans_le hs
    have hlog : L ≤ Real.log s := by
      rw [← Real.log_exp L]
      exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos L) hspos hs
    have he1S : Real.exp 1 ≤ S := by
      exact Real.exp_le_exp.mpr (by linarith)
    have he1s : Real.exp 1 ≤ s := he1S.trans hs
    have hxi : Real.log s < xi s := canonical_log_lt_xi he1s
    have hsone : 1 ≤ s := by
      have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
      exact this.le.trans he1s
    have htwo_div : 2 / s ≤ 2 :=
      (div_le_iff₀ hspos).2 (by nlinarith)
    rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hspos), Real.log_exp]
    norm_num
    nlinarith

/-- Canonical `ξ` package used by the first-crossing constructor. -/
theorem canonicalXiTheorem : CanonicalXiTheorem xi where
  continuous := xi_continuous
  positive := fun _s hs => xi_pos hs
  equation := fun _s hs => xi_equation hs
  eventual_log_lower := canonicalXi_eventual_log_lower

/-- The Section-13 source DDE, positivity and proved pairing identity give the
complete non-circular first-crossing apparatus for the single function `Qhat`. -/
noncomputable def section13QhatFirstCrossingData
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    FirstCrossingDDEApparatus (section13Qhat H) 3 where
  adjoint := section13AdjointPlus
  beta_ge_one := by norm_num
  continuous := (section13Qhat_continuousOn hH.toSection13HatContract).mono (by
    intro s hs
    norm_num at hs ⊢
    linarith)
  positive := by
    intro s hs
    exact section13Qhat_pos hH.toSection13HatContract (by linarith)
  original_dde := by
    intro s hs
    exact section13Qhat_dde hH.toSection13HatContract hs
  adjoint_positive := by
    intro s hs
    dsimp [section13AdjointPlus]
    nlinarith [sq_nonneg (s - 1)]
  adjoint_dde := by
    intro s _hs
    exact section13AdjointPlus_dde s
  pairing_zero := by
    intro s hs
    have hz := section13Qhat_pairing_zero hH hs
    have heq := sub_eq_zero.mp hz
    simpa [section10SignedPairing, section13AdjointPlus] using heq

/-- Compactness turns the source-valid exclusion of genuine earliest candidates
into the global nonpositive normalized slope.  No derivative at the left
endpoint is used: the construction is entirely a closed-set minimum argument. -/
theorem global_nonpos_of_uniformQhatStationaryExclusion
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (hexcl : UniformQhatStationaryExclusion H) :
    ∃ c : ℝ, 1 ≤ c ∧ ∀ s : ℝ, 4 ≤ s →
      normalizedMinusBase (section13Qhat H) xi s - c ≤ 0 := by
  rcases hexcl with ⟨s₀, C, hs₀, hC, hexcl⟩
  let f : ℝ → ℝ := normalizedMinusBase (section13Qhat H) xi
  have hf : ContinuousOn f (Ici 4) :=
    normalizedMinusBase_continuousOn
      (section13QhatFirstCrossingData hH) canonicalXiTheorem (by norm_num)
  have hcompact : ContinuousOn f (Icc 4 s₀) :=
    hf.mono (by intro u hu; exact hu.1)
  obtain ⟨B, hB⟩ := isCompact_Icc.bddAbove_image hcompact
  let c : ℝ := max C (B + 1)
  have hCc : C ≤ c := le_max_left _ _
  have hc1 : 1 ≤ c := hC.trans hCc
  have hinitial : ∀ u ∈ Icc (4 : ℝ) s₀, f u < c := by
    intro u hu
    have huB : f u ≤ B := hB ⟨u, hu, rfl⟩
    have hBc : B + 1 ≤ c := le_max_right _ _
    linarith
  refine ⟨c, hc1, ?_⟩
  intro v hv4
  by_cases hv₀ : v ≤ s₀
  · exact (sub_nonpos.mpr (hinitial v ⟨hv4, hv₀⟩).le)
  · have hs₀v : s₀ ≤ v := (lt_of_not_ge hv₀).le
    by_contra hn
    have hcv : c ≤ f v := by linarith
    let K : Set ℝ := Icc s₀ v ∩ f ⁻¹' Ici c
    have hfK : ContinuousOn f (Icc s₀ v) :=
      hf.mono (by intro u hu; exact hs₀.trans hu.1)
    have hKclosed : IsClosed K :=
      hfK.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hKcompact : IsCompact K :=
      isCompact_Icc.of_isClosed_subset hKclosed inter_subset_left
    have hvK : v ∈ K := ⟨⟨hs₀v, le_rfl⟩, hcv⟩
    obtain ⟨s, hsK, hsleast⟩ := hKcompact.exists_isLeast ⟨v, hvK⟩
    have hs₀s : s₀ ≤ s := hsK.1.1
    have hsv : s ≤ v := hsK.1.2
    have hcs : c ≤ f s := hsK.2
    have hleft : f s₀ < c := hinitial s₀ ⟨hs₀, le_rfl⟩
    have hcIcc : c ∈ Icc (f s₀) (f s) := ⟨hleft.le, hcs⟩
    have hcont : ContinuousOn f (Icc s₀ s) :=
      hf.mono (by intro u hu; exact hs₀.trans hu.1)
    obtain ⟨w, hw, hfw⟩ := intermediate_value_Icc hs₀s hcont hcIcc
    have hwK : w ∈ K := by
      exact ⟨⟨hw.1, hw.2.trans hsv⟩, hfw.ge⟩
    have hsw : s ≤ w := hsleast hwK
    have hws : w = s := le_antisymm hw.2 hsw
    have hfs : f s = c := by simpa [hws] using hfw
    have hbefore : ∀ u : ℝ, s₀ ≤ u → u < s → f u < c := by
      intro u hs₀u hus
      by_contra hnu
      have hcu : c ≤ f u := le_of_not_gt hnu
      have huK : u ∈ K := ⟨⟨hs₀u, hus.le.trans hsv⟩, hcu⟩
      exact (not_le_of_gt hus) (hsleast huK)
    exact hexcl c hCc hinitial s hs₀s hbefore hfs

/-- A single honest cutoff majorant for `Qhat`, produced from source data and the
raw uniform stationary exclusion. -/
noncomputable def section13Qhat_cutoffMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (hexcl : UniformQhatStationaryExclusion H) :
    CutoffMajorant (section13Qhat H) := by
  let hw := global_nonpos_of_uniformQhatStationaryExclusion hH hexcl
  let c : ℝ := Classical.choose hw
  have hc : 1 ≤ c := (Classical.choose_spec hw).1
  have hslope : ∀ s : ℝ, 4 ≤ s →
      normalizedMinusBase (section13Qhat H) xi s - c ≤ 0 :=
    (Classical.choose_spec hw).2
  let hlogw := canonicalXi_eventual_log_lower c
  let S : ℝ := Classical.choose hlogw
  let hAw := Classical.choose_spec hlogw
  let A : ℝ := Classical.choose hAw
  have hspec := Classical.choose_spec hAw
  let T : ℝ := max 4 S
  refine ⟨xi, c, T, A, le_max_left _ _, hspec.2.1, ?_, ?_⟩
  · intro s hs
    exact hspec.2.2 s ((le_max_right 4 S).trans hs)
  · intro s hs
    have hs4 : 4 ≤ s := (le_max_left 4 S).trans hs
    have hs0 : 0 < s := by linarith
    have hQs : 0 < section13Qhat H s :=
      section13Qhat_pos hH.toSection13HatContract (by linarith)
    have hn := hslope s hs4
    have hscale : 0 < s * section13Qhat H s := mul_pos hs0 hQs
    have heq :
        -(section13Qhat H (s - 1)) +
            s * (xi s - c - 2 / s) * section13Qhat H s =
          (s * section13Qhat H s) *
            (normalizedMinusBase (section13Qhat H) xi s - c) := by
      dsimp [normalizedMinusBase]
      field_simp [ne_of_gt hs0, ne_of_gt hQs]
      ring
    rw [heq]
    exact mul_nonpos_of_nonneg_of_nonpos hscale.le hn

/-- The sign-indexed bridges are definitionally based on the same scalar `Qhat`;
therefore the one majorant is reused, not reconstructed, for both signs. -/
noncomputable def duplicateQhatMajorant
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    (Q : CutoffMajorant (section13Qhat H)) :
    ∀ sign, CutoffMajorant (section13_bridgeAtThree hH sign).Qhat :=
  fun _ => Q

/-- Exact moving Claim 14.6(iii) conclusion. -/
def MovingClaim146iiiConclusion
    (H : Section13HatLayers) (d Δ : ℝ) : Prop :=
  ∃ D₀ : ℝ, 1 < D₀ ∧ ∀ D : ℝ, D₀ ≤ D →
    ∀ (sign : ErrorSign) (s : ℝ),
      2 + sign.epsilon ≤ s → s ≤ sourceSigma D d →
      (∫ t in s..sourceSigma D d, qD H sign.opposite D d Δ t) <
        (1 - 1 / sourceSigma D d) ^ (1 - Δ) *
          lambda H sign D d 0 s

/-- Section 13 `Qhat` single-majorant closure through the moving Claim 14.6(iii).
The only residual premise is the quantified candidate-level stationary exclusion
above; no majorant, ratio, certificate, or Claim conclusion is assumed. -/
theorem moving_claim14_6_iii_of_uniformQhatStationaryExclusion
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {d Δ : ℝ} (hd : 0 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hexcl : UniformQhatStationaryExclusion H) :
    MovingClaim146iiiConclusion H d Δ := by
  let Q := section13Qhat_cutoffMajorant hH hexcl
  exact moving_claim14_6_iii_of_source_contract_and_cutoffMajorants
    hH hd hΔ0 hΔ1 (duplicateQhatMajorant hH Q)


end Section13QhatMajorantClosure
end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
