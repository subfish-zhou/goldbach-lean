import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NoDminFullInduction
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseOneAllD
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144BaseFullUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- The literal no-cutoff depth-one base.  The low strip is supplied by
`lemma14_4_base_one_lowStrip_global_allD`; on the complementary Case-I strip
`3 < s`, both the discrete depth-one source and its continuous main term vanish. -/
theorem lemma14_4_base_one_full_global_allD
    {S : BoundingSieve} {H : Section13HatLayers}
    (hH : Section13HatContract H 2)
    {d Δ C K : ℝ} (hΔ1 : Δ < 1)
    (hCbase : lemma144BaseOneGlobalConstant Δ ≤ C)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    Lemma144MovingDomainNatCeilAt S H C K d Δ 1 2 := by
  intro D _hcut hD s hs hsSigma hz2
  by_cases hs3 : s ≤ 3
  · exact lemma14_4_base_one_lowStrip_global_allD hH hΔ1 hCbase hK hlocal
      D s hD hs hs3 hz2
  · have hs3' : 3 < s := lt_of_not_ge hs3
    rw [suzukiActualT_one_natCeil_eq_zero_of_three_lt S (by omega) hs3']
    rw [finiteSourceLayer_one_eq_zero_of_three_le hs3'.le, zero_add]
    have hs1 : 1 < s := by
      norm_num [KappaOneModel.parityDomain] at hs ⊢
      exact hs
    have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
    have hE : 0 ≤ errorEnvelope H 1 (D : ℝ) d s :=
      errorEnvelope_nonneg H 1 hD1 (by linarith) (hH.positive _ s (by linarith)).le
    have hC0 : 0 ≤ C :=
      (by unfold lemma144BaseOneGlobalConstant; positivity :
        0 ≤ lemma144BaseOneGlobalConstant Δ) |>.trans hCbase
    exact mul_nonneg (suzukiVProduct_nonneg S _) (by positivity)

/-- Convert the additive output exported by the strict/even Case-I producers to
exactly the bracketed moving-domain target used by the no-`Dmin` induction. -/
theorem lemma144_caseI_additive_to_moving
    (S : BoundingSieve) (H : Section13HatLayers)
    {C K d Δ s : ℝ} {M D : ℕ}
    (h : suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ * finiteSourceLayer 1 2 M s +
        sigma12InheritedBudget S H M D ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s) :
    suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 M s +
          C * Real.exp (Real.sqrt K) * errorEnvelope H M (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
  apply h.trans_eq
  unfold sigma12InheritedBudget
  ring

/-- Literal all-depth/no-`Dmin` assembly interface after the pointwise
source-large strict and even-endpoint Case-I producers land.  Their conclusions
are kept in the additive form they actually export; this glue performs only the
parity/endpoint split and algebraic repackaging. -/
theorem lemma14_4_noDmin_allDepth_of_sourceLarge_strict_even
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ C1 Θ : ℝ}
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hCnorm : claim145UniformNormalizationConstant C145 d ≤ C)
    (hH : Section13HatSourceContract H)
    (hΔ1 : Δ < 1)
    (hCbase : lemma144BaseOneGlobalConstant Δ ≤ C)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hclaim : ∀ (N D : ℕ) (s : ℝ),
      1 ≤ N → 2 ≤ D → 2 ≤ s →
      (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ActualClaim145BoundAt S H N D d Δ K s C145)
    (hstrict : ∀ (M D : ℕ) (s : ℝ),
      2 ≤ M → s ∈ KappaOneModel.parityDomain 2 M →
      s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) →
      2 ≤ s → 2 + (ErrorSign.ofDepth M).epsilon ≤ s →
      C1 * K ^ Θ < Real.log (D : ℝ) →
      s ≤ sourceSigma (D : ℝ) d →
      H.betaHat + (ErrorSign.ofDepth M).epsilon < s →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
      suzukiActualT S M D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S ⌈(D : ℝ) ^ (1 / s)⌉₊ * finiteSourceLayer 1 2 M s +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / s)⌉₊ C K d Δ s)
    (heven : ∀ (M D : ℕ),
      Even M → 2 ≤ M → (2 : ℝ) ≤ sourceSigma (D : ℝ) d →
      C1 * K ^ Θ < Real.log (D : ℝ) →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
      suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
        suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
          finiteSourceLayer 1 2 M 2 +
        sigma12InheritedBudget S H M D
          ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2)
    (hcaseII : ∀ (N D : ℕ) (s : ℝ),
      1 ≤ N → 2 ≤ D →
      s ∈ KappaOneModel.parityDomain 2 (N + 1) →
      s ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      Lemma144CaseIIFinalSide (N + 1) s →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N 2 →
      suzukiActualT S (N + 1) D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 (N + 1) s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H (N + 1) (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ))) :
    ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2 := by
  apply lemma14_4_noDmin_allDepth_of_actualClaim145_and_cases S H
    hC145 hd hCnorm hH hK hlocal
    (lemma14_4_base_one_full_global_allD hH.toSection13HatContract hΔ1 hCbase hK hlocal)
    hclaim
  · intro N D s hN hD hs hsSigma hz hregime hnotII hglobal
    have hlarge : C1 * K ^ Θ < Real.log (D : ℝ) :=
      lt_of_not_ge (fun hsmall => hregime (Or.inl hsmall))
    let M := N + 1
    have hM2 : 2 ≤ M := by dsimp [M]; omega
    by_cases hMeven : Even M
    · by_cases hsEq : s = 2
      · subst s
        exact lemma144_caseI_additive_to_moving S H
          (heven M D hMeven hM2 hsSigma hlarge (by simpa [M] using hglobal))
      · have hs2lt : (2 : ℝ) < s := lt_of_le_of_ne (by
          simpa [M, KappaOneModel.parityDomain, Nat.even_iff.mp hMeven] using hs) (Ne.symm hsEq)
        have hpredMod : (M - 1) % 2 = 1 := by
          have hm := Nat.even_iff.mp hMeven
          omega
        have hspred : s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) := by
          simp [KappaOneModel.parityDomain, hpredMod]
          linarith
        have hnotOdd : ¬ Odd M := Nat.not_odd_iff_even.mpr hMeven
        have hlower : 2 + (ErrorSign.ofDepth M).epsilon ≤ s := by
          simp [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon]
          exact hs2lt.le
        have hthreshold : H.betaHat + (ErrorSign.ofDepth M).epsilon < s := by
          rw [hH.betaHat_eq]
          simpa [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon] using hs2lt
        exact lemma144_caseI_additive_to_moving S H
          (hstrict M D s hM2 (by simpa [M] using hs) hspred hs2lt.le hlower
            hlarge hsSigma hthreshold (by simpa [M] using hglobal))
    · have hModd : Odd M := Nat.not_even_iff_odd.mp hMeven
      have hs3 : (3 : ℝ) < s := by
        apply lt_of_not_ge
        intro hsle
        exact hnotII ⟨by simpa [M] using hModd, hsle⟩
      have hpredMod : (M - 1) % 2 = 0 := by
        have hm := Nat.odd_iff.mp hModd
        omega
      have hspred : s - 1 ∈ KappaOneModel.parityDomain 2 (M - 1) := by
        simp [KappaOneModel.parityDomain, hpredMod]
        linarith
      have hlower : 2 + (ErrorSign.ofDepth M).epsilon ≤ s := by
        rw [ErrorSign.ofDepth_of_odd hModd]
        norm_num [ErrorSign.epsilon]
        exact hs3.le
      have hthreshold : H.betaHat + (ErrorSign.ofDepth M).epsilon < s := by
        rw [hH.betaHat_eq, ErrorSign.ofDepth_of_odd hModd]
        norm_num [ErrorSign.epsilon]
        exact hs3
      exact lemma144_caseI_additive_to_moving S H
        (hstrict M D s hM2 (by simpa [M] using hs) hspred (by linarith) hlower
          hlarge hsSigma hthreshold (by simpa [M] using hglobal))
  · exact hcaseII


end MathlibNt.SieveTheory
