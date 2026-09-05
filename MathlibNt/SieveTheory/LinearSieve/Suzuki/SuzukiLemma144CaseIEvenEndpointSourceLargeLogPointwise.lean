import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpointSourceLargeLogSameC
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma0CaseBUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeCoefficientUniform
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144SourceLargeLogFixedThreshold
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseISourceLargeLogUniform

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-!
# Even Case-I source-large pointwise producer

This is the no-post-`K` endpoint producer at `s = 2`.  The induction threshold is
literally `Dmin = 2`.  Every source-fixed cutoff is selected before `C1,C,K,M,D`
and is paid pointwise by `C1 * K ^ Θ < log D`.  The only exponent assumptions
are the formal `SuzukiClaim145SourceParameters` packet.
-/

/-- Even `s=2` Case-I pointwise producer with fixed induction threshold `2`.
There is no eventual quantifier after `K`; the source separator pays the finite
geometry, source-coordinate, error-transport, Claim-14.6, and `Σ₁₂` cutoffs. -/
theorem exists_lemma14_4_caseI_evenEndpoint_sourceLargeLog_pointwise_uniform_in_S
    (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min CB : ℝ, 1 ≤ C1min ∧ 0 < CB ∧
      ∀ (S : BoundingSieve) (C1 C K : ℝ) (M D : ℕ),
        C1min ≤ C1 → max 3 CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        Even M → 2 ≤ M →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
            finiteSourceLayer 1 2 M 2 +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  have hd1 : 1 < d := by
    have hden : 0 < 1 - Δ := sub_pos.mpr hsrc.hDelta_lt
    have hdenlt : 1 - Δ < 1 := by linarith [hsrc.hDelta_pos]
    have hseven : 7 < 7 / (1 - Δ) := by
      apply (lt_div_iff₀ hden).2
      nlinarith
    linarith [hsrc.h14_1]
  obtain ⟨L, hL, hfinite⟩ :=
    lemma132_finiteSourceLayer_evenEndpoint_uniform_sourceLargeConsumer hH
  obtain ⟨R, hR, _hratio⟩ :=
    proposition131iii_uniform_reverse_adjacent_ratio_of_source hH
  let Amax : ℝ := 1 + 2 * L * R + 12 * R
  have hAmax : 0 ≤ Amax := by dsimp [Amax]; positivity
  obtain ⟨C1coef, hC1coef, hcoef⟩ :=
    exists_caseISourceOrderCoefficient_sourceLargeLog_uniform
      hAmax hsrc.hDelta_pos hsrc.hDelta_lt hsrc.h14_1 hsrc.hTheta_pos
  obtain ⟨C1scalar, hC1scalar, hscalar⟩ :=
    exists_caseI1423_sourceScalar_sourceLargeLog_uniform_of_source hsrc
  obtain ⟨C1B, CB, hC1B, hCB, hcaseB⟩ :=
    claim145_caseB_sigmaZero_uniform_even_in_S H hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hsrc.one_le_theta hH
  obtain ⟨D12, hD12pos, h12⟩ :=
    exists_sigmaTwelve_internal_contraction_binderUniform_in_S
      (H := H) hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨D146, hD146pos, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma
      hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt
  obtain ⟨Dg, hDgpos, hg⟩ := exists_caseI_preThreshold_geometry_packet d hd1
  obtain ⟨Dσ, hDσpos, hσlarge⟩ := exists_sourceSigma_three_threshold d hsrc.d_pos
  obtain ⟨Drec, hrec⟩ := eventually_atTop.1
    (eventually_recursiveCoordinate_le_quotient_sourceSigma_uniform hd1)
  obtain ⟨Derr, herr⟩ := eventually_atTop.1
    (eventually_caseI_errorEnvelope_transport_uniform_in_S
      H hH hd1 hsrc.hDelta_pos hsrc.hDelta_lt)
  let Dcut : ℝ := max 4 (max D12 (max D146
    (max Dg (max Dσ (max (Drec : ℝ) (Derr : ℝ))))))
  have hDcut : 0 < Dcut := (by norm_num : (0 : ℝ) < 4).trans_le (le_max_left _ _)
  obtain ⟨C1cut, hC1cut, hcut⟩ :=
    exists_sourceLargeLog_fixedThreshold_of_source hsrc Dcut hDcut
  let C1min : ℝ := max 1 (max C1coef (max C1scalar (max C1B C1cut)))
  have hC1min : 1 ≤ C1min := le_max_left _ _
  refine ⟨C1min, CB, hC1min, hCB, ?_⟩
  intro S C1 C K M D hC1 hCcommon hK hlocal hM hM2 hlarge hglobal
  have hCBC : CB ≤ C := (le_max_right 3 CB).trans hCcommon
  have hC3 : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
  have hCpos : 0 < C := by linarith
  have hcoefC1 : C1coef ≤ C1 :=
    (le_max_left C1coef (max C1scalar (max C1B C1cut))).trans
      ((le_max_right 1 _).trans hC1)
  have hscalarC1 : C1scalar ≤ C1 :=
    (le_max_left C1scalar (max C1B C1cut)).trans
      ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1))
  have hcaseBC1 : C1B ≤ C1 :=
    (le_max_left C1B C1cut).trans
      ((le_max_right C1scalar _).trans
        ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1)))
  have hcutC1 : C1cut ≤ C1 :=
    (le_max_right C1B C1cut).trans
      ((le_max_right C1scalar _).trans
        ((le_max_right C1coef _).trans ((le_max_right 1 _).trans hC1)))
  have hDpos : 0 < (D : ℝ) := by
    exact_mod_cast (show 0 < D by
      by_contra hn
      have hD0 : D = 0 := by omega
      subst D
      norm_num at hlarge
      have hC10 : 0 ≤ C1 :=
        (show (0 : ℝ) ≤ 1 by norm_num).trans (hC1min.trans hC1)
      have hKpow : 0 ≤ K ^ Θ := Real.rpow_nonneg (by linarith) _
      nlinarith [mul_nonneg hC10 hKpow])
  have hDcutD : Dcut < (D : ℝ) := hcut C1 K (D : ℝ) hcutC1 hK hDpos hlarge
  have hD4 : 4 ≤ D := by
    exact_mod_cast ((le_max_left 4 _).trans hDcutD.le)
  have hD3 : 3 ≤ D := by omega
  have hD2 : 2 ≤ D := by omega
  have hD12 : D12 ≤ (D : ℝ) :=
    (le_max_left D12 _).trans ((le_max_right 4 _).trans hDcutD.le)
  have hD146 : D146 ≤ (D : ℝ) :=
    (le_max_left D146 _).trans
      ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))
  have hDg : Dg ≤ (D : ℝ) :=
    (le_max_left Dg _).trans
      ((le_max_right D146 _).trans
        ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le)))
  have hDσ : Dσ ≤ (D : ℝ) :=
    (le_max_left Dσ _).trans
      ((le_max_right Dg _).trans
        ((le_max_right D146 _).trans
          ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))))
  have hDrec : Drec ≤ D := by
    exact_mod_cast ((le_max_left (Drec : ℝ) (Derr : ℝ)).trans
      ((le_max_right Dσ _).trans
        ((le_max_right Dg _).trans
          ((le_max_right D146 _).trans
            ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))))))
  have hDerr : Derr ≤ D := by
    exact_mod_cast ((le_max_right (Drec : ℝ) (Derr : ℝ)).trans
      ((le_max_right Dσ _).trans
        ((le_max_right Dg _).trans
          ((le_max_right D146 _).trans
            ((le_max_right D12 _).trans ((le_max_right 4 _).trans hDcutD.le))))))
  have hσ3 : (3 : ℝ) ≤ sourceSigma (D : ℝ) d := hσlarge _ hDσ
  have h2σ : (2 : ℝ) ≤ sourceSigma (D : ℝ) d := by linarith
  have g := hg D M hDg 2 (by norm_num) h2σ
  let σ : ℝ := sourceSigma (D : ℝ) d
  let z : ℕ := ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊
  have hz : z = ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ := rfl
  have hDreal : 1 < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hprime : ∀ p ∈ suzukiSupportedBelow S z, p.Prime := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
  have toFull : ∀ p, p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2 →
      p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
    intro p hp
    simpa only [sigmaOneCarrier, suzukiSupportedBelow, Finset.mem_filter] using
      ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).1,
        (Finset.mem_filter.mp hp).2⟩
  have hscale : CarrierQuotientThresholdGeometry
      (suzukiSupportedBelow S z) D 2 σ 2 := by
    intro p hp
    exact evenEndpoint_carrier_scale S (by norm_num) (by norm_num [show 4 ≤ D from hD4])
      p (toFull p hp)
  have hrecursiveD := hrec D hDrec S
  have hrecursiveSigma : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      recursiveCoordinate D p ≤ sourceSigma ((D ⌈/⌉ p : ℕ) : ℝ) d := by
    intro p hp
    exact hrecursiveD 2 (by norm_num) p (toFull p hp)
  have hinheritedFull : ∀ p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2,
      inheritedCoordinate D p ∈ KappaOneModel.parityDomain 2 (M - 1) := by
    intro p hp
    apply lemma144_caseI_even_endpoint_inherited_domain S hM hM2 hD4 hz p
    apply Finset.mem_filter.mpr
    exact ⟨(Finset.mem_filter.mp hp).1,
      (nat_lt_natCeil_iff_lt_real (natCast_rpow_one_div_pos (by omega) (2 : ℝ)) hz).2
        (Finset.mem_filter.mp hp).2.2⟩
  have herrorD := herr D hDerr S
  have herror : ∀ p ∈ sigmaOneCarrier (suzukiSupportedBelow S z) D σ 2,
      errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (recursiveCoordinate D p) ≤
        errorEnvelope H (M - 1) (D ⌈/⌉ p : ℕ) d (inheritedCoordinate D p) := by
    intro p hp
    exact herrorD M 2 (by norm_num) hinheritedFull
      (hrecursiveD 2 (by norm_num)) p (toFull p hp)
  have hpoint := evenEndpoint_pointwiseContract_of_movingIH_sourceLargeConsumer
    S H C K d Δ M D 2 (by norm_num) hM hM2 hD4 hscale hrecursiveSigma herror
      (by
        have hC3' : (3 : ℝ) ≤ C := (le_max_left 3 CB).trans hCcommon
        linarith) hglobal
  have h10 := equation14_10_finset_assembly
    (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
    (suzukiActualT S) (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
    (suzukiVProduct S z) 2 C K Δ M D σ 2
    (ne_of_gt (suzukiVProduct_pos S z))
    (by intro p hp; have hpS := (Finset.mem_filter.mp hp).1
        exact (S.nu_pos_of_prime p (hprime p hpS)
          ((Nat.mem_primeFactors.mp (Finset.mem_filter.mp hpS).1).2.1)).le) hpoint
  have h149 : suzukiActualT S M D z =
      suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ)) ((D : ℝ) ^ (1 / (2 : ℝ))) +
          suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) := by
    simpa [σ] using suzuki_equation14_9_strict (D := D) (z := z) S hM2
      (fun hOdd => (Nat.not_even_iff_odd.mpr hOdd hM).elim) g.hpowerOrder
  have h11 := caseI_evenEndpointSigma11Edge S hM hM2 h2σ hDreal
    g.hpowerS g.hpowerSigma g.hpowerOrder hK hlocal
  have hceil : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) → 2 ≤ p ∧ 2 * p ≤ D := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    exact ⟨(Nat.prime_of_mem_primeFactors hp).two_le,
      evenEndpoint_carrier_scale S (by norm_num)
        (by norm_num [show 4 ≤ D from hD4]) p hpc⟩
  have hT : ∀ p ∈ S.prodPrimes.primeFactors,
      (D : ℝ) ^ (1 / σ) ≤ (p : ℝ) →
      (p : ℝ) < (D : ℝ) ^ (1 / (2 : ℝ)) →
      0 ≤ H.T (ErrorSign.ofDepth (M - 1)) (inheritedCoordinate D p) := by
    intro p hp hpw hpv
    have hpc : p ∈ sigmaOneCarrier S.prodPrimes.primeFactors D σ 2 := by
      simp only [sigmaOneCarrier, Finset.mem_filter]
      exact ⟨hp, hpw, hpv⟩
    have hcoord := hinheritedFull p hpc
    have hpred : (M - 1) % 2 = 1 := by
      have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
      omega
    have hcoord0 : 0 < inheritedCoordinate D p := by
      simp only [KappaOneModel.parityDomain, hpred, if_pos, Set.mem_Ioi] at hcoord
      norm_num at hcoord
      linarith
    exact (hH.positive _ _ hcoord0).le
  have hEvenLower : 2 + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    have hnotOdd : ¬ Odd M := fun ho => (Nat.not_even_iff_odd.mpr ho) hM
    simp [ErrorSign.ofDepth, hnotOdd, ErrorSign.epsilon]
  have hthreshold : H.betaHat + (ErrorSign.ofDepth M).epsilon ≤ (2 : ℝ) := by
    rw [hH.betaHat_eq]
    exact hEvenLower
  obtain ⟨q12, hq12, _h12raw, h12q⟩ :=
    h12 S C K hK hlocal (by linarith [hCcommon]) D M 2 z hD12
      (by norm_num) hEvenLower (by linarith [hσ3]) h2σ hDreal
      g.hpowerS g.hpowerSigma g.hpowerOrder hz hthreshold hceil hT
      (by
        intro p hp hpw hpv
        have hcp := hceil p hp hpw hpv
        exact claim14_13_pointwise_carrier H (by omega) hcp.1 hcp.2 hd1
          hsrc.hDelta_pos (hT p hp hpw hpv))
  have h12qSupported :
      sigmaTwelve (suzukiSupportedBelow S z) S.nu
          (fun p => suzukiVProduct S (p : ℝ))
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S (z : ℝ)) C K Δ M D σ 2 ≤
        q12.ρ * sigma12InheritedBudget S H M D z C K d Δ 2 +
          caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ := by
    rw [show suzukiSupportedBelow S z =
      S.prodPrimes.primeFactors.filter (fun p => p < z) from rfl]
    rw [sigmaTwelve_supportedBelow_eq_full S
      (fun p => suzukiVProduct S (p : ℝ))
      (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
      (suzukiVProduct S (z : ℝ)) C K Δ M D z σ 2
      (by dsimp [z]; exact Nat.le_ceil _)]
    simpa [sigma12EndpointRemainder, caseI1423Sigma12Endpoint] using h12q
  have hscalarD := hscalar C1 K (D : ℝ) hscalarC1 hK
    (by exact_mod_cast hD2) hlarge
  have hend := caseI1423EndpointSourceBounds_evenEndpoint_explicit
    S H C K d Δ L R hH hCpos hsrc.hDelta_pos
      hsrc.hDelta_lt hsrc.h14_1 hL hfinite hR _hratio
      D M hD3 hscalarD hM hM2 h2σ
  have hzσ : (D : ℝ) ^ (1 / sourceSigma (D : ℝ) d) ≤ (z : ℝ) := by
    simpa [z, σ] using g.hpowerOrder.trans (Nat.le_ceil _)
  have hzeroRaw := hcaseB S C1 C K M D z hcaseBC1 hCBC hK hlocal hD2
    hlarge hM hM2 hzσ
  have hi := (h146 (D : ℝ) hD146).1
  have hEtransport : errorEnvelope H M (D : ℝ) d σ ≤
      errorEnvelope H M (D : ℝ) d 2 := by
    apply errorEnvelope_endpoint_le_of_claim14_6 hH.toSection13HatContract hDreal hi
    rw [hH.betaHat_eq]
    exact ⟨hEvenLower, by simpa [σ] using h2σ⟩
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hDreal
  have hll : 0 < Real.log (Real.log (D : ℝ)) := by
    apply Real.log_pos
    have he : Real.exp 1 < (D : ℝ) := by
      calc Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
           _ ≤ (D : ℝ) := by exact_mod_cast hD3
    exact (Real.lt_log_iff_exp_lt hDpos).2 he
  have hlllog : Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos hlog]
  have hzD : (z : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast (Nat.ceil_le.mpr (by
      calc
        (D : ℝ) ^ (1 / (2 : ℝ)) ≤ (D : ℝ) ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hDreal.le
          norm_num
        _ = (D : ℝ) := by norm_num))
  have hEσ0 : 0 ≤ errorEnvelope H M (D : ℝ) d σ :=
    errorEnvelope_nonneg H M hDreal (by dsimp [σ]; linarith [h2σ])
      (hH.positive _ _ (by dsimp [σ]; linarith [h2σ])).le
  have hzeroDirect : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      caseISigmaZeroDirectRemainder S H M D CB K d Δ := by
    have hCpos : 0 < C := by linarith [hC3]
    have hzraw := hzeroRaw
    have heq : (CB / C) * (C * claim14_5Scale S H M (D : ℝ) d Δ
        (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)) =
        caseISigmaZeroDirectRemainder S H M D CB K d Δ := by
      unfold caseISigmaZeroDirectRemainder
      field_simp [ne_of_gt hCpos]
    rw [heq] at hzraw
    simpa [σ] using hzraw
  have hzeroSource := caseISigmaZeroDirectRemainder_le_sourceOrder
    (S := S) (H := H) (N := M) (D := D) (z := z)
    (C := C) (C145 := CB) (K := K) (d := d) (Δ := Δ)
    hDreal hll hlllog hzD (by simpa [σ] using (show (0 : ℝ) <
      sourceSigma (D : ℝ) d by linarith [h2σ]))
    hCpos hCB.le (by simpa [σ] using hEσ0)
  have hbudgetTransport : sigma12InheritedBudget S H M D z C K d Δ σ ≤
      sigma12InheritedBudget S H M D z C K d Δ 2 := by
    unfold sigma12InheritedBudget
    apply mul_le_mul_of_nonneg_left hEtransport
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg hCpos.le (Real.exp_pos _).le)
        (suzukiVProduct_pos S (z : ℝ)).le)
      (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _)
  have hzeroUnit : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) ≤
      (CB / C) * caseI1423RemainderUnit
        (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
    apply hzeroDirect.trans
    calc
      caseISigmaZeroDirectRemainder S H M D CB K d Δ ≤
          caseISourceOrderCoefficient (CB / C) (D : ℝ) d *
            sigma12InheritedBudget S H M D z C K d Δ σ := hzeroSource
      _ ≤ caseISourceOrderCoefficient (CB / C) (D : ℝ) d *
            sigma12InheritedBudget S H M D z C K d Δ 2 := by
        apply mul_le_mul_of_nonneg_left hbudgetTransport
        unfold caseISourceOrderCoefficient
        exact div_nonneg (div_nonneg hCB.le hCpos.le) (by positivity)
      _ = (CB / C) * caseI1423RemainderUnit
          (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
        simp [caseISourceOrderCoefficient, caseI1423RemainderUnit, σ]
        ring
  have hAactual : 0 ≤ CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R := by
    positivity
  have hAupper : CB / C + 6 * L * R /
      (C * Real.exp (Real.sqrt K)) + 12 * R ≤ Amax := by
    have hb := caseI_endpointCoefficient_le_commonScale
      (A := (1 : ℝ)) (C := C) (C145 := CB) (K := K) (L := L) (R := R)
      (by norm_num) hC3 (by simpa using hCBC) (by linarith [hL]) (by linarith [hR])
    norm_num at hb
    simpa [Amax] using hb
  obtain ⟨qgap, hqgap, hcoefGap⟩ := hcoef C1 K (D : ℝ)
    (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
    hcoefC1 hK (by exact_mod_cast hD2) hAactual hAupper hlarge
  have hqrho : q12.ρ = qgap.ρ := by rw [hq12, hqgap]
  have hbudget : 0 ≤ sigma12InheritedBudget S H M D z C K d Δ 2 := by
    unfold sigma12InheritedBudget
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg hCpos.le (Real.exp_pos _).le)
          (suzukiVProduct_pos S (z : ℝ)).le)
        (Real.rpow_nonneg (Real.log_nonneg hDreal.le) _))
      (errorEnvelope_nonneg H M hDreal (by norm_num)
        (hH.positive _ _ (by norm_num)).le)
  have hunit : (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R) *
        caseI1423RemainderUnit
          (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ =
      caseISourceOrderCoefficient
          (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R)
          (D : ℝ) d * sigma12InheritedBudget S H M D z C K d Δ 2 := by
    simp [caseI1423RemainderUnit, caseISourceOrderCoefficient, σ]
    ring
  have hside : suzukiSigmaZero S M D z ((D : ℝ) ^ (1 / σ)) +
        suzukiVProduct S z * (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log ((D : ℝ) ^ (1 / σ))) +
        caseI1423Sigma12Endpoint S H M D z C K d Δ 2 σ ≤
      (1 - q12.ρ) * sigma12InheritedBudget S H M D z C K d Δ 2 := by
    have hsrcBound := add_le_add (add_le_add hzeroUnit hend.1) hend.2
    calc
      _ ≤ (CB / C + 6 * L * R / (C * Real.exp (Real.sqrt K)) + 12 * R) *
          caseI1423RemainderUnit
            (sigma12InheritedBudget S H M D z C K d Δ 2) (D : ℝ) σ := by
        linarith
      _ = _ := hunit
      _ ≤ (1 - qgap.ρ) * sigma12InheritedBudget S H M D z C K d Δ 2 :=
        mul_le_mul_of_nonneg_right hcoefGap hbudget
      _ = _ := by rw [hqrho]
  have h2raw := lemma144_sigmaTwo_eq_zero_of_kappaOne_caseI
    (N := M) S hD4 (by norm_num : (2 : ℝ) ≤ 2) hz
  have h2 : suzukiSigmaTwo S M D z ((D : ℝ) ^ (1 / (2 : ℝ))) = 0 := by
    simpa [lemma144_realTau_eq_s_of_caseI hD4 (by norm_num : (2 : ℝ) ≤ 2)] using h2raw
  have hmiddle : suzukiSigmaOne S M D z ((D : ℝ) ^ (1 / σ))
      ((D : ℝ) ^ (1 / (2 : ℝ))) ≤
      sigmaEleven (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (suzukiVProduct S z) 2 M D σ 2 +
        sigmaTwelve (suzukiSupportedBelow S z) S.nu (fun p => suzukiVProduct S p)
          (fun n D' x => errorEnvelope H n (D' : ℝ) d x)
          (suzukiVProduct S z) C K Δ M D σ 2 := by
    change sigmaOne (suzukiSupportedBelow S z) S.nu (suzukiActualT S) M D σ 2 ≤ _
    exact h10
  dsimp [CaseIEvenEndpointSigma11Edge] at h11
  rw [h149, h2]
  linarith [hmiddle, h11, h12qSupported, hside]

/-- Compatibility specialization of the producer uniform in the bounding sieve. -/
theorem exists_lemma14_4_caseI_evenEndpoint_sourceLargeLog_pointwise
    (S : BoundingSieve) (H : Section13HatLayers) {d Δ Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hsrc : SuzukiClaim145SourceParameters d Δ Θ) :
    ∃ C1min CB : ℝ, 1 ≤ C1min ∧ 0 < CB ∧
      ∀ (C1 C K : ℝ) (M D : ℕ),
        C1min ≤ C1 → max 3 CB ≤ C → 2 ≤ K →
        HasDimensionOneLocalProductBound S K →
        Even M → 2 ≤ M →
        C1 * K ^ Θ < Real.log (D : ℝ) →
        Lemma144MovingDomainGlobalDepthAt S H C K d Δ (M - 1) 2 →
        suzukiActualT S M D ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ ≤
          suzukiVProduct S ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ *
            finiteSourceLayer 1 2 M 2 +
          sigma12InheritedBudget S H M D
            ⌈(D : ℝ) ^ (1 / (2 : ℝ))⌉₊ C K d Δ 2 := by
  obtain ⟨C1min, CB, hC1min, hCB, hall⟩ :=
    exists_lemma14_4_caseI_evenEndpoint_sourceLargeLog_pointwise_uniform_in_S
      H hH hsrc
  exact ⟨C1min, CB, hC1min, hCB, hall S⟩


end MathlibNt.SieveTheory
