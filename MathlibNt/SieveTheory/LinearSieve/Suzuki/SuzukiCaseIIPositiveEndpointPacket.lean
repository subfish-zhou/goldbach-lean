import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIEndpointFiniteAbsorption
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIISharpRawEndpoint
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCaseIIPositiveDeltaDecay

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple
open SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The Claim-14.6(iii) integral contribution in the transported Case-II
endpoint.  It is kept separate from all finite endpoint corrections. -/
noncomputable def caseIIPositiveDeltaIntegralPart
    (H : Section13HatLayers) (N : ℕ)
    (D y d Δ σ C K s : ℝ) : ℝ :=
  (3 / s) * (1 + K / Real.log y) *
    (C * Real.exp (Real.sqrt K) * (Real.log D) ^ (-Δ) *
      ((1 / 3) * (∫ t in (3 : ℝ)..σ,
        qD H (ErrorSign.ofDepth N).opposite D d Δ t)))

/-- Exact expansion of `caseIIEndpointErr` used by the positive-`Δ` packet.
The algebraic and `q_D(3)` endpoint terms are not merged: their distinct
logarithmic scales remain visible. -/
theorem caseIIEndpointErr_eq_positiveDelta_packet_expansion
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {w d Δ σ C K B0 s : ℝ}
    (hw : w = (D : ℝ) ^ (1 / σ)) :
    caseIIEndpointErr S H N D y z d Δ σ C K B0 s =
      B0 + suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart
            H N (D : ℝ) (y : ℝ) d Δ σ C K s +
          caseIINonIntegralEndpointCorrections
            H N (D : ℝ) (y : ℝ) w d Δ σ C K s) := by
  unfold caseIIEndpointErr caseIIPositiveDeltaIntegralPart
    caseIINonIntegralEndpointCorrections caseIIEndpointSigma11 caseIIEndpointQD
  rw [hw]
  ring

/-- Source-positive-`Δ` relative Case-II endpoint packet.

For `0 < Δ < 1`, the two finite endpoint scales and the sharp source-base loss
are retained exactly as

* `A * (log D)^(Δ-1)` for the algebraic endpoint terms;
* `Aq / log D` for the cubic `q_D(3)` endpoint term;
* `27 K * (log D)^(Δ-1) * errorEnvelope` for the sharp raw base term.

Thus no coefficient is prematurely replaced by a constant.  In particular,
this statement uses neither an artificial `hScale : 1 ≤ (log D)^(-Δ)` nor a
nonpositive-`Δ` hypothesis. -/
theorem caseII_positiveDelta_relative_endpoint_packet
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D y z : ℕ} {w d Δ σ C K B0 s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : Real.exp 1 ≤ (D : ℝ))
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hy : (y : ℝ) = (D : ℝ) ^ (1 / (3 : ℝ)))
    (hw : w = (D : ℝ) ^ (1 / σ))
    (hσ : 0 < σ) (hs1 : 1 < s) (hs3 : s ≤ 3)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hsmall : (3 : ℝ) ^ d ≤ Real.log (D : ℝ)) :
    caseIIEndpointErr S H N D y z d Δ σ C K B0 s +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ))) ≤
      B0 + suzukiVProduct S (z : ℝ) *
        (caseIIPositiveDeltaIntegralPart
            H N (D : ℝ) (y : ℝ) d Δ σ C K s +
          (caseIIAlgebraicEndpointCoeff N σ K *
                (Real.log (D : ℝ)) ^ (Δ - 1) +
            caseIIQDEndpointCoeff d Δ σ C K / Real.log (D : ℝ) +
            27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
              errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
  have _hΔrange : Δ ∈ Set.Ioo (0 : ℝ) 1 := ⟨hΔ0, hΔ1⟩
  have hD1 : 1 < (D : ℝ) :=
    (Real.one_lt_exp_iff.mpr (by norm_num)).trans_le hD
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hs : 0 < s := zero_lt_one.trans hs1
  have hE : (1 / 3 : ℝ) ≤ errorEnvelope H N (D : ℝ) d s :=
    one_third_le_errorEnvelope_caseII (d := d) hH hN hD1 hs1 hs3
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) :=
    Real.rpow_nonneg hlog.le _
  have hAq : 0 ≤ caseIIQDEndpointCoeff d Δ σ C K := by
    unfold caseIIQDEndpointCoeff
    positivity
  have hA : 0 ≤ caseIIAlgebraicEndpointCoeff N σ K := by
    unfold caseIIAlgebraicEndpointCoeff
    have hFy := caseII_finiteSourceLayer_three_nonneg hN
    have hNm : (N - 1) % 2 = 0 := by
      have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
      omega
    have hFw : 0 ≤ finiteSourceLayer 1 2 (N - 1) 2 := by
      apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
      simp [KappaOneModel.parityDomain, hNm]
    positivity
  rcases caseII_nonIntegral_endpoint_corrections_separate (Δ := Δ)
    hH hN hD hy hw hσ hs1 hs3 hK hC hsmall with ⟨halg, hq⟩
  have hfactor (A : ℝ) :
      A / Real.log (D : ℝ) =
        (A * (Real.log (D : ℝ)) ^ (Δ - 1)) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
    rw [mul_assoc, ← Real.rpow_add hlog]
    have hexp : Δ - 1 + -Δ = -(1 : ℝ) := by ring
    rw [hexp, Real.rpow_neg hlog.le, Real.rpow_one]
    simp [div_eq_mul_inv]
  have hbase0 :
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
        9 * K / Real.log (D : ℝ) := by
    calc
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) =
          (9 * K / Real.log (D : ℝ)) / s := by ring
      _ ≤ 9 * K / Real.log (D : ℝ) :=
        div_le_self (div_nonneg (mul_nonneg (by norm_num) hK) hlog.le) hs1.le
  have hbase :
      K * 3 ^ 2 / (s * Real.log (D : ℝ)) ≤
        (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
          errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ) := by
    calc
      _ ≤ 9 * K / Real.log (D : ℝ) := hbase0
      _ = (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) * (1 / 3)) *
          (Real.log (D : ℝ)) ^ (-Δ) := by
            rw [hfactor (9 * K)]
            ring
      _ ≤ (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
          errorEnvelope H N (D : ℝ) d s) *
            (Real.log (D : ℝ)) ^ (-Δ) := by
        have hp : 0 ≤ 27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) := by positivity
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hE hp) hL
  rw [caseIIEndpointErr_eq_positiveDelta_packet_expansion S H hw]
  have hVz : 0 ≤ suzukiVProduct S (z : ℝ) :=
    (suzukiVProduct_pos S (z : ℝ)).le
  rw [add_assoc]
  apply add_le_add le_rfl
  calc
    suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart
              H N (D : ℝ) (y : ℝ) d Δ σ C K s +
            caseIINonIntegralEndpointCorrections
              H N (D : ℝ) (y : ℝ) w d Δ σ C K s) +
        suzukiVProduct S (z : ℝ) *
          (K * 3 ^ 2 / (s * Real.log (D : ℝ)))
      = suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart
              H N (D : ℝ) (y : ℝ) d Δ σ C K s +
            (caseIINonIntegralEndpointCorrections
              H N (D : ℝ) (y : ℝ) w d Δ σ C K s +
              K * 3 ^ 2 / (s * Real.log (D : ℝ)))) := by ring
    _ ≤ suzukiVProduct S (z : ℝ) *
          (caseIIPositiveDeltaIntegralPart
              H N (D : ℝ) (y : ℝ) d Δ σ C K s +
            ((caseIIAlgebraicEndpointCoeff N σ K *
                  (Real.log (D : ℝ)) ^ (Δ - 1) +
              caseIIQDEndpointCoeff d Δ σ C K / Real.log (D : ℝ) +
              27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
                errorEnvelope H N (D : ℝ) d s) *
              (Real.log (D : ℝ)) ^ (-Δ))) := by
      apply mul_le_mul_of_nonneg_left _ hVz
      apply add_le_add le_rfl
      calc
        caseIINonIntegralEndpointCorrections
              H N (D : ℝ) (y : ℝ) w d Δ σ C K s +
            K * 3 ^ 2 / (s * Real.log (D : ℝ))
          ≤ (caseIIAlgebraicEndpointCoeff N σ K / Real.log (D : ℝ) +
              caseIIQDEndpointCoeff d Δ σ C K / Real.log (D : ℝ) *
                (Real.log (D : ℝ)) ^ (-Δ)) +
              (27 * K * (Real.log (D : ℝ)) ^ (Δ - 1) *
                errorEnvelope H N (D : ℝ) d s) *
                (Real.log (D : ℝ)) ^ (-Δ) :=
            add_le_add (add_le_add halg hq) hbase
        _ = _ := by rw [hfactor (caseIIAlgebraicEndpointCoeff N σ K)]; ring


end MathlibNt.SieveTheory
