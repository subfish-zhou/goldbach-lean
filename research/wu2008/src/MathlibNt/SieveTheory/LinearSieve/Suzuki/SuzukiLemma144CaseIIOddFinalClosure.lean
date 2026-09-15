import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIEndpointGap
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIIBracketGapQuantitative
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim146FullInternal
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144ErrorEnvelopeTransportFull
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSourceRoundedGeometryPacket

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

private theorem suzukiVProduct_antitone_local
    (S : BoundingSieve) {x y : ℝ} (hxy : x ≤ y) :
    suzukiVProduct S y ≤ suzukiVProduct S x := by
  unfold suzukiVProduct
  apply Finset.prod_le_prod_of_subset_of_le_one
  · intro p hp
    simp only [Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.trans_le hxy⟩
  · intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
    have hdvd : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hprime hdvd).le
  · intro p hp _
    have hnu := S.nu_pos_of_prime p
      (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hp).1).2.1
    linarith

/-- The quantitative Case-II bracket gap, Claim 14.5 at the moving source
endpoint, full Claim 14.6(i), and Euler-product monotonicity give the exact
same-`C` odd endpoint scaling bridge.  The cutoff is chosen before `s`. -/
theorem lemma144_caseII_odd_claim145_scaling_bridge
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C K C145 : ℝ}
    (hH : Section13HatSourceContract H)
    (hd1 : 1 < d) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1)
    (hd : 7 / (1 - Δ) < d)
    (hC : 0 < C) (hK : 0 < K) (hC145 : 0 < C145) :
    Lemma144CaseIIOddClaim145ScalingBridge S H d Δ C K C145 := by
  obtain ⟨D146, hD146, h146⟩ :=
    eventually_claim14_6_full_internal_at_sourceSigma hH hd1 hΔ0 hΔ1
  obtain ⟨Dgeom, hDgeom, hgeom⟩ :=
    exists_sourceSigma_doubleRounded_geometry_threshold d hd1
  obtain ⟨Dconst, hDconst, hconst⟩ :=
    exists_claim145_gap_constant_threshold hC hΔ1
  let A : ℝ := (1 + 3 * d) * (4 : ℝ) ^ d
  let Dlarge : ℝ := Real.exp (max 1 (3 * A))
  have hDlarge : 1 < Dlarge := by
    apply Real.one_lt_exp_iff.mpr
    exact zero_lt_one.trans_le (le_max_left _ _)
  intro N hN hN3
  obtain ⟨Dgap, hDgap, hgap⟩ :=
    exists_caseIIConcreteRoundedRelativeBracket_gap_threshold
      N K C d Δ
      (caseII_finiteSourceLayer_three_nonneg hN)
      (by
        apply finiteSourceLayer_nonneg_on_parityDomain (by norm_num) (N - 1)
        have hm : (N - 1) % 2 = 0 := by
          have hnmod : N % 2 = 1 := Nat.odd_iff.mp hN
          omega
        simp [KappaOneModel.parityDomain, hm])
      hK.le hC.le hΔ0 hΔ1 hd
  let D0 : ℝ := max D146 (max Dgeom (max Dconst (max Dlarge Dgap)))
  refine ⟨D0, hD146.trans_le (le_max_left _ _), ?_⟩
  intro D hD s hs1 hs3
  have h146D : D146 ≤ (D : ℝ) := (le_max_left D146 _).trans hD
  have hgeomD : Dgeom ≤ (D : ℝ) :=
    (le_max_left Dgeom _).trans ((le_max_right D146 _).trans hD)
  have hconstD : Dconst ≤ (D : ℝ) :=
    (le_max_left Dconst _).trans
      ((le_max_right Dgeom _).trans ((le_max_right D146 _).trans hD))
  have hlargeD : Dlarge ≤ (D : ℝ) :=
    (le_max_left Dlarge Dgap).trans
      ((le_max_right Dconst _).trans
        ((le_max_right Dgeom _).trans ((le_max_right D146 _).trans hD)))
  have hgapD : Dgap ≤ (D : ℝ) :=
    (le_max_right Dlarge Dgap).trans
      ((le_max_right Dconst _).trans
        ((le_max_right Dgeom _).trans ((le_max_right D146 _).trans hD)))
  have hg := hgeom S D hgeomD s hs1 hs3
  obtain ⟨hi, _hii, _hiii⟩ := h146 (D : ℝ) h146D
  have hD1 : 1 < (D : ℝ) := hDlarge.trans_le hlargeD
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hlogLarge : 3 * A ≤ Real.log (D : ℝ) := by
    have hmax : max 1 (3 * A) ≤ Real.log (D : ℝ) := by
      apply (Real.le_log_iff_exp_le (show 0 < (D : ℝ) by positivity)).2
      exact hlargeD
    exact (le_max_right 1 (3 * A)).trans hmax
  have hlarge : A ≤ (1 / 3 : ℝ) * Real.log (D : ℝ) := by linarith
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  have hs0 : 0 < s := zero_lt_one.trans hs1
  have hrootD : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    have hbase : 1 ≤ (D : ℝ) := hD1.le
    have hexp : 1 / s ≤ (1 : ℝ) := by
      rw [div_le_one hs0]
      exact hs1.le
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hbase hexp
  have hzDnat : z ≤ D := by
    dsimp [z]
    exact Nat.ceil_le.mpr hrootD
  have hzD : (z : ℝ) ≤ (D : ℝ) := by exact_mod_cast hzDnat
  have hV := suzukiVProduct_antitone_local S hzD
  have hsdomain : s ∈ KappaOneModel.parityDomain 2 N := by
    simp only [KappaOneModel.parityDomain, Nat.odd_iff.mp hN]
    norm_num
    exact hs1
  have hE := errorEnvelope_coordinate_transport_full hH.toSection13HatContract
    (N := N) (D := (D : ℝ)) (d := d) (σ := sourceSigma (D : ℝ) d)
    (x := s) (y := sourceSigma (D : ℝ) d)
    (by linarith) hD1 (by simpa [A] using hlarge) hi hsdomain
    (hs3.trans hg.h3σ) le_rfl
  have hEσ0 : 0 ≤ errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) :=
    errorEnvelope_nonneg H N hD1 (show 0 ≤ sourceSigma (D : ℝ) d by linarith [hg.h3σ])
      (hH.positive (ErrorSign.ofDepth N) _ (by linarith [hg.h3σ])).le
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlog.le _
  unfold claim14_5Scale
  simpa [claim14_5VProduct, suzukiVProduct, z, mul_assoc] using
    (claim145_endpoint_absorbed_by_caseII_gap
      (suzukiVProduct_pos S (D : ℝ)).le hV
      (Real.exp_pos (Real.sqrt K)).le hEσ0 hE hL hlog
      (by linarith [hg.h3σ]) hΔ1.le hC145.le hC.le
      (hgap (D : ℝ) hgapD) (hconst (D : ℝ) hconstD))


end MathlibNt.SieveTheory
