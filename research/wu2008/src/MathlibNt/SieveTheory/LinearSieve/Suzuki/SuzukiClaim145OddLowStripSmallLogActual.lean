import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145OddLowStripSmallLogScalar
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseALowSFinal

open scoped Classical BigOperators
open Filter Finset Set Topology

namespace MathlibNt.SieveTheory

open SwitchingPrinciple
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-- In the odd strip `1 < s < 2`, Lemma 14.1 with lower tail index zero
bounds the actual parity sum by the full exponential series. -/
theorem suzukiActualT_odd_lowStrip_le_exp_sourceL
    (S : BoundingSieve) {N D z : ℕ} {K s : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hD : 1 < D) (hs : 1 < s)
    (hz : z = ⌈(D : ℝ) ^ (1 / s)⌉₊) :
    suzukiActualT S N D z ≤ Real.exp (suzukiSourceL (z : ℝ) K) := by
  let L := suzukiSourceL (z : ℝ) K
  have hs0 : 0 < s := by linarith
  have hDreal : (1 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hroot : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
    Real.one_lt_rpow hDreal (one_div_pos.mpr hs0)
  have hz2 : 2 ≤ z := by
    have hz1 : 1 < ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
      rw [Nat.lt_ceil]
      exact_mod_cast hroot
    rw [hz]
    omega
  have hL : 0 ≤ L := by
    let A : ℝ := ∑ p ∈ suzukiSupportedBelow S z, S.nu p
    have hA : 0 ≤ A := by
      apply Finset.sum_nonneg
      intro p hp
      have hpP := (Finset.mem_filter.mp hp).1
      exact (S.nu_pos_of_prime p (Nat.prime_of_mem_primeFactors hpP)
        (Nat.mem_primeFactors.mp hpP).2.1).le
    have hAL : A ≤ L := by
      dsimp only [A, L]
      rw [suzukiPrimeMassBelow_natCast S z]
      exact lemmaFourteenOne_localProduct_mass hlocal (by exact_mod_cast hz2)
    exact hA.trans hAL
  have htail : suzukiActualT S N D z ≤ suzukiExponentialTail L 0 := by
    apply suzukiActualT_le_exponentialTail_of_support S hL
    · intro n hn
      omega
    · intro n
      dsimp only [L]
      exact suzukiLemma14_1_pointwise_of_localProduct S n D z hlocal hz2
  have hexp := (suzuki_lemma14_2_infinite_tail L 0 hL).2
  simpa [suzukiExponentialTail] using htail.trans hexp

/-- The Section-13 initial profile gives a uniform positive odd error envelope
throughout the whole low strip. -/
theorem odd_lowStrip_half_le_errorEnvelope
    {H : Section13HatLayers} {N : ℕ} {D d s : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hD : 1 < D) (hs1 : 1 < s) (hs2 : s ≤ 2) :
    (1 / 2 : ℝ) ≤ errorEnvelope H N D d s := by
  have hs0 : 0 < s := by linarith
  have hlog : 0 < Real.log D := Real.log_pos hD
  have hbase : 1 ≤ 1 + s ^ d / Real.log D := by
    have : 0 ≤ s ^ d / Real.log D :=
      div_nonneg (Real.rpow_nonneg hs0.le _) hlog.le
    linarith
  have hpow : 1 ≤ (1 + s ^ d / Real.log D) ^ s :=
    Real.one_le_rpow hbase hs0.le
  have hinit : weightedHat H .plus s = 1 := by
    have hi := hH.initial_plus s hs0 (by linarith)
    norm_num at hi ⊢
    exact hi
  have hweighted : s * H.Tplus s = 1 / s := by
    have hh : s ^ 2 * H.Tplus s = 1 := by
      simpa [weightedHat, Section13HatLayers.T] using hinit
    field_simp [ne_of_gt hs0]
    nlinarith
  have hTs : 0 ≤ s * H.Tplus s :=
    mul_nonneg hs0.le (hH.positive .plus s hs0).le
  rw [errorEnvelope_odd hN]
  calc
    (1 / 2 : ℝ) ≤ 1 / s := by
      apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2) hs0).2
      linarith
    _ = s * H.Tplus s := hweighted.symm
    _ ≤ (1 + s ^ d / Real.log D) ^ s * s * H.Tplus s := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hpow hTs

/-- The local Euler-product contract at the fixed lower endpoint `2`. -/
theorem one_le_lowStrip_localFactor_mul_claimV
    (S : BoundingSieve) {D : ℕ} {K : ℝ}
    (hlocal : HasDimensionOneLocalProductBound S K) (hD : 2 ≤ D) :
    1 ≤ ((Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)) *
      claim14_5VProduct S (D : ℝ) := by
  exact MathlibNt.SieveTheory.one_le_claim145_local_factor_mul_vProduct S hlocal hD

/-- Pointwise Claim 14.5 on `1 < s ≤ 2`, reduced only to the
uniform scalar domination above.  In particular no finite scan, Claim 14.5
hypothesis, or desired pointwise conclusion is used. -/
theorem claim145_odd_lowStrip_pointwise_of_scalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D : ℕ} {d Δ K s A : ℝ}
    (hH : Section13HatContract H 2) (hN : Odd N)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hD : 2 ≤ D) (hs1 : 1 < s) (hs2 : s ≤ 2)
    (hscalar :
      let R := (Real.log (D : ℝ) / Real.log 2) * (1 + K / Real.log 2)
      2 * R ^ 2 * Real.log (D : ℝ) * sourceSigma (D : ℝ) d *
          (Real.log (D : ℝ)) ^ Δ ≤ A * Real.exp (Real.sqrt K)) :
    ActualClaim145BoundAt S H N D d Δ K s A := by
  let z : ℕ := ⌈(D : ℝ) ^ (1 / s)⌉₊
  let L := Real.log (D : ℝ)
  let R := (L / Real.log 2) * (1 + K / Real.log 2)
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hD1
  have hs0 : 0 < s := by linarith
  have hrootD : (D : ℝ) ^ (1 / s) ≤ (D : ℝ) := by
    exact Real.rpow_le_self_of_one_le hD1.le ((div_le_one hs0).2 hs1.le)
  have hzD : z ≤ D := by
    dsimp [z]
    exact Nat.ceil_le.mpr hrootD
  have hz2 : 2 ≤ z := by
    have hroot1 : (1 : ℝ) < (D : ℝ) ^ (1 / s) :=
      Real.one_lt_rpow hD1 (one_div_pos.mpr hs0)
    have hz1 : 1 < ⌈(D : ℝ) ^ (1 / s)⌉₊ := by
      rw [Nat.lt_ceil]
      exact_mod_cast hroot1
    dsimp [z]
    omega
  have hlogz : 0 < Real.log (z : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < z by omega))
  have hlogzD : Real.log (z : ℝ) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by exact_mod_cast (show 0 < z by omega))
      (by exact_mod_cast hzD)
  have hKfactor : 0 < 1 + K / Real.log 2 := by
    positivity
  have hexpL : Real.exp (suzukiSourceL (z : ℝ) K) ≤ R := by
    have hzratio : 0 < Real.log (z : ℝ) / Real.log 2 := by positivity
    have heq : Real.exp (suzukiSourceL (z : ℝ) K) =
        (Real.log (z : ℝ) / Real.log 2) * (1 + K / Real.log 2) := by
      unfold suzukiSourceL
      rw [Real.exp_add, Real.exp_log hzratio, Real.exp_log hKfactor]
    rw [heq]
    dsimp [R, L]
    exact mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right hlogzD (Real.log_pos (by norm_num)).le)
      hKfactor.le
  have hT := suzukiActualT_odd_lowStrip_le_exp_sourceL (N := N) S hlocal
    (show 1 < D by omega) hs1 rfl
  have hE := odd_lowStrip_half_le_errorEnvelope (d := d) hH hN hD1 hs1 hs2
  have hRV := one_le_lowStrip_localFactor_mul_claimV S hlocal hD
  have hV0 : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    unfold claim14_5VProduct
    apply Finset.prod_nonneg
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p
      (Nat.prime_of_mem_primeFactors hpS) (Nat.mem_primeFactors.mp hpS).2.1).le
  have hsigma : 0 < sourceSigma (D : ℝ) d := sourceSigma_pos_of_nat_two_le hD
  have hpow : 0 < L ^ Δ := Real.rpow_pos_of_pos hL _
  have hsc : 2 * R ^ 2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ ≤
      A * Real.exp (Real.sqrt K) := by simpa [R, L, mul_assoc] using hscalar
  have htarget : R ≤ A * claim14_5Scale S H N (D : ℝ) d Δ
      (sourceSigma (D : ℝ) d) K s := by
    unfold claim14_5Scale
    rw [Real.rpow_neg (by exact hL.le)]
    have hden : 0 < L * sourceSigma (D : ℝ) d := mul_pos hL hsigma
    have hR0 : 0 ≤ R := by dsimp [R]; positivity
    have hRsqV : R ≤ R ^ 2 * claim14_5VProduct S (D : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hRV hR0
      nlinarith
    have hcoef0 : 0 ≤ 2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ := by positivity
    have hleft := mul_le_mul_of_nonneg_right hRsqV hcoef0
    have hmul := mul_le_mul_of_nonneg_left hsc hV0
    have hcore :
        2 * R * (L * sourceSigma (D : ℝ) d) * L ^ Δ ≤
          claim14_5VProduct S (D : ℝ) * (A * Real.exp (Real.sqrt K)) := by
      calc
        2 * R * (L * sourceSigma (D : ℝ) d) * L ^ Δ =
            R * (2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ) := by ring
        _ ≤ (R ^ 2 * claim14_5VProduct S (D : ℝ)) *
            (2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ) := hleft
        _ = claim14_5VProduct S (D : ℝ) *
            (2 * R ^ 2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ) := by ring
        _ ≤ claim14_5VProduct S (D : ℝ) * (A * Real.exp (Real.sqrt K)) := hmul
    have hEscale := mul_le_mul_of_nonneg_left hE
      (show 0 ≤ 2 * A * claim14_5VProduct S (D : ℝ) * Real.exp (Real.sqrt K) by positivity)
    rw [show A * (claim14_5VProduct S (D : ℝ) *
        (Real.exp (Real.sqrt K) / (L * sourceSigma (D : ℝ) d)) *
        errorEnvelope H N (D : ℝ) d s * (L ^ Δ)⁻¹) =
      (2 * A * claim14_5VProduct S (D : ℝ) * Real.exp (Real.sqrt K) *
        errorEnvelope H N (D : ℝ) d s) /
          (2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ) by
            field_simp [hden.ne', hpow.ne']]
    apply (le_div_iff₀ (show 0 < 2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ by
      positivity)).2
    calc
      R * (2 * (L * sourceSigma (D : ℝ) d) * L ^ Δ) =
          2 * R * (L * sourceSigma (D : ℝ) d) * L ^ Δ := by ring
      _ ≤ claim14_5VProduct S (D : ℝ) * (A * Real.exp (Real.sqrt K)) := hcore
      _ ≤ 2 * A * claim14_5VProduct S (D : ℝ) * Real.exp (Real.sqrt K) *
          errorEnvelope H N (D : ℝ) d s := by nlinarith
  unfold ActualClaim145BoundAt
  exact hT.trans (hexpL.trans htarget)



/-- Production-facing completion of Suzuki's omitted source-small odd strip.
The chosen coefficient precedes `K,N,D,s` literally, and the conclusion now
covers every `K ≥ 2`. -/
theorem claim145_odd_lowStrip_smallLog_actual
    (S : BoundingSieve) (H : Section13HatLayers)
    {d Δ C1 Θ : ℝ}
    (hH : Section13HatSourceContract H)
    (hC1 : 0 ≤ C1) (hΘ : 0 < Θ) (hd : 0 < d)
    (hsource : 2 / d < 1 / Θ) (hΔ0 : 0 ≤ Δ) (hΔ1 : Δ ≤ 1) :
    ∃ C145 : ℝ, 0 ≤ C145 ∧
      ∀ (K : ℝ) (N D : ℕ) (s : ℝ),
        2 ≤ K → Odd N → HasDimensionOneLocalProductBound S K →
        2 ≤ D → 1 < s → s ≤ 2 →
        Real.log (D : ℝ) ≤ C1 * K ^ Θ →
        ActualClaim145BoundAt S H N D d Δ K s C145 := by
  rcases claim145_odd_lowStrip_smallLog_scalarUniform
      hC1 hΘ hd hsource hΔ0 hΔ1 with ⟨A, hA, hscalar⟩
  refine ⟨A, hA, ?_⟩
  intro K N D s hK hN hlocal hD hs1 hs2 hsmall
  exact claim145_odd_lowStrip_pointwise_of_scalar S H hH.toSection13HatContract
    hN hlocal (by linarith) hA hD hs1 hs2 (hscalar K D hK hD hsmall)


end MathlibNt.SieveTheory
