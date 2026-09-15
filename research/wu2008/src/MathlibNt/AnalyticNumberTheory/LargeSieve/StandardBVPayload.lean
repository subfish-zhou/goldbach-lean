

import MathlibNt.AnalyticNumberTheory.LargeSieve.StandardBVElementaryPayments
import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIActualDyadicClosure

/-!
 # Closed elementary payload for Standard Bombieri--Vinogradov

This module packages the elementary lanes left by the low/high conductor split.
The asymptotic payment is proved from Mathlib's `Real.isLittleO_pow_log_id_atTop`;
no scalar asymptotic inequality is retained as a premise.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset Filter
open scoped BigOperators ArithmeticFunction Topology

noncomputable section

private lemma card_primitiveCharacter_le_totient_payload (q : ℕ) (hq : 0 < q) :
    Fintype.card (PrimitiveCharacter q) ≤ q.totient :=
  card_primitiveCharacter_le_totient q hq

/-- The small Vaughan lane in AP normalization costs only the number of
conductors, rather than a large-sieve square mean. -/
theorem apNormalizedPrimitiveMeanOn_vaughanSmall_le_explicit
    (N v : ℕ) (S : Finset ℕ) (hS : ∀ q ∈ S, 0 < q) :
    apNormalizedPrimitiveMeanOn
        (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N S ≤
      (S.card : ℝ) * ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)) := by
  unfold apNormalizedPrimitiveMeanOn
  calc
    (∑ q ∈ S, ((q.totient : ℝ)⁻¹) *
        ∑ ψ : PrimitiveCharacter q,
          primitivePrefixAmplitude
            (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q ψ) ≤
      ∑ _q ∈ S, ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hφ0 : (0 : ℝ) < q.totient := by
        exact_mod_cast Nat.totient_pos.mpr (hS q hq)
      have hcard : ((Fintype.card (PrimitiveCharacter q) : ℕ) : ℝ) ≤ q.totient := by
        exact_mod_cast card_primitiveCharacter_le_totient_payload q (hS q hq)
      have hV : 0 ≤ (v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ) := by positivity
      calc
        ((q.totient : ℝ)⁻¹) *
            (∑ ψ : PrimitiveCharacter q,
              primitivePrefixAmplitude
                (vaughanSmallCoeff vaughanUnitIntegerCoeff v) N q ψ) ≤
          ((q.totient : ℝ)⁻¹) *
            (∑ _ψ : PrimitiveCharacter q,
              ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ))) := by
                gcongr with ψ
                exact vaughanSmall_primitivePrefixAmplitude_le N q v ψ
        _ = ((q.totient : ℝ)⁻¹) *
            ((Fintype.card (PrimitiveCharacter q) : ℝ) *
              ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ))) := by simp
        _ ≤ 1 * ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)) := by
          have hratio : ((q.totient : ℝ)⁻¹) *
              (Fintype.card (PrimitiveCharacter q) : ℝ) ≤ 1 := by
            rw [inv_mul_le_one₀ hφ0]
            exact hcard
          nlinarith
        _ = _ := by ring
    _ = (S.card : ℝ) * ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)) := by simp

/-- In particular a conductor interval contained in `[1,Q]` costs at most
`Q v log(v+1)`. -/
theorem highConductorVaughanSmallMean_le_explicit (N Q C v : ℕ) :
    highConductorVaughanSmallMean N Q C v ≤
      (Q : ℝ) * ((v : ℝ) * Real.log ((v + 1 : ℕ) : ℝ)) := by
  unfold highConductorVaughanSmallMean
  refine (apNormalizedPrimitiveMeanOn_vaughanSmall_le_explicit N v
    (highConductorSet N Q C) (fun q hq => by
      have hqI : q ∈ Finset.Icc 2 Q := (Finset.mem_filter.mp hq).1
      have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hqI).1
      omega)).trans ?_
  apply mul_le_mul_of_nonneg_right
  · norm_cast
    exact (Finset.card_le_card (by
      intro d hd
      exact (Finset.mem_filter.mp hd).1 :
        highConductorSet N Q C ⊆ Finset.Icc 2 Q)).trans (by simp)
  · positivity

/-- A convenient closed packet for exactly the elementary Standard-BV lanes. -/
def StandardBVPayload (N Q : ℕ) : ℝ :=
  discreteAbelAmplifierPrefixMax N *
    (principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q)

lemma natLog2_cast_le_two_log {n : ℕ} (hn : 2 ≤ n) :
    (Nat.log2 n : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have hp : 2 ^ Nat.log2 n ≤ n := Nat.log2_self_le (by omega)
  have hpR : (0 : ℝ) < (2 : ℝ) ^ Nat.log2 n := by positivity
  have hnR : (0 : ℝ) < n := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hpR hnR (by exact_mod_cast hp)
  rw [Real.log_pow] at hlog
  have htwo : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  nlinarith

lemma natSqrt_cast_le_realSqrt (n : ℕ) :
    (n.sqrt : ℝ) ≤ Real.sqrt n := by
  have hsq : ((n.sqrt : ℝ) : ℝ) ^ 2 ≤ (n : ℝ) := by
    exact_mod_cast (show n.sqrt ^ 2 ≤ n by simpa [pow_two] using Nat.sqrt_le n)
  have hrsq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  nlinarith [Real.sqrt_nonneg (n : ℝ), (show (0 : ℝ) ≤ n.sqrt by positivity)]

/-- Mathlib's polynomial-versus-log little-o theorem, specialized to the
square-root scale needed in BV scalar payments. -/
theorem log_pow_le_sqrt_eventually (k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop,
      Real.log (N : ℝ) ^ k ≤ Real.sqrt N := by
  have hR := (Real.isLittleO_pow_log_id_atTop (n := 2 * k)).eventuallyLE
  have hN := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hR
  filter_upwards [hN, eventually_ge_atTop (2 : ℕ)] with N hlog hN2
  have hlog0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hs : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  simp only [id, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hlog0 _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ N)] at hlog
  rw [mul_comm, pow_mul] at hlog
  nlinarith [Real.sqrt_nonneg (N : ℝ), pow_nonneg hlog0 k]

/-- The exact `Q ≤ sqrt N / log^(A+k) N` calculation.  This is the reusable
polynomial-versus-log payment lemma for every elementary lane below. -/
theorem Q_sqrt_log_payable (A k : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + k) →
      (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ k ≤
        2 * (N : ℝ) / Real.log N ^ A := by
  filter_upwards [log_pow_le_sqrt_eventually k,
    eventually_ge_atTop (3 : ℕ)] with N hk hN Q hQ
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by
    exact_mod_cast (show 1 < N by omega))
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := Real.one_le_sqrt.mpr (by
    exact_mod_cast (show 1 ≤ N by omega))
  have hs2 : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hden : 0 < Real.log (N : ℝ) ^ (A + k) := pow_pos hlog _
  have hQ' : (Q : ℝ) * Real.log (N : ℝ) ^ (A + k) ≤ Real.sqrt N :=
    (le_div_iff₀ hden).mp hQ
  have hmain : (Q : ℝ) * Real.sqrt N * Real.log N ^ k ≤
      (N : ℝ) / Real.log N ^ A := by
    apply (le_div_iff₀ (pow_pos hlog A)).2
    calc
      (Q : ℝ) * Real.sqrt N * Real.log N ^ k * Real.log N ^ A =
          Real.sqrt N * ((Q : ℝ) * Real.log N ^ (A + k)) := by
            rw [pow_add]
            ring
      _ ≤ Real.sqrt N * Real.sqrt N := by gcongr
      _ = (N : ℝ) := by rw [← sq, hs2]
  have hsmall : (Q : ℝ) * 1 * Real.log N ^ k ≤
      (Q : ℝ) * Real.sqrt N * Real.log N ^ k := by gcongr
  calc
    (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ k =
        (Q : ℝ) * Real.sqrt N * Real.log N ^ k +
          (Q : ℝ) * 1 * Real.log N ^ k := by ring
    _ ≤ (N : ℝ) / Real.log N ^ A + (N : ℝ) / Real.log N ^ A :=
      add_le_add hmain (hsmall.trans hmain)
    _ = 2 * (N : ℝ) / Real.log N ^ A := by ring

/-- Abel, bad-principal, higher-prime-power, and conductor-change terms have a
single explicit `Q (sqrt N+1) log^3 N` envelope throughout the BV-relevant
range `Q ≤ N`. -/
theorem StandardBVPayload_le_explicit :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ, Q ≤ N →
      StandardBVPayload N Q ≤
        90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 := by
  filter_upwards [eventually_ge_atTop (3 : ℕ)] with N hN Q hQN
  by_cases hQzero : Q = 0
  · subst Q
    simp [StandardBVPayload, principalBadPhysical, primePowerPhysical,
      directConductorCorrectionMean]
  have hQpos : 0 < Q := Nat.pos_of_ne_zero hQzero
  have hQone : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
  have hNR : (0 : ℝ) < N := by positivity
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hexp : Real.exp 1 < (N : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    exact ((Real.lt_log_iff_exp_lt hNR).2 hexp).le
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlog2N := natLog2_cast_le_two_log (show 2 ≤ N by omega)
  have hpp := primePowerPhysical_le_explicit N Q
  have hbad := principalBadPhysical_le_explicit N Q
  have hcond := directConductorCorrectionMean_vonMangoldt_le N Q
  have hsqrt := natSqrt_cast_le_realSqrt N
  have habel := discreteAbelAmplifierPrefixMax_le_two_inv_log_two N
  have hab3 : discreteAbelAmplifierPrefixMax N ≤ 3 := by
    refine habel.trans ?_
    have htwo : (2 / 3 : ℝ) < Real.log 2 := by
      linarith [Real.log_two_gt_d9]
    rw [mul_inv_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))]
    linarith
  have hlogQ : (Nat.log2 Q : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    by_cases hQ2 : 2 ≤ Q
    · have hlogmono : Real.log (Q : ℝ) ≤ Real.log (N : ℝ) :=
        Real.strictMonoOn_log.monotoneOn
          (by change (0 : ℝ) < (Q : ℝ); exact_mod_cast hQpos)
          hNR (by exact_mod_cast hQN)
      linarith [natLog2_cast_le_two_log hQ2]
    · have hQle : Q ≤ 1 := by omega
      have hlog2Q : Nat.log2 Q = 0 := by interval_cases Q <;> rfl
      rw [hlog2Q]
      norm_num
      exact hlog0
  have hL : (Nat.log2 N + 1 : ℝ) ≤ 3 * Real.log N := by linarith
  let X : ℝ := (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hbad' : principalBadPhysical N Q ≤ 6 * X := by
    refine hbad.trans ?_
    dsimp [X]
    calc
      (Q : ℝ) * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N
          ≤ (Q : ℝ) * (2 * Real.log N) * (3 * Real.log N) * Real.log N := by
            gcongr
      _ ≤ 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
            have hs : 1 ≤ Real.sqrt (N : ℝ) + 1 := by
              linarith [Real.sqrt_nonneg (N : ℝ)]
            calc
              (Q : ℝ) * (2 * Real.log N) * (3 * Real.log N) * Real.log N =
                  (6 * (Q : ℝ) * Real.log N ^ 3) * 1 := by ring
              _ ≤ (6 * (Q : ℝ) * Real.log N ^ 3) *
                    (Real.sqrt N + 1) :=
                mul_le_mul_of_nonneg_left hs (by positivity)
              _ = 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by ring
  have hcond' : 2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤
      12 * X := by
    have hc := mul_le_mul_of_nonneg_left hcond (by norm_num : (0 : ℝ) ≤ 2)
    refine hc.trans ?_
    dsimp [X]
    calc
      2 * ((Q : ℝ) *
          (2 * (Nat.log2 Q : ℝ) * (Nat.log2 N + 1 : ℝ) * Real.log N))
          ≤ 2 * ((Q : ℝ) *
            (2 * (2 * Real.log N) * (3 * Real.log N) * Real.log N)) := by
              gcongr
      _ ≤ 12 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
              have hs : 2 ≤ Real.sqrt (N : ℝ) + 1 := by
                have hsN : 1 ≤ Real.sqrt (N : ℝ) :=
                  Real.one_le_sqrt.mpr (by exact_mod_cast (show 1 ≤ N by omega))
                linarith
              calc
                2 * ((Q : ℝ) *
                    (2 * (2 * Real.log N) * (3 * Real.log N) * Real.log N)) =
                    (12 * (Q : ℝ) * Real.log N ^ 3) * 2 := by ring
                _ ≤ (12 * (Q : ℝ) * Real.log N ^ 3) *
                      (Real.sqrt N + 1) :=
                  mul_le_mul_of_nonneg_left hs (by positivity)
                _ = 12 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by ring
  have hpp' : primePowerPhysical N Q ≤ 6 * X := by
    refine hpp.trans ?_
    unfold primePowerCorrectionExplicitBound
    change (Q : ℝ) * (((N.sqrt + 1 : ℕ) : ℝ) *
      (Nat.log2 N + 1 : ℝ) * Real.log N) ≤ 6 * X
    dsimp [X]
    have hsN : ((N.sqrt + 1 : ℕ) : ℝ) ≤ Real.sqrt N + 1 := by
      norm_num
      linarith
    calc
      (Q : ℝ) * (((N.sqrt + 1 : ℕ) : ℝ) *
          (Nat.log2 N + 1 : ℝ) * Real.log N)
          ≤ (Q : ℝ) * ((Real.sqrt N + 1) *
            (3 * Real.log N) * Real.log N) := by gcongr
      _ ≤ 6 * ((Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3) := by
            have := mul_nonneg (show (0 : ℝ) ≤ (Q : ℝ) * (Real.sqrt N + 1) by positivity)
              (sq_nonneg (Real.log N))
            nlinarith
  unfold StandardBVPayload
  have hins : principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q ≤ 30 * X := by
    calc
      _ ≤ 6 * X + 6 * X + 12 * X := add_le_add (add_le_add hbad' hpp') hcond'
      _ ≤ 30 * X := by nlinarith [hX0]
  have hins0 : 0 ≤ principalBadPhysical N Q + primePowerPhysical N Q +
      2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
    have hb0 : 0 ≤ principalBadPhysical N Q := by
      unfold principalBadPhysical
      positivity
    have hp0 : 0 ≤ primePowerPhysical N Q := by
      unfold primePowerPhysical
      apply Finset.sum_nonneg
      intro q hq
      unfold lambdaPrimePowerCorrectionPrefixMaxError
      exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
    have hc0 : 0 ≤ directConductorCorrectionMean vonMangoldtIntegerCoeff N Q := by
      unfold directConductorCorrectionMean
      apply Finset.sum_nonneg
      intro q hq
      exact mul_nonneg (by positivity)
        (Finset.sum_nonneg fun χ _ => conductorErrorAmplitude_nonneg χ _ _)
    positivity
  calc
    discreteAbelAmplifierPrefixMax N *
        (principalBadPhysical N Q + primePowerPhysical N Q +
          2 * directConductorCorrectionMean vonMangoldtIntegerCoeff N Q)
        ≤ 3 * (30 * X) := mul_le_mul hab3 hins hins0 (by norm_num)
    _ = 90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 := by
      dsimp [X]
      ring

/-- For every requested logarithmic saving, choosing the modulus exponent three
larger pays the entire closed elementary packet. -/
theorem StandardBVPayload_payable (A : ℕ) :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ Q : ℕ,
      (Q : ℝ) ≤ Real.sqrt N / Real.log N ^ (A + 3) →
      StandardBVPayload N Q ≤
        180 * (N : ℝ) / Real.log N ^ A := by
  filter_upwards [StandardBVPayload_le_explicit,
    Q_sqrt_log_payable A 3, eventually_ge_atTop (3 : ℕ)] with
      N hpayload hpay hN Q hQ
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hNR : (0 : ℝ) < N := by positivity
    have hexp : Real.exp 1 < (N : ℝ) := by
      calc
        Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
        _ ≤ (N : ℝ) := by exact_mod_cast hN
    exact ((Real.lt_log_iff_exp_lt hNR).2 hexp).le
  have hden : 1 ≤ Real.log N ^ (A + 3) := one_le_pow₀ hlog
  have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hcut : Real.sqrt N / Real.log N ^ (A + 3) ≤ Real.sqrt N :=
    div_le_self hsqrt0 hden
  have hsquare : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by positivity)
  have hsqrtN : Real.sqrt (N : ℝ) ≤ N := by
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    nlinarith
  have hQNreal : (Q : ℝ) ≤ N := hQ.trans (hcut.trans hsqrtN)
  have hQN : Q ≤ N := by exact_mod_cast hQNreal
  calc
    StandardBVPayload N Q ≤
        90 * (Q : ℝ) * (Real.sqrt N + 1) * Real.log N ^ 3 :=
      hpayload Q hQN
    _ ≤ 90 * (2 * (N : ℝ) / Real.log N ^ A) := by
      have hm := mul_le_mul_of_nonneg_left (hpay Q hQ) (by norm_num : (0 : ℝ) ≤ 90)
      simpa [mul_assoc] using hm
    _ = 180 * (N : ℝ) / Real.log N ^ A := by ring

end

end AnalyticNumberTheory.LargeSieve
