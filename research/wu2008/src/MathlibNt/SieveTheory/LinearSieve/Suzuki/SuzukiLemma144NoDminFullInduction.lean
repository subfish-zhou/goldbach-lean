import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144NoDminMovingBridge

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# Lemma 14.4: actual-type, all-depth, no-`Dmin` induction

This module contains only logical assembly over production objects.  Claim 14.5
is consumed as `ActualClaim145BoundAt`, its normalization is the concrete
`ActualClaim145BoundAt.to_lemma144_moving_of_scalar`, and the induction invariant
is `Lemma144MovingDomainNatCeilAt ... N 2`.  No abstract quantitative-complement
predicate is introduced.
-/

/-- On the production parity domain the natural power ceiling never exceeds
`D`.  This is the endpoint-order premise of the actual Claim-14.5 bridge. -/
theorem natCeil_rpow_le_self_on_parityDomain
    {N D : ℕ} {s : ℝ} (hD : 2 ≤ D)
    (hs : s ∈ KappaOneModel.parityDomain 2 N) :
    ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤ D := by
  have hs1 : 1 < s := by
    by_cases hodd : N % 2 = 1
    · simp [KappaOneModel.parityDomain, hodd] at hs
      norm_num at hs ⊢
      exact hs
    · have hs2 : 2 ≤ s := by
        simpa [KappaOneModel.parityDomain, hodd] using hs
      linarith
  have hs0 : 0 < s := zero_lt_one.trans hs1
  apply Nat.ceil_le.mpr
  calc
    (D : ℝ) ^ (1 / s) ≤ (D : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ D by omega))
        ((div_le_one hs0).2 hs1.le)
    _ = (D : ℝ) := Real.rpow_one _

/-- The actual Claim-14.5 regime gives the moving Lemma-14.4 target at any
positive common constant dominating the explicit normalization constant. -/
theorem actualClaim145_to_moving_at_common_constant
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ s : ℝ} {N D : ℕ}
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hCnorm : claim145UniformNormalizationConstant C145 d ≤ C)
    (hH : Section13HatSourceContract H)
    (hD : 2 ≤ D) (hs : s ∈ KappaOneModel.parityDomain 2 N)
    (hclaim : ActualClaim145BoundAt S H N D d Δ K s C145) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s +
          C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
  apply ActualClaim145BoundAt.to_lemma144_moving_of_scalar S H hC145 hH hD hs
    (by exact_mod_cast natCeil_rpow_le_self_on_parityDomain hD hs)
  · exact (claim145_uniform_scalar_normalization C145 d hC145 hd).2 D hD |>.trans hCnorm
  · exact hclaim

/-- Base `N=1`: Claim 14.5 closes its literal source disjunction, while on the
complement its logarithmic inequality pays the one production base cutoff.
Thus the resulting invariant has cutoff exactly `2`, not an existential
`Dmin`. -/
theorem lemma14_4_noDmin_base_one_of_actualClaim145
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ C1 Θ : ℝ} {Dbase : ℕ}
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hCnorm : claim145UniformNormalizationConstant C145 d ≤ C)
    (hH : Section13HatSourceContract H)
    (_hK : 2 ≤ K) (_hlocal : HasDimensionOneLocalProductBound S K)
    (hDbase : 2 ≤ Dbase)
    (hbase : Lemma144MovingDomainNatCeilAt S H C K d Δ 1 Dbase)
    (hbudget : Real.log (Dbase : ℝ) ≤ C1 * K ^ Θ)
    (hclaim : ∀ (N D : ℕ) (s : ℝ),
      2 ≤ D → 2 ≤ s →
      (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ActualClaim145BoundAt S H N D d Δ K s C145)
    (hcaseIIBase : ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 1 →
      s ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ → ¬ 2 ≤ s →
      suzukiActualT S 1 D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 1 s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H 1 (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ))) :
    Lemma144MovingDomainNatCeilAt S H C K d Δ 1 2 := by
  intro D _hcut hD s hs hsSigma hz
  by_cases hs2 : 2 ≤ s
  · by_cases hregime :
        Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s
    · exact actualClaim145_to_moving_at_common_constant S H hC145 hd hCnorm hH hD hs
        (hclaim 1 D s hD hs2 hregime)
    · have hlarge : C1 * K ^ Θ < Real.log (D : ℝ) :=
        lt_of_not_ge (fun h => hregime (Or.inl h))
      have hDbaseD : Dbase ≤ D :=
        nat_cutoff_paid_by_source_log_large hD hDbase hbudget hlarge
      exact hbase D hDbaseD hD s hs hsSigma hz
  · exact hcaseIIBase D s hD hs hsSigma hz hs2

/-- Narrow successor bridge for the forthcoming `K`-uniform Case-I/II
producers.  Its assumptions are their literal production output types at the
single point `(N+1,D,s)`; the predecessor is the actual moving exact-power
contract at cutoff `2`. -/
theorem lemma14_4_noDmin_successor_of_actual_cases
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ C1 Θ : ℝ} (N : ℕ)
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hCnorm : claim145UniformNormalizationConstant C145 d ≤ C)
    (hH : Section13HatSourceContract H)
    (_hK : 2 ≤ K) (_hlocal : HasDimensionOneLocalProductBound S K)
    (hpred : Lemma144MovingDomainNatCeilAt S H C K d Δ N 2)
    (hclaim : ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → 2 ≤ s →
      (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ActualClaim145BoundAt S H (N + 1) D d Δ K s C145)
    (hcaseI : ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 (N + 1) →
      s ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      ¬ (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ¬ Lemma144CaseIIFinalSide (N + 1) s →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N 2 →
      suzukiActualT S (N + 1) D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 (N + 1) s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H (N + 1) (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)))
    (hcaseII : ∀ (D : ℕ) (s : ℝ),
      2 ≤ D → s ∈ KappaOneModel.parityDomain 2 (N + 1) →
      s ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      Lemma144CaseIIFinalSide (N + 1) s →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N 2 →
      suzukiActualT S (N + 1) D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 (N + 1) s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H (N + 1) (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ))) :
    Lemma144MovingDomainNatCeilAt S H C K d Δ (N + 1) 2 := by
  have hpredGlobal := lemma144MovingDomainGlobalDepthAt_of_natCeil
    S H C K d Δ N 2 hpred
  intro D _hcut hD s hs hsSigma hz
  by_cases hs2 : 2 ≤ s
  · by_cases hregime :
        Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s
    · exact actualClaim145_to_moving_at_common_constant S H hC145 hd hCnorm hH hD hs
        (hclaim D s hD hs2 hregime)
    · by_cases hII : Lemma144CaseIIFinalSide (N + 1) s
      · exact hcaseII D s hD hs hsSigma hz hII hpredGlobal
      · exact hcaseI D s hD hs hsSigma hz hregime hII hpredGlobal
  · have hodd : Odd (N + 1) := by
      by_contra heven
      have hmod : (N + 1) % 2 ≠ 1 := by simpa [Nat.odd_iff] using heven
      have : 2 ≤ s := by simpa [KappaOneModel.parityDomain, hmod] using hs
      exact hs2 this
    have hII : Lemma144CaseIIFinalSide (N + 1) s :=
      ⟨hodd, le_trans (le_of_not_ge hs2) (by norm_num)⟩
    exact hcaseII D s hD hs hsSigma hz hII hpredGlobal

/-- Pure all-depth induction glue.  There is no depth bound and no cutoff in the
conclusion.  The successor argument is intended to be instantiated by the
preceding actual Case-I/II bridge once their `K`-uniform producers land. -/
theorem lemma14_4_noDmin_allDepth_induction
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ)
    (hbase : Lemma144MovingDomainNatCeilAt S H C K d Δ 1 2)
    (hsucc : ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2 →
      Lemma144MovingDomainNatCeilAt S H C K d Δ (N + 1) 2) :
    ∀ N : ℕ, 1 ≤ N →
      Lemma144MovingDomainNatCeilAt S H C K d Δ N 2 := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => exact hbase
  | succ N hN ih => exact hsucc N hN ih

/-- All-depth no-`Dmin` assembler with the real Claim-14.5 and moving-domain
types exposed at the headline.  The only unfilled inputs are the forthcoming
pointwise outputs of the `K`-uniform Case-I and Case-II producers; they are not
collapsed into an abstract complement predicate. -/
theorem lemma14_4_noDmin_allDepth_of_actualClaim145_and_cases
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ C1 Θ : ℝ}
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hCnorm : claim145UniformNormalizationConstant C145 d ≤ C)
    (hH : Section13HatSourceContract H)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hbase : Lemma144MovingDomainNatCeilAt S H C K d Δ 1 2)
    (hclaim : ∀ (N D : ℕ) (s : ℝ),
      1 ≤ N → 2 ≤ D → 2 ≤ s →
      (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ActualClaim145BoundAt S H N D d Δ K s C145)
    (hcaseI : ∀ (N D : ℕ) (s : ℝ),
      1 ≤ N → 2 ≤ D →
      s ∈ KappaOneModel.parityDomain 2 (N + 1) →
      s ≤ sourceSigma (D : ℝ) d →
      2 ≤ ⌈(D : ℝ) ^ (1 / s)⌉₊ →
      ¬ (Real.log (D : ℝ) ≤ C1 * K ^ Θ ∨ sourceSigma (D : ℝ) d ≤ s) →
      ¬ Lemma144CaseIIFinalSide (N + 1) s →
      Lemma144MovingDomainGlobalDepthAt S H C K d Δ N 2 →
      suzukiActualT S (N + 1) D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
        suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 (N + 1) s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H (N + 1) (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)))
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
  apply lemma14_4_noDmin_allDepth_induction S H C K d Δ hbase
  intro N hN hpred
  exact lemma14_4_noDmin_successor_of_actual_cases S H N hC145 hd hCnorm
    hH hK hlocal hpred
    (fun D s hD hs hregime => hclaim (N + 1) D s (by omega) hD hs hregime)
    (fun D s hD hs hsSigma hz hregime hside hglobal =>
      hcaseI N D s hN hD hs hsSigma hz hregime hside hglobal)
    (fun D s hD hs hsSigma hz hside hglobal =>
      hcaseII N D s hN hD hs hsSigma hz hside hglobal)


end MathlibNt.SieveTheory
