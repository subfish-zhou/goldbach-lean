import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145SourceBranchInterface
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144MovingDomainFiniteInduction

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1200000

/-!
# No-`Dmin` bridges for the source Lemma 14.4 induction

The literal all-`D ≥ 2` predecessor assertion is exactly the production moving
contract at cutoff `2`.  This file records that conversion and the two concrete
pre-branch transports needed by the direct source induction.  It deliberately
reuses `ActualClaim145BoundAt` and `claim14_5Scale`; no second Claim-14.5 scale is
introduced.
-/

/-- A literal all-`D ≥ 2` predecessor assertion is the moving-domain contract
with `Dmin = 2`.  This is the bridge used when the source induction hypothesis
has no cutoff binder. -/
theorem lemma144MovingDomainGlobalDepthAt_two_iff_allD
    (S : BoundingSieve) (H : Section13HatLayers)
    (C K d Δ : ℝ) (N : ℕ) :
    Lemma144MovingDomainGlobalDepthAt S H C K d Δ N 2 ↔
      ∀ D z : ℕ, 2 ≤ D → 2 ≤ z →
        ∀ x : ℝ, x ∈ KappaOneModel.parityDomain 2 N →
          x ≤ sourceSigma (D : ℝ) d →
          (D : ℝ) ^ (1 / x) = (z : ℝ) →
          suzukiActualT S N D z ≤
            suzukiVProduct S z *
              (finiteSourceLayer 1 2 N x +
                C * Real.exp (Real.sqrt K) *
                  errorEnvelope H N (D : ℝ) d x *
                    (Real.log (D : ℝ)) ^ (-Δ)) := by
  constructor
  · intro h D z hD hz x hx hxSigma hpower
    exact h D z hD hD hz x hx hxSigma hpower
  · intro h D z hcut hD hz x hx hxSigma hpower
    exact h D z hD hz x hx hxSigma hpower

/-- A source logarithmic lower bound pays any fixed natural cutoff.  The cutoff
is selected before the depth, exactly as in the production moving Case-I and
Case-II eventual APIs. -/
theorem nat_cutoff_paid_by_source_log_large
    {D D0 : ℕ} {C1 K Θ : ℝ}
    (hD : 2 ≤ D) (hD0 : 2 ≤ D0)
    (hbudget : Real.log (D0 : ℝ) ≤ C1 * K ^ Θ)
    (hlarge : C1 * K ^ Θ < Real.log (D : ℝ)) :
    D0 ≤ D := by
  by_contra hnot
  have hDD0 : D < D0 := by omega
  have hloglt : Real.log (D : ℝ) < Real.log (D0 : ℝ) := by
    apply Real.strictMonoOn_log
    · show (0 : ℝ) < (D : ℝ)
      exact_mod_cast (show 0 < D by omega)
    · show (0 : ℝ) < (D0 : ℝ)
      exact_mod_cast (show 0 < D0 by omega)
    · exact_mod_cast hDD0
  linarith

/-- The production Euler product decreases when its cutoff is enlarged. -/
theorem claim14_5VProduct_le_suzukiVProduct
    (S : BoundingSieve) {z D : ℝ} (hzD : z ≤ D) :
    claim14_5VProduct S D ≤ suzukiVProduct S z := by
  classical
  let A := S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < z)
  let B := S.prodPrimes.primeFactors.filter (fun p : ℕ => (p : ℝ) < D)
  have hAB : A ⊆ B := by
    intro p hp
    simp only [A, B, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.trans_le hzD⟩
  have hfac0 : ∀ p ∈ B \ A, 0 ≤ (1 - S.nu p) := by
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := by
      exact (Finset.mem_sdiff.mp hp).1 |> Finset.mem_filter.mp |>.1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
  have hfac1 : ∀ p ∈ B \ A, (1 - S.nu p) ≤ 1 := by
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := by
      exact (Finset.mem_sdiff.mp hp).1 |> Finset.mem_filter.mp |>.1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_le_self 1 (S.nu_pos_of_prime p hpprime hpdiv).le
  have hdiff0 : 0 ≤ ∏ p ∈ B \ A, (1 - S.nu p) :=
    Finset.prod_nonneg hfac0
  have hdiff1 : (∏ p ∈ B \ A, (1 - S.nu p)) ≤ 1 :=
    Finset.prod_le_one hfac0 hfac1
  have hA0 : 0 ≤ ∏ p ∈ A, (1 - S.nu p) := by
    apply Finset.prod_nonneg
    intro p hp
    have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hp).1
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpS
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hpS).2.1
    exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
  have hsplit := Finset.prod_sdiff (f := fun p : ℕ => (1 - S.nu p)) hAB
  unfold claim14_5VProduct suzukiVProduct
  change (∏ p ∈ B, (1 - S.nu p)) ≤ ∏ p ∈ A, (1 - S.nu p)
  rw [← hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hdiff1 hA0]

/-- Concrete normalization from the production Claim-14.5 bound to the
Lemma-14.4 right-hand side.  The only scalar input is the literal inequality
needed after unfolding the already-defined production scale. -/
theorem ActualClaim145BoundAt.to_lemma144_moving_of_scalar
    (S : BoundingSieve) (H : Section13HatLayers)
    {C C145 K d Δ s : ℝ} {N D : ℕ}
    (hC145 : 0 ≤ C145)
    (hH : Section13HatSourceContract H)
    (hD : 2 ≤ D) (hs : s ∈ KappaOneModel.parityDomain 2 N)
    (hzD : (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) ≤ (D : ℝ))
    (hscalar : C145 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) ≤ C)
    (hclaim : ActualClaim145BoundAt S H N D d Δ K s C145) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s +
          C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
  have hD1 : (1 : ℝ) < (D : ℝ) := by exact_mod_cast (show 1 < D by omega)
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD1
  have hsig : 0 < sourceSigma (D : ℝ) d := sourceSigma_pos_of_nat_two_le hD
  have hs0 : 0 < s := by
    by_cases hodd : N % 2 = 1
    · rw [KappaOneModel.parityDomain, if_pos hodd] at hs
      norm_num at hs
      exact lt_trans zero_lt_one hs
    · rw [KappaOneModel.parityDomain, if_neg hodd] at hs
      exact lt_of_lt_of_le (by norm_num) hs
  have hE : 0 ≤ errorEnvelope H N (D : ℝ) d s :=
    errorEnvelope_nonneg H N hD1 hs0.le
      (hH.toSection13HatContract.positive _ s hs0).le
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlog.le _
  have hV := claim14_5VProduct_le_suzukiVProduct S hzD
  have hV0 : 0 ≤ claim14_5VProduct S (D : ℝ) := by
    simpa [claim14_5VProduct, suzukiVProduct] using
      (suzukiVProduct_pos S (D : ℝ)).le
  have hVz0 : 0 ≤ suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) :=
    (suzukiVProduct_pos S _).le
  have hratio0 : 0 ≤ C145 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) :=
    div_nonneg hC145 (mul_pos hlog hsig).le
  have hmain := finiteSourceLayer_nonneg_on_parityDomain (by norm_num : (1 : ℝ) < 2) N hs
  change suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
    C145 * claim14_5Scale S H N (D : ℝ) d Δ (sourceSigma (D : ℝ) d) K s at hclaim
  apply hclaim.trans
  unfold claim14_5Scale
  calc
    C145 * (claim14_5VProduct S (D : ℝ) *
          (Real.exp (Real.sqrt K) /
            (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
          errorEnvelope H N (D : ℝ) d s * (Real.log (D : ℝ)) ^ (-Δ))
        = claim14_5VProduct S (D : ℝ) *
            (C145 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) *
              Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
                (Real.log (D : ℝ)) ^ (-Δ)) := by ring
    _ ≤ suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
            (Real.log (D : ℝ)) ^ (-Δ)) := by
      gcongr
    _ ≤ suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
          (finiteSourceLayer 1 2 N s +
            C * Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) := by
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hmain) hVz0

/-- A concrete normalization constant for the Claim-14.5 scalar.  It is fixed
before the natural quotient `D` and uses only the lower endpoint `D = 2`. -/
noncomputable def claim145UniformNormalizationConstant (C145 d : ℝ) : ℝ :=
  C145 / (Real.log 2 * sourceSigma 2 d)

/-- The Claim-14.5 scalar is uniformly bounded on the full source range
`D ≥ 2`; no eventual-`D` threshold is used. -/
theorem claim145_uniform_scalar_normalization
    (C145 d : ℝ) (hC145 : 0 ≤ C145) (hd : 0 < d) :
    0 ≤ claim145UniformNormalizationConstant C145 d ∧
      ∀ D : ℕ, 2 ≤ D →
        C145 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) ≤
          claim145UniformNormalizationConstant C145 d := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hinner2 : 1 < Real.log (27 * (2 : ℝ)) := by
    have harg : 0 < 27 * (2 : ℝ) := by norm_num
    apply (Real.lt_log_iff_exp_lt harg).2
    exact Real.exp_one_lt_d9.trans (by norm_num)
  have hsigma2 : 0 < sourceSigma 2 d := by
    unfold sourceSigma
    exact mul_pos (Real.rpow_pos_of_pos hlog2 _) (Real.log_pos hinner2)
  have hden2 : 0 < Real.log 2 * sourceSigma 2 d := mul_pos hlog2 hsigma2
  constructor
  · exact div_nonneg hC145 hden2.le
  intro D hD
  have hDreal : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hDpos : 0 < (D : ℝ) := by positivity
  have hlogD : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < D by omega))
  have hlog_mono : Real.log (2 : ℝ) ≤ Real.log (D : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hDpos hDreal
  have hrpow_mono :
      (Real.log (2 : ℝ)) ^ (1 / d) ≤
        (Real.log (D : ℝ)) ^ (1 / d) :=
    Real.rpow_le_rpow hlog2.le hlog_mono (by positivity)
  have h27mono : (27 : ℝ) * 2 ≤ 27 * (D : ℝ) := by nlinarith
  have hlog27Dpos : 0 < Real.log (27 * (D : ℝ)) :=
    Real.log_pos (by nlinarith)
  have hlog27mono :
      Real.log (27 * (2 : ℝ)) ≤ Real.log (27 * (D : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (show 0 < 27 * (2 : ℝ) by norm_num)
      (show 0 < 27 * (D : ℝ) by positivity) h27mono
  have hloglog_mono :
      Real.log (Real.log (27 * (2 : ℝ))) ≤
        Real.log (Real.log (27 * (D : ℝ))) :=
    Real.strictMonoOn_log.monotoneOn
      (show 0 < Real.log (27 * (2 : ℝ)) by linarith [hinner2])
      hlog27Dpos hlog27mono
  have hsigma_mono : sourceSigma 2 d ≤ sourceSigma (D : ℝ) d := by
    unfold sourceSigma
    exact mul_le_mul hrpow_mono hloglog_mono
      (Real.log_pos hinner2).le (Real.rpow_nonneg hlogD.le _)
  have hden_mono :
      Real.log 2 * sourceSigma 2 d ≤
        Real.log (D : ℝ) * sourceSigma (D : ℝ) d :=
    mul_le_mul hlog_mono hsigma_mono hsigma2.le hlogD.le
  exact div_le_div_of_nonneg_left hC145 hden2 hden_mono

/-- Existential form of the same uniform normalization, with the constant chosen
before `D`. -/
theorem exists_claim145_uniform_scalar_normalization
    (C145 d : ℝ) (hC145 : 0 ≤ C145) (hd : 0 < d) :
    ∃ Cnorm : ℝ, 0 ≤ Cnorm ∧ ∀ D : ℕ, 2 ≤ D →
      C145 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) ≤ Cnorm := by
  exact ⟨claim145UniformNormalizationConstant C145 d,
    claim145_uniform_scalar_normalization C145 d hC145 hd⟩

/-- Claim 14.5 implies the Lemma-14.4 moving right-hand side with one explicit
constant independent of `D`.  The natural ceiling and parity-domain hypotheses
are unchanged from `to_lemma144_moving_of_scalar`. -/
theorem ActualClaim145BoundAt.to_lemma144_moving
    (S : BoundingSieve) (H : Section13HatLayers)
    {C145 K d Δ s : ℝ} {N D : ℕ}
    (hC145 : 0 ≤ C145) (hd : 0 < d)
    (hH : Section13HatSourceContract H)
    (hD : 2 ≤ D) (hs : s ∈ KappaOneModel.parityDomain 2 N)
    (hzD : (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) ≤ (D : ℝ))
    (hclaim : ActualClaim145BoundAt S H N D d Δ K s C145) :
    suzukiActualT S N D ⌈(D : ℝ) ^ (1 / s)⌉₊ ≤
      suzukiVProduct S (⌈(D : ℝ) ^ (1 / s)⌉₊ : ℝ) *
        (finiteSourceLayer 1 2 N s +
          claim145UniformNormalizationConstant C145 d *
            Real.exp (Real.sqrt K) * errorEnvelope H N (D : ℝ) d s *
              (Real.log (D : ℝ)) ^ (-Δ)) := by
  exact ActualClaim145BoundAt.to_lemma144_moving_of_scalar S H hC145 hH hD hs hzD
    (claim145_uniform_scalar_normalization C145 d hC145 hd |>.2 D hD) hclaim


end MathlibNt.SieveTheory
