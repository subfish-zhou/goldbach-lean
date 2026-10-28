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


/-- The production Euler product decreases when its cutoff is enlarged. -/
theorem claim14_5VProduct_le_suzukiVProduct
    (S : BoundingSieve) {z D : ℝ} (hzD : z ≤ D) :
    claim14_5VProduct S D ≤ suzukiVProduct S z := by
  simpa only [claim14_5VProduct, suzukiVProduct] using
    (suzukiVProduct_mono_antitone S hzD)

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


end MathlibNt.SieveTheory
