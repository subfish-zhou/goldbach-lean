import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIAbsorption

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 1600000

/-!
# Lemma 14.4, Case I: explicit remainder source order

This file separates the three literal remainders at `σ = sourceSigma D d` and
`τ = s`.  It proves the elementary cutoff and logarithmic normalisations and
freezes the first genuinely analytic comparison which is not supplied by the
reachable production cone.  In particular no source-order inequality is made a
premise of an absorption theorem.
-/

/-- The direct Claim-14.5 packet used for `Σ₀` at the moving endpoint. -/
noncomputable def caseISigmaZeroDirectRemainder
    (S : BoundingSieve) (H : Section13HatLayers)
    (N D : ℕ) (C145 K d Δ : ℝ) : ℝ :=
  C145 * claim14_5Scale S H N (D : ℝ) d Δ
    (sourceSigma (D : ℝ) d) K (sourceSigma (D : ℝ) d)

/-- The Euler product decreases when its cutoff increases. -/
theorem suzukiVProduct_mono_antitone
    (S : BoundingSieve) {x y : ℝ} (hxy : x ≤ y) :
    suzukiVProduct S y ≤ suzukiVProduct S x := by
  classical
  unfold suzukiVProduct
  simp only [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro p hp
    split_ifs
    · have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
      have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
      exact sub_nonneg.mpr (S.nu_lt_one_of_prime p hpprime hpdiv).le
    · norm_num
  · intro p hp
    have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp).2.1
    by_cases hpy : (p : ℝ) < y
    · by_cases hpx : (p : ℝ) < x
      · simp [hpy, hpx]
      · simp [hpy, hpx]
        exact (S.nu_pos_of_prime p hpprime hpdiv).le
    · have hnpx : ¬ (p : ℝ) < x := fun hpx => hpy (hpx.trans_le hxy)
      simp [hpy, hnpx]

/-- The logarithm in both Lemma-8.7 endpoints is exactly `log D / σ`. -/
theorem log_rpow_one_div_sourceSigma
    {D d : ℝ} (hD : 0 < D) :
    Real.log (D ^ (1 / sourceSigma D d)) =
      Real.log D / sourceSigma D d := by
  rw [Real.log_rpow hD]
  ring

/-- The direct Claim-14.5 packet already has (indeed, is smaller than) the
required `1/(loglog D * σ)` source order.  This is the complete `Σ₀`
normalisation; its hypotheses are only positivity/range data. -/
theorem caseISigmaZeroDirectRemainder_le_sourceOrder
    (S : BoundingSieve) (H : Section13HatLayers)
    {N D z : ℕ} {C C145 K d Δ : ℝ}
    (hD : 1 < (D : ℝ))
    (hll : 0 < Real.log (Real.log (D : ℝ)))
    (hlllog : Real.log (Real.log (D : ℝ)) ≤ Real.log (D : ℝ))
    (hzD : (z : ℝ) ≤ (D : ℝ))
    (hσ : 0 < sourceSigma (D : ℝ) d)
    (hC : 0 < C) (hC145 : 0 ≤ C145)
    (hE : 0 ≤ errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d)) :
    caseISigmaZeroDirectRemainder S H N D C145 K d Δ ≤
      caseISourceOrderCoefficient (C145 / C) (D : ℝ) d *
        sigma12InheritedBudget S H N D z C K d Δ
          (sourceSigma (D : ℝ) d) := by
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos hD
  have hV := suzukiVProduct_mono_antitone S hzD
  have hexp : 0 ≤ Real.exp (Real.sqrt K) := (Real.exp_pos _).le
  have hL : 0 ≤ (Real.log (D : ℝ)) ^ (-Δ) := Real.rpow_nonneg hlog.le _
  have hVz : 0 ≤ suzukiVProduct S (z : ℝ) := (suzukiVProduct_pos S _).le
  unfold caseISigmaZeroDirectRemainder claim14_5Scale
    caseISourceOrderCoefficient sigma12InheritedBudget
  have hfront :
      C145 * suzukiVProduct S (D : ℝ) * Real.exp (Real.sqrt K) *
          errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
          (Real.log (D : ℝ)) ^ (-Δ) ≤
        C145 * suzukiVProduct S (z : ℝ) * Real.exp (Real.sqrt K) *
          errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
          (Real.log (D : ℝ)) ^ (-Δ) := by gcongr
  have hden :
      1 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d) ≤
        1 / (Real.log (Real.log (D : ℝ)) * sourceSigma (D : ℝ) d) := by
    apply one_div_le_one_div_of_le
    · positivity
    · exact mul_le_mul_of_nonneg_right hlllog hσ.le
  calc
    C145 * (suzukiVProduct S (D : ℝ) *
        (Real.exp (Real.sqrt K) /
          (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) *
        errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
        (Real.log (D : ℝ)) ^ (-Δ)) =
      (C145 * suzukiVProduct S (D : ℝ) * Real.exp (Real.sqrt K) *
        errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
        (Real.log (D : ℝ)) ^ (-Δ)) *
        (1 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) := by ring
    _ ≤ (C145 * suzukiVProduct S (z : ℝ) * Real.exp (Real.sqrt K) *
        errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
        (Real.log (D : ℝ)) ^ (-Δ)) *
        (1 / (Real.log (D : ℝ) * sourceSigma (D : ℝ) d)) := by
          gcongr
    _ ≤ (C145 * suzukiVProduct S (z : ℝ) * Real.exp (Real.sqrt K) *
        errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d) *
        (Real.log (D : ℝ)) ^ (-Δ)) *
        (1 / (Real.log (Real.log (D : ℝ)) * sourceSigma (D : ℝ) d)) := by
          apply mul_le_mul_of_nonneg_left hden
          exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC145 hVz) hexp) hE) hL
    _ = (C145 / C /
          (Real.log (Real.log (D : ℝ)) * sourceSigma (D : ℝ) d)) *
        (C * Real.exp (Real.sqrt K) * suzukiVProduct S (z : ℝ) *
          (Real.log (D : ℝ)) ^ (-Δ) *
          errorEnvelope H N (D : ℝ) d (sourceSigma (D : ℝ) d)) := by
          field_simp [ne_of_gt hC]

/-- First concrete missing factor in the `Σ₁₁` route.  It is exactly the
source comparison needed after expanding the endpoint denominator, not a
renamed source-order or absorption inequality. -/
def CaseISigma11FiniteLayerEnvelopeFactor : Prop :=
  ∀ (H : Section13HatLayers) (N : ℕ) (D : ℝ) (d Δ s : ℝ),
    1 < D → 2 ≤ s →
    finiteSourceLayer 1 2 (N - 1) (s - 1) ≤
      errorEnvelope H N D d s * (Real.log D) ^ (-Δ)

/-- First concrete missing factor in the `Σ₁₂` endpoint route.  This is the
literal pointwise `q_D^∓(s)` versus inherited envelope comparison. -/
def CaseISigma12QDEnvelopeFactor : Prop :=
  ∀ (H : Section13HatLayers) (N : ℕ) (D : ℝ) (d Δ s : ℝ),
    1 < D → 2 ≤ s →
    qD H (ErrorSign.ofDepth N).opposite D d Δ s ≤
      errorEnvelope H N D d s

/-- The remaining common scalar factor after either Lemma-8.7 endpoint has
been reduced to the inherited envelope.  This is the precise asymptotic
calculation still required: `σ² loglog D / log D`, with the extra
`(log D)^Δ` only for `Σ₁₁`. -/
def CaseIEndpointSourceScalarFactors (d Δ : ℝ) : Prop :=
  (∀ᶠ D : ℝ in atTop,
      sourceSigma D d ^ 2 * Real.log (Real.log D) / Real.log D ≤ 1) ∧
  (∀ᶠ D : ℝ in atTop,
      sourceSigma D d ^ 2 * Real.log (Real.log D) *
          (Real.log D) ^ Δ / Real.log D ≤ 1)

/-- Once the direct `Σ₀` packet has been normalised with coefficient
`C145 / C`, the accepted scalar gap theorem absorbs that coefficient. -/
theorem eventually_caseISigmaZeroCoefficient_le_sameC_gap
    {C C145 d Δ : ℝ} (hC : 0 < C) (hC145 : 0 ≤ C145)
    (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) (hd : 7 / (1 - Δ) < d) :
    ∀ᶠ D : ℝ in atTop,
      ∃ q : Lemma144StrictFactor,
        q.ρ = (1 + sigma12ContractionMultiplier (sourceSigma D d) Δ) / 2 ∧
        caseISourceOrderCoefficient (C145 / C) D d ≤ 1 - q.ρ := by
  exact eventually_caseISourceOrderCoefficient_le_sameC_gap
    (div_nonneg hC145 hC.le) hΔ0 hΔ1 hd


end MathlibNt.SieveTheory
