import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiClaim145CaseAssembly
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Equation1410

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple
namespace SuzukiLemma144KappaOne

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

private lemma sigma11_parityDomain_eq_of_mod_eq {β : ℝ} {m n : ℕ}
    (h : m % 2 = n % 2) :
    KappaOneModel.parityDomain β m = KappaOneModel.parityDomain β n := by
  simp only [KappaOneModel.parityDomain, h]

private lemma sigma11_sourceTerm_continuousOn {β : ℝ} (hβ : 1 < β) (N n : ℕ) :
    ContinuousOn (fun s => if n % 2 = N % 2 then suzukiLayer 1 β n s else 0)
      (KappaOneModel.parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := KappaOneModel.continuousOn_parityDomain hβ n
    rw [sigma11_parityDomain_eq_of_mod_eq h] at hn
    exact hn.congr fun s _ => (KappaOneModel.layer_eq_suzukiLayer β n s).symm
  · simp only [h, if_false]
    exact continuousOn_const

private lemma sigma11_sourceTerm_nonneg {β : ℝ} (hβ : 1 < β) (N n : ℕ)
    {s : ℝ} (hs : s ∈ KappaOneModel.parityDomain β N) :
    0 ≤ (if n % 2 = N % 2 then suzukiLayer 1 β n s else 0) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    rw [← KappaOneModel.layer_eq_suzukiLayer]
    apply KappaOneModel.nonneg_on_parityDomain hβ n s
    rwa [sigma11_parityDomain_eq_of_mod_eq h]
  · simp [h]

private lemma sigma11_sourceTerm_weighted_antitone {β : ℝ} (hβ : 1 < β)
    (N n : ℕ) :
    AntitoneOn (fun s => s *
      (if n % 2 = N % 2 then suzukiLayer 1 β n s else 0))
      (KappaOneModel.parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := KappaOneModel.weighted_antitoneOn_parityDomain hβ n
    rw [sigma11_parityDomain_eq_of_mod_eq h] at hn
    intro s hs t ht hst
    simpa only [← KappaOneModel.layer_eq_suzukiLayer] using hn hs ht hst
  · simp only [h, if_false, mul_zero]
    intro s hs t ht hst
    exact le_rfl

private lemma sigma11_sourceTerm_antitone {β : ℝ} (hβ : 1 < β) (N n : ℕ) :
    AntitoneOn (fun s => if n % 2 = N % 2 then suzukiLayer 1 β n s else 0)
      (KappaOneModel.parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := KappaOneModel.antitoneOn_parityDomain hβ n
    rw [sigma11_parityDomain_eq_of_mod_eq h] at hn
    intro s hs t ht hst
    simpa only [← KappaOneModel.layer_eq_suzukiLayer] using hn hs ht hst
  · simp only [h, if_false]
    intro s hs t ht hst
    exact le_rfl

private theorem sigma11_finiteSourceLayer_continuousOn
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    ContinuousOn (finiteSourceLayer 1 β N) (KappaOneModel.parityDomain β N) := by
  classical
  unfold finiteSourceLayer
  induction Finset.Icc 1 N using Finset.induction_on with
  | empty => simpa using (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) _)
  | @insert n u hn ih =>
      simp only [Finset.sum_insert hn]
      exact (sigma11_sourceTerm_continuousOn hβ N n).add ih

private theorem sigma11_finiteSourceLayer_nonneg
    {β : ℝ} (hβ : 1 < β) (N : ℕ) {s : ℝ}
    (hs : s ∈ KappaOneModel.parityDomain β N) :
    0 ≤ finiteSourceLayer 1 β N s := by
  unfold finiteSourceLayer
  exact Finset.sum_nonneg fun n _ => sigma11_sourceTerm_nonneg hβ N n hs

private theorem sigma11_finiteSourceLayer_weighted_antitone
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (fun s => s * finiteSourceLayer 1 β N s)
      (KappaOneModel.parityDomain β N) := by
  intro s hs t ht hst
  unfold finiteSourceLayer
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ =>
    sigma11_sourceTerm_weighted_antitone hβ N n hs ht hst

private theorem sigma11_finiteSourceLayer_antitone
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (finiteSourceLayer 1 β N) (KappaOneModel.parityDomain β N) := by
  intro s hs t ht hst
  unfold finiteSourceLayer
  exact Finset.sum_le_sum fun n _ => sigma11_sourceTerm_antitone hβ N n hs ht hst

private theorem shiftedParityDomain_mono
    {β x y : ℝ} {M : ℕ}
    (hx : x - 1 ∈ KappaOneModel.parityDomain β M) (hxy : x ≤ y) :
    y - 1 ∈ KappaOneModel.parityDomain β M := by
  by_cases hpar : M % 2 = 1
  · simp only [KappaOneModel.parityDomain, hpar,
      if_true, Set.mem_Ioi] at hx ⊢
    linarith
  · simp only [KappaOneModel.parityDomain, hpar,
      if_false, Set.mem_Ici] at hx ⊢
    linarith

/-- Global clamp used only to feed Proposition 9.3 into Lemma 8.7. -/
noncomputable def sigma11ShiftClamp
    (β : ℝ) (M : ℕ) (τ t : ℝ) : ℝ :=
  finiteSourceLayer 1 β M (max (τ - 1) (t - 1))

@[simp] theorem sigma11ShiftClamp_eq_of_le
    (β : ℝ) (M : ℕ) {τ t : ℝ} (hτt : τ ≤ t) :
    sigma11ShiftClamp β M τ t = finiteSourceLayer 1 β M (t - 1) := by
  simp [sigma11ShiftClamp, max_eq_right (by linarith : τ - 1 ≤ t - 1)]

private theorem sigma11ShiftClamp_conditions
    {β τ σ : ℝ} (hβ : 1 < β) (M : ℕ)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β M) (_hτσ : τ ≤ σ) :
    Continuous (sigma11ShiftClamp β M τ) ∧
      (∀ t ∈ Set.Icc τ σ, 0 ≤ sigma11ShiftClamp β M τ t) ∧
      AntitoneOn (fun t => sigma11ShiftClamp β M τ t * t)
        (Set.Icc τ σ) := by
  have hcont : Continuous (sigma11ShiftClamp β M τ) := by
    unfold sigma11ShiftClamp
    apply (sigma11_finiteSourceLayer_continuousOn hβ M).comp_continuous
      (continuous_const.max (continuous_id.sub continuous_const))
    intro t
    simpa using shiftedParityDomain_mono (x := τ)
      (y := max (τ - 1) (t - 1) + 1) hτdom
      (by have h := le_max_left (τ - 1) (t - 1); linarith)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    rw [sigma11ShiftClamp_eq_of_le β M ht.1]
    exact sigma11_finiteSourceLayer_nonneg hβ M
      (shiftedParityDomain_mono hτdom ht.1)
  · intro x hx y hy hxy
    change sigma11ShiftClamp β M τ y * y ≤ sigma11ShiftClamp β M τ x * x
    rw [sigma11ShiftClamp_eq_of_le β M hx.1,
      sigma11ShiftClamp_eq_of_le β M hy.1]
    have hxdom := shiftedParityDomain_mono hτdom hx.1
    have hydom := shiftedParityDomain_mono hτdom hy.1
    have hw := sigma11_finiteSourceLayer_weighted_antitone hβ M
      hxdom hydom (by linarith : x - 1 ≤ y - 1)
    have hu := sigma11_finiteSourceLayer_antitone hβ M
      hxdom hydom (by linarith : x - 1 ≤ y - 1)
    nlinarith

/-- Direct source-layer instance of Lemma 8.7, kept in the same import cone as
Claim 14.5 to avoid the legacy/production finite-layer declaration collision. -/
theorem sigma11_finiteSourceLayer_lemma8_7
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hτσ : τ ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      (1 / s) * (∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1)) +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) := by
  let F : ℝ → ℝ := sigma11ShiftClamp β (N - 1) τ
  obtain ⟨hcont, hnonneg, hanti⟩ :=
    sigma11ShiftClamp_conditions hβ (N - 1) hτdom hτσ
  have h87 := suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz
    hz hv hw hcont hnonneg hanti hK hlocal
  have hτpos : 0 < τ := by
    have hp : 0 < τ - 1 := KappaOneModel.closedDomain_pos hβ
      (KappaOneModel.parityDomain_subset_closedDomain β (N - 1) hτdom)
    linarith
  have hcoord : ∀ x ∈ Set.Icc w v,
      Real.log D / Real.log x ∈ Set.Icc τ σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hτpos hτσ hv hw hx
  have hprime : suzukiLemmaEightSevenPrimeSum S D w v z F =
      suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) := by
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show F (Real.log D / Real.log p) =
        finiteSourceLayer 1 β (N - 1) (Real.log D / Real.log p - 1) by
      exact sigma11ShiftClamp_eq_of_le β (N - 1) ht.1]
  have hint : (∫ t in τ..σ, F t) =
      ∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hτσ]
    intro t ht
    exact sigma11ShiftClamp_eq_of_le β (N - 1) ht.1
  rw [hprime, hint, sigma11ShiftClamp_eq_of_le β (N - 1) le_rfl] at h87
  exact h87

/-- Monotonicity of the source-faithful Lemma-8.7 middle-range functional.
Only values at the actual prime coordinates are required.  The Euler suffix
continues to use the third cutoff `z`; the prime carrier stops at `v`. -/
theorem suzukiLemmaEightSevenPrimeSum_mono_on_middle
    (S : BoundingSieve) (D w v z : ℝ) (F G : ℝ → ℝ)
    (hFG : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      F (Real.log D / Real.log p) ≤ G (Real.log D / Real.log p)) :
    suzukiLemmaEightSevenPrimeSum S D w v z F ≤
      suzukiLemmaEightSevenPrimeSum S D w v z G := by
  classical
  unfold suzukiLemmaEightSevenPrimeSum
  apply Finset.sum_le_sum
  intro p hp
  have hp' := Finset.mem_filter.mp hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp'.1
  have hpdiv : p ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hp'.1).2.1
  have hnu : 0 ≤ S.nu p := (S.nu_pos_of_prime p hpprime hpdiv).le
  have hsuffix : 0 ≤ ∏ q ∈ S.prodPrimes.primeFactors.filter
      (fun q : ℕ => p ≤ q ∧ (q : ℝ) < z), (1 - S.nu q)⁻¹ := by
    apply Finset.prod_nonneg
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq'.1
    have hqdiv : q ∣ S.prodPrimes := (Nat.mem_primeFactors.mp hq'.1).2.1
    exact inv_nonneg.mpr
      (sub_nonneg.mpr (S.nu_lt_one_of_prime q hqprime hqdiv).le)
  exact mul_le_mul_of_nonneg_left
    (hFG p hp'.1 hp'.2.1 hp'.2.2) (mul_nonneg hnu hsuffix)

/-- Source-correct `Σ₁₁` middle-range assembly.  Lemma 8.7 is used only on
`w ≤ p < v`, with `H(t)=T_{N-1}(t-1)`.  Proposition 9.3 supplies all analytic
conditions, while the source recursion bounds the truncated main integral by
`T_N(s)`.  No equality is asserted: it generally fails when `τ > s` or when
`σ` truncates the source support. -/
theorem sigma11_middle_le_finiteSourceLayer_add_endpoint
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      finiteSourceLayer 1 β N s +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) := by
  have h87 := sigma11_finiteSourceLayer_lemma8_7
    hβ hτdom hτσ hD hz2 hv2 hw2 hwv hvz hz hv hw hK hlocal
  exact h87.trans (add_le_add
    (Sigma11FiniteLayerMajorization hβ hsdom hτdom hsτ hτσ) le_rfl)

/-- Source-correct `Σ₁₂` middle-range assembly after the pointwise majorant
(14.13).  The prime carrier is exactly `w ≤ p < v`; `z` is deliberately kept
as the independent original sieve cutoff controlling `V(p)/V(z)`. -/
theorem sigma12_middle_le_qD_lemma8_7
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} (sign : ErrorSign) (R : ℝ → ℝ)
    (hmajorant : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      R (Real.log D / Real.log p) ≤
        qD H sign.opposite D d Δ (Real.log D / Real.log p))
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + sign.epsilon < τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    suzukiLemmaEightSevenPrimeSum S D w v z R ≤
      (1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) +
        (6 * K ^ 2 * qD H sign.opposite D d Δ τ / Real.log w) *
          (τ / s) := by
  exact (suzukiLemmaEightSevenPrimeSum_mono_on_middle
    S D w v z R (qD H sign.opposite D d Δ) hmajorant).trans
      (lemma8_7_qD_of_claim14_6_ii (S := S) (H := H) (sign := sign)
        hH hD hz2 hv2 hw2 hwv hvz hz hv hw hτ hτσ hK hlocal hii)

/-- Combined source-correct middle-range estimate for `Σ₁₁ + Σ₁₂`.
Both terms use the same exact carrier `w ≤ p < v` and the same independent
Euler-ratio cutoff `z`. -/
theorem sigma11_add_sigma12_middle_le
    {S : BoundingSieve} {H : Section13HatLayers}
    {β D z v w s τ σ K d Δ : ℝ} {N : ℕ}
    (sign : ErrorSign) (R : ℝ → ℝ)
    (hβ : 1 < β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ)
    (hmajorant : ∀ p ∈ S.prodPrimes.primeFactors,
      w ≤ (p : ℝ) → (p : ℝ) < v →
      R (Real.log D / Real.log p) ≤
        qD H sign.opposite D d Δ (Real.log D / Real.log p))
    (hH : Section13HatContract H β)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hτ : H.betaHat + sign.epsilon < τ) (hτσ : τ ≤ σ)
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K)
    (hii : Claim14_6_MonotoneQPremise H D d Δ σ) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) +
      suzukiLemmaEightSevenPrimeSum S D w v z R ≤
      finiteSourceLayer 1 β N s +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) +
      ((1 / s) * (∫ t in τ..σ, qD H sign.opposite D d Δ t) +
        (6 * K ^ 2 * qD H sign.opposite D d Δ τ / Real.log w) *
          (τ / s)) := by
  exact add_le_add
    (sigma11_middle_le_finiteSourceLayer_add_endpoint hβ hsdom hτdom hsτ hτσ
      hD hz2 hv2 hw2 hwv hvz hz hv hw hK hlocal)
    (sigma12_middle_le_qD_lemma8_7 sign R hmajorant hH hD hz2 hv2 hw2
      hwv hvz hz hv hw hτ hτσ hK hlocal hii)


end SuzukiLemma144KappaOne
end MathlibNt.SieveTheory.SwitchingPrinciple
