module

public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144Sigma11Internal
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma144CaseIEvenEndpointFinal
public import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87FiniteSourceRecursion

@[expose] public section

open scoped Classical BigOperators Interval
open Finset MeasureTheory Set

namespace MathlibNt.SieveTheory

open LinearSieve SwitchingPrinciple SuzukiFiniteContinuousLayers
open SwitchingPrinciple.SuzukiLemma144Equation1410
open SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 2000000

/-! # Lemma 14.4: the even `Σ₁₁` endpoint

At even depth `M`, the predecessor depth `M-1` is odd.  Its source domain is
open at `1`, but the κ=1 layers are regular on the closed envelope.  We use that
closed-envelope regularity only to run Lemma 8.7 and the finite recursion at the
endpoint.  The prime carrier itself is strict, so no prime coordinate is added.
-/

/-- Finite source layers are continuous on the closed parity domain for `beta > 1`. -/
theorem finiteSourceLayer_continuousOn_closedDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    ContinuousOn (finiteSourceLayer 1 β N) (KappaOneModel.closedDomain β N) := by
  classical
  unfold finiteSourceLayer
  apply continuousOn_finsetSum
  intro n hn
  by_cases hpar : n % 2 = N % 2
  · simp only [hpar, ite_true]
    have hclosed : KappaOneModel.closedDomain β n =
        KappaOneModel.closedDomain β N := by
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      rw [hpar]
    have hreg := (KappaOneModel.regular hβ n).continuous
    rw [hclosed] at hreg
    exact hreg.congr fun s _ =>
      (KappaOneModel.layer_eq_suzukiLayer β n s).symm
  · simpa only [hpar, ite_false] using
      (continuousOn_const : ContinuousOn (fun _ : ℝ => (0 : ℝ)) _)

private theorem finiteSourceLayer_nonneg_on_closedDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) {s : ℝ}
    (hs : s ∈ KappaOneModel.closedDomain β N) :
    0 ≤ finiteSourceLayer 1 β N s := by
  classical
  unfold finiteSourceLayer
  apply Finset.sum_nonneg
  intro n hn
  by_cases hpar : n % 2 = N % 2
  · simp only [hpar, ite_true]
    rw [← KappaOneModel.layer_eq_suzukiLayer]
    apply (KappaOneModel.regular hβ n).nonneg s
    unfold KappaOneModel.closedDomain KappaOneModel.eps at hs ⊢
    simpa [hpar] using hs
  · simp [hpar]

private theorem finiteSourceLayer_weighted_antitoneOn_closedDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (fun s => s * finiteSourceLayer 1 β N s)
      (KappaOneModel.closedDomain β N) := by
  classical
  intro s hs t ht hst
  unfold finiteSourceLayer
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  by_cases hpar : n % 2 = N % 2
  · simp only [hpar, ite_true]
    rw [← KappaOneModel.layer_eq_suzukiLayer,
      ← KappaOneModel.layer_eq_suzukiLayer]
    apply (KappaOneModel.regular hβ n).weighted_antitone
    · unfold KappaOneModel.closedDomain KappaOneModel.eps at hs ⊢
      simpa [hpar] using hs
    · unfold KappaOneModel.closedDomain KappaOneModel.eps at ht ⊢
      simpa [hpar] using ht
    · exact hst
  · simp [hpar]

private theorem finiteSourceLayer_antitoneOn_closedDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (finiteSourceLayer 1 β N)
      (KappaOneModel.closedDomain β N) := by
  intro s hs t ht hst
  have hweighted := finiteSourceLayer_weighted_antitoneOn_closedDomain hβ N
    hs ht hst
  have hnonneg := finiteSourceLayer_nonneg_on_closedDomain hβ N ht
  have hspos := KappaOneModel.closedDomain_pos hβ hs
  have hscale : s * finiteSourceLayer 1 β N t ≤
      t * finiteSourceLayer 1 β N t :=
    mul_le_mul_of_nonneg_right hst hnonneg
  nlinarith

private noncomputable def sigma11EvenEndpointClamp
    (M : ℕ) (t : ℝ) : ℝ :=
  finiteSourceLayer 1 2 (M - 1) (max 1 (t - 1))

private theorem sigma11EvenEndpointClamp_eq_of_two_le
    (M : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    sigma11EvenEndpointClamp M t =
      finiteSourceLayer 1 2 (M - 1) (t - 1) := by
  simp [sigma11EvenEndpointClamp, max_eq_right (by linarith : 1 ≤ t - 1)]

private theorem sigma11EvenEndpointClamp_conditions
    {M : ℕ} (hM : Even M) (hM2 : 2 ≤ M) {σ : ℝ} (_hσ : 2 ≤ σ) :
    Continuous (sigma11EvenEndpointClamp M) ∧
      (∀ t ∈ Set.Icc (2 : ℝ) σ, 0 ≤ sigma11EvenEndpointClamp M t) ∧
      AntitoneOn (fun t => sigma11EvenEndpointClamp M t * t)
        (Set.Icc (2 : ℝ) σ) := by
  have hpred : (M - 1) % 2 = 1 := by
    have hm : M % 2 = 0 := Nat.even_iff.mp hM
    omega
  have hmap : ∀ t : ℝ, max 1 (t - 1) ∈
      KappaOneModel.closedDomain 2 (M - 1) := by
    intro t
    unfold KappaOneModel.closedDomain KappaOneModel.eps
    simp only [hpred, Nat.cast_one, Set.mem_Ici]
    norm_num
  have hcont : Continuous (sigma11EvenEndpointClamp M) := by
    unfold sigma11EvenEndpointClamp
    apply (finiteSourceLayer_continuousOn_closedDomain (by norm_num) (M - 1)).comp_continuous
      (continuous_const.max (continuous_id.sub continuous_const))
    exact hmap
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    rw [sigma11EvenEndpointClamp_eq_of_two_le M ht.1]
    apply finiteSourceLayer_nonneg_on_closedDomain (by norm_num) (M - 1)
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    exact ht.1
  · intro x hx y hy hxy
    change sigma11EvenEndpointClamp M y * y ≤ sigma11EvenEndpointClamp M x * x
    rw [sigma11EvenEndpointClamp_eq_of_two_le M hx.1,
      sigma11EvenEndpointClamp_eq_of_two_le M hy.1]
    have hxdom : x - 1 ∈ KappaOneModel.closedDomain 2 (M - 1) := by
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [hpred, Nat.cast_one, Set.mem_Ici]
      linarith [hx.1]
    have hydom : y - 1 ∈ KappaOneModel.closedDomain 2 (M - 1) := by
      unfold KappaOneModel.closedDomain KappaOneModel.eps
      simp only [hpred, Nat.cast_one, Set.mem_Ici]
      linarith [hy.1]
    have hw := finiteSourceLayer_weighted_antitoneOn_closedDomain
      (by norm_num) (M - 1) hxdom hydom (by linarith : x - 1 ≤ y - 1)
    have hu := finiteSourceLayer_antitoneOn_closedDomain
      (by norm_num) (M - 1) hxdom hydom (by linarith : x - 1 ≤ y - 1)
    nlinarith

/-- Lemma 8.7 at `s=τ=2`, using closed-envelope regularity at the one
formal boundary point.  Its prime sum remains on the original strict carrier. -/
theorem sigma11_finiteSourceLayer_lemma8_7_even_endpoint
    {S : BoundingSieve} {D z v w σ K : ℝ} {M : ℕ}
    (hM : Even M) (hM2 : 2 ≤ M)
    (hσ : 2 ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / (2 : ℝ)))
    (hv : v = D ^ (1 / (2 : ℝ)))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 2 (M - 1) (t - 1)) ≤
      (1 / (2 : ℝ)) *
          (∫ t in (2 : ℝ)..σ, finiteSourceLayer 1 2 (M - 1) (t - 1)) +
        (6 * K ^ 2 * finiteSourceLayer 1 2 (M - 1) 1 /
          Real.log w) := by
  let H : ℝ → ℝ := sigma11EvenEndpointClamp M
  obtain ⟨hcont, hnonneg, hanti⟩ :=
    sigma11EvenEndpointClamp_conditions hM hM2 hσ
  have h87 := suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz
    hz hv hw hcont hnonneg hanti hK hlocal
  have hcoord : ∀ x ∈ Set.Icc w v,
      Real.log D / Real.log x ∈ Set.Icc (2 : ℝ) σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD (by norm_num) hσ hv hw hx
  have hprime : suzukiLemmaEightSevenPrimeSum S D w v z H =
      suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 2 (M - 1) (t - 1)) := by
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show H (Real.log D / Real.log p) =
        finiteSourceLayer 1 2 (M - 1) (Real.log D / Real.log p - 1) by
      exact sigma11EvenEndpointClamp_eq_of_two_le M ht.1]
  have hint : (∫ t in (2 : ℝ)..σ, H t) =
      ∫ t in (2 : ℝ)..σ, finiteSourceLayer 1 2 (M - 1) (t - 1) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hσ]
    intro t ht
    exact sigma11EvenEndpointClamp_eq_of_two_le M ht.1
  have hH2 : sigma11EvenEndpointClamp M 2 =
      finiteSourceLayer 1 2 (M - 1) 1 := by
    norm_num [sigma11EvenEndpointClamp]
  rw [hprime, hint, hH2] at h87
  norm_num at h87 ⊢
  simpa only [mul_one] using h87

/-- The finite `(9.2)` majorization remains valid when the odd predecessor is
used at its closed left endpoint. -/
theorem Sigma11FiniteLayerMajorization_even_endpoint
    {M : ℕ} (hM : Even M) (hM2 : 2 ≤ M) {σ : ℝ} (hσ : 2 ≤ σ) :
    (1 / (2 : ℝ)) *
        (∫ t in (2 : ℝ)..σ, finiteSourceLayer 1 2 (M - 1) (t - 1)) ≤
      finiteSourceLayer 1 2 M 2 := by
  classical
  rw [integral_finiteSourceLayer_shift_eq_recursionIntegrand]
  unfold finiteSourceRecursionIntegrand
  have hm0 : M % 2 = 0 := Nat.even_iff.mp hM
  have hpred : (M - 1) % 2 = 1 := by omega
  have hclosed : (1 : ℝ) ∈ KappaOneModel.closedDomain 2 (M - 1) := by
    simp [KappaOneModel.closedDomain, KappaOneModel.eps, hpred]
    norm_num
  have hsdom : (2 : ℝ) ∈ KappaOneModel.parityDomain 2 M := by
    unfold KappaOneModel.parityDomain
    rw [ite_eq_right (by omega : M % 2 ≠ 1)]
    change (2 : ℝ) ≤ 2
    exact le_rfl
  have hint : ∀ n ∈ finiteSourceRecursionIndices M,
      IntervalIntegrable (fun t => suzukiLayer 1 2 (n - 1) (t - 1))
        MeasureTheory.volume 2 σ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn'.1).1
    have hnN : n ≤ M := (Finset.mem_Icc.mp hn'.1).2
    have hpredpar : (n - 1) % 2 = (M - 1) % 2 := by omega
    have hdom : (1 : ℝ) ∈ KappaOneModel.closedDomain 2 (n - 1) := by
      unfold KappaOneModel.closedDomain KappaOneModel.eps at hclosed ⊢
      simpa [hpredpar] using hclosed
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hσ]
    apply ((KappaOneModel.regular (by norm_num) (n - 1)).continuous.congr
      (fun x _ => (KappaOneModel.layer_eq_suzukiLayer 2 (n - 1) x).symm)).comp
      (continuous_id.sub continuous_const).continuousOn
    intro t ht
    unfold KappaOneModel.closedDomain KappaOneModel.eps at hdom ⊢
    simp only [Set.mem_Ici] at hdom ⊢
    change (2 : ℝ) - (((n - 1) % 2 : ℕ) : ℝ) ≤ t - 1
    calc
      (2 : ℝ) - (((n - 1) % 2 : ℕ) : ℝ) ≤ (1 : ℝ) := hdom
      _ ≤ t - 1 := by linarith [ht.1]
  rw [intervalIntegral.integral_finsetSum hint, Finset.mul_sum]
  calc
    (∑ n ∈ finiteSourceRecursionIndices M,
        (1 / (2 : ℝ)) * ∫ t in (2 : ℝ)..σ,
          suzukiLayer 1 2 (n - 1) (t - 1)) ≤
        ∑ n ∈ finiteSourceRecursionIndices M, suzukiLayer 1 2 n 2 := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnmem := Finset.mem_Icc.mp hn'.1
      have hnpar : n % 2 = M % 2 := hn'.2
      have hpredpar : (n - 1) % 2 = (M - 1) % 2 := by omega
      apply suzukiLayer_one_step_closed_predecessor (by norm_num) hnmem.1
      · simpa [KappaOneModel.parityDomain, hnpar] using hsdom
      · unfold KappaOneModel.closedDomain KappaOneModel.eps at hclosed ⊢
        simp only [hpredpar, hpred, Nat.cast_one, Set.mem_Ici]
        norm_num
      · exact le_rfl
      · exact hσ
    _ ≤ finiteSourceLayer 1 2 M 2 := by
      unfold finiteSourceRecursionIndices finiteSourceLayer
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
      · intro n hn hnnot
        have hn' := Finset.mem_filter.mp hn
        have hndom : (2 : ℝ) ∈ KappaOneModel.parityDomain 2 n := by
          simpa [KappaOneModel.parityDomain, hn'.2] using hsdom
        rw [← KappaOneModel.layer_eq_suzukiLayer]
        exact KappaOneModel.nonneg_on_parityDomain (by norm_num) n 2 hndom

/-- Production closure of the even Case-I `Σ₁₁` endpoint, with no predecessor
open-domain hypothesis. -/
theorem caseI_evenEndpointSigma11Edge
    (S : BoundingSieve) {M D : ℕ} {K σ : ℝ}
    (hM : Even M) (hM2 : 2 ≤ M) (hσ : 2 ≤ σ)
    (hD : 1 < (D : ℝ))
    (hroot2 : 2 ≤ (D : ℝ) ^ (1 / (2 : ℝ)))
    (hw2 : 2 ≤ (D : ℝ) ^ (1 / σ))
    (hwroot : (D : ℝ) ^ (1 / σ) ≤ (D : ℝ) ^ (1 / (2 : ℝ)))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    CaseIEvenEndpointSigma11Edge S M D K σ := by
  let w : ℝ := (D : ℝ) ^ (1 / σ)
  let v : ℝ := (D : ℝ) ^ (1 / (2 : ℝ))
  let r : ℝ := (D : ℝ) ^ (1 / (2 : ℝ))
  let z : ℕ := ⌈r⌉₊
  have h87 := sigma11_finiteSourceLayer_lemma8_7_even_endpoint
    (S := S) (D := (D : ℝ)) (z := r) (v := v) (w := w)
    (σ := σ) (K := K) (M := M) hM hM2 hσ hD hroot2 hroot2 hw2
    hwroot le_rfl rfl rfl rfl hK hlocal
  have hmain := Sigma11FiniteLayerMajorization_even_endpoint hM hM2 hσ
  have hprime := h87.trans (add_le_add hmain le_rfl)
  have hscale := mul_le_mul_of_nonneg_left hprime (suzukiVProduct_pos S z).le
  unfold CaseIEvenEndpointSigma11Edge
  rw [sigmaEleven_eq_lemmaEightSevenPrimeSum_natCeil
    S 2 σ 2 w v r M D z rfl rfl le_rfl rfl]
  change suzukiVProduct S z *
      suzukiLemmaEightSevenPrimeSum S (D : ℝ) w v r
        (fun t => finiteSourceLayer 1 2 (M - 1) (t - 1)) ≤ _
  simpa only [w, z, r, mul_add, mul_assoc] using hscale


end MathlibNt.SieveTheory
