import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerProp93
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

open scoped Classical BigOperators Interval
open Filter Finset MeasureTheory Set Topology

namespace MathlibNt.SieveTheory

open SuzukiFiniteContinuousLayers

set_option autoImplicit false
set_option maxHeartbeats 800000

private def finiteSourceRecursionIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun n => n % 2 = N % 2)

private lemma finiteSourceRecursionIntegrand_eq
    (β : ℝ) (N : ℕ) (t : ℝ) :
    (∑ n ∈ finiteSourceRecursionIndices N,
      suzukiLayer 1 β (n - 1) (t - 1)) =
      finiteSourceLayer 1 β (N - 1) (t - 1) := by
  classical
  unfold finiteSourceRecursionIndices finiteSourceLayer
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun m _ => m + 1)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    constructor <;> omega
  · intro a ha b hb hab
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨n - 1, by omega, by omega⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    congr 1

private lemma shifted_predecessor_continuousOn
    {n : ℕ} (hn : 2 ≤ n) {x B : ℝ}
    (hx : 2 + ((n % 2 : ℕ) : ℝ) ≤ x) :
    ContinuousOn (fun t => suzukiLayer 1 2 (n - 1) (t - 1)) (Icc x B) := by
  have hc : ContinuousOn (suzukiLayer 1 2 (n - 1))
      (KappaOneModel.closedDomain 2 (n - 1)) := by
    apply (KappaOneModel.regular (by norm_num : (1 : ℝ) < 2) (n - 1)).continuous.congr
    intro s hs
    exact (KappaOneModel.layer_eq_suzukiLayer 2 (n - 1) s).symm
  apply hc.comp (continuous_id.sub continuous_const).continuousOn
  intro t ht
  rcases ht with ⟨hxt, htB⟩
  unfold KappaOneModel.closedDomain KappaOneModel.eps
  simp only [Set.mem_Ici]
  have hmod : (n - 1) % 2 = 1 - n % 2 := by omega
  rw [hmod]
  have hnmod : n % 2 ≤ 1 := by omega
  have hsumNat : n % 2 + (1 - n % 2) = 1 := by omega
  have hsum : ((n % 2 : ℕ) : ℝ) + ((1 - n % 2 : ℕ) : ℝ) = 1 := by
    exact_mod_cast hsumNat
  change 2 - ((1 - n % 2 : ℕ) : ℝ) ≤ t - 1
  linarith

private lemma shifted_predecessor_zero
    {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : 2 + (n : ℝ) ≤ t) :
    suzukiLayer 1 2 (n - 1) (t - 1) = 0 := by
  apply suzukiLayer_eq_zero_of_le
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  rw [hcast]
  linarith

private lemma suzukiLayerNumerator_eq_sourceRecursion_of_two_le
    (β s : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    suzukiLayerNumerator 1 β n s =
      ∫ t in recursionLower β s n..(β + n),
        suzukiLayer 1 β (n - 1) (t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simpa [dPowDensity, Nat.cast_add, Nat.cast_ofNat] using
    suzukiLayerNumerator_succ_succ (1 : ℝ) β s k

private lemma compact_tail_integral
    {f : ℝ → ℝ} {x B : ℝ}
    (hcont : ContinuousOn f (Icc x B))
    (hzero : ∀ t, B ≤ t → f t = 0) :
    IntegrableOn f (Ioi x) ∧
      (∫ t in Ioi x, f t) = ∫ t in min x B..B, f t := by
  by_cases hxb : x ≤ B
  · have hIcc : IntegrableOn f (Icc x B) := hcont.integrableOn_Icc
    have hIoc : IntegrableOn f (Ioc x B) :=
      hIcc.mono_set Ioc_subset_Icc_self
    have heq : (Ioi x).indicator f = (Ioc x B).indicator f := by
      funext t
      by_cases hxt : x < t
      · by_cases htB : t ≤ B
        · simp [Set.indicator, hxt, htB]
        · have hz : f t = 0 := hzero t (le_of_not_ge htB)
          simp [Set.indicator, hxt, htB, hz]
      · simp [Set.indicator, hxt]
    have hInd : Integrable ((Ioi x).indicator f) :=
      (hIoc.integrable_indicator measurableSet_Ioc).congr
        (Filter.Eventually.of_forall fun t => congrFun heq.symm t)
    refine ⟨(integrable_indicator_iff measurableSet_Ioi).mp hInd, ?_⟩
    rw [min_eq_left hxb, intervalIntegral.integral_of_le hxb,
      ← integral_indicator measurableSet_Ioi,
      ← integral_indicator measurableSet_Ioc, heq]
  · have hBx : B ≤ x := le_of_not_ge hxb
    have hzIoi : EqOn f 0 (Ioi x) := by
      intro t ht
      exact hzero t (hBx.trans ht.le)
    have hInt : IntegrableOn f (Ioi x) :=
      (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi x)).congr_fun
        (fun t ht => (hzIoi ht).symm) measurableSet_Ioi
    refine ⟨hInt, ?_⟩
    rw [min_eq_right hBx, intervalIntegral.integral_same]
    exact integral_eq_zero_of_ae (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hzIoi ht)

private lemma suzukiLayer_finite_tail
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ}
    (hx : 2 + ((n % 2 : ℕ) : ℝ) ≤ x) :
    IntegrableOn (fun t => suzukiLayer 1 2 (n - 1) (t - 1)) (Ioi x) ∧
      x * suzukiLayer 1 2 n x =
        ∫ t in Ioi x, suzukiLayer 1 2 (n - 1) (t - 1) := by
  let B : ℝ := 2 + (n : ℝ)
  have hcompact := compact_tail_integral
    (shifted_predecessor_continuousOn hn (B := B) hx)
    (fun t ht => shifted_predecessor_zero hn ht)
  refine ⟨hcompact.1, ?_⟩
  have hxpos : 0 < x := by
    have : (0 : ℝ) ≤ ((n % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have hlower : recursionLower 2 x n = min x B := by
    unfold recursionLower B sourceEpsilon
    have hepsNat : n % 2 ≤ 1 :=
      Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num : 0 < 2))
    have heps : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hepsNat
    have hmax : max x (2 + (n % 2 : ℕ)) = x := by
      apply max_eq_left
      linarith
    rw [hmax]
  rw [suzukiLayer_eq_inv_rpow_mul_numerator,
    show x ^ (1 : ℝ) = x by norm_num,
    ← mul_assoc, mul_inv_cancel₀ hxpos.ne', one_mul]
  rw [suzukiLayerNumerator_eq_sourceRecursion_of_two_le 2 x hn, hlower]
  exact hcompact.2.symm

private lemma finiteSourceLayer_eq_recursion_sum
    {N : ℕ} {x : ℝ}
    (hx : 2 + ((N % 2 : ℕ) : ℝ) ≤ x) :
    finiteSourceLayer 1 2 N x =
      ∑ n ∈ finiteSourceRecursionIndices N, suzukiLayer 1 2 n x := by
  classical
  unfold finiteSourceLayer finiteSourceRecursionIndices
  symm
  conv_rhs => rw [← Finset.sum_filter]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
  · intro n hn hnsmall
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : n = 1 := by
      have : ¬ 2 ≤ n := by
        intro h2
        apply hnsmall
        simp only [Finset.mem_filter, Finset.mem_Icc]
        exact ⟨⟨h2, hn.1.2⟩, hn.2⟩
      omega
    subst n
    apply suzukiLayer_eq_zero_of_le
    have hNodd : N % 2 = 1 := by omega
    rw [hNodd] at hx
    norm_num at hx
    norm_num
    linarith

/-- The finite-tail identity at the exact lower threshold used by the recursive
numerator: `2` on even layers and `3` on odd layers.

The weaker hypothesis `x ∈ parityDomain 2 N` is sufficient on the even branch,
but not on the odd branch: there it only says `1 < x`, while the recursive
lower endpoint remains clamped at `3`. -/
theorem Lemma132FiniteTailIdentity_exactRecursionThreshold :
    ∀ (N : ℕ) (x : ℝ), 2 ≤ N →
      2 + ((N % 2 : ℕ) : ℝ) ≤ x →
      IntegrableOn (fun t => finiteSourceLayer 1 2 (N - 1) (t - 1)) (Ioi x) ∧
      x * finiteSourceLayer 1 2 N x =
        ∫ t in Ioi x, finiteSourceLayer 1 2 (N - 1) (t - 1) := by
  intro N x _hN hx
  let S := finiteSourceRecursionIndices N
  have hterm : ∀ n ∈ S,
      IntegrableOn (fun t => suzukiLayer 1 2 (n - 1) (t - 1)) (Ioi x) ∧
        x * suzukiLayer 1 2 n x =
          ∫ t in Ioi x, suzukiLayer 1 2 (n - 1) (t - 1) := by
    intro n hn
    have hmem := Finset.mem_filter.mp hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hmem.1).1
    have hnpar : n % 2 = N % 2 := hmem.2
    apply suzukiLayer_finite_tail hn2
    rw [hnpar]
    exact hx
  have hsumInt : IntegrableOn
      (fun t => ∑ n ∈ S, suzukiLayer 1 2 (n - 1) (t - 1)) (Ioi x) := by
    classical
    have hsumInt' : IntegrableOn
        (∑ n ∈ S, fun t => suzukiLayer 1 2 (n - 1) (t - 1)) (Ioi x) := by
      apply Finset.sum_induction (s := S)
          (fun n t => suzukiLayer 1 2 (n - 1) (t - 1))
          (fun f => IntegrableOn f (Ioi x) volume)
      · intro f g hf hg
        exact hf.add hg
      · exact integrableOn_zero
      · intro n hn
        exact (hterm n hn).1
    apply hsumInt'.congr_fun_ae
    filter_upwards [] with t
    simp
  have hfun : (fun t => ∑ n ∈ S, suzukiLayer 1 2 (n - 1) (t - 1)) =
      (fun t => finiteSourceLayer 1 2 (N - 1) (t - 1)) := by
    funext t
    exact finiteSourceRecursionIntegrand_eq 2 N t
  have htargetInt : IntegrableOn
      (fun t => finiteSourceLayer 1 2 (N - 1) (t - 1)) (Ioi x) := by
    rwa [← hfun]
  refine ⟨htargetInt, ?_⟩
  rw [finiteSourceLayer_eq_recursion_sum hx, Finset.mul_sum]
  calc
    (∑ n ∈ S, x * suzukiLayer 1 2 n x) =
        ∑ n ∈ S, ∫ t in Ioi x, suzukiLayer 1 2 (n - 1) (t - 1) := by
          apply Finset.sum_congr rfl
          intro n hn
          exact (hterm n hn).2
    _ = ∫ t in Ioi x, ∑ n ∈ S, suzukiLayer 1 2 (n - 1) (t - 1) := by
          symm
          exact integral_finsetSum S (fun n hn => (hterm n hn).1)
    _ = ∫ t in Ioi x, finiteSourceLayer 1 2 (N - 1) (t - 1) := by
          apply integral_congr_ae
          filter_upwards [] with t
          exact finiteSourceRecursionIntegrand_eq 2 N t

/-- On the even parity branch, Suzuki's exact parity-domain lower endpoint is
already the exact recursion threshold. -/
theorem Lemma132FiniteTailIdentity_even_parityDomain
    (N : ℕ) (x : ℝ) (hN : 2 ≤ N) (hEven : N % 2 = 0)
    (hx : x ∈ KappaOneModel.parityDomain 2 N) :
    IntegrableOn (fun t => finiteSourceLayer 1 2 (N - 1) (t - 1)) (Ioi x) ∧
      x * finiteSourceLayer 1 2 N x =
        ∫ t in Ioi x, finiteSourceLayer 1 2 (N - 1) (t - 1) := by
  apply Lemma132FiniteTailIdentity_exactRecursionThreshold N x hN
  unfold KappaOneModel.parityDomain at hx
  rw [hEven] at hx ⊢
  norm_num at hx ⊢
  exact hx


end MathlibNt.SieveTheory
