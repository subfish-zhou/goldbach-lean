import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteSourceLayerLemma86
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiLemma87DimensionOne

open scoped Classical BigOperators
open MeasureTheory Set

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open SuzukiFiniteContinuousLayers

set_option maxHeartbeats 800000

/-- Global continuous extension of `t ↦ T_M(t-1)`, clamped at the left
source coordinate `τ-1`. -/
noncomputable def finiteSourceLayerShiftClamp
    (β : ℝ) (M : ℕ) (τ : ℝ) (t : ℝ) : ℝ :=
  finiteSourceLayerOneClamp β M (τ - 1) (t - 1)

@[simp] theorem finiteSourceLayerShiftClamp_eq_of_le
    (β : ℝ) (M : ℕ) {τ t : ℝ} (hτt : τ ≤ t) :
    finiteSourceLayerShiftClamp β M τ t = finiteSourceLayer 1 β M (t - 1) := by
  unfold finiteSourceLayerShiftClamp
  rw [finiteSourceLayerOneClamp_eq_of_le β M (by linarith)]

private theorem shifted_parityDomain_mono
    {β x y : ℝ} {M : ℕ}
    (hx : x - 1 ∈ suzukiParityDomainOne β M) (hxy : x ≤ y) :
    y - 1 ∈ suzukiParityDomainOne β M := by
  by_cases hpar : M % 2 = 1
  · simp only [suzukiParityDomainOne, KappaOneModel.parityDomain, hpar,
      if_true, Set.mem_Ioi] at hx ⊢
    linarith
  · simp only [suzukiParityDomainOne, KappaOneModel.parityDomain, hpar,
      if_false, Set.mem_Ici] at hx ⊢
    linarith

/-- The shifted clamp supplies exactly the global continuity, nonnegativity,
and `t H(t)` antitonicity required by Lemma 8.7. -/
theorem finiteSourceLayerShiftClamp_lemmaEightSeven_conditions
    {β τ σ : ℝ} (hβ : 1 < β) (M : ℕ)
    (hτdom : τ - 1 ∈ suzukiParityDomainOne β M) (_hτσ : τ ≤ σ) :
    Continuous (finiteSourceLayerShiftClamp β M τ) ∧
      (∀ t ∈ Set.Icc τ σ, 0 ≤ finiteSourceLayerShiftClamp β M τ t) ∧
      AntitoneOn (fun t => finiteSourceLayerShiftClamp β M τ t * t)
        (Set.Icc τ σ) := by
  have hcont0 := finiteSourceLayerOneClamp_continuous hβ M hτdom
  have hcont : Continuous (finiteSourceLayerShiftClamp β M τ) := by
    unfold finiteSourceLayerShiftClamp
    exact hcont0.comp (continuous_id.sub continuous_const)
  refine ⟨hcont, ?_, ?_⟩
  · intro t ht
    rw [finiteSourceLayerShiftClamp_eq_of_le β M ht.1]
    exact finiteSourceLayer_nonneg_on_parityDomain hβ M
      (shifted_parityDomain_mono hτdom ht.1)
  · intro x hx y hy hxy
    change finiteSourceLayerShiftClamp β M τ y * y ≤
      finiteSourceLayerShiftClamp β M τ x * x
    rw [finiteSourceLayerShiftClamp_eq_of_le β M hx.1,
      finiteSourceLayerShiftClamp_eq_of_le β M hy.1]
    have hxdom := shifted_parityDomain_mono hτdom hx.1
    have hydom := shifted_parityDomain_mono hτdom hy.1
    have hw := finiteSourceLayer_weighted_antitoneOn_parityDomain hβ M
      hxdom hydom (by linarith : x - 1 ≤ y - 1)
    have hu := finiteSourceLayer_antitoneOn_parityDomain hβ M
      hxdom hydom (by linarith : x - 1 ≤ y - 1)
    nlinarith

/-- Lemma 8.7 instantiated with Suzuki's preceding finite source layer
`H(t)=T_{N-1}(t-1)`.  The only extra analytic device is the global clamp,
which disappears from the prime sum, integral, and endpoint value. -/
theorem suzukiLemmaEightSeven_finiteSourceLayer_shift
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hτdom : τ - 1 ∈ suzukiParityDomainOne β (N - 1))
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
  let H : ℝ → ℝ := finiteSourceLayerShiftClamp β (N - 1) τ
  obtain ⟨hcont, hnonneg, hanti⟩ :=
    finiteSourceLayerShiftClamp_lemmaEightSeven_conditions hβ (N - 1) hτdom hτσ
  have h87 := suzukiLemmaEightSevenDimensionOne hD hz2 hv2 hw2 hwv hvz
    hz hv hw hcont hnonneg hanti hK hlocal
  have hτpos : 0 < τ := by
    have hprevpos : 0 < τ - 1 :=
      KappaOneModel.closedDomain_pos hβ
        (KappaOneModel.parityDomain_subset_closedDomain β (N - 1) hτdom)
    linarith
  have hcoord : ∀ x ∈ Set.Icc w v,
      Real.log D / Real.log x ∈ Set.Icc τ σ := by
    intro x hx
    exact SuzukiPowerCoordinates.log_div_log_mem_Icc hD hτpos hτσ hv hw hx
  have hprime : suzukiLemmaEightSevenPrimeSum S D w v z H =
      suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) := by
    unfold suzukiLemmaEightSevenPrimeSum
    apply Finset.sum_congr rfl
    intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have ht := hcoord (p : ℝ) ⟨hp'.1, hp'.2.le⟩
    rw [show H (Real.log D / Real.log p) =
        finiteSourceLayer 1 β (N - 1) (Real.log D / Real.log p - 1) by
      exact finiteSourceLayerShiftClamp_eq_of_le β (N - 1) ht.1]
  have hint : (∫ t in τ..σ, H t) =
      ∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1) := by
    apply intervalIntegral.integral_congr
    rw [Set.uIcc_of_le hτσ]
    intro t ht
    exact finiteSourceLayerShiftClamp_eq_of_le β (N - 1) ht.1
  rw [hprime, hint,
    finiteSourceLayerShiftClamp_eq_of_le β (N - 1) le_rfl] at h87
  exact h87

/-- Source indices whose `(9.2)` predecessors comprise `T_{N-1}`. -/
def finiteSourceRecursionIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 2 N).filter (fun n => n % 2 = N % 2)

/-- The sum of the normalized predecessor integrands appearing in `(9.2)` for
all source indices selected by `T_N`. -/
noncomputable def finiteSourceRecursionIntegrand
    (β : ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ n ∈ finiteSourceRecursionIndices N, suzukiLayer 1 β (n - 1) (t - 1)

/-- Exact index shift: the `(9.2)` recursion integrand for the `T_N` source
indices is precisely `T_{N-1}(t-1)`. -/
theorem finiteSourceRecursionIntegrand_eq
    (β : ℝ) (N : ℕ) (t : ℝ) :
    finiteSourceRecursionIntegrand β N t =
      finiteSourceLayer 1 β (N - 1) (t - 1) := by
  classical
  unfold finiteSourceRecursionIntegrand finiteSourceRecursionIndices
    finiteSourceLayer
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun m _ => m + 1)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    constructor
    · omega
    · omega
  · intro a ha b hb hab
    omega
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    refine ⟨n - 1, ?_, ?_⟩
    · constructor <;> omega
    · omega
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm
    congr 1

/-- The main integral in the specialized Lemma 8.7 is exactly the aggregate
continuous-recursion increment: every summand is one predecessor integrand from
source equation `(9.2)`. -/
theorem integral_finiteSourceLayer_shift_eq_recursionIntegrand
    (β : ℝ) (N : ℕ) (τ σ : ℝ) :
    (∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1)) =
      ∫ t in τ..σ, finiteSourceRecursionIntegrand β N t := by
  apply intervalIntegral.integral_congr
  intro t _
  exact (finiteSourceRecursionIntegrand_eq β N t).symm

/-- Each term selected in the aggregate recursion integrand is literally the
normalized predecessor occurring on the right side of source equation `(9.2)`. -/
theorem suzukiLayerNumerator_eq_sourceRecursion_of_two_le
    (β s : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    suzukiLayerNumerator 1 β n s =
      ∫ t in recursionLower β s n..(β + n),
        suzukiLayer 1 β (n - 1) (t - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := by
    exact ⟨n - 2, by omega⟩
  simpa [dPowDensity, Nat.cast_add, Nat.cast_ofNat] using
    suzukiLayerNumerator_succ_succ (1 : ℝ) β s k

/-- Lemma 8.7 with its main term rewritten as the aggregate `(9.2)` recursion
increment for the source indices of `T_N`. -/
theorem suzukiLemmaEightSeven_finiteSourceLayer_recursionIncrement
    {S : BoundingSieve} {D z v w s τ σ K β : ℝ} {N : ℕ}
    (hβ : 1 < β)
    (hτdom : τ - 1 ∈ suzukiParityDomainOne β (N - 1))
    (hτσ : τ ≤ σ)
    (hD : 1 < D) (hz2 : 2 ≤ z) (hv2 : 2 ≤ v) (hw2 : 2 ≤ w)
    (hwv : w ≤ v) (hvz : v ≤ z)
    (hz : z = D ^ (1 / s)) (hv : v = D ^ (1 / τ))
    (hw : w = D ^ (1 / σ))
    (hK : 2 ≤ K) (hlocal : HasDimensionOneLocalProductBound S K) :
    suzukiLemmaEightSevenPrimeSum S D w v z
        (fun t => finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      (1 / s) * (∫ t in τ..σ, finiteSourceRecursionIntegrand β N t) +
        (6 * K ^ 2 * finiteSourceLayer 1 β (N - 1) (τ - 1) /
          Real.log w) * (τ / s) := by
  have h := suzukiLemmaEightSeven_finiteSourceLayer_shift hβ hτdom hτσ
    hD hz2 hv2 hw2 hwv hvz hz hv hw hK hlocal
  rwa [integral_finiteSourceLayer_shift_eq_recursionIntegrand] at h


private theorem one_step
    {β s τ σ : ℝ} {n : ℕ} (hβ : 1 < β) (hn : 2 ≤ n)
    (hsdom : s ∈ KappaOneModel.parityDomain β n)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (n - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ) :
    (1 / s) * (∫ t in τ..σ, suzukiLayer 1 β (n - 1) (t - 1)) ≤
      suzukiLayer 1 β n s := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  let f : ℝ → ℝ := fun t => suzukiLayer 1 β (k + 1) (t - 1)
  let a : ℝ := recursionLower β s (k + 2)
  let b : ℝ := β + (k + 2 : ℕ)
  have hspos : 0 < s := KappaOneModel.closedDomain_pos hβ
    (KappaOneModel.parityDomain_subset_closedDomain β (k + 2) hsdom)
  have hpred : k + 2 - 1 = k + 1 := by omega
  rw [hpred] at hτdom
  have hthreshold : β + KappaOneModel.eps (k + 2) ≤ τ := by
    unfold KappaOneModel.parityDomain at hτdom
    by_cases hp : (k + 2) % 2 = 1
    · have hprev : (k + 1) % 2 = 0 := by omega
      simp [hprev] at hτdom
      simp [KappaOneModel.eps, hp]
      linarith
    · have hp0 : (k + 2) % 2 = 0 := by omega
      have hprev : (k + 1) % 2 = 1 := by omega
      simp [hprev] at hτdom
      simp [KappaOneModel.eps, hp0]
      linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    exact (KappaOneModel.lower_mem β s (k + 2)).2
  have hthra : β + KappaOneModel.eps (k + 2) ≤ a := by
    dsimp [a]
    exact (KappaOneModel.lower_mem β s (k + 2)).1
  have haτ : a ≤ τ := by
    dsimp [a]
    calc
      recursionLower β s (k + 2) ≤ max s (β + KappaOneModel.eps (k + 2)) :=
        min_le_left _ _
      _ ≤ τ := max_le hsτ hthreshold
  have hmodelcont : ContinuousOn
      (fun t : ℝ => KappaOneModel.layer β (k + 1) (t - 1))
      (Set.Icc a (max b σ)) := by
    apply (KappaOneModel.regular hβ (k + 1)).continuous.comp
      (continuous_id.sub continuous_const).continuousOn
    intro t ht
    exact KappaOneModel.shifted_mem_previous (hthra.trans ht.1)
  have hfcont : ContinuousOn f (Set.Icc a (max b σ)) := by
    apply hmodelcont.congr
    intro t ht
    exact (KappaOneModel.layer_eq_suzukiLayer β (k + 1) (t - 1)).symm
  have hfnonneg : ∀ t ∈ Set.Icc a (max b σ), 0 ≤ f t := by
    intro t ht
    rw [show f t = KappaOneModel.layer β (k + 1) (t - 1) by
      exact (KappaOneModel.layer_eq_suzukiLayer β (k + 1) (t - 1)).symm]
    exact (KappaOneModel.regular hβ (k + 1)).nonneg _
      (KappaOneModel.shifted_mem_previous (hthra.trans ht.1))
  have hfullint : IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hab]
    exact hfcont.mono (Set.Icc_subset_Icc_right (le_max_left _ _))
  have hrhs_nonneg : 0 ≤ suzukiLayer 1 β (k + 2) s := by
    rw [← KappaOneModel.layer_eq_suzukiLayer]
    exact KappaOneModel.nonneg_on_parityDomain hβ (k + 2) s hsdom
  by_cases hτb : τ ≤ b
  · have hmain : (∫ t in τ..σ, f t) ≤ ∫ t in a..b, f t := by
      by_cases hσb : σ ≤ b
      · apply intervalIntegral.integral_mono_interval haτ hτσ hσb
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
          apply hfnonneg t
          exact ⟨ht.1.le, ht.2.trans (le_max_left _ _)⟩
        · exact hfullint
      · have hbσ : b ≤ σ := le_of_not_ge hσb
        have hτb_int : IntervalIntegrable f MeasureTheory.volume τ b := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hτb]
          exact hfcont.mono (by
            intro t ht
            exact ⟨haτ.trans ht.1, ht.2.trans (le_max_left _ _)⟩)
        have hbσ_int : IntervalIntegrable f MeasureTheory.volume b σ := by
          apply ContinuousOn.intervalIntegrable
          rw [Set.uIcc_of_le hbσ]
          exact hfcont.mono (by
            intro t ht
            exact ⟨hab.trans ht.1, ht.2.trans (le_max_right _ _)⟩)
        have hsuffix : (∫ t in b..σ, f t) = 0 := by
          calc
            (∫ t in b..σ, f t) = ∫ _t in b..σ, (0 : ℝ) := by
              apply intervalIntegral.integral_congr
              rw [Set.uIcc_of_le hbσ]
              intro t ht
              dsimp [f, b]
              apply suzukiLayer_eq_zero_of_le
              have hcast : ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by
                push_cast
                ring
              dsimp [b] at ht
              rw [hcast] at ht
              linarith [ht.1]
            _ = 0 := intervalIntegral.integral_zero
        rw [← intervalIntegral.integral_add_adjacent_intervals hτb_int hbσ_int,
          hsuffix, add_zero]
        apply intervalIntegral.integral_mono_interval haτ hτb le_rfl
        · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
          apply hfnonneg t
          exact ⟨ht.1.le, ht.2.trans (le_max_left _ _)⟩
        · exact hfullint
    have hraw : (∫ t in τ..σ, f t) ≤ suzukiLayerNumerator 1 β (k + 2) s := by
      calc
        (∫ t in τ..σ, f t) ≤ ∫ t in a..b, f t := hmain
        _ = suzukiLayerNumerator 1 β (k + 2) s := by
          symm
          simpa [a, b, f] using
            suzukiLayerNumerator_eq_sourceRecursion_of_two_le β s (by omega : 2 ≤ k + 2)
    have hscale := mul_le_mul_of_nonneg_left hraw (by positivity : 0 ≤ 1 / s)
    rw [← rpow_mul_suzukiLayer 1 β (k + 2) hspos] at hscale
    simpa [f, one_div, hspos.ne'] using hscale
  · have hbτ : b ≤ τ := le_of_not_ge hτb
    have hzero : (∫ t in τ..σ, f t) = 0 := by
      calc
        (∫ t in τ..σ, f t) = ∫ _t in τ..σ, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          rw [Set.uIcc_of_le hτσ]
          intro t ht
          dsimp [f, b] at hbτ ⊢
          apply suzukiLayer_eq_zero_of_le
          have hcast : ((k + 2 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ) + 1 := by
            push_cast
            ring
          rw [hcast] at hbτ
          linarith [ht.1]
        _ = 0 := intervalIntegral.integral_zero
    rw [hpred]
    rw [show (∫ t in τ..σ, suzukiLayer 1 β (k + 1) (t - 1)) = 0 by
      simpa [f] using hzero, mul_zero]
    exact hrhs_nonneg

private theorem parityDomain_upperClosed {β : ℝ} {m : ℕ} :
    ∀ {x y : ℝ}, x ∈ KappaOneModel.parityDomain β m → x ≤ y →
      y ∈ KappaOneModel.parityDomain β m := by
  intro x y hx hxy
  by_cases hpar : m % 2 = 1
  · simp [KappaOneModel.parityDomain, hpar] at hx ⊢
    exact hx.trans_le hxy
  · simp [KappaOneModel.parityDomain, hpar] at hx ⊢
    exact hx.trans hxy

/-- The truncated middle-range recursion integral is bounded by the full finite
source layer.  Equality need not hold when the lower endpoint is larger than
`s` or when the upper endpoint truncates source support. -/
theorem Sigma11FiniteLayerMajorization
    {β s τ σ : ℝ} {N : ℕ} (hβ : 1 < β)
    (hsdom : s ∈ KappaOneModel.parityDomain β N)
    (hτdom : τ - 1 ∈ KappaOneModel.parityDomain β (N - 1))
    (hsτ : s ≤ τ) (hτσ : τ ≤ σ) :
    (1 / s) *
        (∫ t in τ..σ, finiteSourceLayer 1 β (N - 1) (t - 1)) ≤
      finiteSourceLayer 1 β N s := by
  classical
  rw [integral_finiteSourceLayer_shift_eq_recursionIntegrand]
  unfold finiteSourceRecursionIntegrand
  have hint : ∀ n ∈ finiteSourceRecursionIndices N,
      IntervalIntegrable (fun t => suzukiLayer 1 β (n - 1) (t - 1))
        MeasureTheory.volume τ σ := by
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn'.1).1
    have hnN : n ≤ N := (Finset.mem_Icc.mp hn'.1).2
    have hpredpar : (n - 1) % 2 = (N - 1) % 2 := by omega
    have hdom : τ - 1 ∈ KappaOneModel.parityDomain β (n - 1) := by
      simpa [KappaOneModel.parityDomain, hpredpar] using hτdom
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hτσ]
    apply (suzukiLayer_one_continuousOn_parityDomain hβ (n - 1)).comp
      (continuous_id.sub continuous_const).continuousOn
    intro t ht
    have hm := parityDomain_upperClosed hdom (sub_le_sub_right ht.1 1)
    simpa using hm
  rw [intervalIntegral.integral_finset_sum hint, Finset.mul_sum]
  calc
    (∑ n ∈ finiteSourceRecursionIndices N,
        (1 / s) * ∫ t in τ..σ, suzukiLayer 1 β (n - 1) (t - 1)) ≤
        ∑ n ∈ finiteSourceRecursionIndices N, suzukiLayer 1 β n s := by
      apply Finset.sum_le_sum
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnmem := Finset.mem_Icc.mp hn'.1
      have hnpar : n % 2 = N % 2 := hn'.2
      have hpredpar : (n - 1) % 2 = (N - 1) % 2 := by omega
      apply one_step hβ hnmem.1
      · simpa [KappaOneModel.parityDomain, hnpar] using hsdom
      · simpa [KappaOneModel.parityDomain, hpredpar] using hτdom
      · exact hsτ
      · exact hτσ
    _ ≤ finiteSourceLayer 1 β N s := by
      unfold finiteSourceRecursionIndices finiteSourceLayer
      rw [← Finset.sum_filter]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        exact ⟨⟨by omega, hn.1.2⟩, hn.2⟩
      · intro n hn hnnot
        have hn' := Finset.mem_filter.mp hn
        have hndom : s ∈ KappaOneModel.parityDomain β n := by
          simpa [KappaOneModel.parityDomain, hn'.2] using hsdom
        rw [← KappaOneModel.layer_eq_suzukiLayer]
        exact KappaOneModel.nonneg_on_parityDomain hβ n s hndom


end MathlibNt.SieveTheory.SwitchingPrinciple
