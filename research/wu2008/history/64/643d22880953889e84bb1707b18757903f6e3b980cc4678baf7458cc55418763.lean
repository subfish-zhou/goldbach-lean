import MathlibNt.Wu2008DoubleSieve.CoefficientRecurrence
import MathlibNt.Wu2008DoubleSieve.ImprovementThresholdIntegrals
import MathlibNt.Wu2008DoubleSieve.BoxMassPNT
import MathlibNt.SieveTheory.Switching.SuzukiPrimeSums

/-!
# A finite PNT quadrature for the actual effective coefficients

Summation by parts uses finite variation, not continuity of the coefficient.
The PNT constant and threshold precede every weight, hence also every choice
of the finite-threshold improvement functions. The exact `p - 2` kernel is
retained. The quadrature is a genuine predecessor, not yet the final `/ t`
integral estimate: its remaining variation and quadrature errors must be paid.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory
open scoped Classical Topology Interval
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.JurkatRichert1965ChenGammaOneQOne

noncomputable def wuEffectiveCoefficient (upper : Bool) (k : ℕ) (δ : ℝ)
    (N0 : ℕ) (t : ℝ) : ℝ :=
  if upper then wuUpperCoefficient t - wuImprovementAt upper k δ t N0
  else wuLowerCoefficient t + wuImprovementAt upper k δ t N0

theorem wuEffectiveCoefficient_uniform_monotone_bound (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N0 : ℕ in atTop,
      MonotoneOn (wuEffectiveCoefficient upper k δ N0) (Icc 1 10) ∧
      ∀ t ∈ Icc (1 : ℝ) 10, |wuEffectiveCoefficient upper k δ N0 t| ≤ 110 := by
  filter_upwards [wu_effective_threshold_uniform_monotone upper k hk hδ hδhi,
    wuImprovementAt_uniform_div_norm_bound upper k hk hδ hδhi] with N0 hm hb
  refine ⟨hm, ?_⟩
  intro t ht
  have ht0 : 0 < t := by linarith [ht.1]
  have hI : |wuImprovementAt upper k δ t N0| ≤ 100 := by
    have h := hb t ht.1 ht.2
    rw [Real.norm_eq_abs, abs_div, abs_of_pos ht0] at h
    have := (div_le_iff₀ ht0).mp h
    linarith [ht.2]
  have hA0 : 0 ≤ wuUpperCoefficient t :=
    div_nonneg (mul_nonneg ht0.le
      ((jr1965f_nonneg ht0).trans (jr1965f_lt_jr1965F ht0).le)) (by positivity)
  have hA : wuUpperCoefficient t ≤ 10 := by
    unfold wuUpperCoefficient
    apply (div_le_iff₀ (by positivity : 0 < 2 * exp eulerMascheroniConstant)).2
    have hf := mul_le_mul_of_nonneg_left (jr1965F_le_delayConstant ht.1) ht0.le
    unfold jr1965DelayConstant at hf
    nlinarith [exp_pos eulerMascheroniConstant, ht.2]
  have ha0 : 0 ≤ wuLowerCoefficient t :=
    div_nonneg (mul_nonneg ht0.le (jr1965f_nonneg ht0)) (by positivity)
  have ha : wuLowerCoefficient t ≤ 10 := by
    apply le_trans _ hA
    unfold wuLowerCoefficient wuUpperCoefficient
    gcongr
    exact (jr1965f_lt_jr1965F ht0).le
  cases upper
  · exact (abs_add_le _ _).trans (by
      rw [abs_of_nonneg ha0]
      change wuLowerCoefficient t + |wuImprovementAt false k δ t N0| ≤ 110
      linarith)
  · exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg hA0]
      change wuUpperCoefficient t + |wuImprovementAt true k δ t N0| ≤ 110
      linarith)

theorem wuEffectiveCoefficient_intervalIntegral_bounds
    {f : ℝ → ℝ} (hf : MonotoneOn f (Icc 1 10))
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) (hb : b ≤ 10) :
    f a * (∫ t in a..b, 1 / t) ≤ (∫ t in a..b, f t / t) ∧
      (∫ t in a..b, f t / t) ≤ f b * (∫ t in a..b, 1 / t) := by
  have hs : uIcc a b ⊆ Icc (1 : ℝ) 10 := by
    rw [uIcc_of_le hab]
    exact Icc_subset_Icc ha hb
  have hi : IntervalIntegrable f volume a b := (hf.mono hs).intervalIntegrable
  have ht : ContinuousOn (fun t : ℝ => t⁻¹) (uIcc a b) := by
    apply continuousOn_id.inv₀
    intro t ht
    have := (hs ht).1
    change t ≠ 0
    linarith
  have hfi : IntervalIntegrable (fun t => f t / t) volume a b := by
    simpa only [div_eq_mul_inv] using hi.mul_continuousOn ht
  have hone : IntervalIntegrable (fun t : ℝ => 1 / t) volume a b := by
    simpa only [one_div] using ht.intervalIntegrable
  have hleft : f a * (∫ t in a..b, 1 / t) =
      ∫ t in a..b, f a / t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  have hright : f b * (∫ t in a..b, 1 / t) =
      ∫ t in a..b, f b / t := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [hleft, hright]
  constructor
  · apply intervalIntegral.integral_mono_on hab
      (by convert hone.const_mul (f a) using 1; ext t; ring) hfi
    intro t ht
    exact div_le_div_of_nonneg_right
      (hf ⟨ha, hab.trans hb⟩ ⟨ha.trans ht.1, ht.2.trans hb⟩ ht.1) (by linarith [ht.1])
  · apply intervalIntegral.integral_mono_on hab hfi
      (by convert hone.const_mul (f b) using 1; ext t; ring)
    intro t ht
    exact div_le_div_of_nonneg_right
      (hf ⟨ha.trans ht.1, ht.2.trans hb⟩ ⟨ha.trans hab, hb⟩ ht.2) (by linarith [ht.1])

noncomputable def wuPrimeCoefficientWeight (f : ℝ → ℝ) (q : ℝ) (p : ℕ) : ℝ :=
  f (log q / log p - 1) / (((p : ℝ) - 2) * (1 - log p / log q))

noncomputable def primeWeightVariation (w : ℕ → ℝ) (a b : ℕ) : ℝ :=
  |w (a + 1)| + |w (b + 1)| +
    ∑ n ∈ Finset.Ico (a + 1) (b + 1), |w (n + 1) - w n|

private theorem prefix_card_increment (n : ℕ) :
    ((boxPrimePrefix (n + 1)).card : ℝ) - (boxPrimePrefix n).card =
      if (n + 1).Prime then 1 else 0 := by
  have hn : n + 1 ∉ boxPrimePrefix n := by
    simp only [mem_boxPrimePrefix]
    omega
  have he : boxPrimePrefix (n + 1) =
      if (n + 1).Prime then insert (n + 1) (boxPrimePrefix n) else boxPrimePrefix n := by
    ext p
    by_cases h : (n + 1).Prime
    · rw [if_pos h]
      simp only [Finset.mem_insert, mem_boxPrimePrefix]
      constructor
      · intro hp
        by_cases he : p = n + 1
        · exact Or.inl he
        · exact Or.inr ⟨hp.1, by omega⟩
      · rintro (rfl | hp)
        · exact ⟨h, le_rfl⟩
        · exact ⟨hp.1, by omega⟩
    · rw [if_neg h]
      simp only [mem_boxPrimePrefix]
      constructor
      · intro hp
        refine ⟨hp.1, ?_⟩
        by_contra hn'
        have he : p = n + 1 := by omega
        exact h (he ▸ hp.1)
      · intro hp
        exact ⟨hp.1, by omega⟩
  rw [he]
  split_ifs
  · rw [card_insert_of_notMem hn]
    push_cast
    ring
  · ring

private theorem abel_error_bound (e w : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b)
    {E : ℝ} (he : ∀ n ∈ Finset.Icc a b, |e n| ≤ E) :
    |∑ n ∈ Finset.Ico a b, (e (n + 1) - e n) * w (n + 1)| ≤
      E * primeWeightVariation w a b := by
  have h := MathlibNt.SieveTheory.SwitchingPrinciple.finiteAbelIdentity
    (fun n => -e n) (fun n => w (n + 1)) a b hab
  simp only [neg_sub_neg] at h
  rw [h]
  have hend :
      |(-e a) * w (a + 1) - (-e b) * w (b + 1)| ≤
        E * |w (a + 1)| + E * |w (b + 1)| := by
    apply (abs_sub _ _).trans
    simp only [abs_mul, abs_neg]
    exact add_le_add
      (mul_le_mul_of_nonneg_right (he a (mem_Icc.mpr ⟨le_rfl, hab⟩)) (abs_nonneg _))
      (mul_le_mul_of_nonneg_right (he b (mem_Icc.mpr ⟨hab, le_rfl⟩)) (abs_nonneg _))
  have hsum :
      |∑ n ∈ Finset.Ico (a + 1) (b + 1),
        (-e n) * (w (n + 1) - w (n - 1 + 1))| ≤
      E * ∑ n ∈ Finset.Ico (a + 1) (b + 1), |w (n + 1) - w n| := by
    apply (abs_sum_le_sum_abs _ _).trans
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    have hn' := mem_Ico.mp hn
    rw [Nat.sub_add_cancel (by omega : 1 ≤ n), abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_right (he n (mem_Icc.mpr ⟨by omega, by omega⟩))
      (abs_nonneg _)
  calc
    _ ≤ |(-e a) * w (a + 1) - (-e b) * w (b + 1)| +
        |∑ n ∈ Finset.Ico (a + 1) (b + 1),
          (-e n) * (w (n + 1) - w (n - 1 + 1))| := abs_add_le _ _
    _ ≤ _ := by
      unfold primeWeightVariation
      nlinarith [hend, hsum]

/-- Arbitrary-weight finite PNT quadrature. The analytic constants are
selected before *all* weights; no continuity or coefficient-dependent
prime-distribution threshold is used. The interval contains `a < p ≤ b`. -/
theorem primeWeight_trueLi_quadrature (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∀ a b : ℕ, 2 ≤ a → a ≤ b → b ≤ X → ∀ w : ℕ → ℝ,
        |(∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime), w (n + 1)) -
          ∑ n ∈ Finset.Ico a b,
            (logarithmicIntegral (n + 1) - logarithmicIntegral n) * w (n + 1)| ≤
          (C * (X : ℝ) / log X ^ A) * primeWeightVariation w a b := by
  obtain ⟨C, hC, X0, hPNT⟩ := boxPrimePrefix_trueLi A hA
  refine ⟨C, hC, X0, ?_⟩
  intro X hX a b ha hab hb w
  let e : ℕ → ℝ := fun n => (boxPrimePrefix n).card - logarithmicIntegral n
  have he : ∀ n ∈ Finset.Icc a b, |e n| ≤ C * (X : ℝ) / log X ^ A := by
    intro n hn
    exact hPNT X hX n (ha.trans (mem_Icc.mp hn).1) ((mem_Icc.mp hn).2.trans hb)
  have h := abel_error_bound e w hab he
  convert h using 1
  congr 1
  rw [sum_filter, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n _
  dsimp [e]
  have hn := prefix_card_increment n
  push_cast
  split_ifs with hp
  · rw [if_pos hp] at hn
    have := congrArg (fun x : ℝ => x * w (n + 1)) hn
    nlinarith only [this]
  · rw [if_neg hp] at hn
    have := congrArg (fun x : ℝ => x * w (n + 1)) hn
    nlinarith only [this]

end Wu2008DoubleSieve
