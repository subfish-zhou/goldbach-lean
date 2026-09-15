import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureTriple
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniformAbel

/-!
# Actual Buchstab weights satisfy the generic quadrature hypotheses

The installed off-corner fundamental theorem and bounded slope prove a
Lipschitz estimate across two. No global differentiability assertion is used.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

theorem primeOrdered_buchstab_lipschitz {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) :
    |buchstab u - buchstab v| ≤ |u - v| := by
  have hordered (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
      |buchstab b - buchstab a| ≤ |b - a| := by
    have hi : IntervalIntegrable buchstabSlope volume a b := by
      apply (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
      have hc : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Icc a b) := continuousOn_const
      apply hc.integrableOn_Icc.mono' measurable_buchstabSlope.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simpa only [Real.norm_eq_abs] using abs_buchstabSlope_le_one (ha.trans ht.1)
    have he := integral_eq_sub_of_hasDerivAt_off_one (c := 2) hab
      continuous_buchstab.continuousOn
      (fun t ht ht2 => hasDerivAt_buchstab_off_two (ha.trans_lt ht.1) ht2) hi
    rw [← he, ← Real.norm_eq_abs]
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1) (f := buchstabSlope) (fun t ht => by
        rw [Real.norm_eq_abs]
        exact abs_buchstabSlope_le_one (ha.trans (by
          rw [uIoc_of_le hab] at ht
          exact ht.1.le)))
    simpa only [one_mul] using hn
  rcases le_total u v with huv | hvu
  · simpa only [abs_sub_comm] using hordered u v hu huv
  · exact hordered v u hv hvu

private theorem div_small_lower {x b : ℝ} (hx : 0 ≤ x) (hb : 1 / 10 ≤ b) :
    x / b ≤ 10 * x := by
  apply (div_le_iff₀ (by linarith)).2
  nlinarith

private theorem quotient_difference {x y b d T : ℝ}
    (hb : 1 / 10 ≤ b) (hd : 1 / 10 ≤ d) (hy : |y| ≤ T) :
    |x / b - y / d| ≤ 10 * |x - y| + 100 * T * |b - d| := by
  have hb0 : 0 < b := by linarith
  have hd0 : 0 < d := by linarith
  have hT : 0 ≤ T := (abs_nonneg y).trans hy
  have he : x / b - y / d = (x - y) / b + y * (d - b) / (b * d) := by
    field_simp
    ring
  rw [he]
  have h₁ := div_small_lower (abs_nonneg (x - y)) hb
  have hprod : 1 / 100 ≤ b * d := by nlinarith
  have h₂ : |y| * |d - b| / (b * d) ≤ 100 * T * |b - d| := by
    rw [abs_sub_comm d b]
    apply (div_le_iff₀ (mul_pos hb0 hd0)).2
    have hyy := mul_le_mul_of_nonneg_right hy (abs_nonneg (b - d))
    have hh := mul_le_mul_of_nonneg_left hprod
      (show 0 ≤ 100 * T * |b - d| by positivity)
    nlinarith
  have hh := abs_add_le ((x - y) / b) (y * (d - b) / (b * d))
  rw [abs_div, abs_of_pos hb0, abs_div, abs_mul, abs_of_pos (mul_pos hb0 hd0)] at hh
  linarith only [h₁, h₂, hh]

noncomputable def primeOrderedBuchstabWeight (φ a b c : ℝ) : ℝ :=
  buchstab ((φ - a - b - c) / b) / b

private theorem argument_one {φ a b c : ℝ} (hφ : 2 ≤ φ)
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hc : c ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    1 ≤ (φ - a - b - c) / b := by
  apply (le_div_iff₀ (by linarith [hb.1])).2
  linarith [ha.2, hb.2, hc.2]

private theorem numerator_bound {φ P a b c : ℝ} (hφ : 2 ≤ φ) (hP : φ ≤ P)
    (ha : a ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hb : b ∈ Icc (1 / 10 : ℝ) (1 / 2))
    (hc : c ∈ Icc (1 / 10 : ℝ) (1 / 2)) :
    |φ - a - b - c| ≤ P := by
  rw [abs_of_nonneg (by linarith [ha.2, hb.2, hc.2])]
  linarith [ha.1, hb.1, hc.1]

private theorem buchstab_abs_le {u : ℝ} (hu : 1 ≤ u) : |buchstab u| ≤ 1 := by
  rw [abs_of_nonneg (buchstab_nonneg hu)]
  exact buchstab_le_one hu

/-- Uniform regularity of the actual source weight on the full exponent cube.
Only the parameter bound `2 <= phi <= P` is assumed, not source geometry. -/
theorem primeOrdered_buchstab_weight {P φ : ℝ} (hφ : 2 ≤ φ) (hP : φ ≤ P) :
    PrimeOrderedWeight 10 (1000 * P + 200) (primeOrderedBuchstabWeight φ) := by
  have hP0 : 0 ≤ P := by linarith
  constructor
  · intro a ha b hb c hc
    unfold primeOrderedBuchstabWeight
    rw [abs_div, abs_of_pos (by linarith [hb.1] : 0 < b)]
    have h := div_le_div_of_nonneg_right
      (buchstab_abs_le (argument_one hφ ha hb hc)) (by linarith [hb.1] : 0 ≤ b)
    exact h.trans (by simpa only [mul_one] using div_small_lower (by norm_num : (0 : ℝ) ≤ 1) hb.1)
  · intro a ha a' ha' b hb c hc
    have hu := argument_one hφ ha hb hc
    have hv := argument_one hφ ha' hb hc
    have harg := quotient_difference hb.1 hb.1 (numerator_bound hφ hP ha' hb hc)
      (x := φ - a - b - c)
    have hdiff : |(φ - a - b - c) - (φ - a' - b - c)| = |a - a'| := by
      rw [show (φ - a - b - c) - (φ - a' - b - c) = -(a - a') by ring, abs_neg]
    rw [hdiff, sub_self, abs_zero, mul_zero, add_zero] at harg
    have hω := (primeOrdered_buchstab_lipschitz hu hv).trans harg
    have hq := quotient_difference hb.1 hb.1 (buchstab_abs_le hv)
      (x := buchstab ((φ - a - b - c) / b))
    rw [sub_self, abs_zero, mul_zero, add_zero] at hq
    unfold primeOrderedBuchstabWeight
    nlinarith [mul_nonneg hP0 (abs_nonneg (a - a'))]
  · intro a ha b hb b' hb' c hc
    have hu := argument_one hφ ha hb hc
    have hv := argument_one hφ ha hb' hc
    have harg := quotient_difference hb.1 hb'.1 (numerator_bound hφ hP ha hb' hc)
      (x := φ - a - b - c)
    have hdiff : |(φ - a - b - c) - (φ - a - b' - c)| = |b - b'| := by
      rw [show (φ - a - b - c) - (φ - a - b' - c) = -(b - b') by ring, abs_neg]
    rw [hdiff] at harg
    have hω := (primeOrdered_buchstab_lipschitz hu hv).trans harg
    have hq := quotient_difference hb.1 hb'.1 (buchstab_abs_le hv)
      (x := buchstab ((φ - a - b - c) / b))
    unfold primeOrderedBuchstabWeight
    nlinarith only [hω, hq]
  · intro a ha b hb c hc c' hc'
    have hu := argument_one hφ ha hb hc
    have hv := argument_one hφ ha hb hc'
    have harg := quotient_difference hb.1 hb.1 (numerator_bound hφ hP ha hb hc')
      (x := φ - a - b - c)
    have hdiff : |(φ - a - b - c) - (φ - a - b - c')| = |c - c'| := by
      rw [show (φ - a - b - c) - (φ - a - b - c') = -(c - c') by ring, abs_neg]
    rw [hdiff, sub_self, abs_zero, mul_zero, add_zero] at harg
    have hω := (primeOrdered_buchstab_lipschitz hu hv).trans harg
    have hq := quotient_difference hb.1 hb.1 (buchstab_abs_le hv)
      (x := buchstab ((φ - a - b - c) / b))
    rw [sub_self, abs_zero, mul_zero, add_zero] at hq
    unfold primeOrderedBuchstabWeight
    nlinarith [mul_nonneg hP0 (abs_nonneg (c - c'))]

theorem primeOrdered_buchstab_uniform (P ε : ℝ) (hP : 2 ≤ P) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ φ A B : ℝ, 2 ≤ φ → φ ≤ P →
      1 / 10 ≤ A → A ≤ B → B ≤ 1 / 2 →
      |primeOrderedTripleSum R A B (primeOrderedBuchstabWeight φ) -
        ∫ a in A..B, ∫ b in a..B, ∫ c in b..B,
          buchstab ((φ - a - b - c) / b) / (a * b ^ 2 * c)| < ε := by
  filter_upwards [primeOrdered_triple_uniform 10 (1000 * P + 200) ε
    (by norm_num) (by linarith) hε] with R h
  intro φ A B hφ hφP hA hAB hB
  have hh := h (primeOrderedBuchstabWeight φ) (primeOrdered_buchstab_weight hφ hφP)
    A B hA hAB hB
  have he :
      (∫ a in A..B, ∫ b in a..B, ∫ c in b..B,
        primeOrderedBuchstabWeight φ a b c / (a * b * c)) =
      ∫ a in A..B, ∫ b in a..B, ∫ c in b..B,
        buchstab ((φ - a - b - c) / b) / (a * b ^ 2 * c) := by
    apply intervalIntegral.integral_congr
    intro a _
    apply intervalIntegral.integral_congr
    intro b _
    apply intervalIntegral.integral_congr
    intro c _
    dsimp only [primeOrderedBuchstabWeight]
    ring
  rwa [he] at hh

end Wu2008DoubleSieve
