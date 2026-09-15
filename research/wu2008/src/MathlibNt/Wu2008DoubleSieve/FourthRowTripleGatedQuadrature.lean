import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedIntegral
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureFinite

/-! # Closed prime quadrature on the two gated domains -/

namespace Wu2008DoubleSieve

open Finset Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def fourthRowTripleGatedPrimeSum (R : ℝ) (ten : Bool)
    (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  primeOrderedClosedSum R (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten)
    (fun t => primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
      (fun u => primeOrderedClosedSum R (100 / 291) (2 / 5) (f t u)))

private theorem weighted_difference {S : Finset ℕ} {f g : ℕ → ℝ} {e : ℝ}
    (h : ∀ p ∈ S, |f p - g p| ≤ e) :
    |(∑ p ∈ S, f p / p) - ∑ p ∈ S, g p / p| ≤ e * ∑ p ∈ S, 1 / (p : ℝ) := by
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (h p hp) (Nat.cast_nonneg p)

theorem fourthRowTripleGated_quadrature (M K ε : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ f : ℝ → ℝ → ℝ → ℝ, PrimeOrderedWeight M K f →
      ∀ ten : Bool,
      |fourthRowTripleGatedPrimeSum R ten f -
        ∫ t in fourthRowTripleGatedStart ten..fourthRowTripleGatedStop ten,
          fourthRowTripleGatedMiddle ten f t / t| < ε := by
  let e := ε / 32
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    primeOrdered_weighted_uniform M K e hM hK he,
    primeOrdered_weighted_uniform (4 * M) (4 * K) e (by positivity) (by positivity) he,
    primeOrdered_weighted_uniform (16 * M) (16 * K + 40 * M) e (by positivity) (by positivity) he]
    with R hR hstart hD h1 h2 h3
  intro f hw ten
  have mass {A B : ℝ} (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
      (∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤ 5 := by
    have hd := (le_abs_self _).trans
      (primeOrdered_reciprocal_Icc_uniform_bound hR hstart hA hAB hB)
    have hi := (primeOrdered_exponent_density_bounds hA hAB hB).2
    linarith
  obtain ⟨hib, _, hil⟩ := fourthRowTripleGated_inner_regular hw hM hK
  obtain ⟨hmb, hml⟩ := fourthRowTripleGated_middle_regular hw hM hK ten
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 2))
      (u : ℝ) (hu : u ∈ Set.Icc (1 / 10 : ℝ) (1 / 2)) :
      |primeOrderedClosedSum R (100 / 291) (2 / 5) (f t u) - fourthRowTripleGatedInner f t u| ≤ e :=
    (h1 (f t u) (100 / 291) (2 / 5)
      (primeOrdered_continuous_of_lipschitz (hw.third t ht u hu))
      (hw.bound t ht u hu) (hw.third t ht u hu) (by norm_num) (by norm_num) (by norm_num)).le
  have hmiddle (t : ℝ) (ht : t ∈ Set.Icc (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten)) :
      |primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
        (fun u => primeOrderedClosedSum R (100 / 291) (2 / 5) (f t u)) -
        fourthRowTripleGatedMiddle ten f t| ≤ 6 * e := by
    have hend := fourthRowTripleGated_endpoints ten
    have hm := fourthRowTripleGated_middle_endpoints ten ht
    have ht' : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) :=
      ⟨hend.1.trans ht.1, by linarith [ht.2, hend.2.2]⟩
    have hr : |primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
        (fun u => primeOrderedClosedSum R (100 / 291) (2 / 5) (f t u)) -
        primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
          (fourthRowTripleGatedInner f t)| ≤ 5 * e := by
      apply le_trans (weighted_difference fun p hp => hinner t ht' (log p / log R) (by
        have hh := omega3XPrime_coordinate_mem hR hp
        exact ⟨hm.1.trans hh.1, by linarith [hh.2]⟩))
      exact (mul_le_mul_of_nonneg_left (mass hm.1 hm.2 (by norm_num)) he.le).trans_eq (mul_comm _ _)
    have hi := h2 (fourthRowTripleGatedInner f t) (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
      (primeOrdered_continuous_of_lipschitz (hil t ht')) (hib t ht') (hil t ht')
      hm.1 hm.2 (by norm_num)
    have hh := abs_sub_le
      (primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
        (fun u => primeOrderedClosedSum R (100 / 291) (2 / 5) (f t u)))
      (primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
        (fourthRowTripleGatedInner f t)) (fourthRowTripleGatedMiddle ten f t)
    change |primeOrderedClosedSum R (fourthRowTripleGatedMiddleStart ten t) (100 / 291)
      (fourthRowTripleGatedInner f t) - fourthRowTripleGatedMiddle ten f t| < e at hi
    linarith
  obtain ⟨hA, hAB, hB⟩ := fourthRowTripleGated_endpoints ten
  have hB' : fourthRowTripleGatedStop ten ≤ 1 / 2 := by linarith
  have hr : |fourthRowTripleGatedPrimeSum R ten f -
      primeOrderedClosedSum R (fourthRowTripleGatedStart ten)
        (fourthRowTripleGatedStop ten) (fourthRowTripleGatedMiddle ten f)| ≤ 30 * e := by
    unfold fourthRowTripleGatedPrimeSum
    apply le_trans (weighted_difference fun p hp => hmiddle _ (omega3XPrime_coordinate_mem hR hp))
    exact (mul_le_mul_of_nonneg_left (mass hA hAB hB') (by positivity : 0 ≤ 6 * e)).trans_eq (by ring)
  have hi := h3 (fourthRowTripleGatedMiddle ten f) (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten)
    (primeOrdered_continuous_of_lipschitz hml) hmb hml hA hAB hB'
  have hh := abs_sub_le (fourthRowTripleGatedPrimeSum R ten f)
    (primeOrderedClosedSum R (fourthRowTripleGatedStart ten) (fourthRowTripleGatedStop ten)
      (fourthRowTripleGatedMiddle ten f))
    (∫ t in fourthRowTripleGatedStart ten..fourthRowTripleGatedStop ten,
      fourthRowTripleGatedMiddle ten f t / t)
  dsimp [e] at hr hi
  linarith

theorem fourthRowTripleGated_buchstab_quadrature (P ε : ℝ) (hP : 2 ≤ P) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ φ : ℝ, 2 ≤ φ → φ ≤ P → ∀ ten : Bool,
      |fourthRowTripleGatedPrimeSum R ten (primeOrderedBuchstabWeight φ) -
        fourthRowTripleGatedIntegral ten φ| < ε := by
  filter_upwards [fourthRowTripleGated_quadrature 10 (1000 * P + 200) ε
    (by norm_num) (by linarith) hε] with R h
  intro φ hφ hφP ten
  rw [fourthRowTripleGated_integral_eq]
  exact h _ (primeOrdered_buchstab_weight hφ hφP) ten

end Wu2008DoubleSieve
