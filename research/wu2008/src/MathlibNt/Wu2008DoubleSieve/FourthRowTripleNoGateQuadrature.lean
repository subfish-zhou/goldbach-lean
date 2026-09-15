import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateIntegral
import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeQuadratureFinite

/-! # Closed band quadrature, including every discrete boundary atom -/

namespace Wu2008DoubleSieve

open Finset Set Real Filter MeasureTheory LiLiuPrereqBuchstab
open scoped Classical Topology Interval

noncomputable def fourthRowTripleNoGatePrimeSum (R : ℝ) (eleven : Bool)
    (f : ℝ → ℝ → ℝ → ℝ) : ℝ :=
  primeOrderedClosedSum R (fourthRowTripleNoGateLower eleven) (fourthRowTripleNoGateUpper eleven)
    (fun t => primeOrderedClosedSum R (100 / 291) (2 / 5)
      (fun u => primeOrderedClosedSum R u (2 / 5) (f t u)))

private theorem weighted_difference {S : Finset ℕ} {f g : ℕ → ℝ} {e : ℝ}
    (h : ∀ p ∈ S, |f p - g p| ≤ e) :
    |(∑ p ∈ S, f p / p) - ∑ p ∈ S, g p / p| ≤
      e * ∑ p ∈ S, 1 / (p : ℝ) := by
  rw [← sum_sub_distrib, mul_sum]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro p hp
  rw [← sub_div, abs_div, abs_of_nonneg (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  simpa only [mul_one_div] using div_le_div_of_nonneg_right (h p hp) (Nat.cast_nonneg p)

theorem fourthRowTripleNoGate_quadrature (M K ε : ℝ)
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ f : ℝ → ℝ → ℝ → ℝ, PrimeOrderedWeight M K f →
      ∀ eleven : Bool,
      |fourthRowTripleNoGatePrimeSum R eleven f -
        ∫ t in fourthRowTripleNoGateLower eleven..fourthRowTripleNoGateUpper eleven,
          fourthRowTripleNoGateMiddle f t / t| < ε := by
  let e := ε / 32
  have he : 0 < e := by dsimp [e]; positivity
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually
      (eventually_ge_atTop primeOrderedMertensStart),
    primeOrderedDiscrepancy_tendsto.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)),
    primeOrdered_weighted_uniform M K e hM hK he,
    primeOrdered_weighted_uniform (4 * M) (4 * K + 10 * M) e (by positivity) (by positivity) he,
    primeOrdered_weighted_uniform (16 * M) (16 * K) e (by positivity) (by positivity) he]
    with R hR hstart hD h1 h2 h3
  intro f hw eleven
  have mass {A B : ℝ} (hA : 1 / 10 ≤ A) (hAB : A ≤ B) (hB : B ≤ 1 / 2) :
      (∑ p ∈ primesIcc (R ^ A) (R ^ B), 1 / (p : ℝ)) ≤ 5 := by
    have hd := (le_abs_self _).trans
      (primeOrdered_reciprocal_Icc_uniform_bound hR hstart hA hAB hB)
    have hi := (primeOrdered_exponent_density_bounds hA hAB hB).2
    linarith
  obtain ⟨hib, _, hil⟩ := primeOrdered_inner_regular hw hM hK
    (by norm_num : (2 / 5 : ℝ) ∈ Set.Icc (1 / 10) (1 / 2))
  obtain ⟨hmb, hml⟩ := fourthRowTripleNoGate_middle_regular hw hM hK
  have hinner (t : ℝ) (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 2))
      (u : ℝ) (hu : u ∈ Set.Icc (100 / 291 : ℝ) (2 / 5)) :
      |primeOrderedClosedSum R u (2 / 5) (f t u) -
        primeOrderedInnerIntegral (2 / 5) f t u| ≤ e := by
    have hu' : u ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
      constructor <;> linarith [hu.1, hu.2]
    exact (h1 (f t u) u (2 / 5)
      (primeOrdered_continuous_of_lipschitz (hw.third t ht u hu'))
      (hw.bound t ht u hu') (hw.third t ht u hu') hu'.1 hu.2 (by norm_num)).le
  have hmiddle (t : ℝ) (ht : t ∈ Set.Icc (1 / 10 : ℝ) (1 / 2)) :
      |primeOrderedClosedSum R (100 / 291) (2 / 5)
        (fun u => primeOrderedClosedSum R u (2 / 5) (f t u)) -
        fourthRowTripleNoGateMiddle f t| ≤ 6 * e := by
    have hr : |primeOrderedClosedSum R (100 / 291) (2 / 5)
        (fun u => primeOrderedClosedSum R u (2 / 5) (f t u)) -
        primeOrderedClosedSum R (100 / 291) (2 / 5)
          (primeOrderedInnerIntegral (2 / 5) f t)| ≤ 5 * e := by
      apply le_trans (weighted_difference fun p hp =>
        hinner t ht _ (omega3XPrime_coordinate_mem hR hp))
      exact (mul_le_mul_of_nonneg_left (mass (by norm_num) (by norm_num) (by norm_num)) he.le).trans_eq
        (mul_comm _ _)
    have hi := h2 (primeOrderedInnerIntegral (2 / 5) f t) (100 / 291) (2 / 5)
      (primeOrdered_continuous_of_lipschitz (hil t ht)) (hib t ht) (hil t ht)
      (by norm_num) (by norm_num) (by norm_num)
    have hh := abs_sub_le
      (primeOrderedClosedSum R (100 / 291) (2 / 5)
        (fun u => primeOrderedClosedSum R u (2 / 5) (f t u)))
      (primeOrderedClosedSum R (100 / 291) (2 / 5) (primeOrderedInnerIntegral (2 / 5) f t))
      (fourthRowTripleNoGateMiddle f t)
    change |primeOrderedClosedSum R (100 / 291) (2 / 5)
      (primeOrderedInnerIntegral (2 / 5) f t) - fourthRowTripleNoGateMiddle f t| < e at hi
    linarith
  obtain ⟨hA, hAB, hB⟩ := fourthRowTripleNoGate_endpoints eleven
  have hr : |fourthRowTripleNoGatePrimeSum R eleven f -
      primeOrderedClosedSum R (fourthRowTripleNoGateLower eleven)
        (fourthRowTripleNoGateUpper eleven) (fourthRowTripleNoGateMiddle f)| ≤ 30 * e := by
    unfold fourthRowTripleNoGatePrimeSum
    apply le_trans (weighted_difference fun p hp => hmiddle (log p / log R) (by
      have hh := omega3XPrime_coordinate_mem hR hp
      exact ⟨hA.trans hh.1, hh.2.trans hB⟩))
    exact (mul_le_mul_of_nonneg_left (mass hA hAB hB) (by positivity : 0 ≤ 6 * e)).trans_eq (by ring)
  have hi := h3 (fourthRowTripleNoGateMiddle f)
    (fourthRowTripleNoGateLower eleven) (fourthRowTripleNoGateUpper eleven)
    (primeOrdered_continuous_of_lipschitz hml) hmb hml hA hAB hB
  have hh := abs_sub_le (fourthRowTripleNoGatePrimeSum R eleven f)
    (primeOrderedClosedSum R (fourthRowTripleNoGateLower eleven)
      (fourthRowTripleNoGateUpper eleven) (fourthRowTripleNoGateMiddle f))
    (∫ t in fourthRowTripleNoGateLower eleven..fourthRowTripleNoGateUpper eleven,
      fourthRowTripleNoGateMiddle f t / t)
  dsimp [e] at hr hi
  linarith

theorem fourthRowTripleNoGate_buchstab_quadrature (P ε : ℝ)
    (hP : 2 ≤ P) (hε : 0 < ε) :
    ∀ᶠ R : ℝ in atTop, ∀ φ : ℝ, 2 ≤ φ → φ ≤ P → ∀ eleven : Bool,
      |fourthRowTripleNoGatePrimeSum R eleven (primeOrderedBuchstabWeight φ) -
        fourthRowTripleNoGateIntegral eleven φ| < ε := by
  filter_upwards [fourthRowTripleNoGate_quadrature 10 (1000 * P + 200) ε
    (by norm_num) (by linarith) hε] with R h
  intro φ hφ hφP eleven
  rw [fourthRowTripleNoGate_integral_eq]
  exact h _ (primeOrdered_buchstab_weight hφ hφP) eleven

end Wu2008DoubleSieve
