import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateRough
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleNoGateQuadrature

/-! # Positive enlargement from the original bands to closed prime quadrature -/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

theorem fourthRowTripleNoGate_prime_band {N d : ℕ} {δ : ℝ} {eleven : Bool}
    {p : ℕ × ℕ × ℕ}
    (hp : p ∈ fourthRowTripleNoGatePrimes N d δ eleven) :
    p.1 ∈ primesIcc (((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleNoGateLower eleven)
      (((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleNoGateUpper eleven) ∧
    p.2.1 ∈ primesIcc (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (100 / 291 : ℝ))
      (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (2 / 5 : ℝ)) ∧
    p.2.2 ∈ primesIcc (p.2.1 : ℝ) (((N : ℝ) ^ (1 / 2 - δ) / d) ^ (2 / 5 : ℝ)) := by
  obtain ⟨hp, hband⟩ := mem_filter.mp hp
  obtain ⟨hq, ht, _, hr, hqr, hrs⟩ := mem_omega3XPrimes.mp hp
  have hq' := mem_primeWindow.mp hq
  have ht' := mem_primeWindow.mp ht
  obtain ⟨hfirst, hsecond⟩ := hband
  have h2 : wuLocalCutoff N δ d (291 / 100) ≤ p.2.1 := by
    unfold fourthRowMotherColour at hsecond
    split_ifs at hsecond <;> simp_all
  have hfirst' :
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleNoGateLower eleven ≤ p.1 ∧
      (p.1 : ℝ) ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleNoGateUpper eleven := by
    cases eleven
    · have hh : (p.1 : ℝ) < wuLocalCutoff N δ d (89 / 25) :=
        (fourthRowMother_colour_zero _ _ _).mp hfirst
      norm_num only [fourthRowTripleNoGateLower, fourthRowTripleNoGateUpper,
        Bool.false_eq_true, if_false]
      constructor
      · simpa only [wuLocalCutoff, show (1 / (103 / 25) : ℝ) = 25 / 103 by norm_num] using ht'.2.2.1
      · simpa only [wuLocalCutoff, show (1 / (89 / 25) : ℝ) = 25 / 89 by norm_num] using hh.le
    · have hh : wuLocalCutoff N δ d (89 / 25) ≤ p.1 ∧
          (p.1 : ℝ) < wuLocalCutoff N δ d (291 / 100) := by
        unfold fourthRowMotherColour at hfirst
        split_ifs at hfirst <;> simp_all
      norm_num only [fourthRowTripleNoGateLower, fourthRowTripleNoGateUpper, if_true]
      constructor
      · simpa only [wuLocalCutoff, show (1 / (89 / 25) : ℝ) = 25 / 89 by norm_num] using hh.1
      · simpa only [wuLocalCutoff, show (1 / (291 / 100) : ℝ) = 100 / 291 by norm_num] using hh.2.le
  have hnonneg (x : ℝ) : 0 ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ x := rpow_nonneg (by positivity) _
  refine ⟨(mem_primesIcc (hnonneg _)).mpr ⟨ht'.1, hfirst'⟩,
    (mem_primesIcc (hnonneg _)).mpr ⟨hq'.1, ?_, ?_⟩,
    (mem_primesIcc (hnonneg _)).mpr ⟨hr, by exact_mod_cast hqr.le, ?_⟩⟩
  · simpa only [wuLocalCutoff, show (1 / (291 / 100) : ℝ) = 100 / 291 by norm_num] using h2
  · simpa only [wuLocalCutoff, show (1 / (5 / 2) : ℝ) = 2 / 5 by norm_num] using hq'.2.2.2.le
  · simpa only [wuLocalCutoff, show (1 / (5 / 2) : ℝ) = 2 / 5 by norm_num] using hrs

theorem fourthRowTripleNoGate_prime_mass {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (eleven : Bool) :
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    (∑ p ∈ fourthRowTripleNoGatePrimes N d δ eleven,
      omega3XScale N d p.1 p.2.1 p.2.2 *
        buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log R) *
        fourthRowTripleNoGatePrimeSum R eleven (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  let φ := omega3XPhi N d δ
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hR : 1 < R := hg.2.1
  have hR0 : 0 < R := by linarith
  have hl := log_pos hR
  have hd0 := (omega3_source_support_le_Q hN hδ hδhi hb hd).1
  have hφ : 2 ≤ φ := by
    have hh : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    dsimp [φ]
    linarith [hg.2.2.1]
  let U := (primesIcc (R ^ fourthRowTripleNoGateLower eleven)
    (R ^ fourthRowTripleNoGateUpper eleven)).sigma fun p =>
    (primesIcc (R ^ (100 / 291 : ℝ)) (R ^ (2 / 5 : ℝ))).sigma fun q =>
      primesIcc (q : ℝ) (R ^ (2 / 5 : ℝ))
  let embed : ℕ × ℕ × ℕ → (p : ℕ) × (q : ℕ) × ℕ := fun p => ⟨p.1, p.2.1, p.2.2⟩
  let f : (p : ℕ) × (q : ℕ) × ℕ → ℝ := fun p =>
    primeOrderedBuchstabWeight φ (log p.1 / log R) (log p.2.1 / log R)
      (log p.2.2 / log R) / ((p.1 : ℝ) * p.2.1 * p.2.2)
  have hinj : Function.Injective embed := by
    rintro ⟨p, q, r⟩ ⟨p', q', r'⟩ he
    simpa only [embed, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] using he
  have hsub : (fourthRowTripleNoGatePrimes N d δ eleven).image embed ⊆ U := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    have hh := fourthRowTripleNoGate_prime_band hp'
    exact mem_sigma.mpr ⟨hh.1, mem_sigma.mpr hh.2⟩
  have hf (p : (p : ℕ) × (q : ℕ) × ℕ) (hp : p ∈ U) : 0 ≤ f p := by
    obtain ⟨hp, hqr⟩ := mem_sigma.mp hp
    obtain ⟨hq, hr⟩ := mem_sigma.mp hqr
    have hp' := omega3XPrime_coordinate_mem hR hp
    have hq' := omega3XPrime_coordinate_mem hR hq
    have hqr' := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hr
    have hq'' := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hq
    have hr' := omega3XPrime_coordinate_mem hR
      ((mem_primesIcc (rpow_nonneg hR0.le _)).mpr
        ⟨hqr'.1, hq''.2.1.trans hqr'.2.1, hqr'.2.2⟩)
    have he := fourthRowTripleNoGate_endpoints eleven
    have hqm : log (p.2.1 : ℝ) / log R ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) :=
      ⟨by linarith [hq'.1], by linarith [hq'.2]⟩
    have hrm : log (p.2.2 : ℝ) / log R ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) :=
      ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    have hw := buchstab_pos (omega3X_argument_bounds hφ
      ⟨he.1.trans hp'.1, hp'.2.trans he.2.2⟩ hqm hrm).2.2
    have hqlog : 0 < log (p.2.1 : ℝ) := log_pos (by exact_mod_cast hq''.1.one_lt)
    dsimp [f, primeOrderedBuchstabWeight]
    positivity
  have hsum : (∑ p ∈ fourthRowTripleNoGatePrimes N d δ eleven, f (embed p)) ≤ ∑ p ∈ U, f p := by
    rw [← sum_image (fun _ _ _ _ h => hinj h)]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hf p hp)
  calc
    _ = (N : ℝ) / ((d : ℝ) * log R) *
        ∑ p ∈ fourthRowTripleNoGatePrimes N d δ eleven, f (embed p) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      have hm := mem_omega3XPrimes.mp (mem_filter.mp hp).1
      exact omega3XPrime_buchstab_term_eq (by omega) hd0
        (mem_primeWindow.mp hm.2.1).1 (mem_primeWindow.mp hm.1).1 hm.2.2.2.1 hR
    _ ≤ (N : ℝ) / ((d : ℝ) * log R) * ∑ p ∈ U, f p :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by
      congr 1
      simp only [U, sum_sigma, fourthRowTripleNoGatePrimeSum, primeOrderedClosedSum]
      apply sum_congr rfl
      intro p hp
      rw [sum_div]
      apply sum_congr rfl
      intro q hq
      rw [sum_div, sum_div]
      have hqpos := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hq
      rw [primeOrdered_coordinate_rpow hR hqpos.1]
      apply sum_congr rfl
      intro r _
      dsimp [f]
      ring

end Wu2008DoubleSieve
