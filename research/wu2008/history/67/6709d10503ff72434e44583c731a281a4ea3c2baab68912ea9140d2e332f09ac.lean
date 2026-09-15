import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedRough
import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedQuadrature

/-! # Positive enlargement into the literal gated closed prime domains -/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

noncomputable def fourthRowTripleGatedPrimeLower (R : ℝ) (ten : Bool) (p : ℕ) : ℝ :=
  if ten then (p : ℝ) else R ^ (25 / 89 : ℝ)

theorem fourthRowTripleGated_middle_rpow {R : ℝ} (hR : 1 < R) (ten : Bool) {p : ℕ} (hp : p.Prime) :
    R ^ fourthRowTripleGatedMiddleStart ten (log p / log R) =
      fourthRowTripleGatedPrimeLower R ten p := by
  cases ten
  · rfl
  · exact primeOrdered_coordinate_rpow hR hp

theorem fourthRowTripleGated_prime_band {N d : ℕ} {δ : ℝ} {ten : Bool}
    {p : ℕ × ℕ × ℕ} (hp : p ∈ fourthRowTripleGatedPrimes N d δ ten) :
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    p.1 ∈ primesIcc (R ^ fourthRowTripleGatedStart ten) (R ^ fourthRowTripleGatedStop ten) ∧
    p.2.1 ∈ primesIcc (fourthRowTripleGatedPrimeLower R ten p.1) (R ^ (100 / 291 : ℝ)) ∧
    p.2.2 ∈ primesIcc (R ^ (100 / 291 : ℝ)) (R ^ (2 / 5 : ℝ)) := by
  obtain ⟨hp, ⟨hfirst, hsecond⟩, hgate⟩ := mem_filter.mp hp
  obtain ⟨hq, ht, _, hr, _, hrs⟩ := mem_omega3XPrimes.mp hp
  have ht' := mem_primeWindow.mp ht
  have hq' := mem_primeWindow.mp hq
  have h2 := (fourthRowTripleGated_colour_one _ _ _).mp hsecond
  have hpos (x : ℝ) : 0 ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ x := rpow_nonneg (by positivity) _
  have h1 :
      ((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleGatedStart ten ≤ p.1 ∧
      (p.1 : ℝ) ≤ ((N : ℝ) ^ (1 / 2 - δ) / d) ^ fourthRowTripleGatedStop ten := by
    cases ten
    · have hh := (fourthRowMother_colour_zero _ _ _).mp hfirst
      norm_num only [fourthRowTripleGatedStart, fourthRowTripleGatedStop, Bool.false_eq_true, if_false]
      constructor
      · simpa only [wuLocalCutoff, show (1 / (103 / 25) : ℝ) = 25 / 103 by norm_num] using ht'.2.2.1
      · simpa only [wuLocalCutoff, show (1 / (89 / 25) : ℝ) = 25 / 89 by norm_num] using hh.le
    · have hh := (fourthRowTripleGated_colour_one _ _ _).mp hfirst
      norm_num only [fourthRowTripleGatedStart, fourthRowTripleGatedStop, if_true]
      constructor
      · simpa only [wuLocalCutoff, show (1 / (89 / 25) : ℝ) = 25 / 89 by norm_num] using hh.1
      · simpa only [wuLocalCutoff, show (1 / (291 / 100) : ℝ) = 100 / 291 by norm_num] using hh.2.le
  refine ⟨(mem_primesIcc (hpos _)).mpr ⟨ht'.1, h1⟩,
    (mem_primesIcc (hpos _)).mpr ⟨hq'.1, ?_, ?_⟩,
    (mem_primesIcc (hpos _)).mpr ⟨hr, ?_, ?_⟩⟩
  · cases ten
    · simpa only [fourthRowTripleGatedPrimeLower, Bool.false_eq_true, if_false, wuLocalCutoff,
        show (1 / (89 / 25) : ℝ) = 25 / 89 by norm_num] using h2.1
    · exact ht'.2.2.2.le
  · simpa only [wuLocalCutoff, show (1 / (291 / 100) : ℝ) = 100 / 291 by norm_num] using h2.2.le
  · simpa only [fourthRowTripleGatedGate, wuLocalCutoff,
      show (1 / (291 / 100) : ℝ) = 100 / 291 by norm_num] using hgate
  · simpa only [wuLocalCutoff, show (1 / (5 / 2) : ℝ) = 2 / 5 by norm_num] using hrs

theorem fourthRowTripleGated_prime_mass {i k N d : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) (ten : Bool) :
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    (∑ p ∈ fourthRowTripleGatedPrimes N d δ ten,
      omega3XScale N d p.1 p.2.1 p.2.2 *
        buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log R) *
        fourthRowTripleGatedPrimeSum R ten (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
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
  let U := (primesIcc (R ^ fourthRowTripleGatedStart ten) (R ^ fourthRowTripleGatedStop ten)).sigma
    fun p => (primesIcc (fourthRowTripleGatedPrimeLower R ten p) (R ^ (100 / 291 : ℝ))).sigma
      fun _q => primesIcc (R ^ (100 / 291 : ℝ)) (R ^ (2 / 5 : ℝ))
  let embed : ℕ × ℕ × ℕ → (p : ℕ) × (q : ℕ) × ℕ := fun p => ⟨p.1, p.2.1, p.2.2⟩
  let f : (p : ℕ) × (q : ℕ) × ℕ → ℝ := fun p =>
    primeOrderedBuchstabWeight φ (log p.1 / log R) (log p.2.1 / log R)
      (log p.2.2 / log R) / ((p.1 : ℝ) * p.2.1 * p.2.2)
  have hinj : Function.Injective embed := by
    rintro ⟨p, q, r⟩ ⟨p', q', r'⟩ he
    simpa only [embed, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] using he
  have hsub : (fourthRowTripleGatedPrimes N d δ ten).image embed ⊆ U := by
    intro p hp
    obtain ⟨p', hp', rfl⟩ := mem_image.mp hp
    have hh := fourthRowTripleGated_prime_band hp'
    exact mem_sigma.mpr ⟨hh.1, mem_sigma.mpr hh.2⟩
  have hf (p : (p : ℕ) × (q : ℕ) × ℕ) (hp : p ∈ U) : 0 ≤ f p := by
    obtain ⟨hp, hqr⟩ := mem_sigma.mp hp
    obtain ⟨hq, hr⟩ := mem_sigma.mp hqr
    have hp' := omega3XPrime_coordinate_mem hR hp
    have hpprime := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hp
    have hm := fourthRowTripleGated_middle_endpoints ten hp'
    have hqcoord : p.2.1 ∈ primesIcc
        (R ^ fourthRowTripleGatedMiddleStart ten (log p.1 / log R)) (R ^ (100 / 291 : ℝ)) := by
      rw [fourthRowTripleGated_middle_rpow hR ten hpprime.1]
      exact hq
    have hq' := omega3XPrime_coordinate_mem hR hqcoord
    have hr' := omega3XPrime_coordinate_mem hR hr
    have he := fourthRowTripleGated_endpoints ten
    have hqm : log (p.2.1 : ℝ) / log R ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) :=
      ⟨hm.1.trans hq'.1, by linarith [hq'.2]⟩
    have hrm : log (p.2.2 : ℝ) / log R ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) :=
      ⟨by linarith [hr'.1], by linarith [hr'.2]⟩
    have hw := buchstab_pos (omega3X_argument_bounds hφ
      ⟨he.1.trans hp'.1, by linarith [hp'.2, he.2.2]⟩ hqm hrm).2.2
    have hqprime := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hq
    have hqlog : 0 < log (p.2.1 : ℝ) := log_pos (by exact_mod_cast hqprime.1.one_lt)
    dsimp [f, primeOrderedBuchstabWeight]
    positivity
  have hsum : (∑ p ∈ fourthRowTripleGatedPrimes N d δ ten, f (embed p)) ≤ ∑ p ∈ U, f p := by
    rw [← sum_image (fun _ _ _ _ h => hinj h)]
    exact sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => hf p hp)
  calc
    _ = (N : ℝ) / ((d : ℝ) * log R) *
        ∑ p ∈ fourthRowTripleGatedPrimes N d δ ten, f (embed p) := by
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
      simp only [U, sum_sigma, fourthRowTripleGatedPrimeSum, primeOrderedClosedSum]
      apply sum_congr rfl
      intro p hp
      have hpp := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hp
      rw [fourthRowTripleGated_middle_rpow hR ten hpp.1, sum_div]
      apply sum_congr rfl
      intro q _
      rw [sum_div, sum_div]
      apply sum_congr rfl
      intro r _
      dsimp [f]
      ring

end Wu2008DoubleSieve
