import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureBuchstab
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabNormalization
import MathlibNt.Wu2008DoubleSieve.Omega3XIntegralDomain

/-!
# The actual finite X carrier in logarithmic coordinates

Wu04, TeX2230--2248. Removing coprimality is an upper comparison.
The strict order and the closed upper endpoint remain literal finite sets.
-/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

theorem omega3XPrime_coordinate_mem {R A B : ℝ} (hR : 1 < R)
    {p : ℕ} (hp : p ∈ primesIcc (R ^ A) (R ^ B)) :
    log p / log R ∈ Set.Icc A B := by
  have hR0 : 0 < R := by linarith
  obtain ⟨hpp, hlo, hhi⟩ := (mem_primesIcc (rpow_nonneg hR0.le _)).mp hp
  have hl := log_le_log (rpow_pos_of_pos hR0 _) hlo
  have hu := log_le_log (by exact_mod_cast hpp.pos : (0 : ℝ) < p) hhi
  rw [log_rpow hR0] at hl hu
  exact ⟨(le_div_iff₀ (log_pos hR)).mpr hl, (div_le_iff₀ (log_pos hR)).mpr hu⟩

theorem omega3XPrime_buchstab_term_eq {N d p1 p2 p3 : ℕ} {δ : ℝ}
    (hN : 0 < N) (hd : 0 < d) (h1 : p1.Prime) (h2 : p2.Prime)
    (h3 : p3.Prime) (hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / d) :
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    let x := omega3XScale N d p1 p2 p3
    x * buchstab (log x / log p2) / log p2 =
      (N : ℝ) / ((d : ℝ) * log R) *
        (primeOrderedBuchstabWeight (omega3XPhi N d δ)
          (log p1 / log R) (log p2 / log R) (log p3 / log R) /
            ((p1 : ℝ) * p2 * p3)) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h10 : (0 : ℝ) < p1 := by exact_mod_cast h1.pos
  have h20 : (0 : ℝ) < p2 := by exact_mod_cast h2.pos
  have h30 : (0 : ℝ) < p3 := by exact_mod_cast h3.pos
  have hL := (log_pos hR).ne'
  have hpL := (log_pos (show (1 : ℝ) < p2 by exact_mod_cast h2.one_lt)).ne'
  have hxlog : log (omega3XScale N d p1 p2 p3) =
      log ((N : ℝ) / d) - log p1 - log p2 - log p3 := by
    rw [omega3XScale, log_div hN0.ne' (by positivity),
      log_mul (by positivity) h30.ne', log_mul (by positivity) h20.ne',
      log_mul hd0.ne' h10.ne', log_div hN0.ne' hd0.ne']
    ring
  have hu :
      (omega3XPhi N d δ - log p1 / log ((N : ℝ) ^ (1 / 2 - δ) / d) -
        log p2 / log ((N : ℝ) ^ (1 / 2 - δ) / d) -
        log p3 / log ((N : ℝ) ^ (1 / 2 - δ) / d)) /
        (log p2 / log ((N : ℝ) ^ (1 / 2 - δ) / d)) =
        log (omega3XScale N d p1 p2 p3) / log p2 := by
    rw [omega3XPhi, hxlog]
    generalize log ((N : ℝ) ^ (1 / 2 - δ) / d) = L at hL ⊢
    field_simp
  rw [primeOrderedBuchstabWeight, hu, omega3XScale]
  generalize log ((N : ℝ) ^ (1 / 2 - δ) / d) = L at hL ⊢
  field_simp

/-- The original support injects into the strict nested prime carrier. -/
theorem omega3XPrime_sum_le_nested {N d : ℕ} {δ s t : ℝ}
    (f : ℕ → ℕ → ℕ → ℝ)
    (hf : ∀ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
      ∀ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), 0 ≤ f p1 p2 p3) :
    (∑ p ∈ omega3XPrimes N δ s t d, f p.1 p.2.1 p.2.2) ≤
      ∑ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
        ∑ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
          ∑ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), f p1 p2 p3 := by
  let U := (primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s)).sigma
    fun p1 => (primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s)).sigma
      fun p2 => primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s)
  let e : ℕ × ℕ × ℕ → (p1 : ℕ) × (p2 : ℕ) × ℕ :=
    fun p => ⟨p.1, p.2.1, p.2.2⟩
  change _ ≤ ∑ p1 ∈ _, _
  rw [show (∑ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∑ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
        ∑ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), f p1 p2 p3) =
      ∑ p ∈ U, f p.1 p.2.1 p.2.2 by simp only [U, sum_sigma]]
  have hinj : Set.InjOn e (omega3XPrimes N δ s t d) := by
    rintro ⟨p1, p2, p3⟩ _ ⟨q1, q2, q3⟩ _ he
    simpa only [e, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] using he
  have himage : (∑ p ∈ (omega3XPrimes N δ s t d).image e, f p.1 p.2.1 p.2.2) =
      ∑ p ∈ omega3XPrimes N δ s t d, f p.1 p.2.1 p.2.2 := sum_image hinj
  rw [← himage]
  apply sum_le_sum_of_subset_of_nonneg
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hq
    obtain ⟨h2, h1, _, h3, h23, h3s⟩ := mem_omega3XPrimes.mp hp
    have hp1 := mem_primeWindow.mp h1
    have hp2 := mem_primeWindow.mp h2
    have hs0 : 0 ≤ wuLocalCutoff N δ d s := by unfold wuLocalCutoff; positivity
    refine mem_sigma.mpr ⟨(mem_primesIcc hs0).mpr
      ⟨hp1.1, hp1.2.2.1, hp1.2.2.2.le.trans hp2.2.2.2.le⟩, ?_⟩
    exact mem_sigma.mpr ⟨(mem_primesIoc hs0).mpr
      ⟨hp2.1, hp1.2.2.2, hp2.2.2.2.le⟩,
      (mem_primesIoc hs0).mpr ⟨h3, by exact_mod_cast h23, h3s⟩⟩
  · intro p hp _
    obtain ⟨h1, h23⟩ := mem_sigma.mp hp
    obtain ⟨h2, h3⟩ := mem_sigma.mp h23
    exact hf p.1 h1 p.2.1 h2 p.2.2 h3

theorem omega3XPrime_buchstab_le_ordered {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10) :
    let R := (N : ℝ) ^ (1 / 2 - δ) / d
    (∑ p ∈ omega3XPrimes N δ s t d,
      let x := omega3XScale N d p.1 p.2.1 p.2.2
      x * buchstab (log x / log p.2.1) / log p.2.1) ≤
      (N : ℝ) / ((d : ℝ) * log R) *
        primeOrderedTripleSum R (1 / t) (1 / s)
          (primeOrderedBuchstabWeight (omega3XPhi N d δ)) := by
  let R := (N : ℝ) ^ (1 / 2 - δ) / d
  have hg := omega3XPhi_source_bounds hN hδ hδhi hb hd
  have hR : 1 < R := hg.2.1
  have hd0 := boxConvolutionSupport_pos
    (fun j p hp => (mem_convolutionWuWindows.mp hp).1.pos) hd
  have hφ : 2 ≤ omega3XPhi N d δ := by
    have := hg.2.2.1
    have : 0 < 2 * δ / (1 / 2 - δ) := by positivity
    linarith
  have hA : 1 / 10 ≤ 1 / t := one_div_le_one_div_of_le (by linarith) ht
  have hB : 1 / s ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hs
  let f := fun p1 p2 p3 : ℕ =>
    (N : ℝ) / ((d : ℝ) * log R) *
      (primeOrderedBuchstabWeight (omega3XPhi N d δ)
        (log p1 / log R) (log p2 / log R) (log p3 / log R) /
          ((p1 : ℝ) * p2 * p3))
  have hf : ∀ p1 ∈ primesIcc (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s),
      ∀ p2 ∈ primesIoc (p1 : ℝ) (wuLocalCutoff N δ d s),
      ∀ p3 ∈ primesIoc (p2 : ℝ) (wuLocalCutoff N δ d s), 0 ≤ f p1 p2 p3 := by
    intro p1 hp1 p2 hp2 p3 hp3
    have hR0 : 0 ≤ R := by linarith
    have h1 := (mem_primesIcc (rpow_nonneg hR0 (1 / s))).mp hp1
    have h2 := (mem_primesIoc (rpow_nonneg hR0 (1 / s))).mp hp2
    have h3 := (mem_primesIoc (rpow_nonneg hR0 (1 / s))).mp hp3
    have hm1 := omega3XPrime_coordinate_mem hR hp1
    have hm2 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1 / s))).mpr ⟨h2.1, h1.2.1.trans h2.2.1.le, h2.2.2⟩)
    have hm3 := omega3XPrime_coordinate_mem hR ((mem_primesIcc
      (rpow_nonneg hR0 (1 / s))).mpr
        ⟨h3.1, (h1.2.1.trans h2.2.1.le).trans h3.2.1.le, h3.2.2⟩)
    have hw := buchstab_pos (omega3X_argument_bounds hφ
      ⟨hA.trans hm1.1, hm1.2.trans hB⟩
      ⟨hA.trans hm2.1, hm2.2.trans hB⟩
      ⟨hA.trans hm3.1, hm3.2.trans hB⟩).2.2
    have hlR := log_pos hR
    have hl2 : 0 < log (p2 : ℝ) := log_pos (by exact_mod_cast h2.1.one_lt)
    dsimp [f, primeOrderedBuchstabWeight]
    positivity
  calc
    _ = ∑ p ∈ omega3XPrimes N δ s t d, f p.1 p.2.1 p.2.2 := by
      apply sum_congr rfl
      intro p hp
      have h := mem_omega3XPrimes.mp hp
      exact omega3XPrime_buchstab_term_eq (by omega) hd0
        (mem_primeWindow.mp h.2.1).1 (mem_primeWindow.mp h.1).1 h.2.2.2.1 hR
    _ ≤ _ := (omega3XPrime_sum_le_nested f hf).trans_eq (by
      simp only [primeOrderedTripleSum, mul_sum, f, wuLocalCutoff, R])

end Wu2008DoubleSieve
