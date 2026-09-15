import MathlibNt.Wu2008DoubleSieve.Omega3XPrimeMass

/-!
# The actual source-X prime budget

Wu04, TeX2215--2238. All three actual ordered primes lie in `[N^η,N]`,
where `η = wuLocalExponent k δ / 10`. Thus their reciprocal mass is at most
`(5 / η)^3`, and the `x / log p2` mass costs at most `(5 / η)^3 / η`.
The same convolution coefficient is used exactly once in the weighted sum.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem omega3XPrimes_mem_prime_interval {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s t d) :
    p.1 ∈ primesIcc ((N : ℝ) ^ (wuLocalExponent k δ / 10)) N ∧
    p.2.1 ∈ primesIcc ((N : ℝ) ^ (wuLocalExponent k δ / 10)) N ∧
    p.2.2 ∈ primesIcc ((N : ℝ) ^ (wuLocalExponent k δ / 10)) N := by
  rcases p with ⟨p1, p2, p3⟩
  obtain ⟨hp2, hp1, hp3N, hp3, h23, _⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hsp := wu_buchstab_prime_window_bounds hN hδ hδhi hb hs hst ht hd
  have h12 : p1 < p2 := by exact_mod_cast h1.2.2.2
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hlow1 := hsp.2.2.2.1.trans h1.2.2.1
  have hlow2 := hsp.2.2.2.1.trans h2.2.2.1
  refine ⟨(mem_primesIcc hN0).mpr ⟨h1.1, hlow1, ?_⟩,
    (mem_primesIcc hN0).mpr ⟨h2.1, hlow2, ?_⟩,
    (mem_primesIcc hN0).mpr ⟨hp3, ?_, ?_⟩⟩
  · exact_mod_cast (h12.le.trans h23.le).trans hp3N
  · exact_mod_cast h23.le.trans hp3N
  · exact hlow2.trans (by exact_mod_cast h23.le)
  · exact_mod_cast hp3N

theorem omega3XPrimes_reciprocal_source_le {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hstart : primeErrorStart ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10)) :
    (∑ p ∈ omega3XPrimes N δ s t d, 1 / ((p.1 : ℝ) * p.2.1 * p.2.2)) ≤
      (5 / (wuLocalExponent k δ / 10)) ^ 3 := by
  apply omega3X_prime_triple_reciprocal_le hN
    (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)) hstart
  intro p hp
  exact omega3XPrimes_mem_prime_interval hN hδ hδhi hb hs hst ht hd hp

theorem omega3X_scale_mass_source_le {i k N d : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hstart : primeErrorStart ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10)) :
    (∑ p ∈ omega3XPrimes N δ s t d,
      omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) ≤
      ((5 / (wuLocalExponent k δ / 10)) ^ 3 / (wuLocalExponent k δ / 10)) *
        ((N : ℝ) / d / log N) := by
  let η := wuLocalExponent k δ / 10
  have hη : 0 < η := div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < log (N : ℝ) :=
    log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsum := omega3XPrimes_reciprocal_source_le hN hδ hδhi hb hs hst ht hd hstart
  calc
    _ ≤ ∑ p ∈ omega3XPrimes N δ s t d,
        ((N : ℝ) / d / (η * log N)) * (1 / ((p.1 : ℝ) * p.2.1 * p.2.2)) := by
      apply sum_le_sum
      intro p hp
      have hP := omega3XPrimes_mem_prime_interval hN hδ hδhi hb hs hst ht hd hp
      have hlow := ((mem_primesIcc hN0.le).mp hP.2.1).2.1
      have hlog := log_le_log (rpow_pos_of_pos hN0 _) hlow
      rw [log_rpow hN0] at hlog
      calc
        _ ≤ omega3XScale N d p.1 p.2.1 p.2.2 / (η * log N) :=
          div_le_div_of_nonneg_left (by unfold omega3XScale; positivity)
            (mul_pos hη hlogN) hlog
        _ = _ := by unfold omega3XScale; ring
    _ = ((N : ℝ) / d / (η * log N)) *
        ∑ p ∈ omega3XPrimes N δ s t d, 1 / ((p.1 : ℝ) * p.2.1 * p.2.2) :=
      (mul_sum ..).symm
    _ ≤ ((N : ℝ) / d / (η * log N)) * (5 / η) ^ 3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [η]; ring

theorem omega3X_weighted_scale_mass_source_le {i k N : ℕ} {δ Δ s t : ℝ}
    {V : Fin i → ℝ} (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hstart : primeErrorStart ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10)) :
    let W := convolutionWuWindows N Δ V
    (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ omega3XPrimes N δ s t d,
        omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) ≤
      ((5 / (wuLocalExponent k δ / 10)) ^ 3 / (wuLocalExponent k δ / 10)) *
        ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  dsimp only
  unfold boxConvolutionReciprocalMass
  rw [mul_sum]
  apply sum_le_sum
  intro d hd
  calc
    _ ≤ (convolutionCoeff (convolutionWuWindows N Δ V) d : ℝ) *
        (((5 / (wuLocalExponent k δ / 10)) ^ 3 / (wuLocalExponent k δ / 10)) *
          ((N : ℝ) / d / log N)) :=
      mul_le_mul_of_nonneg_left
        (omega3X_scale_mass_source_le hN hδ hδhi hb hs hst ht hd hstart)
        (Nat.cast_nonneg _)
    _ = _ := by ring

theorem omega3X_prime_mass_threshold (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      primeErrorStart ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10) := by
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop primeErrorStart))
  exact ⟨max 4 T, le_max_left _ _, fun N hN => hT N ((le_max_right _ _).trans hN)⟩

theorem omega3XPrimes_reciprocal_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        (∑ p ∈ omega3XPrimes N δ s t d, 1 / ((p.1 : ℝ) * p.2.1 * p.2.2)) ≤
          (5 / (wuLocalExponent k δ / 10)) ^ 3 := by
  obtain ⟨T, hT4, hT⟩ := omega3X_prime_mass_threshold k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht
  exact omega3XPrimes_reciprocal_source_le (by omega) hδ hδhi hb hs hst ht hd (hT N hN)

/-- One positive constant and one threshold precede N and every source box. -/
theorem omega3X_weighted_scale_mass_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ (C : ℝ) (T : ℕ), 0 < C ∧ 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
        let W := convolutionWuWindows N Δ V
        (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
          ∑ p ∈ omega3XPrimes N δ s t d,
            omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) ≤
          C * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
  obtain ⟨T, hT4, hT⟩ := omega3X_prime_mass_threshold k hδ hδhi
  have hη : 0 < wuLocalExponent k δ / 10 :=
    div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num)
  refine ⟨(5 / (wuLocalExponent k δ / 10)) ^ 3 / (wuLocalExponent k δ / 10),
    T, by positivity, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht
  exact omega3X_weighted_scale_mass_source_le (by omega) hδ hδhi hb hs hst ht (hT N hN)

end Wu2008DoubleSieve
