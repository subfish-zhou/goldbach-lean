import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitMaskedUniform

open scoped BigOperators Classical
namespace SecondFunctionalUnitMasked
open Set MeasureTheory Wu2008DoubleSieve SecondFunctionalUnitKernel SecondFunctionalUnitPrimeFibre

/-- Exact coordinate adapter, with the original labelled atom type unchanged. -/
theorem coordinates_eq {n : ℕ} {R : ℝ} (f : Fin n → primeSlabPrimes R) :
    gridCoordinates R f = coordinate f := rfl

noncomputable def selected {m r : ℕ} (R : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) : Finset (Fin (m+1) → primeSlabPrimes R) :=
  Finset.univ.filter (fun f => mask C gamma strict (coordinate f))

/-- Filter identity on full functions, retaining all repeated primes and multiplicities. -/
theorem filter_identity {m r : ℕ} (R phi b : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (strict : Fin r → Bool) :
    (∑ f ∈ selected R C gamma strict, primeSlabWeight R f *
      SecondFunctionalUnitFiniteKernel.F (phi - ∑ i, coordinate f i)
        (coordinate f (Fin.last m)) b) = primeSum R phi b C gamma strict := by
  unfold selected primeSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  rw [coordinates_eq]
  by_cases hm : mask C gamma strict (coordinate f)
  · simp only [hm, if_true, G, U]
  · simp only [hm, if_false, G, mul_zero]

/-- Literal prime reciprocal quadrature, with no mass or regularity hypotheses. -/
theorem quadrature (m r : ℕ) (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |(∑ f : Fin (m+1) → primeSlabPrimes R,
          primeSlabWeight R f * G phi b C gamma strict (coordinate f)) -
        (∫ t in continuousCube (m+1), G phi b C gamma strict t * continuousDensity t)| < epsilon := by
  simpa only [primeSum, integral, coordinates_eq] using uniform m r C hC epsilon he

/-- The physical producer and actual quadrature each receive epsilon/2. -/
theorem physical_uniform (m r : ℕ) (C : Fin r → Fin (m+1) → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |Real.log R / R^phi *
        (∑ f ∈ selected R C gamma strict,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) -
        (∫ t in continuousCube (m+1), G phi b C gamma strict t * continuousDensity t)| < epsilon := by
  obtain ⟨Tp,hTp,hp⟩ := SecondFunctionalUnitFiniteKernel.physical_uniform m (epsilon/2) (by positivity)
  obtain ⟨Tq,_,hq⟩ := uniform m r C hC (epsilon/2) (by positivity)
  refine ⟨max Tp Tq, hTp.trans_le (le_max_left _ _), ?_⟩
  intro R hR phi b gamma strict
  have hp' := (hp R ((le_max_left _ _).trans hR) (selected R C gamma strict) phi b).2
  rw [filter_identity] at hp'
  have hq' := hq R ((le_max_right _ _).trans hR) phi b gamma strict
  have ht := abs_sub_le
    (Real.log R / R^phi * (∑ f ∈ selected R C gamma strict,
      ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)))
    (primeSum R phi b C gamma strict) (integral phi b C gamma strict)
  change |_ - integral phi b C gamma strict| < epsilon
  linarith

theorem physical_fin4 (r : ℕ) (C : Fin r → Fin 4 → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |Real.log R / R^phi *
        (∑ f ∈ selected R C gamma strict,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 3)).val (R^b)).card : ℝ)) -
        (∫ t in continuousCube 4, G phi b C gamma strict t * continuousDensity t)| < epsilon :=
  physical_uniform 3 r C hC epsilon he

theorem physical_fin5 (r : ℕ) (C : Fin r → Fin 5 → ℝ)
    (hC : ∀ q, ∃ j, 1 ≤ |C q j|) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ)
      (gamma : Fin r → ℝ) (strict : Fin r → Bool),
      |Real.log R / R^phi *
        (∑ f ∈ selected R C gamma strict,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last 4)).val (R^b)).card : ℝ)) -
        (∫ t in continuousCube 5, G phi b C gamma strict t * continuousDensity t)| < epsilon :=
  physical_uniform 4 r C hC epsilon he

theorem selected_empty (m : ℕ) (R : ℝ) (C : Fin 0 → Fin (m+1) → ℝ)
    (gamma : Fin 0 → ℝ) (strict : Fin 0 → Bool) : selected R C gamma strict = Finset.univ := by
  simp [selected, mask]

/-- No extra mask, all prime labels, arbitrary b, and both original strict kernel gates. -/
theorem physical_empty (m : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ (phi b : ℝ),
      |Real.log R / R^phi *
        (∑ f : Fin (m+1) → primeSlabPrimes R,
          ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) -
        (∫ t in continuousCube (m+1), U phi b t * continuousDensity t)| < epsilon := by
  obtain ⟨T,hT,h⟩ := physical_uniform m 0 Fin.elim0 (fun q => Fin.elim0 q) epsilon he
  refine ⟨T,hT,fun R hR phi b => ?_⟩
  simpa only [selected_empty, G_empty] using h R hR phi b Fin.elim0 Fin.elim0

end SecondFunctionalUnitMasked
