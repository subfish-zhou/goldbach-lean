import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleErrorInputs
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitRoughPurification

namespace Wu2008DoubleSieve.LowerTripleGrouped
open Finset Real
open scoped Classical

/-- Only the original residual is required to be rough at the original q. -/
def profileRough (x : Label) : Prop :=
  LiLiuPrereqBuchstab.Rough (x.2.2.1 : ℝ) x.2.2.2

noncomputable def roughFamily {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) : LabelledPhysical.Family Label N :=
  (sourceFamily N δ Δ V p j).restrictLabels profileRough

theorem mem_roughFamily_labels {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 6) (x : Label) :
    x ∈ (roughFamily N δ Δ V p j).labels ↔
      x ∈ (sourceFamily N δ Δ V p j).labels ∧ profileRough x := mem_filter

/-- No numerical data, bands, weights or physical prime fibres are changed. -/
theorem roughFamily_data {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) :
    (roughFamily N δ Δ V p j).weight = (sourceFamily N δ Δ V p j).weight ∧
    (roughFamily N δ Δ V p j).cofactor = (sourceFamily N δ Δ V p j).cofactor ∧
    (roughFamily N δ Δ V p j).lower = (sourceFamily N δ Δ V p j).lower ∧
    (roughFamily N δ Δ V p j).upper = (sourceFamily N δ Δ V p j).upper ∧
    (roughFamily N δ Δ V p j).primes = (sourceFamily N δ Δ V p j).primes :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem profileRough_one (d p q : ℕ) : profileRough (d,p,q,1) := by
  intro r hr hd
  exact (hr.ne_one (Nat.dvd_one.mp hd)).elim

/-- In particular, the canonical restriction never removes a unit residual. -/
theorem roughFamily_unit_retained {i N d a q : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 6)
    (hx : (d,a,q,1) ∈ (sourceFamily N δ Δ V p j).labels) :
    (d,a,q,1) ∈ (roughFamily N δ Δ V p j).labels :=
  (mem_roughFamily_labels p j _).mpr ⟨hx,profileRough_one d a q⟩

theorem roughFamily_original_mask {i N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (p : SecondFunctionalParameters) (j : Fin 6) {x : Label}
    (hx : x ∈ (roughFamily N δ Δ V p j).labels) :
    0 < x.2.2.2 ∧ Sifted (x.1*x.2.1*N) (cofactor x) x.2.2.1 :=
  source_mask p j ((mem_roughFamily_labels p j x).mp hx).1

/-- A proof adapter only; no nonunit or arity membership is imported. -/
def squareProfile (x : Label) : HighNonunit.Profile := ⟨x.1,[x.2.1],x.2.2.1,x.2.2.2⟩

theorem squareProfile_cofactor (x : Label) :
    HighNonunit.cofactor (squareProfile x) = cofactor x := by
  simp only [squareProfile, HighNonunit.cofactor, cofactor, List.prod_append,
    List.prod_cons, List.prod_nil, mul_one, mul_comm, mul_left_comm]

theorem squareProfile_mask (N : ℕ) (x : Label) :
    (squareProfile x).1 * (squareProfile x).2.1.prod * N = x.1*x.2.1*N := by
  simp only [squareProfile, List.prod_cons, List.prod_nil, mul_one]

/-- First descend the full E-mask to n; good nonrough labels force a square in E. -/
theorem masked_good_nonrough_square {N : ℕ} {Y : ℝ} {x : Label}
    (hs : Sifted (x.1*x.2.1*N) (cofactor x) x.2.2.1)
    (hc : (cofactor x).Coprime N) (hn : ¬ profileRough x)
    (hrel : ∀ r, r.Prime → r ∣ cofactor x → r.Coprime N → Y ≤ (r : ℝ)) :
    LabelledPhysical.Sq (cofactor x) Y := by
  have hsn : Sifted (x.1*x.2.1*N) x.2.2.2 x.2.2.1 := by
    exact (sifted_mul_iff _ _ _ _).mp hs |>.2
  have hs' : Sifted ((squareProfile x).1*(squareProfile x).2.1.prod*N)
      (squareProfile x).2.2.2 (squareProfile x).2.2.1 := by
    rw [squareProfile_mask]
    exact hsn
  have h := HighNonunit.masked_good_nonrough_square hs'
    (by simpa only [squareProfile_cofactor] using hc) hn
    (by simpa only [squareProfile_cofactor] using hrel)
  simpa only [squareProfile_cofactor] using h

/-- Actual prime-layer split, with raw-square and prime-bad exceptions kept distinct. -/
theorem source_primeMass_rough_square_bad (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      (sourceFamily N δ Δ V p j).primeMass ≤
        (roughFamily N δ Δ V p j).primeMass +
        (sourceFamily N δ Δ V p j).squareRawMass ((N : ℝ)^(wuLocalExponent k δ/10)) +
        (sourceFamily N δ Δ V p j).noncoprimePart.primeMass := by
  obtain ⟨T,hT,hu⟩ := source_error_inputs k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  apply LabelledPhysical.Family.primeMass_le_restrict_add_square_add_bad
  intro x hx hc hn
  exact masked_good_nonrough_square (source_mask p j hx).2 hc hn
    (((hu N hN i Δ V hb p hp).1 j).1 x hx)

theorem source_prime_six_le_rough_square_bad (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 6, (sourceFamily N δ Δ V p j).primeMass) ≤
        (∑ j : Fin 6, (roughFamily N δ Δ V p j).primeMass) +
        (∑ j : Fin 6, (sourceFamily N δ Δ V p j).squareRawMass
          ((N : ℝ)^(wuLocalExponent k δ/10))) +
        ∑ j : Fin 6, (sourceFamily N δ Δ V p j).noncoprimePart.primeMass := by
  obtain ⟨T,hT,hu⟩ := source_primeMass_rough_square_bad k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  simpa only [sum_add_distrib] using
    sum_le_sum (s := (univ : Finset (Fin 6))) (fun j _ => hu N hN i Δ V hb p hp j)

/-- A raw physical output equals the prime-filter dictionary only at prime ell. -/
theorem sourceFamily_weightAt_prime {i N ell : ℕ} {δ Δ : ℝ} (V : Fin i → ℝ)
    (p : SecondFunctionalParameters) (j : Fin 6) (hell : ell.Prime) :
    (sourceFamily N δ Δ V p j).weightAt ell =
      ∑ x ∈ (sourceFamily N δ Δ V p j).labels,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          ((LowerTripleGroupedOutput.outputFibre N δ Δ V p j x).filter
            (fun r => N-cofactor x*r = ell)).card := by
  change (∑ x ∈ (sourceFamily N δ Δ V p j).labels,
    (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
      (((sourceFamily N δ Δ V p j).primes x).filter
        (fun r => N-cofactor x*r = ell)).card) = _
  apply sum_congr rfl
  intro x _
  apply congrArg (fun s : Finset ℕ =>
    (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) * (s.card : ℝ))
  ext r
  simp only [LowerTripleGroupedOutput.outputFibre, mem_filter]
  constructor
  · rintro ⟨hr,he⟩
    exact ⟨⟨hr,he ▸ hell⟩,he⟩
  · rintro ⟨⟨hr,_⟩,he⟩
    exact ⟨hr,he⟩

theorem source_prime_weightAt_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      ∀ ell : ℕ, ell.Prime → (sourceFamily N δ Δ V p j).weightAt ell ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) := by
  obtain ⟨T,hT,hm⟩ := LowerTripleGroupedOutput.source_output_multiplicity k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j ell hell
  rw [sourceFamily_weightAt_prime V p j hell]
  exact hm N hN i Δ V hb p hp j ell

/-- Only bad prime mass is bounded; no bad raw mass estimate is asserted. -/
theorem source_bad_primeMass_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      (sourceFamily N δ Δ V p j).noncoprimePart.primeMass ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_prime_weightAt_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j
  apply LabelledPhysical.Family.noncoprimePart_primeMass_le_log
    (sourceFamily N δ Δ V p j) (by have := hT.trans hN; omega) (by positivity)
  intro ell hell
  exact hm N hN i Δ V hb p hp j ell (Nat.prime_of_mem_primeFactors hell)

theorem source_bad_primeMass_six_log_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible →
      (∑ j : Fin 6, (sourceFamily N δ Δ V p j).noncoprimePart.primeMass) ≤
        6 * (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) * log N / log 2 := by
  obtain ⟨T,hT,hm⟩ := source_bad_primeMass_log_uniform k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp
  calc
    _ ≤ ∑ _j : Fin 6, (max 1 (1/(wuLocalExponent k δ / 10)))^(k+3) *
        log N / log 2 := sum_le_sum (fun j _ => hm N hN i Δ V hb p hp j)
    _ = _ := by simp; ring

/-- The full original sigma fixed-E producer bounds raw square mass. -/
theorem source_squareRawMass_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ p : SecondFunctionalParameters, p.MotherAdmissible → ∀ j : Fin 6,
      ∀ Y : ℝ, 2 ≤ Y → (sourceFamily N δ Δ V p j).squareRawMass Y ≤
        (max 1 (1/(wuLocalExponent k δ / 10)))^(k+2) * N * (1+log N)/(Y-1) := by
  obtain ⟨T,hT,hm⟩ := source_error_inputs k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb p hp j Y hY
  exact (sourceFamily N δ Δ V p j).squareRawMass_le hY (by positivity)
    ((hm N hN i Δ V hb p hp).1 j).2

end Wu2008DoubleSieve.LowerTripleGrouped
