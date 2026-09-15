import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighUnitSourceGeometry

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighUnitPrimeOutput
open Finset HighUnitSource SecondFunctionalUnitPrimeFibre

/-- The original source atom is prime; no new primality hypothesis is imposed. -/
theorem unit_prime {N d ell : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeUnitCarrier N d l) : ell.Prime := by
  exact (mem_filter.mp (mem_filter.mp h).1).2.1

/-- This subtraction identity uses the source range bound, including at d=0. -/
theorem unit_complement {N d ell : ℕ} {l : List ℕ}
    (h : ell ∈ secondFunctionalFourPrimeUnitCarrier N d l) :
    ell = N - d * l.prod := by
  have he := (mem_filter.mp h).2
  have hle := FourPrimeUnit.carrier_le h
  omega

/-- The earlier product is masked; the last two primes are above the strict cutoff. -/
theorem unit_mem_iff {N d ell p q : ℕ} (pre : List ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    ell ∈ secondFunctionalFourPrimeUnitCarrier N d (pre ++ [p,q]) ↔
      ell.Prime ∧ ell + d * (pre ++ [p,q]).prod = N := by
  constructor
  · intro h
    have he := (mem_filter.mp h).2
    have hle := FourPrimeUnit.carrier_le h
    exact ⟨unit_prime h, by omega⟩
  · rintro ⟨hell,he⟩
    have hle : ell ≤ N := by omega
    have hsub : N - ell = d * (pre ++ [p,q]).prod := by omega
    apply mem_filter.mpr
    refine ⟨?_, hsub⟩
    change ell ∈ sourceSieveCarrier N (d * (pre ++ [p,q]).prod)
      (d * ((pre ++ [p,q]).take ((pre ++ [p,q]).length - 2)).prod * N)
      ((pre ++ [p,q]).getD ((pre ++ [p,q]).length - 2) 0)
    have ht : (pre ++ [p,q]).take ((pre ++ [p,q]).length - 2) = pre := by
      simp
    have hg : (pre ++ [p,q]).getD ((pre ++ [p,q]).length - 2) 0 = p := by
      simp
    rw [ht, hg]
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), hell, ?_, ?_⟩
    · rw [hsub]
    · rw [hsub]
      have hmask : Sifted (d * pre.prod * N) (d * pre.prod) (p : ℝ) := by
        intro r hr hc hz
        exact siftedLE_of_dvd_modulus (dvd_mul_right (d * pre.prod) N) _
          r hr hc hz.le
      have hs := (sifted_mul_iff (d * pre.prod * N) (d * pre.prod * p) q (p : ℝ)).mpr
        ⟨(sifted_mul_iff _ _ _ _).mpr ⟨hmask, sifted_prime_of_le hp le_rfl⟩,
          sifted_prime_of_le hq (by exact_mod_cast hpq)⟩
      simpa [List.prod_append, mul_assoc] using hs

/-- Exact singleton-or-empty source formula, valid even when d=0 or the product exceeds N. -/
theorem unit_eq {N d p q : ℕ} (pre : List ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    secondFunctionalFourPrimeUnitCarrier N d (pre ++ [p,q]) =
      if (N - d * (pre ++ [p,q]).prod).Prime then
        {N - d * (pre ++ [p,q]).prod} else ∅ := by
  ext ell
  rw [unit_mem_iff pre hp hq hpq]
  by_cases h : (N - d * (pre ++ [p,q]).prod).Prime
  · simp only [if_pos h, mem_singleton]
    have hpos := h.pos
    constructor
    · rintro ⟨_,he⟩
      omega
    · intro he
      exact ⟨he ▸ h, by omega⟩
  · simp only [if_neg h, notMem_empty, iff_false, not_and]
    intro hell he
    apply h
    have heq : ell = N - d * (pre ++ [p,q]).prod := by omega
    simpa only [← heq] using hell

theorem unit_card {N d p q : ℕ} (pre : List ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≤ q) :
    (secondFunctionalFourPrimeUnitCarrier N d (pre ++ [p,q])).card =
      if (N - d * (pre ++ [p,q]).prod).Prime then 1 else 0 := by
  rw [unit_eq pre hp hq hpq]
  split_ifs <;> simp

/-- All free natural prime labels, not a four-coordinate truncation. -/
def freeProduct {n : ℕ} {R : ℝ} (g : Fin n → primeSlabPrimes R) : ℕ :=
  ∏ j, (g j).val

theorem freeProduct_cast {n : ℕ} {R : ℝ} (g : Fin n → primeSlabPrimes R) :
    (freeProduct g : ℝ) = prefixProduct g := by
  simp [freeProduct, prefixProduct, Nat.cast_prod]

theorem fullList_prod {n : ℕ} {R : ℝ} (g : Fin n → primeSlabPrimes R) (q : ℕ) :
    (fullList ⟨g,q⟩).prod = freeProduct g * q := by
  simp [fullList, freeProduct, List.prod_ofFn]

/-- The old closed physical geometry with precisely the retained output-prime test. -/
noncomputable def filteredPhysical {n : ℕ} {R : ℝ} (N d : ℕ)
    (g : Fin n → primeSlabPrimes R) (j : Fin n) (H : ℝ) : Finset ℕ :=
  (physical (prefixProduct g) ((N : ℝ)/d) (g j).val H).filter
    fun q => (N - d * freeProduct g * q).Prime

theorem filtered_subset {N d n : ℕ} {R H : ℝ}
    (g : Fin n → primeSlabPrimes R) (j : Fin n) :
    filteredPhysical N d g j H ⊆ physical (prefixProduct g) ((N : ℝ)/d) (g j).val H :=
  filter_subset _ _

/-- Upgrading the existing full-list embedding recovers the original prime atom. -/
theorem injection_filtered {N d n : ℕ} {a B c e f R : ℝ} {cs : List ℕ}
    (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n)
    (geometry : ∀ x ∈ atoms N d a B c e f cs,
      ∃ y ∈ S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f),
        fullList y = x.1) :
    ∃ E : (atoms N d a B c e f cs) ↪
        (S.sigma (fun g => filteredPhysical N d g j f)),
      ∀ x, fullList (E x).val = x.val.1 := by
  obtain ⟨E,hE⟩ := injection_of_geometry S j geometry
  have hmem (x : atoms N d a B c e f cs) :
      (E x).val ∈ S.sigma (fun g => filteredPhysical N d g j f) := by
    obtain ⟨hg,hq⟩ := mem_sigma.mp (E x).property
    refine mem_sigma.mpr ⟨hg, mem_filter.mpr ⟨hq, ?_⟩⟩
    have hu := (mem_sigma.mp x.property).2
    have he := unit_complement hu
    rw [← hE x, fullList_prod, ← mul_assoc] at he
    exact he ▸ unit_prime hu
  let F (x : atoms N d a B c e f cs) : S.sigma (fun g => filteredPhysical N d g j f) :=
    ⟨(E x).val, hmem x⟩
  refine ⟨⟨F, ?_⟩, hE⟩
  intro x x' h
  apply E.injective
  apply Subtype.ext
  exact congrArg (fun z : S.sigma (fun g => filteredPhysical N d g j f) => z.val) h

theorem count_filtered {N d n : ℕ} {a B c e f R : ℝ} {cs : List ℕ}
    (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n)
    (geometry : ∀ x ∈ atoms N d a B c e f cs,
      ∃ y ∈ S.sigma (fun g => physical (prefixProduct g) ((N : ℝ)/d) (g j).val f),
        fullList y = x.1) :
    FourPrimeUnit.prefixTerm true N d a B c e f cs ≤
      ∑ g ∈ S, ((filteredPhysical N d g j f).card : ℝ) := by
  obtain ⟨E,_⟩ := injection_filtered S j geometry
  have hc := Fintype.card_le_of_injective E E.injective
  simp only [Fintype.card_coe] at hc
  rw [← atoms_card]
  have hc' : ((atoms N d a B c e f cs).card : ℝ) ≤
      (S.sigma (fun g => filteredPhysical N d g j f)).card := by exact_mod_cast hc
  simpa only [card_sigma, Nat.cast_sum] using hc'

theorem filtered_sum_le_old {N d n : ℕ} {R H : ℝ}
    (S : Finset (Fin n → primeSlabPrimes R)) (j : Fin n) :
    (∑ g ∈ S, ((filteredPhysical N d g j H).card : ℝ)) ≤
      ∑ g ∈ S, ((physical (prefixProduct g) ((N : ℝ)/d) (g j).val H).card : ℝ) := by
  apply sum_le_sum
  intro g _
  exact_mod_cast card_le_card (filtered_subset g j)

end Wu2008DoubleSieve.HighUnitPrimeOutput
