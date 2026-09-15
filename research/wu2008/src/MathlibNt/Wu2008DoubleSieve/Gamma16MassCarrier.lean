import MathlibNt.Wu2008DoubleSieve.Gamma16Quotient
import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteRough
import MathlibNt.Wu2008DoubleSieve.PrimeOrderedQuadratureTriple

/-!
# Four-prime mass carrier with a positive last-prime diagonal enlargement

The first three primes are strict. The last comparison is p3 <= p4,
as required by the existing triple quadrature. This is an upper
enlargement, not an equality with the original strict/copN carrier.
-/

namespace Wu2008DoubleSieve

open Finset Real LiLiuPrereqBuchstab
open scoped Classical

abbrev Gamma16MassTuple := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

def gamma16MassProduct (p : Gamma16MassTuple) : ℕ := p.2.1 * p.2.2.1 * p.2.2.2 * p.1

noncomputable def gamma16MassPrimes (R : ℝ) : Finset Gamma16MassTuple :=
  (primesIcc (R ^ gamma16Alpha) (R ^ gamma16Beta)).sigma fun p4 =>
    (primesIcc (R ^ gamma16Alpha) p4).sigma fun p1 =>
      (primesIoc p1 p4).sigma fun p2 => primesIoc p2 p4

noncomputable def gamma16MassScale (N d : ℕ) (p : Gamma16MassTuple) : ℝ :=
  (N : ℝ) / ((d : ℝ) * p.2.1 * p.2.2.1 * p.2.2.2 * p.1)

def Gamma16RoughExceptions (p1 p2 p3 n : ℕ) : Prop :=
  ∀ q : ℕ, q.Prime → (q : ℝ) < p3 → q ≠ p1 → q ≠ p2 → ¬q ∣ n

noncomputable def gamma16MassNFibre (N d : ℕ) (p : Gamma16MassTuple) : Finset ℕ :=
  (range (N + 1)).filter fun n => 0 < n ∧ d * gamma16MassProduct p * n ≤ N ∧
    Gamma16RoughExceptions p.2.1 p.2.2.1 p.2.2.2 n

theorem gamma16_mass_prime_bounds {R : ℝ} (hR : 0 ≤ R) {p : Gamma16MassTuple}
    (hp : p ∈ gamma16MassPrimes R) :
    p.1.Prime ∧ p.2.1.Prime ∧ p.2.2.1.Prime ∧ p.2.2.2.Prime ∧
      R ^ gamma16Alpha ≤ (p.2.1 : ℝ) ∧ p.2.1 < p.2.2.1 ∧
      p.2.2.1 < p.2.2.2 ∧ p.2.2.2 ≤ p.1 ∧ (p.1 : ℝ) ≤ R ^ gamma16Beta := by
  obtain ⟨h4, hp⟩ := mem_sigma.mp hp
  obtain ⟨h1, hp⟩ := mem_sigma.mp hp
  obtain ⟨h2, h3⟩ := mem_sigma.mp hp
  have h4' := (mem_primesIcc (rpow_nonneg hR _)).mp h4
  have h1' := (mem_primesIcc (Nat.cast_nonneg p.1)).mp h1
  have h2' := (mem_primesIoc (Nat.cast_nonneg p.1)).mp h2
  have h3' := (mem_primesIoc (Nat.cast_nonneg p.1)).mp h3
  exact ⟨h4'.1, h1'.1, h2'.1, h3'.1, h1'.2.1,
    by exact_mod_cast h2'.2.1, by exact_mod_cast h3'.2.1,
    by exact_mod_cast h3'.2.2, h4'.2.2⟩

theorem gamma16_mass_unit_iff {N d : ℕ} {p : Gamma16MassTuple} {R : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hp : p ∈ gamma16MassPrimes R) :
    1 ∈ gamma16MassNFibre N d p ↔ 1 ≤ gamma16MassScale N d p := by
  have h := gamma16_mass_prime_bounds hR hp
  have hprod : 0 < d * gamma16MassProduct p := by
    dsimp [gamma16MassProduct]
    exact Nat.mul_pos hd (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos h.2.1.pos h.2.2.1.pos)
      h.2.2.2.1.pos) h.1.pos)
  have hprodR : (0 : ℝ) < (d : ℝ) * p.2.1 * p.2.2.1 * p.2.2.2 * p.1 := by
    exact_mod_cast (show 0 < d * p.2.1 * p.2.2.1 * p.2.2.2 * p.1 by
      simpa only [gamma16MassProduct, mul_assoc] using hprod)
  have hsize : 1 ≤ gamma16MassScale N d p ↔ d * gamma16MassProduct p ≤ N := by
    rw [gamma16MassScale, le_div_iff₀ hprodR, one_mul]
    norm_cast
    simp only [gamma16MassProduct, mul_assoc]
  rw [hsize]
  constructor
  · intro h
    simpa only [mul_one] using (mem_filter.mp h).2.2.1
  · intro hs
    refine mem_filter.mpr ⟨mem_range.mpr (by omega), by decide, by simpa only [mul_one] using hs, ?_⟩
    intro q hq _ _ _ hq1
    exact hq.not_dvd_one hq1

theorem gamma16_mass_fibre_rough {N d : ℕ} {p : Gamma16MassTuple} {R : ℝ}
    (hd : 0 < d) (hR : 0 ≤ R) (hp : p ∈ gamma16MassPrimes R) :
    (gamma16MassNFibre N d p).card ≤
      roughCount (gamma16MassScale N d p) p.2.2.2 +
        ⌊gamma16MassScale N d p / p.2.1⌋₊ + ⌊gamma16MassScale N d p / p.2.2.1⌋₊ := by
  have hb := gamma16_mass_prime_bounds hR hp
  have hD : (0 : ℝ) < (d : ℝ) * p.2.1 * p.2.2.1 * p.2.2.2 * p.1 := by
    have h4 := hb.1.pos
    have h1 := hb.2.1.pos
    have h2 := hb.2.2.1.pos
    have h3 := hb.2.2.2.1.pos
    positivity
  have hsub : gamma16MassNFibre N d p ⊆
      (roughNumbers (gamma16MassScale N d p) p.2.2.2 ∪
        omega3XPositiveMultiples (gamma16MassScale N d p) p.2.1) ∪
        omega3XPositiveMultiples (gamma16MassScale N d p) p.2.2.1 := by
    intro n hn
    obtain ⟨_, hn0, hnsize, hnrough⟩ := mem_filter.mp hn
    have hnx : (n : ℝ) ≤ gamma16MassScale N d p := by
      rw [gamma16MassScale, le_div_iff₀ hD]
      exact_mod_cast (show n * (d * p.2.1 * p.2.2.1 * p.2.2.2 * p.1) ≤ N by
        simpa only [gamma16MassProduct, mul_assoc, mul_left_comm, mul_comm] using hnsize)
    by_cases h1 : p.2.1 ∣ n
    · exact mem_union_left _ (mem_union_right _
        (mem_omega3XPositiveMultiples.mpr ⟨hn0, hnx, h1⟩))
    by_cases h2 : p.2.2.1 ∣ n
    · exact mem_union_right _ (mem_omega3XPositiveMultiples.mpr ⟨hn0, hnx, h2⟩)
    apply mem_union_left _ (mem_union_left _ (mem_roughNumbers.mpr ⟨hn0, hnx, ?_⟩))
    apply rough_iff_no_small_prime.mpr
    intro q hq hsmall hqn
    by_cases he1 : q = p.2.1
    · exact h1 (he1 ▸ hqn)
    by_cases he2 : q = p.2.2.1
    · exact h2 (he2 ▸ hqn)
    exact hnrough q hq hsmall he1 he2 hqn
  have hc := (card_le_card hsub).trans
    ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
  have hx : 0 ≤ gamma16MassScale N d p := by unfold gamma16MassScale; positivity
  rw [omega3XPositiveMultiples_card hx hb.2.1.pos,
    omega3XPositiveMultiples_card hx hb.2.2.1.pos] at hc
  exact hc

end Wu2008DoubleSieve
