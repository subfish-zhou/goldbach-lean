import MathlibNt.SieveTheory.LiLiuPrereqWFSignedFamily
import MathlibNt.SieveTheory.LiLiuPrereqWFPrimeSquareMass

/-!
# The actual non-squarefree support of the unmasked family

The small Rosser factor is squarefree and its prime range is disjoint from
every large box. Consequently a repeated prime in a nonzero coefficient must
be a rough prime. This is a statement about the original full-integer weights;
no squarefree mask is applied and no preservation of well-factorability by a
mask is asserted.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

theorem signedSmallWeight_squarefree (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (r n : ℕ) (hn : signedSmallWeight upper P D ε r n ≠ 0) : Squarefree n := by
  unfold signedSmallWeight at hn
  split at hn
  · exact SmallRosser.upperSmallWeight_squarefree hn
  · exact SmallRosser.lowerSmallWeight_squarefree hn

/-- A square in the small range cannot occur in a separated convolution whose
small factor is supported on squarefree integers. -/
theorem separated_mul_not_small_prime_sq {B C : Finset ℕ}
    {f g : ArithmeticFunction ℝ} (hBC : Disjoint B C)
    (hg : PrimeSupported C g) (hf : ∀ n, f n ≠ 0 → Squarefree n)
    {n p : ℕ} (hn : (f * g) n ≠ 0) (hp : p.Prime) (hpB : p ∈ B) :
    ¬ p ^ 2 ∣ n := by
  rw [mul_apply] at hn
  obtain ⟨d, hd, hfg⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
  obtain ⟨hfd, hgd⟩ := mul_ne_zero_iff.mp hfg
  have hb0 : d.2 ≠ 0 := by
    rintro hz
    exact hgd (by simp [hz])
  have hpb : ¬ p ∣ d.2 := by
    intro hdiv
    exact Finset.disjoint_left.mp hBC hpB
      (hg d.2 hgd (Nat.mem_primeFactors.mpr ⟨hp, hdiv, hb0⟩))
  have hcop : (p ^ 2).Coprime d.2 := (hp.coprime_pow_of_not_dvd hpb).symm
  intro hsq
  rw [← (Nat.mem_divisorsAntidiagonal.mp hd).1] at hsq
  have hsmall := hcop.dvd_of_dvd_mul_right hsq
  exact (Nat.squarefree_iff_prime_squarefree.mp (hf d.1 hfd) p hp)
    (by simpa only [pow_two] using hsmall)

/-- All repeated primes of a nonzero family coefficient lie above the genuine
small-prime cutoff, irrespective of the tag or its parity. -/
theorem signedFamilyTerm_not_small_prime_sq (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (t : List ℕ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    {n p : ℕ} (hn : signedFamilyTerm upper P D ε t n ≠ 0)
    (hp : p.Prime) (hps : p ∈ geometricSmallPrimes P D ε) : ¬ p ^ 2 ∣ n := by
  have hc :
      (signedSmallWeight upper P D ε t.length *
        boxProduct t.toFinset (geometricPrimeBox P D ε (ε ^ 9)) t.count) n ≠ 0 := by
    intro hz
    exact hn (by simp only [signedFamilyTerm, smul_map, smul_eq_mul,
      geometricBoxTerm, hz, mul_zero])
  exact separated_mul_not_small_prime_sq
    (geometricSmallPrimes_disjoint P hD (pow_nonneg hε _) t.toFinset)
    (boxProduct_primeSupported _ _ _)
    (signedSmallWeight_squarefree upper P D ε t.length) hc hp hps

theorem signedFamilyTerm_squarefree_dvd_primorial (upper : Bool) (P : Finset ℕ)
    (D ε : ℝ) (t : List ℕ) {n : ℕ}
    (hn : signedFamilyTerm upper P D ε t n ≠ 0) (hsf : Squarefree n) :
    n ∣ P.prod id := by
  have hsub := signedFamilyTerm_primeSupported upper P D ε t n hn
  simpa only [id_eq, Nat.prod_primeFactors_of_squarefree hsf] using
    Finset.prod_dvd_prod_of_subset n.primeFactors P id hsub

/-- The precise exceptional support when replacing the primorial-restricted
remainder by the full-modulus remainder. -/
theorem signedFamilyTerm_exceptional_support (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (t : List ℕ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    {n : ℕ} (hn : signedFamilyTerm upper P D ε t n ≠ 0)
    (hnot : ¬ n ∣ P.prod id) :
    ∃ p ∈ P \ geometricSmallPrimes P D ε, p.Prime ∧
      D ^ (ε ^ 2) ≤ (p : ℝ) ∧ p ^ 2 ∣ n := by
  have hnsf : ¬ Squarefree n :=
    fun hs => hnot (signedFamilyTerm_squarefree_dvd_primorial upper P D ε t hn hs)
  rw [Nat.squarefree_iff_prime_squarefree] at hnsf
  push Not at hnsf
  obtain ⟨p, hp, hsq⟩ := hnsf
  have hsq' : p ^ 2 ∣ n := by simpa only [pow_two] using hsq
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hn (by simp)
  have hpP := signedFamilyTerm_primeSupported upper P D ε t n hn
    (Nat.mem_primeFactors.mpr ⟨hp, (dvd_mul_right p p).trans hsq, hn0⟩)
  have hps : p ∉ geometricSmallPrimes P D ε := by
    intro hmem
    exact signedFamilyTerm_not_small_prime_sq upper P t hD hε hn hp hmem hsq'
  have hlo : D ^ (ε ^ 2) ≤ (p : ℝ) := by
    by_contra h
    exact hps (Finset.mem_filter.mpr ⟨hpP, hp, lt_of_not_ge h⟩)
  exact ⟨p, Finset.mem_sdiff.mpr ⟨hpP, hps⟩, hp, hlo, hsq'⟩

/-- Each fixed unmasked member has a small canonical density outside the
primorial. The bound is uniform in the tag and uses the real rough cutoff. -/
theorem signedFamilyTerm_exceptional_mass_le (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (t : List ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (ht : t ∈ signedTags upper P D ε label) (T : ℕ) :
    (∑ n ∈ (Icc 1 T).filter (fun n => ¬ n ∣ P.prod id),
      |signedFamilyTerm upper P D ε t n| * (n.totient : ℝ)⁻¹) ≤
        (4 / D ^ (ε ^ 2)) * (1 + Real.log T) ^ 2 := by
  let R := P \ geometricSmallPrimes P D ε
  let R' := R.filter Nat.Prime
  have hf := signedTags_common_wellFactorable upper P label hD hε hεsmall t ht
  have hsub : ∀ n ∈ (Icc 1 T).filter (fun n => ¬ n ∣ P.prod id),
      signedFamilyTerm upper P D ε t n ≠ 0 → n ∈ PrimeSquareMass.badModuli T R' := by
    intro n hn hfn
    obtain ⟨p, hp, hprime, _, hsq⟩ := signedFamilyTerm_exceptional_support upper P t
      (by linarith) hε.le hfn (mem_filter.mp hn).2
    exact mem_filter.mpr ⟨(mem_filter.mp hn).1,
      p, mem_filter.mpr ⟨hp, hprime⟩, hsq⟩
  calc
    _ ≤ ∑ n ∈ PrimeSquareMass.badModuli T R', (n.totient : ℝ)⁻¹ := by
      apply sum_le_sum_of_subset_of_nonneg
        (s := ((Icc 1 T).filter (fun n => ¬ n ∣ P.prod id)).filter
          (fun n => signedFamilyTerm upper P D ε t n ≠ 0)) ?_ ?_
        |>.trans' ?_
      · intro n hn
        exact hsub n (mem_filter.mp hn).1 (mem_filter.mp hn).2
      · intro n _ _
        positivity
      · calc
          _ = ∑ n ∈ ((Icc 1 T).filter (fun n => ¬ n ∣ P.prod id)).filter
              (fun n => signedFamilyTerm upper P D ε t n ≠ 0),
              |signedFamilyTerm upper P D ε t n| * (n.totient : ℝ)⁻¹ := by
            simp only [sum_filter]
            apply sum_congr rfl
            intro n _
            split_ifs <;> simp_all
          _ ≤ _ := sum_le_sum fun n _ => by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right (hf.2.1 n) (by positivity : 0 ≤ (n.totient : ℝ)⁻¹)
    _ ≤ _ := PrimeSquareMass.badModuli_mass_le_log T R' (D ^ (ε ^ 2))
      (Real.rpow_pos_of_pos (by linarith) _) (fun p hp => (mem_filter.mp hp).2)
      (fun p hp => by
        have hp' := mem_filter.mp hp
        have hR := mem_sdiff.mp hp'.1
        by_contra h
        exact hR.2 (mem_filter.mpr ⟨hR.1, hp'.2, lt_of_not_ge h⟩))

#check signedFamilyTerm_exceptional_support
#print axioms signedFamilyTerm_exceptional_support
#check signedFamilyTerm_exceptional_mass_le
#print axioms signedFamilyTerm_exceptional_mass_le

end MathlibNt.SieveTheory.LiLiuPrereqWF
