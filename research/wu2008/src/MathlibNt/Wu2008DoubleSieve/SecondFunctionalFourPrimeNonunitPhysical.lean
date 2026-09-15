import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeNonunit
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitPhysical

namespace Wu2008DoubleSieve.FourPrimeNonunit
open Finset
open scoped Classical

noncomputable def lastLower (c e : ℕ → ℝ) (cs : List ℕ) (d : ℕ) : ℝ :=
  if cs.getD 3 0 = 2 then c d else e d

noncomputable def lastUpper (e f : ℕ → ℝ) (cs : List ℕ) (d : ℕ) : ℝ :=
  if cs.getD 3 0 = 2 then e d else f d

noncomputable def physicalLower (c e : ℕ → ℝ) (cs : List ℕ) (x : Gamma16Profile) : ℝ :=
  max (x.2.1 : ℝ) ((Nat.ceil (lastLower c e cs x.1) : ℝ) - 1)

noncomputable def physicalUpper (N : ℕ) (e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) : ℝ :=
  min (lastUpper e f cs x.1) ((N : ℝ) / gamma16Cofactor x)

/-- No output-prime or additional coprimality screen occurs here. -/
noncomputable def rawFibre (N : ℕ) (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) : Finset ℕ :=
  (range (N+1)).filter fun q => q.Prime ∧ x.2.1 < q ∧
    lastLower c e cs x.1 ≤ (q : ℝ) ∧ (q : ℝ) ≤ lastUpper e f cs x.1 ∧
    gamma16Cofactor x * q ≤ N

theorem fibre_eq_raw_filter (N : ℕ) (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) :
    fibre N c e f cs x = (rawFibre N c e f cs x).filter
      (fun q => (N-gamma16Cofactor x*q).Prime) := by
  ext q
  simp only [fibre, rawFibre, mem_filter]
  dsimp only [lastLower, lastUpper]
  tauto

theorem rawFibre_eq_profile {N : ℕ} (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) (hx : 0 < gamma16Cofactor x) :
    rawFibre N c e f cs x =
      omega3ProfilePrimes N (physicalLower c e cs x) (physicalUpper N e f cs x) := by
  have hxR : (0 : ℝ) < gamma16Cofactor x := by exact_mod_cast hx
  ext q
  simp only [rawFibre, omega3ProfilePrimes, mem_filter, physicalLower, physicalUpper,
    max_lt_iff, le_min_iff, HighNonunit.ceil_strict_lower, le_div_iff₀ hxR]
  have ho : x.2.1 < q ↔ (x.2.1 : ℝ) < q := by exact_mod_cast Iff.rfl
  have hc : gamma16Cofactor x * q ≤ N ↔ (q : ℝ) * gamma16Cofactor x ≤ N := by
    rw [mul_comm]
    exact_mod_cast Iff.rfl
  rw [ho, hc]
  tauto

/-- The original coordinates, mask, ordering and colours remain unchanged. -/
theorem profile_data {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} {x : Gamma16Profile}
    (hx : x ∈ profiles N W a b c e f cs) :
    x.1 ∈ boxConvolutionSupport W ∧
    x.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧
    x.2.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧
    x.2.2.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧
    x.2.2.2.2 < N+1 ∧ 2 ≤ x.2.2.2.2 ∧
    Sifted (x.1*x.2.2.2.1*x.2.2.1*N) x.2.2.2.2 x.2.1 ∧
    x.2.2.2.1 < x.2.2.1 ∧ x.2.2.1 < x.2.1 ∧
    [x.2.2.2.1,x.2.2.1,x.2.1].map
      (secondFunctionalMotherColour (b x.1) (c x.1) (e x.1)) = cs.take 3 ∧
    gamma16Cofactor x * x.2.1 ≤ N := by
  exact mem_profiles.mp hx

theorem profile_cofactor_pos {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) {x : Gamma16Profile}
    (hx : x ∈ profiles N W a b c e f cs) : 0 < gamma16Cofactor x := by
  obtain ⟨hxd,h3,h2,h1,_,hn,_⟩ := profile_data hx
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hd _ hxd) (by omega))
    (mem_primeWindow.mp h1).1.pos) (mem_primeWindow.mp h2).1.pos)
    (mem_primeWindow.mp h3).1.pos

noncomputable def physicalLabels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset Gamma16Profile :=
  (profiles N W a b c e f cs).filter fun x =>
    physicalLower c e cs x ≤ physicalUpper N e f cs x

theorem physical_cap {N : ℕ} (e f : ℕ → ℝ) (cs : List ℕ) (x : Gamma16Profile)
    (hx : 0 < gamma16Cofactor x) :
    (gamma16Cofactor x : ℝ) * physicalUpper N e f cs x ≤ N := by
  have hxR : (0 : ℝ) < gamma16Cofactor x := by exact_mod_cast hx
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hxR).mp (min_le_right _ _))

noncomputable def physicalFamily {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    LabelledPhysical.Family Gamma16Profile N where
  labels := physicalLabels N W a b c e f cs
  weight := fun x => (convolutionCoeff W x.1 : ℝ)
  cofactor := gamma16Cofactor
  lower := physicalLower c e cs
  upper := physicalUpper N e f cs
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := by
    intro x hx
    obtain ⟨hx,hfeas⟩ := mem_filter.mp hx
    have hpos := profile_cofactor_pos hd hx
    refine ⟨hpos, ?_, hfeas, physical_cap e f cs x hpos⟩
    exact le_trans (by exact_mod_cast (mem_primeWindow.mp (profile_data hx).2.1).1.two_le)
      (le_max_left _ _)

theorem rawFibre_empty_of_deleted {N : ℕ} (c e f : ℕ → ℝ) (cs : List ℕ)
    (x : Gamma16Profile) (hx : 0 < gamma16Cofactor x)
    (hdel : ¬ physicalLower c e cs x ≤ physicalUpper N e f cs x) :
    rawFibre N c e f cs x = ∅ := by
  rw [rawFibre_eq_profile c e f cs x hx]
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨_,_,hl,hu⟩ := mem_filter.mp hq
  exact hdel (hl.le.trans hu)

/-- Arbitrary tests on the literal original labels, not on quotient products. -/
theorem physical_sum_dictionary {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) (test : Gamma16Profile → ℕ → ℝ) :
    (∑ x ∈ (physicalFamily N W a b c e f cs hd).labels,
      ∑ q ∈ (physicalFamily N W a b c e f cs hd).primes x, test x q) =
    ∑ x ∈ profiles N W a b c e f cs, ∑ q ∈ rawFibre N c e f cs x, test x q := by
  change (∑ x ∈ physicalLabels N W a b c e f cs,
    ∑ q ∈ omega3ProfilePrimes N (physicalLower c e cs x)
      (physicalUpper N e f cs x), test x q) = _
  calc
    _ = ∑ x ∈ physicalLabels N W a b c e f cs,
        ∑ q ∈ rawFibre N c e f cs x, test x q := by
      apply sum_congr rfl
      intro x hx
      rw [rawFibre_eq_profile c e f cs x (profile_cofactor_pos hd (mem_filter.mp hx).1)]
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro x hx hdel
      have hh : ¬ physicalLower c e cs x ≤ physicalUpper N e f cs x := by
        intro h
        exact hdel (mem_filter.mpr ⟨hx,h⟩)
      rw [rawFibre_empty_of_deleted c e f cs x (profile_cofactor_pos hd hx) hh, sum_empty]

theorem physical_mass_dictionary {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (physicalFamily N W a b c e f cs hd).mass =
    ∑ x ∈ profiles N W a b c e f cs,
      (convolutionCoeff W x.1 : ℝ) * (rawFibre N c e f cs x).card := by
  simpa only [LabelledPhysical.Family.mass, physicalFamily, sum_const,
    nsmul_eq_mul, mul_comm] using
    (physical_sum_dictionary (a := a) (b := b) (c := c) (e := e) (f := f)
      (cs := cs) hd (fun x _ => (convolutionCoeff W x.1 : ℝ)))

theorem physical_primeMass_dictionary {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (physicalFamily N W a b c e f cs hd).primeMass = envelope N W a b c e f cs := by
  have h := physical_sum_dictionary (N := N) (a := a) (b := b) (c := c)
    (e := e) (f := f) (cs := cs) hd
    (fun x q => if (N-gamma16Cofactor x*q).Prime then (convolutionCoeff W x.1 : ℝ) else 0)
  simp only [← sum_filter, sum_const, nsmul_eq_mul, ← fibre_eq_raw_filter] at h
  simpa only [LabelledPhysical.Family.primeMass, envelope, physicalFamily, mul_comm] using h

theorem penultimate_dvd (x : Gamma16Profile) : x.2.1 ∣ gamma16Cofactor x :=
  dvd_mul_left _ _

end Wu2008DoubleSieve.FourPrimeNonunit
