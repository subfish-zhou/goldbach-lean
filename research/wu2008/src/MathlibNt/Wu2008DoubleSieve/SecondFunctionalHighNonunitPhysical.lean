import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitWindowBounds
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLabelledRelativeRoughness

namespace Wu2008DoubleSieve.HighNonunit
open Finset
open scoped Classical

noncomputable def physicalLower (e : ℕ → ℝ) (x : Profile) : ℝ :=
  max (x.2.2.1 : ℝ) ((Nat.ceil (e x.1) : ℝ) - 1)

noncomputable def physicalUpper (N : ℕ) (f : ℕ → ℝ) (x : Profile) : ℝ :=
  min (f x.1) ((N : ℝ) / cofactor x)

noncomputable def rawFibre (N : ℕ) (e f : ℕ → ℝ) (x : Profile) : Finset ℕ :=
  (range (N+1)).filter fun q => q.Prime ∧ x.2.2.1 < q ∧
    e x.1 ≤ (q : ℝ) ∧ (q : ℝ) ≤ f x.1 ∧ cofactor x * q ≤ N

theorem fibre_eq_raw_filter (N : ℕ) (e f : ℕ → ℝ) (x : Profile) :
    fibre N e f x = (rawFibre N e f x).filter (fun q => (N-cofactor x*q).Prime) := by
  ext q
  simp only [fibre, rawFibre, mem_filter]
  tauto

theorem ceil_strict_lower (a : ℝ) (q : ℕ) :
    (Nat.ceil a : ℝ) - 1 < (q : ℝ) ↔ a ≤ (q : ℝ) := by
  have hn : (Nat.ceil a : ℝ) - 1 < (q : ℝ) ↔ Nat.ceil a ≤ q := by
    constructor
    · intro h
      have : (Nat.ceil a : ℝ) < (q+1 : ℕ) := by push_cast; linarith
      exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
    · intro h
      have : (Nat.ceil a : ℝ) ≤ q := by exact_mod_cast h
      linarith
  exact hn.trans Nat.ceil_le

theorem rawFibre_eq_profile {N : ℕ} (e f : ℕ → ℝ) (x : Profile)
    (hx : 0 < cofactor x) :
    rawFibre N e f x = omega3ProfilePrimes N (physicalLower e x) (physicalUpper N f x) := by
  have hxR : (0 : ℝ) < cofactor x := by exact_mod_cast hx
  ext q
  simp only [rawFibre, omega3ProfilePrimes, mem_filter, physicalLower, physicalUpper,
    max_lt_iff, le_min_iff, ceil_strict_lower, le_div_iff₀ hxR]
  have ho : x.2.2.1 < q ↔ (x.2.2.1 : ℝ) < q := by exact_mod_cast Iff.rfl
  have hc : cofactor x * q ≤ N ↔ (q : ℝ) * cofactor x ≤ N := by
    rw [mul_comm]
    exact_mod_cast Iff.rfl
  rw [ho, hc]
  tauto

theorem profile_data {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ} {x : Profile}
    (hx : x ∈ profiles N W a b c e f cs) :
    x.1 ∈ boxConvolutionSupport W ∧
    (∀ r ∈ x.2.1, r ∈ primeWindow N (a x.1) (f x.1)) ∧
    x.2.2.1 ∈ primeWindow N (a x.1) (f x.1) ∧
    2 ≤ x.2.2.2 ∧ Sifted (x.1*x.2.1.prod*N) x.2.2.2 x.2.2.1 ∧
    cofactor x * x.2.2.1 ≤ N := by
  obtain ⟨hd, hpn⟩ := mem_sigma.mp hx
  obtain ⟨ht, hrest⟩ := mem_sigma.mp hpn
  obtain ⟨hmem, hn, hs, _, _, hcap⟩ := mem_filter.mp hrest
  exact ⟨hd, ((secondFunctionalMother_tuple_mem _ _ _).mp ht).2.2,
    (mem_product.mp hmem).1, hn, hs, hcap⟩

theorem profile_cofactor_pos {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) {x : Profile}
    (hx : x ∈ profiles N W a b c e f cs) : 0 < cofactor x := by
  obtain ⟨hxd, hpre, hp, hn, _⟩ := profile_data hx
  apply Nat.mul_pos (Nat.mul_pos (hd _ hxd) (by omega))
  apply List.prod_pos
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · exact (mem_primeWindow.mp (hpre r hr)).1.pos
  · have : r = x.2.2.1 := by simpa using hr
    subst r
    exact (mem_primeWindow.mp hp).1.pos

noncomputable def physicalLabels {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ) : Finset Profile :=
  (profiles N W a b c e f cs).filter fun x => physicalLower e x ≤ physicalUpper N f x

theorem physical_cap {N : ℕ} (f : ℕ → ℝ) (x : Profile) (hx : 0 < cofactor x) :
    (cofactor x : ℝ) * physicalUpper N f x ≤ N := by
  have hxR : (0 : ℝ) < cofactor x := by exact_mod_cast hx
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hxR).mp (min_le_right _ _))

noncomputable def physicalFamily {i : ℕ} (N : ℕ) (W : Fin i → Finset ℕ)
    (a b c e f : ℕ → ℝ) (cs : List ℕ)
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) : LabelledPhysical.Family Profile N where
  labels := physicalLabels N W a b c e f cs
  weight := fun x => (convolutionCoeff W x.1 : ℝ)
  cofactor := cofactor
  lower := physicalLower e
  upper := physicalUpper N f
  weight_nonneg := fun _ _ => Nat.cast_nonneg _
  geometry := by
    intro x hx
    obtain ⟨hx, hfeas⟩ := mem_filter.mp hx
    have hpos := profile_cofactor_pos hd hx
    refine ⟨hpos, ?_, hfeas, physical_cap f x hpos⟩
    exact le_trans (by exact_mod_cast (mem_primeWindow.mp (profile_data hx).2.2.1).1.two_le)
      (le_max_left _ _)

theorem rawFibre_empty_of_deleted {N : ℕ} (e f : ℕ → ℝ) (x : Profile)
    (hx : 0 < cofactor x) (hdel : ¬ physicalLower e x ≤ physicalUpper N f x) :
    rawFibre N e f x = ∅ := by
  rw [rawFibre_eq_profile e f x hx]
  apply eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨_, _, hl, hu⟩ := mem_filter.mp hq
  exact hdel (hl.le.trans hu)

/-- Arbitrary profile-dependent real tests: deletion is justified fibrewise, not by a bound. -/
theorem physical_sum_dictionary {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) (test : Profile → ℕ → ℝ) :
    (∑ x ∈ (physicalFamily N W a b c e f cs hd).labels,
      ∑ q ∈ (physicalFamily N W a b c e f cs hd).primes x, test x q) =
    ∑ x ∈ profiles N W a b c e f cs, ∑ q ∈ rawFibre N e f x, test x q := by
  change (∑ x ∈ physicalLabels N W a b c e f cs,
    ∑ q ∈ omega3ProfilePrimes N (physicalLower e x) (physicalUpper N f x), test x q) = _
  calc
    _ = ∑ x ∈ physicalLabels N W a b c e f cs, ∑ q ∈ rawFibre N e f x, test x q := by
      apply sum_congr rfl
      intro x hx
      rw [rawFibre_eq_profile e f x (profile_cofactor_pos hd (mem_filter.mp hx).1)]
    _ = _ := by
      apply sum_subset (filter_subset _ _)
      intro x hx hdel
      have hh : ¬ physicalLower e x ≤ physicalUpper N f x := by
        intro h
        exact hdel (mem_filter.mpr ⟨hx, h⟩)
      rw [rawFibre_empty_of_deleted e f x (profile_cofactor_pos hd hx) hh, sum_empty]

theorem physical_mass_dictionary {i N : ℕ} {W : Fin i → Finset ℕ}
    {a b c e f : ℕ → ℝ} {cs : List ℕ}
    (hd : ∀ d ∈ boxConvolutionSupport W, 0 < d) :
    (physicalFamily N W a b c e f cs hd).mass =
    ∑ x ∈ profiles N W a b c e f cs,
      (convolutionCoeff W x.1 : ℝ) * (rawFibre N e f x).card := by
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
    (fun x q => if (N-cofactor x*q).Prime then (convolutionCoeff W x.1 : ℝ) else 0)
  simp only [← sum_filter, sum_const, nsmul_eq_mul, ← fibre_eq_raw_filter] at h
  simpa only [LabelledPhysical.Family.primeMass, envelope, physicalFamily, mul_comm] using h

/-- The redundant range cap follows from positivity and the physical product cap. -/
theorem rawFibre_mem_iff {N : ℕ} (e f : ℕ → ℝ) (x : Profile)
    (hx : 0 < cofactor x) (q : ℕ) :
    q ∈ rawFibre N e f x ↔ q.Prime ∧ x.2.2.1 < q ∧
      e x.1 ≤ (q : ℝ) ∧ (q : ℝ) ≤ f x.1 ∧ cofactor x*q ≤ N := by
  simp only [rawFibre, mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · exact And.right
  · intro h
    exact ⟨(Nat.le_mul_of_pos_left q hx).trans h.2.2.2.2, h⟩

theorem penultimate_dvd (x : Profile) : x.2.2.1 ∣ cofactor x := by
  exact (List.dvd_prod (by simp : x.2.2.1 ∈ x.2.1 ++ [x.2.2.1])).trans
    (dvd_mul_left _ _)

theorem fibre_empty_of_deleted {N : ℕ} (e f : ℕ → ℝ) (x : Profile)
    (hx : 0 < cofactor x) (hdel : ¬ physicalLower e x ≤ physicalUpper N f x) :
    fibre N e f x = ∅ := by
  rw [fibre_eq_raw_filter, rawFibre_empty_of_deleted e f x hx hdel, filter_empty]

end Wu2008DoubleSieve.HighNonunit
