import MathlibNt.Wu2008DoubleSieve.Omega3LabelsFibre

/-! # Actual finite switching loss for each selected triple -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def omega3GoodOriginalFibre (N d p1 p2 p3 : ℕ) (Z : ℝ) : Finset ℕ :=
  (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
    fun ell => ¬Omega3BadD N d ell ∧ ¬ell ∣ N ∧ Z ≤ (ell : ℝ)

noncomputable def omega3SiftedSwitchedFibre (N d p1 p2 p3 : ℕ) (Z : ℝ) : Finset ℕ :=
  (omega3SwitchedFibre N d p1 p2 p3).filter
    fun n => Sifted N (N - omega3Cofactor d p1 p2 n * p3) Z

theorem omega3_good_original_injects {N d p1 p2 p3 : ℕ} {Z : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d)
    (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N) :
    (omega3GoodOriginalFibre N d p1 p2 p3 Z).card ≤
      (omega3SiftedSwitchedFibre N d p1 p2 p3 Z).card := by
  apply card_le_card_of_injOn (omega3Quotient N d p1 p2 p3)
  · intro ell hell
    obtain ⟨hsrc, hgoodd, hgoodN, hlarge⟩ := mem_filter.mp hell
    obtain ⟨hb, hp, hdiv, hs⟩ := mem_filter.mp hsrc
    have hle : ell ≤ N := by simpa using mem_range.mp hb
    have hlt := omega3_prime_output_lt hN heven hp hle
    obtain ⟨hn, _, hout, hsize⟩ := omega3_quotient_equation hlt hdiv
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨?_, hn, hsize, ?_⟩, ?_⟩
    · exact (mem_filter.mp (omega3_quotient_mem hN heven hsrc)).1
    · exact omega3_strengthened_of_source hd h1 h1N h2N hp hle hdiv hs hgoodd hgoodN
    · rw [← hout]
      exact sifted_prime_of_le hp hlarge
  · intro a ha b hb hab
    have ha' := mem_filter.mp (mem_filter.mp ha).1
    have hb' := mem_filter.mp (mem_filter.mp hb).1
    have hla := omega3_prime_output_lt hN heven ha'.2.1 (by
      simpa using mem_range.mp ha'.1)
    have hlb := omega3_prime_output_lt hN heven hb'.2.1 (by
      simpa using mem_range.mp hb'.1)
    rw [(omega3_quotient_equation hla ha'.2.2.1).2.2.1,
      (omega3_quotient_equation hlb hb'.2.2.1).2.2.1, hab]

noncomputable def omega3BadDFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
    (Omega3BadD N d)

noncomputable def omega3BadNFibre (N d p1 p2 p3 : ℕ) : Finset ℕ :=
  (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
    fun ell => ell ∣ N

noncomputable def omega3SmallOutputFibre (N d p1 p2 p3 : ℕ) (Z : ℝ) : Finset ℕ :=
  (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
    fun ell => (ell : ℝ) < Z

/-- The three losses are actual subsets of the original source carrier.
They are not assumed negligible here and may overlap. -/
theorem omega3_fibre_switching_bound {N d p1 p2 p3 : ℕ} {Z : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d)
    (h1 : p1.Prime) (h1N : p1.Coprime N) (h2N : p2.Coprime N) :
    (sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).card ≤
      (omega3SiftedSwitchedFibre N d p1 p2 p3 Z).card +
      (omega3BadDFibre N d p1 p2 p3).card +
      (omega3BadNFibre N d p1 p2 p3).card +
      (omega3SmallOutputFibre N d p1 p2 p3 Z).card := by
  have hcover :
      sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ) ⊆
        ((omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3) ∪
          omega3BadNFibre N d p1 p2 p3) ∪ omega3SmallOutputFibre N d p1 p2 p3 Z := by
    intro ell hell
    by_cases hd' : Omega3BadD N d ell
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hell, hd'⟩)))
    by_cases hN' : ell ∣ N
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hell, hN'⟩))
    by_cases hZ : (ell : ℝ) < Z
    · exact mem_union_right _ (mem_filter.mpr ⟨hell, hZ⟩)
    · exact mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_filter.mpr
        ⟨hell, hd', hN', le_of_not_gt hZ⟩)))
  have hcard := card_le_card hcover
  have h01 := card_union_le (omega3GoodOriginalFibre N d p1 p2 p3 Z)
    (omega3BadDFibre N d p1 p2 p3)
  have h012 := card_union_le
    (omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3)
    (omega3BadNFibre N d p1 p2 p3)
  have h0123 := card_union_le
    ((omega3GoodOriginalFibre N d p1 p2 p3 Z ∪ omega3BadDFibre N d p1 p2 p3) ∪
      omega3BadNFibre N d p1 p2 p3) (omega3SmallOutputFibre N d p1 p2 p3 Z)
  have hgood := omega3_good_original_injects (p3 := p3) (Z := Z) hN heven hd h1 h1N h2N
  omega

end Wu2008DoubleSieve
