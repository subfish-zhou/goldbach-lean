import MathlibNt.Wu2008DoubleSieve.Omega3MultiplicityIndexed
import MathlibNt.Wu2008DoubleSieve.Omega3SwitchedGeometry

/-!
# Actual cofactor profiles with bounded weighted multiplicity

Only the varying prime p3 is separated out. A profile retains d,p2,p1,n,
so both its lower prime endpoint and its d-dependent upper endpoint survive.
The profile map is independent of any later sieve modulus.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

def omega3CofactorProfile (a : Omega3Index) : Omega3CofactorMultiplicityLabel :=
  omega3ProjectCofactor a

def omega3ProfileCofactor (c : Omega3CofactorMultiplicityLabel) : ℕ :=
  omega3Cofactor c.1 c.2.2.1 c.2.1 c.2.2.2

noncomputable def omega3CofactorProfiles {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) : Finset Omega3CofactorMultiplicityLabel :=
  omega3ProjectedCofactorLabels N δ s t W

noncomputable def omega3ProfileFibre {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (e : ℕ) : Finset Omega3CofactorMultiplicityLabel :=
  omega3ActualCofactorFibre N e δ s t W

/-- Arbitrary tests of all labels regroup by profile without forgetting the
varying prime fibre. In particular this applies to divisible or sifted counts. -/
theorem omega3_profile_sum_identity {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (f : Omega3Index → ℝ) :
    (∑ a ∈ omega3SwitchedLabels N δ s t W, (convolutionCoeff W a.1 : ℝ) * f a) =
      ∑ c ∈ omega3CofactorProfiles N δ s t W,
        ∑ a ∈ (omega3SwitchedLabels N δ s t W).filter (fun a => omega3CofactorProfile a = c),
          (convolutionCoeff W a.1 : ℝ) * f a :=
  (sum_fiberwise_of_maps_to (fun _ ha => mem_image_of_mem _ ha) _).symm

theorem omega3_profile_fibre_subset {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (e : ℕ) :
    omega3ProfileFibre N δ s t W e ⊆ omega3CofactorMultiplicityCarrier N e W
      (fun d => wuLocalCutoff N δ d t) (fun d => wuLocalCutoff N δ d s) :=
  omega3_actual_cofactor_fibre_subset W

/-- The true weighted cofactor fibre is uniformly bounded, without the
paper's unsupported g(e)<=1 claim. No p3 is included in this fibre bound. -/
theorem omega3_profile_fibre_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ e : ℕ,
        (∑ c ∈ omega3ProfileFibre N δ s t (convolutionWuWindows N Δ V) e,
          (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)) ≤
        (max 1 (1 / (wuLocalExponent k δ / 10))) ^ (k + 2) := by
  obtain ⟨T1, hT14, hT1⟩ := omega3_source_window_lower k hδ hδhi
  obtain ⟨T2, _, hT2⟩ := omega3_switched_geometry k hδ hδhi
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht e
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  by_cases hne : (omega3ProfileFibre N δ s t (convolutionWuWindows N Δ V) e).Nonempty
  · obtain ⟨c, hc⟩ := hne
    obtain ⟨hc, he⟩ := mem_filter.mp hc
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hc
    have hg := hT2 N hN2 i Δ V hb s t hs hst ht a ha
    have he' : omega3IndexCofactor a = e := he
    have hep : 0 < e := he' ▸ hg.1
    have heN : e ≤ N := he' ▸ hg.2.2.1
    apply omega3_actual_cofactor_weight_le _ hb.1 (by omega) hep heN
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num))
    · intro j p hp
      exact ⟨(hT1 N hN1 i Δ V hb j p hp).1, (hT1 N hN1 i Δ V hb j p hp).2.2⟩
    · intro d hd
      exact (wu_buchstab_prime_window_bounds (d := d) (show 2 ≤ N by omega)
        hδ hδhi hb hs hst ht hd).2.2.2.1
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
    positivity

end Wu2008DoubleSieve
