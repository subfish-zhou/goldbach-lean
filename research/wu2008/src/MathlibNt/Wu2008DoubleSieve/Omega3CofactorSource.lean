import MathlibNt.Wu2008DoubleSieve.Omega3LabelsCofactor
import MathlibNt.Wu2008DoubleSieve.Omega3CofactorGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3MultiplicityCofactor

/-!
# Support and multiplicity of the cofactor-first source sequence

This also includes cofactor labels whose varying-prime fibre is empty.
The actual switched sifted count is the exact cofactor-first sum proved in
`omega3_switched_sifted_cofactor_first`.
-/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

theorem omega3_cofactor_labels_geometry (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ c ∈ omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V),
        0 < omega3CofactorValue c ∧ (omega3CofactorValue c).Coprime N ∧
        omega3CofactorValue c ≤ N ∧
        (omega3CofactorValue c : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
        ∀ r : ℕ, r.Prime → r ∣ omega3CofactorValue c →
          (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ r := by
  obtain ⟨T, hT4, hT⟩ := omega3_source_cofactor_geometry k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht c hc
  rcases c with ⟨d, p2, p1, n⟩
  obtain ⟨hd, h2, h1, _, hn, hsize, hgood⟩ := mem_omega3CofactorLabels.mp hc
  exact hT N hN i Δ V hb d n p1 p2 s t hd hs hst ht h1 h2 hn
    (Nat.coprime_mul_iff_right.mp hgood.2.1).2 hgood.2.2 hsize

theorem omega3_cofactor_labels_subset {i : ℕ} (N : ℕ) (δ s t : ℝ)
    (W : Fin i → Finset ℕ) (e : ℕ) :
    (omega3CofactorLabels N δ s t W).filter (fun c => omega3CofactorValue c = e) ⊆
      omega3CofactorMultiplicityCarrier N e W
        (fun d => wuLocalCutoff N δ d t) (fun d => wuLocalCutoff N δ d s) := by
  rintro ⟨d, p2, p1, n⟩ hc
  obtain ⟨hc, he⟩ := mem_filter.mp hc
  obtain ⟨hd, h2, h1, hnN, hn, _, _⟩ := mem_omega3CofactorLabels.mp hc
  exact mem_sigma.mpr ⟨hd, mem_sigma.mpr ⟨h2, mem_sigma.mpr
    ⟨h1, mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le hnN), hn, he⟩⟩⟩⟩

/-- The genuine cofactor-first coefficient g(e), including labels with
empty prime fibres, has a uniform constant bound rather than g(e)<=1. -/
theorem omega3_cofactor_labels_fibre_uniform (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ e : ℕ,
        (∑ c ∈ (omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)).filter
            (fun c => omega3CofactorValue c = e),
          (convolutionCoeff (convolutionWuWindows N Δ V) c.1 : ℝ)) ≤
        (max 1 (1 / (wuLocalExponent k δ / 10))) ^ (k + 2) := by
  obtain ⟨T1, hT14, hT1⟩ := omega3_source_window_lower k hδ hδhi
  obtain ⟨T2, _, hT2⟩ := omega3_cofactor_labels_geometry k hδ hδhi
  refine ⟨max T1 T2, hT14.trans (le_max_left _ _), ?_⟩
  intro N hN i Δ V hb s t hs hst ht e
  have hN1 := (le_max_left T1 T2).trans hN
  have hN2 := (le_max_right T1 T2).trans hN
  have hN4 := hT14.trans hN1
  by_cases hne : ((omega3CofactorLabels N δ s t (convolutionWuWindows N Δ V)).filter
      (fun c => omega3CofactorValue c = e)).Nonempty
  · obtain ⟨c, hc⟩ := hne
    obtain ⟨hc, he⟩ := mem_filter.mp hc
    have hg := hT2 N hN2 i Δ V hb s t hs hst ht c hc
    apply omega3_cofactor_subcarrier_weight_le _ _ _ _
      (omega3_cofactor_labels_subset N δ s t _ e) hb.1 (by omega)
      (he ▸ hg.1) (he ▸ hg.2.2.1)
      (div_pos (wuLocalExponent_pos k hδ hδhi) (by norm_num))
    · intro j p hp
      exact ⟨(hT1 N hN1 i Δ V hb j p hp).1, (hT1 N hN1 i Δ V hb j p hp).2.2⟩
    · intro d hd
      exact (wu_buchstab_prime_window_bounds (d := d) (show 2 ≤ N by omega)
        hδ hδhi hb hs hst ht hd).2.2.2.1
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
    positivity

end Wu2008DoubleSieve
