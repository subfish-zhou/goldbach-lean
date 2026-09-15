import MathlibNt.Wu2008DoubleSieve.Omega3CofactorGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3LabelsIndexed

/-! # Support of the actual strengthened switched multiset -/

namespace Wu2008DoubleSieve

open Finset Real
open scoped Classical

/-- Every actual switched label satisfies the source cofactor geometry.
The threshold precedes all source boxes, both parameters and all labels. -/
theorem omega3_switched_geometry (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ a ∈ omega3SwitchedLabels N δ s t (convolutionWuWindows N Δ V),
        0 < omega3IndexCofactor a ∧ (omega3IndexCofactor a).Coprime N ∧
        omega3IndexCofactor a ≤ N ∧
        (omega3IndexCofactor a : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
        (∀ r : ℕ, r.Prime → r ∣ omega3IndexCofactor a →
          (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ r) ∧
        a.2.2.1 < a.2.1 ∧
        (a.2.1 : ℝ) ≤ (N : ℝ) / omega3IndexCofactor a ∧
        (a.2.1 : ℝ) < wuLocalCutoff N δ a.1 s := by
  obtain ⟨T, hT4, hT⟩ := omega3_source_cofactor_geometry k hδ hδhi
  refine ⟨T, hT4, ?_⟩
  intro N hN i Δ V hb s t hs hst ht a ha
  rcases a with ⟨d, p3, p2, p1, n⟩
  obtain ⟨hd, h3, h2, h1, _⟩ := mem_omega3SwitchedLabels.mp ha
  have hsize := omega3_switched_label_size ha
  have h2z : p2 ∈ primeWindow N (wuLocalCutoff N δ d t) (wuLocalCutoff N δ d s) := by
    have h2' := mem_primeWindow.mp h2
    exact mem_primeWindow.mpr ⟨h2'.1, h2'.2.1, h2'.2.2.1,
      h2'.2.2.2.trans (mem_primeWindow.mp h3).2.2.2⟩
  have hgood := hsize.2.2.2.2
  have hnN : n.Coprime N := (Nat.coprime_mul_iff_right.mp hgood.2.1).2
  have hg := hT N hN i Δ V hb d n p1 p2 s t hd hs hst ht
    h1 h2z hsize.1 hnN hgood.2.2 hsize.2.2.1
  change 0 < omega3Cofactor d p1 p2 n ∧
    (omega3Cofactor d p1 p2 n).Coprime N ∧
    omega3Cofactor d p1 p2 n ≤ N ∧
    (omega3Cofactor d p1 p2 n : ℝ) ≤ (N : ℝ) ^ (1 - wuLocalExponent k δ / 10) ∧
    (∀ r : ℕ, r.Prime → r ∣ omega3Cofactor d p1 p2 n →
      (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ r) ∧
    p2 < p3 ∧ (p3 : ℝ) ≤ (N : ℝ) / omega3Cofactor d p1 p2 n ∧
    (p3 : ℝ) < wuLocalCutoff N δ d s
  refine ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2,
    by exact_mod_cast (mem_primeWindow.mp h2).2.2.2, ?_, hsize.2.2.2.1⟩
  apply (le_div_iff₀ (by exact_mod_cast hg.1 : (0 : ℝ) < omega3Cofactor d p1 p2 n)).mpr
  have he : (omega3Cofactor d p1 p2 n : ℝ) * p3 ≤ N := by
    exact_mod_cast hsize.2.1
  simpa only [mul_comm] using he

end Wu2008DoubleSieve
