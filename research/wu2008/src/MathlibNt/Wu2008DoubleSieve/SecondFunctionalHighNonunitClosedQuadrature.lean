import MathlibNt.Wu2008DoubleSieve.HighNonunitMaskedUniform
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedMaskMass

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.HighNonunitMasked
open Set MeasureTheory

private theorem sum_fintype_congr {A : Type*} (I J : Fintype A) (f g : A → ℝ)
    (h : ∀ a, f a = g a) :
    @Finset.sum A ℝ _ (@Finset.univ A I) f = @Finset.sum A ℝ _ (@Finset.univ A J) g := by
  have he : I = J := Subsingleton.elim _ _
  subst J
  exact Finset.sum_congr rfl (fun a _ => h a)

/-- Relabel only the finite face index; all moving intercepts still follow the threshold. -/
theorem uniform_finite_rows (m : ℕ) {Q : Type*} [Fintype Q] (j : Fin (m+1))
    (C : Q → Fin (m+1) → ℝ) (hC : ∀ q, ∃ i, 1 ≤ |C q i|)
    (Phi : ℝ) (hPhi : 2 ≤ Phi) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ gamma : Q → ℝ,
      |(∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f *
          (if ∀ q, (∑ i, C q i*gridCoordinates R f i) ≤ gamma q
            then HighNonunitLegal.G j phi (gridCoordinates R f) else 0)) -
        (∫ t in continuousCube (m+1),
          (if ∀ q, (∑ i, C q i*t i) ≤ gamma q then HighNonunitLegal.G j phi t else 0) *
            continuousDensity t)| < epsilon := by
  let e := Fintype.equivFin Q
  let C' := fun q => C (e.symm q)
  obtain ⟨T,hT,h⟩ := uniform m (Fintype.card Q) j C'
    (fun q => hC (e.symm q)) Phi hPhi epsilon he
  refine ⟨T,hT,fun R hR phi hphi gamma => ?_⟩
  let gamma' := fun q => gamma (e.symm q)
  have hF (t : Fin (m+1) → ℝ) : F j phi C' gamma' t =
      (if ∀ q, (∑ i, C q i*t i) ≤ gamma q then HighNonunitLegal.G j phi t else 0) := by
    have hp : (∀ q, (∑ i, C' q i*t i) ≤ gamma' q) ↔
        ∀ q, (∑ i, C q i*t i) ≤ gamma q := by
      constructor
      · intro hq q
        simpa only [C', gamma', Equiv.symm_apply_apply] using hq (e q)
      · intro hq q
        exact hq (e.symm q)
    unfold F mask
    split_ifs with h1 h2 h2
    · rfl
    · exact False.elim (h2 (hp.mp h1))
    · exact False.elim (h1 (hp.mpr h2))
    · rfl
  simpa only [primeSum, integral, hF] using h R hR phi hphi gamma'

end Wu2008DoubleSieve.HighNonunitMasked

namespace Wu2008DoubleSieve.HighNonunitLegal
open Set MeasureTheory
attribute [local instance] affineDomainsDecidable

theorem closedPrimeK20_uniform (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → b ≤ 1/2 →
        |closedPrimeK20 R a2 a3 b phi - K20 a2 a3 b phi| < epsilon := by
  obtain ⟨T,hT,h⟩ := HighNonunitMasked.uniform_finite_rows 4 3 C20 C20_nonzero
    Phi hPhi epsilon he
  refine ⟨T,hT,fun R hR phi hphi a2 a3 b ha hb => ?_⟩
  rw [closedPrimeK20_literal, K20_closed_mask_literal ha hb]
  convert h R hR phi hphi (gamma20 a2 a3 b) using 1
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ => x-y)
  · apply HighNonunitMasked.sum_fintype_congr
    intro f
    split_ifs <;> rfl
  · congr 1
    funext t
    split_ifs <;> rfl

theorem closedPrimeK21_uniform (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ a3 b : ℝ, 1/10 ≤ a3 → b ≤ 1/2 →
        |closedPrimeK21 R a3 b phi - K21 a3 b phi| < epsilon := by
  obtain ⟨T,hT,h⟩ := HighNonunitMasked.uniform_finite_rows 5 4 C21 C21_nonzero
    Phi hPhi epsilon he
  refine ⟨T,hT,fun R hR phi hphi a3 b ha hb => ?_⟩
  rw [closedPrimeK21_literal, K21_closed_mask_literal ha hb]
  convert h R hR phi hphi (gamma21 a3 b) using 1
  apply congrArg abs
  apply congrArg₂ (fun x y : ℝ => x-y)
  · apply HighNonunitMasked.sum_fintype_congr
    intro f
    split_ifs <;> rfl
  · congr 1
    funext t
    split_ifs <;> rfl

/-- One tolerance and one scale threshold for both complete words. -/
theorem closedPrimeK_pair_uniform (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ a2 a3 b : ℝ, 1/10 ≤ a2 → a2 ≤ a3 → b ≤ 1/2 →
        |(closedPrimeK20 R a2 a3 b phi + closedPrimeK21 R a3 b phi) -
          (K20 a2 a3 b phi + K21 a3 b phi)| < epsilon := by
  obtain ⟨T0,hT0,h0⟩ := closedPrimeK20_uniform Phi hPhi (epsilon/2) (half_pos he)
  obtain ⟨T1,_,h1⟩ := closedPrimeK21_uniform Phi hPhi (epsilon/2) (half_pos he)
  refine ⟨max T0 T1, hT0.trans_le (le_max_left _ _), ?_⟩
  intro R hR phi hphi a2 a3 b ha h23 hb
  have h20 := h0 R ((le_max_left _ _).trans hR) phi hphi a2 a3 b ha hb
  have h21 := h1 R ((le_max_right _ _).trans hR) phi hphi a3 b (ha.trans h23) hb
  have ht := abs_add_le (closedPrimeK20 R a2 a3 b phi - K20 a2 a3 b phi)
    (closedPrimeK21 R a3 b phi - K21 a3 b phi)
  rw [show (closedPrimeK20 R a2 a3 b phi - K20 a2 a3 b phi) +
    (closedPrimeK21 R a3 b phi - K21 a3 b phi) =
    (closedPrimeK20 R a2 a3 b phi + closedPrimeK21 R a3 b phi) -
      (K20 a2 a3 b phi + K21 a3 b phi) by ring] at ht
  linarith

end Wu2008DoubleSieve.HighNonunitLegal
