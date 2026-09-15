import MathlibNt.Wu2008DoubleSieve.Omega3Multiplicity
import MathlibNt.Wu2008DoubleSieve.Omega3LabelsFibre
import Mathlib.Data.Finset.Sigma

/-!
# Concrete cofactor fibres retaining d, p2, p1, n

The cofactor labels are not identified merely because their products agree.
Instead, the finite fibre is bounded using its ordered convolution weight,
and the only reconstruction used is cancellation to recover n after d,p1,p2
have been fixed. Repetitions and n=1 are permitted.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev Omega3CofactorMultiplicityLabel := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

def omega3CofactorSelected (a : Omega3CofactorMultiplicityLabel) : Fin 2 → ℕ :=
  ![a.2.2.1, a.2.1]

/-- An endpoint-preserving finite enlargement of the good cofactor labels.
The endpoint functions may depend on the retained d label. -/
noncomputable def omega3CofactorMultiplicityCarrier {i : ℕ}
    (N e : ℕ) (W : Fin i → Finset ℕ) (z y : ℕ → ℝ) :
    Finset Omega3CofactorMultiplicityLabel :=
  (boxConvolutionSupport W).sigma fun d =>
    (primeWindow N (z d) (y d)).sigma fun p2 =>
      (primeWindow N (z d) (p2 : ℝ)).sigma fun p1 =>
        (range (N + 1)).filter fun n => 0 < n ∧ omega3Cofactor d p1 p2 n = e

/-- A literal switched label lands in the cofactor carrier without losing
its d, middle-prime label, or d-dependent upper endpoint. -/
theorem omega3_switched_mem_cofactor_carrier {i N d p1 p2 p3 n : ℕ}
    (W : Fin i → Finset ℕ) (z y : ℕ → ℝ)
    (hd : d ∈ boxConvolutionSupport W)
    (h3 : p3 ∈ primeWindow N (z d) (y d))
    (h2 : p2 ∈ primeWindow N (z d) (p3 : ℝ))
    (h1 : p1 ∈ primeWindow N (z d) (p2 : ℝ))
    (hn : n ∈ omega3SwitchedFibre N d p1 p2 p3) :
    ⟨d, p2, p1, n⟩ ∈ omega3CofactorMultiplicityCarrier N
      (omega3Cofactor d p1 p2 n) W z y := by
  have hp2 := mem_primeWindow.mp h2
  have hp3 := mem_primeWindow.mp h3
  have hn' := mem_filter.mp hn
  refine mem_sigma.mpr ⟨hd, mem_sigma.mpr ⟨?_, mem_sigma.mpr
    ⟨h1, mem_filter.mpr ⟨hn'.1, hn'.2.1, rfl⟩⟩⟩⟩
  exact mem_primeWindow.mpr ⟨hp2.1, hp2.2.1, hp2.2.2.1, hp2.2.2.2.trans hp3.2.2.2⟩

theorem omega3_cofactor_quotient_unique {d p1 p2 n m e : ℕ}
    (he : 0 < e)
    (hn : omega3Cofactor d p1 p2 n = e)
    (hm : omega3Cofactor d p1 p2 m = e) : n = m := by
  have hn' : (d * p1 * p2) * n = e := by
    simpa only [omega3Cofactor, mul_assoc, mul_left_comm, mul_comm] using hn
  have hm' : (d * p1 * p2) * m = e := by
    simpa only [omega3Cofactor, mul_assoc, mul_left_comm, mul_comm] using hm
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_mul_pos_right (hn' ▸ he)) (hn'.trans hm'.symm)

theorem omega3_cofactor_labels_injOn {e : ℕ}
    (S : Finset Omega3CofactorMultiplicityLabel) (he : 0 < e)
    (hprod : ∀ a ∈ S, omega3Cofactor a.1 a.2.2.1 a.2.1 a.2.2.2 = e) :
    Set.InjOn (fun a => (a.1, omega3CofactorSelected a)) S := by
  rintro ⟨ad, a2, a1, an⟩ ha ⟨bd, b2, b1, bn⟩ hb heq
  have hd : ad = bd := congr_arg Prod.fst heq
  have ht := congr_arg Prod.snd heq
  have h1 : a1 = b1 := congr_fun ht 0
  have h2 : a2 = b2 := congr_fun ht 1
  subst bd; subst b1; subst b2
  have hn : an = bn := omega3_cofactor_quotient_unique he (hprod _ ha) (hprod _ hb)
  subst bn
  rfl

/-- A concrete cofactor fibre, with no coprimality or squarefreeness premise.
All ordered convolution labels are counted by their literal coefficient. -/
theorem omega3_concrete_cofactor_fibre_le {i k N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (S : Finset Omega3CofactorMultiplicityLabel)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hprod : ∀ a ∈ S, omega3Cofactor a.1 a.2.2.1 a.2.1 a.2.2.2 = e)
    (ht : ∀ a ∈ S, ∀ j, (omega3CofactorSelected a j).Prime ∧
      (N : ℝ) ^ η ≤ (omega3CofactorSelected a j : ℝ)) :
    (∑ a ∈ S, (convolutionCoeff W a.1 : ℝ)) ≤ (max 1 (1 / η)) ^ (k + 2) := by
  refine omega3_cofactor_weighted_fibre_le W S Sigma.fst omega3CofactorSelected
    hik hN he heN hη hW (omega3_cofactor_labels_injOn S he hprod) ?_ ?_
  · intro a ha
    rw [← hprod a ha]
    exact ⟨a.2.2.2 * a.2.2.1 * a.2.1, by unfold omega3Cofactor; ring⟩
  · intro a ha j
    refine ⟨(ht a ha j).1, ?_, (ht a ha j).2⟩
    rw [← hprod a ha]
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
    · exact ⟨a.1 * a.2.2.2 * a.2.1, by
        change a.1 * a.2.2.2 * a.2.2.1 * a.2.1 = a.2.2.1 * (a.1 * a.2.2.2 * a.2.1)
        ring⟩
    · exact ⟨a.1 * a.2.2.2 * a.2.2.1, by
        change a.1 * a.2.2.2 * a.2.2.1 * a.2.1 = a.2.1 * (a.1 * a.2.2.2 * a.2.2.1)
        ring⟩

theorem omega3_cofactor_carrier_weight_le {i k N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (z y : ℕ → ℝ)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ z d) :
    (∑ a ∈ omega3CofactorMultiplicityCarrier N e W z y,
      (convolutionCoeff W a.1 : ℝ)) ≤ (max 1 (1 / η)) ^ (k + 2) := by
  apply omega3_concrete_cofactor_fibre_le W _ hik hN he heN hη hW
  · intro a ha
    exact (mem_filter.mp (mem_sigma.mp (mem_sigma.mp (mem_sigma.mp ha).2).2).2).2.2
  · intro a ha j
    obtain ⟨hd, hrest⟩ := mem_sigma.mp ha
    obtain ⟨h2, hrest⟩ := mem_sigma.mp hrest
    obtain ⟨h1, _⟩ := mem_sigma.mp hrest
    have hp1 := mem_primeWindow.mp h1
    have hp2 := mem_primeWindow.mp h2
    refine Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)) j
    · exact ⟨hp1.1, (hlow _ hd).trans hp1.2.2.1⟩
    · exact ⟨hp2.1, (hlow _ hd).trans hp2.2.2.1⟩

theorem omega3_cofactor_subcarrier_weight_le {i k N e : ℕ} {η : ℝ}
    (W : Fin i → Finset ℕ) (z y : ℕ → ℝ)
    (S : Finset Omega3CofactorMultiplicityLabel)
    (hS : S ⊆ omega3CofactorMultiplicityCarrier N e W z y)
    (hik : i ≤ k) (hN : 1 < N) (he : 0 < e) (heN : e ≤ N) (hη : 0 < η)
    (hW : ∀ j p, p ∈ W j → p.Prime ∧ (N : ℝ) ^ η ≤ (p : ℝ))
    (hlow : ∀ d ∈ boxConvolutionSupport W, (N : ℝ) ^ η ≤ z d) :
    (∑ a ∈ S, (convolutionCoeff W a.1 : ℝ)) ≤ (max 1 (1 / η)) ^ (k + 2) :=
  (sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => Nat.cast_nonneg _)).trans
    (omega3_cofactor_carrier_weight_le W z y hik hN he heN hη hW hlow)

end Wu2008DoubleSieve
