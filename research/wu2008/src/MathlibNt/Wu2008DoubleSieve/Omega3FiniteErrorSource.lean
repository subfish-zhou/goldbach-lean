import MathlibNt.Wu2008DoubleSieve.Omega3FiniteError
import MathlibNt.Wu2008DoubleSieve.Omega3Switching
import Mathlib.Data.Finset.Sigma

/-!
# Applying finite multiplicity bounds to the literal Omega3 fibres

The auxiliary sigma carrier is exactly the nested selected-prime/output
sum. Its first three labels have the original increasing order and strict
upper endpoints. No selected prime, output, or convolution weight is dropped.
-/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

abbrev Omega3FiniteLabel := Σ _ : ℕ, Σ _ : ℕ, Σ _ : ℕ, ℕ

noncomputable def omega3FiniteLabels (N d : ℕ) (z y : ℝ) : Finset Omega3FiniteLabel :=
  (primeWindow N z y).sigma fun p3 =>
    (primeWindow N z (p3 : ℝ)).sigma fun p2 =>
      (primeWindow N z (p2 : ℝ)).sigma fun p1 =>
        sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)

def omega3FiniteOutput (a : Omega3FiniteLabel) : ℕ := a.2.2.2

def omega3FiniteTriple (a : Omega3FiniteLabel) : Fin 3 → ℕ :=
  ![a.2.2.1, a.2.1, a.1]

theorem omega3_finite_label_injective :
    Function.Injective (fun a => (omega3FiniteOutput a, omega3FiniteTriple a)) := by
  rintro ⟨a3, a2, a1, a0⟩ ⟨b3, b2, b1, b0⟩ heq
  have h0 : a0 = b0 := congr_arg Prod.fst heq
  have ht := congr_arg Prod.snd heq
  have h1 : a1 = b1 := congr_fun ht 0
  have h2 : a2 = b2 := congr_fun ht 1
  have h3 : a3 = b3 := congr_fun ht 2
  subst b0; subst b1; subst b2; subst b3
  rfl

theorem omega3_finite_filter_card (N d : ℕ) (z y : ℝ) (P : ℕ → Prop) [DecidablePred P] :
    (((omega3FiniteLabels N d z y).filter
      (fun a => P (omega3FiniteOutput a))).card : ℝ) =
    ∑ p3 ∈ primeWindow N z y,
      ∑ p2 ∈ primeWindow N z (p3 : ℝ),
        ∑ p1 ∈ primeWindow N z (p2 : ℝ),
          (((sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
            P).card : ℝ) := by
  unfold omega3FiniteLabels
  rw [filter_sigma, card_sigma, Nat.cast_sum]
  apply sum_congr rfl
  intro p3 _
  rw [filter_sigma, card_sigma, Nat.cast_sum]
  apply sum_congr rfl
  intro p2 _
  rw [filter_sigma, card_sigma, Nat.cast_sum]
  rfl

theorem omega3_finite_label_source {N d : ℕ} {z y : ℝ} {a : Omega3FiniteLabel}
    (ha : a ∈ omega3FiniteLabels N d z y) :
    omega3FiniteOutput a ∈ sourceSieveCarrier N
      (d * a.2.2.1 * a.2.1 * a.1) (d * a.2.2.1 * N) (a.2.1 : ℝ) :=
  (mem_sigma.mp (mem_sigma.mp (mem_sigma.mp ha).2).2).2

theorem omega3_finite_output_lt {N d : ℕ} {z y : ℝ}
    (hN : 4 ≤ N) (heven : Even N) {a : Omega3FiniteLabel}
    (ha : a ∈ omega3FiniteLabels N d z y) : omega3FiniteOutput a < N := by
  obtain ⟨hb, hp, _, _⟩ := mem_filter.mp (omega3_finite_label_source ha)
  exact omega3_prime_output_lt hN heven hp (by simpa using mem_range.mp hb)

theorem omega3_finite_label_divisor {N d : ℕ} {z y : ℝ} {a : Omega3FiniteLabel}
    (ha : a ∈ omega3FiniteLabels N d z y) : d ∣ N - omega3FiniteOutput a := by
  have hdiv := (mem_filter.mp (omega3_finite_label_source ha)).2.2.1
  exact (show d ∣ d * a.2.2.1 * a.2.1 * a.1 from
    ⟨a.2.2.1 * a.2.1 * a.1, by ring⟩).trans hdiv

theorem omega3_finite_triple_large {N d : ℕ} {z y η : ℝ}
    (hlow : (N : ℝ) ^ η ≤ z) {a : Omega3FiniteLabel}
    (ha : a ∈ omega3FiniteLabels N d z y) (j : Fin 3) :
    (omega3FiniteTriple a j).Prime ∧
      omega3FiniteTriple a j ∣ N - omega3FiniteOutput a ∧
      (N : ℝ) ^ η ≤ (omega3FiniteTriple a j : ℝ) := by
  obtain ⟨h3, hrest⟩ := mem_sigma.mp ha
  obtain ⟨h2, hrest⟩ := mem_sigma.mp hrest
  obtain ⟨h1, hout⟩ := mem_sigma.mp hrest
  have hdiv := (mem_filter.mp hout).2.2.1
  have hp1 := mem_primeWindow.mp h1
  have hp2 := mem_primeWindow.mp h2
  have hp3 := mem_primeWindow.mp h3
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i))) j
  · exact ⟨hp1.1, (show a.2.2.1 ∣ d * a.2.2.1 * a.2.1 * a.1 from
        ⟨d * a.2.1 * a.1, by ring⟩).trans hdiv, hlow.trans hp1.2.2.1⟩
  · exact ⟨hp2.1, (show a.2.1 ∣ d * a.2.2.1 * a.2.1 * a.1 from
        ⟨d * a.2.2.1 * a.1, by ring⟩).trans hdiv, hlow.trans hp2.2.2.1⟩
  · exact ⟨hp3.1, (dvd_mul_left a.1 (d * a.2.2.1 * a.2.1)).trans hdiv,
      hlow.trans hp3.2.2.1⟩

/-- The literal triple sum of filtered source counts is bounded by the
allowed-output cardinality with its full per-output triple multiplicity. -/
theorem omega3_source_filter_sum_le_outputs
    {N d : ℕ} {z y η : ℝ} (P : ℕ → Prop) [DecidablePred P] (E : Finset ℕ)
    (hN : 4 ≤ N) (heven : Even N) (hη : 0 < η)
    (hlow : (N : ℝ) ^ η ≤ z)
    (hPE : ∀ ell, ell.Prime → ell ≤ N → P ell → ell ∈ E) :
    (∑ p3 ∈ primeWindow N z y,
      ∑ p2 ∈ primeWindow N z (p3 : ℝ),
        ∑ p1 ∈ primeWindow N z (p2 : ℝ),
          (((sourceSieveCarrier N (d * p1 * p2 * p3) (d * p1 * N) (p2 : ℝ)).filter
            P).card : ℝ)) ≤ (1 / η) ^ 3 * (E.card : ℝ) := by
  rw [← omega3_finite_filter_card N d z y P]
  have hsub : (omega3FiniteLabels N d z y).filter (fun a => P (omega3FiniteOutput a)) ⊆
      (omega3FiniteLabels N d z y).filter (fun a => omega3FiniteOutput a ∈ E) := by
    intro a ha
    obtain ⟨ha, hp⟩ := mem_filter.mp ha
    have hs := mem_filter.mp (omega3_finite_label_source ha)
    exact mem_filter.mpr ⟨ha, hPE _ hs.2.1 (omega3_finite_output_lt hN heven ha).le hp⟩
  calc
    _ ≤ (((omega3FiniteLabels N d z y).filter
      (fun a => omega3FiniteOutput a ∈ E)).card : ℝ) := by exact_mod_cast card_le_card hsub
    _ ≤ _ := omega3_labels_card_le_allowed_outputs _ _ _ E
      omega3_finite_label_injective.injOn (by omega) hη
      (fun _ ha => omega3_finite_output_lt hN heven ha)
      (fun _ ha => omega3_finite_triple_large hlow ha)

theorem omega3_source_badD_sum_le
    {N d : ℕ} {z y η : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d) (hη : 0 < η)
    (hlow : (N : ℝ) ^ η ≤ z) :
    (∑ p3 ∈ primeWindow N z y,
      ∑ p2 ∈ primeWindow N z (p3 : ℝ),
        ∑ p1 ∈ primeWindow N z (p2 : ℝ),
          ((omega3BadDFibre N d p1 p2 p3).card : ℝ)) ≤
      (1 / η) ^ 3 * ∑ q ∈ d.primeFactors, ((N / (d * q) : ℕ) : ℝ) := by
  unfold omega3BadDFibre
  rw [← omega3_finite_filter_card N d z y (Omega3BadD N d)]
  unfold Omega3BadD
  convert omega3_bad_labels_card_le (N := N) (d := d) (η := η) (r := 3)
    (omega3FiniteLabels N d z y)
    omega3FiniteOutput omega3FiniteTriple omega3_finite_label_injective.injOn
    (by omega) hd hη (fun _ ha => omega3_finite_output_lt hN heven ha)
    (fun _ ha => omega3_finite_label_divisor ha)
    (fun _ ha => omega3_finite_triple_large hlow ha) using 1
  congr 2
  ext a
  simp only [mem_filter]

theorem omega3_source_badD_sum_le_power
    {N d : ℕ} {z y η : ℝ}
    (hN : 4 ≤ N) (heven : Even N) (hd : 0 < d) (hdN : d ≤ N) (hη : 0 < η)
    (hlow : (N : ℝ) ^ η ≤ z)
    (hlarge : ∀ q ∈ d.primeFactors, (N : ℝ) ^ η ≤ (q : ℝ)) :
    (∑ p3 ∈ primeWindow N z y,
      ∑ p2 ∈ primeWindow N z (p3 : ℝ),
        ∑ p1 ∈ primeWindow N z (p2 : ℝ),
          ((omega3BadDFibre N d p1 p2 p3).card : ℝ)) ≤
      (1 / η) ^ 4 * (N : ℝ) / ((d : ℝ) * (N : ℝ) ^ η) := by
  unfold omega3BadDFibre
  rw [← omega3_finite_filter_card N d z y (Omega3BadD N d)]
  unfold Omega3BadD
  convert omega3_bad_labels_card_le_power (N := N) (d := d) (η := η) (r := 3)
    (omega3FiniteLabels N d z y)
    omega3FiniteOutput omega3FiniteTriple omega3_finite_label_injective.injOn
    (by omega) hd hdN hη hlarge (fun _ ha => omega3_finite_output_lt hN heven ha)
    (fun _ ha => omega3_finite_label_divisor ha)
    (fun _ ha => omega3_finite_triple_large hlow ha) using 1
  congr 2
  ext a
  simp only [mem_filter]

end Wu2008DoubleSieve
