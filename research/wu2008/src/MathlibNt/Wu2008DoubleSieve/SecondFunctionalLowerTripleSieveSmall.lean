import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleFixedOutput

open scoped BigOperators Classical
namespace Wu2008DoubleSieve.LowerTripleGroupedOutput
open Finset LowerTripleGrouped

/-- The original weighted sum with a closed real cutoff; no endpoint atom is removed. -/
noncomputable def closedSmall {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (Z : ℝ) : ℝ :=
  ∑ x ∈ (sourceFamily N δ Δ V P j).labels,
    (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
      ((outputFibre N δ Δ V P j x).filter
        (fun r => ((N-cofactor x*r : ℕ) : ℝ) ≤ Z)).card

/-- Primality supplies the lower endpoint even when the fibre is empty. -/
theorem small_card_disintegration {i : ℕ} (N Z : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (x : Label) :
    (∑ ell ∈ Icc 1 Z, ((outputFibre N δ Δ V P j x).filter
      (fun r => N-cofactor x*r = ell)).card) =
      ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r ≤ Z)).card := by
  rw [sum_card_fiberwise_eq_card_filter]
  congr 1
  ext r
  simp only [mem_filter, mem_Icc]
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · intro h
    have hp : (N-cofactor x*r).Prime := (mem_filter.mp h.1).2
    exact ⟨h.1,hp.pos,h.2⟩

/-- Exact exchange of the label and output sums, using the closed natural floor. -/
theorem closedSmall_disintegration {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) {Z : ℝ} (hZ : 0 ≤ Z) :
    closedSmall N δ Δ V P j Z =
      ∑ ell ∈ Icc 1 ⌊Z⌋₊, ∑ x ∈ (sourceFamily N δ Δ V P j).labels,
        (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
          ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card := by
  rw [sum_comm]
  unfold closedSmall
  apply sum_congr rfl
  intro x _
  rw [← mul_sum, ← Nat.cast_sum, small_card_disintegration]
  simp only [Nat.le_floor_iff hZ]

/-- Pay each integer output once, rather than once per label. -/
theorem closedSmall_le_of_output_bound {i N : ℕ} {δ Δ C Z : ℝ} (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (hZ : 0 ≤ Z) (hC : 0 ≤ C)
    (h : ∀ ell, (∑ x ∈ (sourceFamily N δ Δ V P j).labels,
      (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
        ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card) ≤ C) :
    closedSmall N δ Δ V P j Z ≤ C*Z := by
  rw [closedSmall_disintegration N δ Δ V P j hZ]
  calc
    _ ≤ ∑ _ell ∈ Icc 1 ⌊Z⌋₊, C := sum_le_sum (fun ell _ => h ell)
    _ = C*(⌊Z⌋₊ : ℝ) := by simp [mul_comm]
    _ ≤ C*Z := mul_le_mul_of_nonneg_left (Nat.floor_le hZ) hC

/-- The actual Family.small uses a strict upper cutoff, hence only a one-sided bridge. -/
theorem source_small_le_closed {i : ℕ} (N : ℕ) (δ Δ : ℝ) (V : Fin i → ℝ)
    (P : SecondFunctionalParameters) (j : Fin 6) (Z : ℝ) :
    (sourceFamily N δ Δ V P j).small Z ≤ closedSmall N δ Δ V P j Z := by
  apply sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro r hr
  obtain ⟨hr,hprime,hlt⟩ := mem_filter.mp hr
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨hr,hprime⟩,hlt.le⟩

/-- A single threshold precedes N, boxes, mother parameters, all six bands and real cutoffs. -/
theorem source_all_small (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1/2) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ P : SecondFunctionalParameters, P.MotherAdmissible →
      let H := max 1 (1/(wuLocalExponent k δ / 10))
      (∀ j : Fin 6,
        (∀ ell, (∑ x ∈ (sourceFamily N δ Δ V P j).labels,
          (convolutionCoeff (convolutionWuWindows N Δ V) x.1 : ℝ) *
            ((outputFibre N δ Δ V P j x).filter (fun r => N-cofactor x*r = ell)).card) ≤ H^(k+3)) ∧
        (∀ Z : ℝ, 0 ≤ Z → closedSmall N δ Δ V P j Z ≤ H^(k+3)*Z) ∧
        (∀ Z : ℝ, 0 ≤ Z → (sourceFamily N δ Δ V P j).small Z ≤ H^(k+3)*Z)) ∧
      (∀ Z : ℝ, 0 ≤ Z → (∑ j : Fin 6, closedSmall N δ Δ V P j Z) ≤ 6*H^(k+3)*Z) ∧
      (∀ Z : ℝ, 0 ≤ Z → (∑ j : Fin 6, (sourceFamily N δ Δ V P j).small Z) ≤ 6*H^(k+3)*Z) := by
  obtain ⟨T,hT,hm⟩ := source_output_multiplicity k hδ hδhi
  refine ⟨T,hT,?_⟩
  intro N hN i Δ V hb P hP
  let H := max 1 (1/(wuLocalExponent k δ / 10))
  have hf (j : Fin 6) := hm N hN i Δ V hb P hP j
  have hc (j : Fin 6) (Z : ℝ) (hZ : 0 ≤ Z) :
      closedSmall N δ Δ V P j Z ≤ H^(k+3)*Z :=
    closedSmall_le_of_output_bound V P j hZ (by dsimp [H]; positivity) (hf j)
  have hs (j : Fin 6) (Z : ℝ) (hZ : 0 ≤ Z) :
      (sourceFamily N δ Δ V P j).small Z ≤ H^(k+3)*Z :=
    (source_small_le_closed N δ Δ V P j Z).trans (hc j Z hZ)
  refine ⟨fun j => ⟨hf j,hc j,hs j⟩, ?_, ?_⟩
  · intro Z hZ
    calc
      _ ≤ ∑ _j : Fin 6, H^(k+3)*Z := sum_le_sum (fun j _ => hc j Z hZ)
      _ = _ := by simp [H]; ring
  · intro Z hZ
    calc
      _ ≤ ∑ _j : Fin 6, H^(k+3)*Z := sum_le_sum (fun j _ => hs j Z hZ)
      _ = _ := by simp [H]; ring

end Wu2008DoubleSieve.LowerTripleGroupedOutput
