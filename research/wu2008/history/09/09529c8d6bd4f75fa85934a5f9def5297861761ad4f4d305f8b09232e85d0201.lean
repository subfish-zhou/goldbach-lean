import MathlibNt.Wu2008DoubleSieve.FourthRowMotherSource
import MathlibNt.Wu2008DoubleSieve.Gamma16Layers
import MathlibNt.Wu2008DoubleSieve.Omega3Relative
import MathlibNt.Wu2008DoubleSieve.Omega3XFiniteReorder

/-! # The two actual no-gate subfamilies of the accepted Omega3 profiles -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

def fourthRowTripleNoGateWord (eleven : Bool) : List ℕ :=
  [if eleven then 1 else 0, 2, 2]

noncomputable def fourthRowTripleNoGateBand (N : ℕ) (δ : ℝ) (eleven : Bool)
    (d p1 p2 : ℕ) : Prop :=
  fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
      (wuLocalCutoff N δ d (291 / 100)) p1 = (if eleven then 1 else 0) ∧
    fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
      (wuLocalCutoff N δ d (291 / 100)) p2 = 2

noncomputable def fourthRowTripleNoGateProfiles {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) : Finset Omega3CofactorIndex :=
  (omega3CofactorLabels N δ (5 / 2) (103 / 25) W).filter
    (fun c => fourthRowTripleNoGateBand N δ eleven c.1 c.2.2.1 c.2.1)

noncomputable def fourthRowTripleNoGateX {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) : ℝ :=
  gamma16FamilyX N δ W (fourthRowTripleNoGateProfiles N δ W eleven)

noncomputable def fourthRowTripleNoGateS {i : ℕ} (N : ℕ) (δ Z : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) : ℝ :=
  gamma16FamilyS N δ Z W (fourthRowTripleNoGateProfiles N δ W eleven)

theorem fourthRowTripleNoGate_profiles_subset {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    fourthRowTripleNoGateProfiles N δ W eleven ⊆ omega3CofactorLabels N δ (5 / 2) (103 / 25) W :=
  filter_subset _ _

theorem fourthRowTripleNoGate_word_iff {N d p q r : ℕ} {δ : ℝ}
    (eleven : Bool) (hqr : q ≤ r) :
    [p, q, r].map (fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
      (wuLocalCutoff N δ d (291 / 100))) = fourthRowTripleNoGateWord eleven ↔
      fourthRowTripleNoGateBand N δ eleven d p q := by
  have hm := fourthRowMother_colour_monotone (wuLocalCutoff N δ d (89 / 25))
    (wuLocalCutoff N δ d (291 / 100)) hqr
  have hc := fourthRowMother_colour_le_two (wuLocalCutoff N δ d (89 / 25))
    (wuLocalCutoff N δ d (291 / 100)) r
  simp only [fourthRowTripleNoGateWord, fourthRowTripleNoGateBand,
    List.map_cons, List.map_nil, List.cons.injEq, and_true]
  omega

theorem fourthRowTripleNoGate_original_sum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    fourthRowMotherPrefixSum N δ W (fourthRowTripleNoGateWord eleven) =
      omega3LabelSum N δ (5 / 2) (103 / 25) W (fun d p q r =>
        if fourthRowTripleNoGateBand N δ eleven d p q then
          ((sourceSieveCarrier N (d * p * q * r) (d * p * N) q).card : ℝ) else 0) := by
  unfold fourthRowMotherPrefixSum omega3LabelSum
  apply sum_congr rfl
  intro d _
  congr 1
  unfold fourthRowMotherPrefixTerm
  have hinj : Function.Injective (fun t : ℕ × ℕ × ℕ => [t.1, t.2.1, t.2.2]) := by
    rintro ⟨p, q, r⟩ ⟨p', q', r'⟩ h
    simpa using h
  change (∑ l ∈ (orderedTriples (primeWindow N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (5 / 2)))).image (fun t => [t.1, t.2.1, t.2.2]), _) = _
  rw [sum_image (fun _ _ _ _ h => hinj h)]
  have h := sum_s3_orderedTriples_descending N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (5 / 2)) (fun t =>
      if fourthRowTripleNoGateBand N δ eleven d t.1 t.2.1 then
        (sourceSieveCount N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1) else 0)
  have hr :
      (∑ t ∈ orderedTriples (primeWindow N (wuLocalCutoff N δ d (103 / 25))
        (wuLocalCutoff N δ d (5 / 2))),
        if fourthRowTripleNoGateBand N δ eleven d t.1 t.2.1 then
          ((sourceSieveCarrier N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1).card : ℝ) else 0) =
      ∑ r ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) (wuLocalCutoff N δ d (5 / 2)),
        ∑ q ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) r,
          ∑ p ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) q,
            if fourthRowTripleNoGateBand N δ eleven d p q then
              ((sourceSieveCarrier N (d * p * q * r) (d * p * N) q).card : ℝ) else 0 := by
    simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, sourceSieveCount,
      Int.cast_natCast] using congrArg (fun x : ℤ => (x : ℝ)) h
  rw [← hr]
  apply sum_congr rfl
  rintro ⟨p, q, r⟩ ht
  have hqr := (mem_s3_ordered_triples.mp ht).2.2.2.2.2.2.2.2.2
  simp only [fourthRowTripleNoGate_word_iff eleven hqr.le]
  congr 1
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

theorem fourthRowTripleNoGate_X_reorder {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (eleven : Bool) :
    fourthRowTripleNoGateX N δ W eleven =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ (omega3XPrimes N δ (5 / 2) (103 / 25) d).filter
          (fun p => fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1),
          ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ) := by
  have h := omega3X_full_label_sum N δ (5 / 2) (103 / 25) W
    (fun c _ => if fourthRowTripleNoGateBand N δ eleven c.1 c.2.2.1 c.2.1
      then (1 : ℝ) else 0)
  dsimp only at h
  have hleft :
      fourthRowTripleNoGateX N δ W eleven =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ omega3XPrimes N δ (5 / 2) (103 / 25) d,
          ∑ n ∈ omega3XNCountFibre N d p.1 p.2.1 p.2.2,
            if fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1 then (1 : ℝ) else 0 := by
    calc
      _ = ∑ c ∈ omega3CofactorLabels N δ (5 / 2) (103 / 25) W,
          (convolutionCoeff W c.1 : ℝ) *
            ∑ p3 ∈ omega3CofactorPrimeFibreLE N δ (5 / 2) c,
              if fourthRowTripleNoGateBand N δ eleven c.1 c.2.2.1 c.2.1 then (1 : ℝ) else 0 := by
        simp only [fourthRowTripleNoGateX, gamma16FamilyX, fourthRowTripleNoGateProfiles,
          sum_filter, sum_const, nsmul_eq_mul, mul_ite, mul_one, mul_zero]
      _ = _ := h
  rw [hleft]
  apply sum_congr rfl
  intro d _
  congr 1
  rw [sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hb : fourthRowTripleNoGateBand N δ eleven d p.1 p.2.1 <;>
    simp only [hb, if_true, if_false, sum_const, nsmul_eq_mul, mul_one, mul_zero]

end Wu2008DoubleSieve
