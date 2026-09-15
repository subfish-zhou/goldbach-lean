import MathlibNt.Wu2008DoubleSieve.FourthRowTripleGatedFamily

/-! # Exact original source counts and the full gated X reindexing -/

namespace Wu2008DoubleSieve

open Finset
open scoped Classical

noncomputable def fourthRowTripleGatedPrimes (N d : ℕ) (δ : ℝ) (ten : Bool) :
    Finset (ℕ × ℕ × ℕ) :=
  (omega3XPrimes N δ (5 / 2) (103 / 25) d).filter
    (fun p => fourthRowTripleGatedBand N δ ten d p.1 p.2.1 ∧ fourthRowTripleGatedGate N d δ p.2.2)

theorem fourthRowTripleGated_original_sum {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) :
    fourthRowMotherPrefixSum N δ W (fourthRowTripleGatedWord ten) =
      omega3LabelSum N δ (5 / 2) (103 / 25) W (fun d p q r =>
        if fourthRowTripleGatedBand N δ ten d p q ∧ fourthRowTripleGatedGate N d δ r then
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
      if fourthRowTripleGatedBand N δ ten d t.1 t.2.1 ∧ fourthRowTripleGatedGate N d δ t.2.2 then
        (sourceSieveCount N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1) else 0)
  have hr :
      (∑ t ∈ orderedTriples (primeWindow N (wuLocalCutoff N δ d (103 / 25))
        (wuLocalCutoff N δ d (5 / 2))),
        if fourthRowTripleGatedBand N δ ten d t.1 t.2.1 ∧ fourthRowTripleGatedGate N d δ t.2.2 then
          ((sourceSieveCarrier N (d * t.1 * t.2.1 * t.2.2) (d * t.1 * N) t.2.1).card : ℝ) else 0) =
      ∑ r ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) (wuLocalCutoff N δ d (5 / 2)),
        ∑ q ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) r,
          ∑ p ∈ primeWindow N (wuLocalCutoff N δ d (103 / 25)) q,
            if fourthRowTripleGatedBand N δ ten d p q ∧ fourthRowTripleGatedGate N d δ r then
              ((sourceSieveCarrier N (d * p * q * r) (d * p * N) q).card : ℝ) else 0 := by
    simpa only [Int.cast_sum, Int.cast_ite, Int.cast_zero, sourceSieveCount,
      Int.cast_natCast] using congrArg (fun x : ℤ => (x : ℝ)) h
  rw [← hr]
  apply sum_congr rfl
  rintro ⟨p, q, r⟩ _
  simp only [fourthRowTripleGated_word_iff]
  congr 1
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

theorem fourthRowTripleGated_X_reorder {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) :
    fourthRowTripleGatedX N δ W (fourthRowTripleGatedProfiles N δ W ten) =
      ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ fourthRowTripleGatedPrimes N d δ ten,
          ((omega3XNCountFibre N d p.1 p.2.1 p.2.2).card : ℝ) := by
  have h := omega3X_full_label_sum N δ (5 / 2) (103 / 25) W
    (fun c p => if fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1 ∧
      fourthRowTripleGatedGate N c.1 δ p then (1 : ℝ) else 0)
  dsimp only at h
  have hleft : fourthRowTripleGatedX N δ W (fourthRowTripleGatedProfiles N δ W ten) =
      ∑ c ∈ omega3CofactorLabels N δ (5 / 2) (103 / 25) W, (convolutionCoeff W c.1 : ℝ) *
        ∑ p ∈ omega3CofactorPrimeFibreLE N δ (5 / 2) c,
          if fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1 ∧
            fourthRowTripleGatedGate N c.1 δ p then (1 : ℝ) else 0 := by
    unfold fourthRowTripleGatedX fourthRowTripleGatedProfiles
    rw [sum_filter]
    apply sum_congr rfl
    intro c _
    by_cases hb : fourthRowTripleGatedBand N δ ten c.1 c.2.2.1 c.2.1
    · simp only [hb, if_true, true_and, sum_boole, fourthRowTripleGatedFibre]
    · simp only [hb, if_false, false_and, sum_const_zero, mul_zero]
  rw [hleft, h]
  apply sum_congr rfl
  intro d _
  congr 1
  rw [fourthRowTripleGatedPrimes, sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : fourthRowTripleGatedBand N δ ten d p.1 p.2.1 ∧
      fourthRowTripleGatedGate N d δ p.2.2 <;>
    simp only [hp, and_self, if_true, if_false, sum_const, nsmul_eq_mul, mul_one, mul_zero]

noncomputable def fourthRowTripleGatedOriginalTuples (N d : ℕ) (δ : ℝ)
    (ten : Bool) : Finset (List ℕ) :=
  (fourthRowMotherTuples (primeWindow N (wuLocalCutoff N δ d (103 / 25))
    (wuLocalCutoff N δ d (5 / 2))) 3).filter fun l =>
      l.map (fourthRowMotherColour (wuLocalCutoff N δ d (89 / 25))
        (wuLocalCutoff N δ d (291 / 100))) = fourthRowTripleGatedWord ten

noncomputable def fourthRowTripleGatedOriginalLabels {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) :
    Finset (Σ _ : Fin i → ℕ, Σ _ : List ℕ, ℕ) :=
  (Fintype.piFinset W).sigma fun t =>
    (fourthRowTripleGatedOriginalTuples N (∏ j, t j) δ ten).sigma
      (fourthRowMotherPrefixCarrier N (∏ j, t j))

theorem fourthRowTripleGated_natural_card {i : ℕ} (N : ℕ) (δ : ℝ)
    (W : Fin i → Finset ℕ) (ten : Bool) :
    (Nat.card {a // a ∈ fourthRowTripleGatedOriginalLabels N δ W ten} : ℝ) =
      fourthRowMotherPrefixSum N δ W (fourthRowTripleGatedWord ten) := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  simp only [fourthRowTripleGatedOriginalLabels, card_sigma, Nat.cast_sum,
    fourthRowMotherPrefixSum, boxConvolution_sum_fibres, fourthRowMotherPrefixTerm,
    fourthRowTripleGatedOriginalTuples, sum_filter, Nat.cast_ite, Nat.cast_zero]
  rfl

end Wu2008DoubleSieve
