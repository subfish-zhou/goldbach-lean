import R2RawMotherWords

namespace WuPaper.R2RawMother

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def rawGamma (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) : ℝ :=
  if j < 7 then secondFunctionalMotherGamma N d M a b c e f j
  else ((secondFunctionalMotherGammaWords j).map (rawTerm N d M a b c e f)).sum

noncomputable def exceptionGamma (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) : ℝ :=
  if j < 7 then 0
  else ((secondFunctionalMotherGammaWords j).map (exceptionTerm N d M a b c e f)).sum

theorem words_exact (N d M : ℕ) (a b c e f : ℝ) (css : List (List ℕ)) :
    (css.map (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum =
      (css.map (rawTerm N d M a b c e f)).sum +
        (css.map (exceptionTerm N d M a b c e f)).sum := by
  induction css with
  | nil => simp
  | cons cs css ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [term_exact, ih]
    ring

theorem gamma_exact (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) :
    secondFunctionalMotherGamma N d M a b c e f j =
      rawGamma N d M a b c e f j + exceptionGamma N d M a b c e f j := by
  rcases j with _ | _ | _ | _ | _ | _ | _ | j <;>
    simp [rawGamma, exceptionGamma, secondFunctionalMotherGamma, words_exact]
  rw [if_neg (by omega), if_neg (by omega)]

noncomputable def rawLocal (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  rawGamma N d M a b c e f 1 - rawGamma N d M a b c e f 2 -
    rawGamma N d M a b c e f 3 - rawGamma N d M a b c e f 4 +
      ∑ j ∈ Icc 5 21, rawGamma N d M a b c e f j

noncomputable def exceptionLocal (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  ∑ j ∈ Icc 5 21, exceptionGamma N d M a b c e f j

theorem local_exact (N d M : ℕ) (a b c e f : ℝ) :
    secondFunctionalMotherLocal N d M a b c e f =
      rawLocal N d M a b c e f + exceptionLocal N d M a b c e f := by
  unfold secondFunctionalMotherLocal rawLocal exceptionLocal
  simp_rw [gamma_exact]
  have h1 : exceptionGamma N d M a b c e f 1 = 0 := by simp [exceptionGamma]
  have h2 : exceptionGamma N d M a b c e f 2 = 0 := by simp [exceptionGamma]
  have h3 : exceptionGamma N d M a b c e f 3 = 0 := by simp [exceptionGamma]
  have h4 : exceptionGamma N d M a b c e f 4 = 0 := by simp [exceptionGamma]
  simp only [h1, h2, h3, h4, add_zero, sum_add_distrib]
  ring

theorem raw_local_with_exact_exception (N d : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hce : c ≤ e) (hef : e ≤ f) :
    5 * (sourceSieveCount N d (d * N) f : ℝ) ≤
      rawLocal N d N a b c e f + exceptionLocal N d N a b c e f +
        fourthRowMotherBadPrime N d a f + fourthRowMotherBadPrime N d a c +
          fourthRowMotherBadPrime N d a e := by
  rw [← local_exact]
  exact secondFunctionalMother_original_windows N d hab hbc hce hef

noncomputable def exceptionFloorTerm (N d M : ℕ)
    (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs ∧ ¬labelsSurvive N d l
    then ((N / (d * l.prod) : ℕ) : ℝ) else 0

theorem exceptionTerm_floor {N : ℕ} (d M : ℕ) (a b c e f : ℝ) (cs : List ℕ)
    (hN : 4 ≤ N) (he : Even N) :
    exceptionTerm N d M a b c e f cs ≤ exceptionFloorTerm N d M a b c e f cs := by
  unfold exceptionTerm exceptionFloorTerm
  apply sum_le_sum
  intro l _
  have h := exceptional_card_floor (d := d) l hN he
  by_cases hc : l.map (secondFunctionalMotherColour b c e) = cs
  · by_cases hs : labelsSurvive N d l
    · simp [hc, hs, exceptionalCarrier]
    · simpa only [hc, hs, not_false_eq_true, and_self, if_true, if_false, Nat.cast_le] using h
  · simp [hc]

noncomputable def rawWeighted (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    rawLocal N d N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
      (wuLocalCutoff N δ d p.s)

noncomputable def exceptionWeighted (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    exceptionLocal N d N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
      (wuLocalCutoff N δ d p.s)

theorem weighted_exact (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    secondFunctionalMotherRHS p N δ W =
      rawWeighted p N δ W + exceptionWeighted p N δ W := by
  rw [← secondFunctionalMother_weighted_identity]
  simp only [rawWeighted, exceptionWeighted, local_exact, mul_add, sum_add_distrib]

theorem raw_source_finite_with_exception
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
      rawWeighted p N δ (convolutionWuWindows N Δ V) +
        exceptionWeighted p N δ (convolutionWuWindows N Δ V) +
          secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) := by
  rw [← weighted_exact]
  exact secondFunctionalMother_source_finite p hp hN hδ hδhi hb

theorem raw_source_with_exception
    (k : ℕ) (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          rawWeighted p N δ (convolutionWuWindows N Δ V) +
            exceptionWeighted p N δ (convolutionWuWindows N Δ V) +
              ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, h⟩ := secondFunctionalMother_source k p hp hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  rw [← weighted_exact]
  exact h N hN he i Δ V hb

theorem rawGamma20_unit_zero (N : ℕ) (a b c e f : ℝ) :
    rawGamma N 1 N a b c e f 20 = 0 := by
  simp only [rawGamma, show ¬(20 : ℕ) < 7 by norm_num, if_false,
    secondFunctionalMotherGammaWords, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  exact rawTerm_unit_zero N a b c e f _ (by simp)

theorem rawGamma21_unit_zero (N : ℕ) (a b c e f : ℝ) :
    rawGamma N 1 N a b c e f 21 = 0 := by
  simp only [rawGamma, show ¬(21 : ℕ) < 7 by norm_num, if_false,
    secondFunctionalMotherGammaWords, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, add_zero]
  exact rawTerm_unit_zero N a b c e f _ (by simp)

theorem exceptionGamma20_unit_full (N : ℕ) (a b c e f : ℝ) :
    exceptionGamma N 1 N a b c e f 20 =
      secondFunctionalMotherGamma N 1 N a b c e f 20 := by
  have h := gamma_exact N 1 N a b c e f 20
  rw [rawGamma20_unit_zero, zero_add] at h
  exact h.symm

theorem exceptionGamma21_unit_full (N : ℕ) (a b c e f : ℝ) :
    exceptionGamma N 1 N a b c e f 21 =
      secondFunctionalMotherGamma N 1 N a b c e f 21 := by
  have h := gamma_exact N 1 N a b c e f 21
  rw [rawGamma21_unit_zero, zero_add] at h
  exact h.symm

end WuPaper.R2RawMother

#check @WuPaper.R2RawMother.rawGamma
#print axioms WuPaper.R2RawMother.rawGamma
#check @WuPaper.R2RawMother.exceptionGamma
#print axioms WuPaper.R2RawMother.exceptionGamma
#check @WuPaper.R2RawMother.words_exact
#print axioms WuPaper.R2RawMother.words_exact
#check @WuPaper.R2RawMother.gamma_exact
#print axioms WuPaper.R2RawMother.gamma_exact
#check @WuPaper.R2RawMother.rawLocal
#print axioms WuPaper.R2RawMother.rawLocal
#check @WuPaper.R2RawMother.exceptionLocal
#print axioms WuPaper.R2RawMother.exceptionLocal
#check @WuPaper.R2RawMother.local_exact
#print axioms WuPaper.R2RawMother.local_exact
#check @WuPaper.R2RawMother.raw_local_with_exact_exception
#print axioms WuPaper.R2RawMother.raw_local_with_exact_exception
#check @WuPaper.R2RawMother.exceptionFloorTerm
#print axioms WuPaper.R2RawMother.exceptionFloorTerm
#check @WuPaper.R2RawMother.exceptionTerm_floor
#print axioms WuPaper.R2RawMother.exceptionTerm_floor
#check @WuPaper.R2RawMother.rawWeighted
#print axioms WuPaper.R2RawMother.rawWeighted
#check @WuPaper.R2RawMother.exceptionWeighted
#print axioms WuPaper.R2RawMother.exceptionWeighted
#check @WuPaper.R2RawMother.weighted_exact
#print axioms WuPaper.R2RawMother.weighted_exact
#check @WuPaper.R2RawMother.raw_source_finite_with_exception
#print axioms WuPaper.R2RawMother.raw_source_finite_with_exception
#check @WuPaper.R2RawMother.raw_source_with_exception
#print axioms WuPaper.R2RawMother.raw_source_with_exception
#check @WuPaper.R2RawMother.rawGamma20_unit_zero
#print axioms WuPaper.R2RawMother.rawGamma20_unit_zero
#check @WuPaper.R2RawMother.rawGamma21_unit_zero
#print axioms WuPaper.R2RawMother.rawGamma21_unit_zero
#check @WuPaper.R2RawMother.exceptionGamma20_unit_full
#print axioms WuPaper.R2RawMother.exceptionGamma20_unit_full
#check @WuPaper.R2RawMother.exceptionGamma21_unit_full
#print axioms WuPaper.R2RawMother.exceptionGamma21_unit_full
