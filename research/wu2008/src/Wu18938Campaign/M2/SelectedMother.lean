import Wu18938Campaign.M2.ModulusBridge
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherSource

namespace Wu18938Campaign.M2

open Finset Wu2008DoubleSieve
open scoped Classical

noncomputable def selectedTerm (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ) : ℝ :=
  ∑ l ∈ secondFunctionalMotherTuples (primeWindow M a f) cs.length,
    if l.map (secondFunctionalMotherColour b c e) = cs then
      ((selectedCarrier N d l).card : ℝ) else 0

theorem selectedTerm_eq_prefix (N d M : ℕ) (a b c e f : ℝ) (cs : List ℕ)
    (hcs : 2 ≤ cs.length) :
    selectedTerm N d M a b c e f cs =
      secondFunctionalMotherPrefixTerm N d M a b c e f cs := by
  unfold selectedTerm secondFunctionalMotherPrefixTerm
  apply sum_congr rfl
  intro l hl
  obtain ⟨hlen, hord, hmem⟩ := (secondFunctionalMother_tuple_mem _ _ _).mp hl
  have hc := prefix_eq_selected (hlen ▸ hcs) hord
    (fun p hp => (mem_primeWindow.mp (hmem p hp)).1) (N := N) (d := d)
  rw [hc]

private theorem word_length {j : ℕ} {cs : List ℕ}
    (hcs : cs ∈ secondFunctionalMotherGammaWords j) : 2 ≤ cs.length := by
  unfold secondFunctionalMotherGammaWords at hcs
  split at hcs <;> simp_all <;> aesop

private theorem selected_words (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) :
    ((secondFunctionalMotherGammaWords j).map (selectedTerm N d M a b c e f)).sum =
      ((secondFunctionalMotherGammaWords j).map
        (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum := by
  congr 1
  apply List.map_congr_left
  intro cs hcs
  exact selectedTerm_eq_prefix N d M a b c e f cs (word_length hcs)

noncomputable def selectedGamma (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) : ℝ :=
  if j < 7 then secondFunctionalMotherGamma N d M a b c e f j
  else ((secondFunctionalMotherGammaWords j).map (selectedTerm N d M a b c e f)).sum

theorem selectedGamma_eq_prefix (N d M : ℕ) (a b c e f : ℝ) (j : ℕ) :
    selectedGamma N d M a b c e f j =
      secondFunctionalMotherGamma N d M a b c e f j := by
  unfold selectedGamma
  split_ifs with hj
  · rfl
  · have hg : secondFunctionalMotherGamma N d M a b c e f j =
        ((secondFunctionalMotherGammaWords j).map
          (secondFunctionalMotherPrefixTerm N d M a b c e f)).sum := by
      rcases j with _ | _ | _ | _ | _ | _ | _ | j
      all_goals first | omega | rfl
    rw [hg]
    exact selected_words N d M a b c e f j

noncomputable def selectedLocal (N d M : ℕ) (a b c e f : ℝ) : ℝ :=
  selectedGamma N d M a b c e f 1 - selectedGamma N d M a b c e f 2 -
    selectedGamma N d M a b c e f 3 - selectedGamma N d M a b c e f 4 +
      ∑ j ∈ Icc 5 21, selectedGamma N d M a b c e f j

theorem selectedLocal_eq_prefix (N d M : ℕ) (a b c e f : ℝ) :
    selectedLocal N d M a b c e f = secondFunctionalMotherLocal N d M a b c e f := by
  simp only [selectedLocal, selectedGamma_eq_prefix, secondFunctionalMotherLocal]

noncomputable def selectedWeighted (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) : ℝ :=
  ∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
    selectedLocal N d N (wuLocalCutoff N δ d p.S) (wuLocalCutoff N δ d p.kappa1)
      (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
      (wuLocalCutoff N δ d p.s)

theorem selectedWeighted_eq_prefix (p : SecondFunctionalParameters)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    selectedWeighted p N δ W = secondFunctionalMotherRHS p N δ W := by
  simp only [selectedWeighted, selectedLocal_eq_prefix,
    secondFunctionalMother_weighted_identity]

theorem selected_source_finite
    (p : SecondFunctionalParameters) (hp : p.MotherAdmissible)
    {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (hb : wuSourceBox k δ N i Δ V) :
    5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
      selectedWeighted p N δ (convolutionWuWindows N Δ V) +
        secondFunctionalMotherError p N δ (convolutionWuWindows N Δ V) := by
  rw [selectedWeighted_eq_prefix]
  exact secondFunctionalMother_source_finite p hp hN hδ hδhi hb

theorem selected_source
    (k : ℕ) (p : SecondFunctionalParameters) (hp : p.MotherAdmissible) {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
        5 * wuBoxPhi N δ (convolutionWuWindows N Δ V) p.s ≤
          selectedWeighted p N δ (convolutionWuWindows N Δ V) +
            ε * boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (convolutionWuWindows N Δ V) := by
  obtain ⟨T, hT, h⟩ := secondFunctionalMother_source k p hp hδ hδhi hε
  refine ⟨T, hT, ?_⟩
  intro N hN he i Δ V hb
  rw [selectedWeighted_eq_prefix]
  exact h N hN he i Δ V hb

end Wu18938Campaign.M2
