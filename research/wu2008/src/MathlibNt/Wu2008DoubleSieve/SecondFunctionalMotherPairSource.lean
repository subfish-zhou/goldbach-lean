import MathlibNt.Wu2008DoubleSieve.SecondFunctionalMotherPairGeometry

namespace Wu2008DoubleSieve.MotherPair
open Finset Real
open scoped Classical

theorem prefix_pair_carrier (N d p q : ℕ) :
    secondFunctionalMotherPrefixCarrier N d [p,q] =
      sourceSieveCarrier N (d*p*q) (d*N) p := by
  simp [fourthRowMotherPrefixCarrier, mul_assoc]

theorem tuple_pairs (P : Finset ℕ) :
    secondFunctionalMotherTuples P 2 =
      ((P ×ˢ P).filter fun x => x.1 < x.2).image (fun x => [x.1,x.2]) := by
  ext l
  rw [secondFunctionalMother_tuple_mem]
  constructor
  · rintro ⟨hl, hp, hm⟩
    obtain ⟨a,b,rfl⟩ := List.length_eq_two.mp hl
    simp at hp
    exact mem_image.mpr ⟨(a,b), mem_filter.mpr
      ⟨mem_product.mpr ⟨hm a (by simp), hm b (by simp)⟩, hp⟩, rfl⟩
  · rintro hl
    obtain ⟨⟨a,b⟩, hx, rfl⟩ := mem_image.mp hl
    obtain ⟨hx,hab⟩ := mem_filter.mp hx
    obtain ⟨ha,hb⟩ := mem_product.mp hx
    simpa using (show [a,b].length = 2 ∧ [a,b].Pairwise (· < ·) ∧
      ∀ q ∈ [a,b], q ∈ P from ⟨rfl, by simpa using hab, by simpa using And.intro ha hb⟩)

theorem prefix_pair_sum (N d M : ℕ) (a b c e f : ℝ) (v w : ℕ) :
    secondFunctionalMotherPrefixTerm N d M a b c e f [v,w] =
    ∑ p ∈ primeWindow M a f, ∑ q ∈ primeWindow M a f,
      if p < q ∧ secondFunctionalMotherColour b c e p = v ∧
        secondFunctionalMotherColour b c e q = w then
        (sourceSieveCount N (d*p*q) (d*N) p : ℝ) else 0 := by
  unfold secondFunctionalMotherPrefixTerm
  rw [show [v,w].length = 2 from rfl, tuple_pairs,
    sum_image (by
      intro x _ y _ h
      have hh : x.1 = y.1 ∧ x.2 = y.2 := by simpa using h
      exact Prod.ext hh.1 hh.2)]
  simp only [sum_filter, sum_product, List.map_cons, List.map_nil,
    List.cons.injEq, and_true, prefix_pair_carrier, sourceSieveCount]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp_all

theorem colour_zero (b c e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 0 ↔ (p:ℝ) < b := by
  unfold secondFunctionalMotherColour
  split_ifs <;> simp_all

theorem colour_one (b c e : ℝ) (p : ℕ) :
    secondFunctionalMotherColour b c e p = 1 ↔ b ≤ (p:ℝ) ∧ (p:ℝ) < c := by
  unfold secondFunctionalMotherColour
  split_ifs <;> simp_all

/-- Empty first physical band, for the original finite dictionary itself. -/
theorem raw_empty (N d M : ℕ) (a c e f : ℝ) :
    secondFunctionalMotherGamma N d M a a c e f 6 = 0 ∧
    secondFunctionalMotherGamma N d M a a c e f 7 = 0 ∧
    secondFunctionalMotherGamma N d M a a c e f 8 = 0 := by
  have hw : primeWindow M a a = ∅ := by
    ext p
    constructor
    · intro hp
      obtain ⟨_,_,ha,hb⟩ := mem_primeWindow.mp hp
      exact False.elim ((not_lt_of_ge ha) hb)
    · intro hp
      simp at hp
  have hz (w : ℕ) : secondFunctionalMotherPrefixTerm N d M a a c e f [0,w] = 0 := by
    rw [prefix_pair_sum]
    apply sum_eq_zero
    intro p hp
    apply sum_eq_zero
    intro q _
    have hp' := (mem_primeWindow.mp hp).2.2.1
    have hc : secondFunctionalMotherColour a c e p ≠ 0 := by
      rw [ne_eq, colour_zero]
      exact not_lt_of_ge hp'
    simp [hc]
  simp [secondFunctionalMotherGamma, fourthRowMotherPair, hw,
    secondFunctionalMotherGammaWords, hz]

theorem original_empty {p : SecondFunctionalParameters} (h : p.S = p.kappa1)
    {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ) :
    secondFunctionalMotherGammaSum p N δ W 6 = 0 ∧
    secondFunctionalMotherGammaSum p N δ W 7 = 0 ∧
    secondFunctionalMotherGammaSum p N δ W 8 = 0 := by
  have hz (d : ℕ) := raw_empty N d N (wuLocalCutoff N δ d p.kappa1)
    (wuLocalCutoff N δ d p.kappa2) (wuLocalCutoff N δ d p.kappa3)
    (wuLocalCutoff N δ d p.s)
  unfold secondFunctionalMotherGammaSum
  rw [h]
  refine ⟨sum_eq_zero (fun d _ => ?_), sum_eq_zero (fun d _ => ?_),
    sum_eq_zero (fun d _ => ?_)⟩
  · rw [(hz d).1, mul_zero]
  · rw [(hz d).2.1, mul_zero]
  · rw [(hz d).2.2, mul_zero]

theorem prefix_pair_restrict (N d M : ℕ) (a b c e f : ℝ) (v w : ℕ) :
    secondFunctionalMotherPrefixTerm N d M a b c e f [v,w] =
    ∑ p ∈ (primeWindow M a f).filter (fun p => secondFunctionalMotherColour b c e p = v),
      ∑ q ∈ (primeWindow M a f).filter (fun q => secondFunctionalMotherColour b c e q = w),
        if p < q then (sourceSieveCount N (d*p*q) (d*N) p : ℝ) else 0 := by
  rw [prefix_pair_sum]
  simp only [sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : secondFunctionalMotherColour b c e p = v
  · simp only [hp, if_true, true_and]
    apply sum_congr rfl
    intro q _
    split_ifs <;> simp_all
  · simp [hp]

theorem colour_zero_window (M : ℕ) {a b c e f : ℝ} (hbf : b ≤ f) :
    (primeWindow M a f).filter (fun p => secondFunctionalMotherColour b c e p = 0) =
      primeWindow M a b := by
  ext p
  simp only [mem_filter, mem_primeWindow, colour_zero]
  constructor
  · tauto
  · rintro ⟨hp,hM,ha,hb⟩
    exact ⟨⟨hp,hM,ha,hb.trans_le hbf⟩,hb⟩

theorem colour_one_window (M : ℕ) {a b c e f : ℝ} (hab : a ≤ b) (hcf : c ≤ f) :
    (primeWindow M a f).filter (fun p => secondFunctionalMotherColour b c e p = 1) =
      primeWindow M b c := by
  ext p
  simp only [mem_filter, mem_primeWindow, colour_one]
  constructor
  · tauto
  · rintro ⟨hp,hM,hb,hc⟩
    exact ⟨⟨hp,hM,hab.trans hb,hc.trans_le hcf⟩,hb,hc⟩

theorem raw_seven (N d M : ℕ) {a b c e f : ℝ} (hbf : b ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 7 =
      ∑ p ∈ primeWindow M a b, ∑ q ∈ primeWindow M a b,
        if p < q then (sourceSieveCount N (d*p*q) (d*N) p : ℝ) else 0 := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [prefix_pair_restrict, colour_zero_window M hbf]

theorem raw_eight (N d M : ℕ) {a b c e f : ℝ}
    (hab : a ≤ b) (hbf : b ≤ f) (hcf : c ≤ f) :
    secondFunctionalMotherGamma N d M a b c e f 8 =
      ∑ p ∈ primeWindow M a b, ∑ q ∈ primeWindow M b c,
        if p < q then (sourceSieveCount N (d*p*q) (d*N) p : ℝ) else 0 := by
  simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [prefix_pair_restrict, colour_zero_window M hbf, colour_one_window M hab hcf]

theorem window_range (N : ℕ) {A B : ℝ} (hB : B ≤ N) :
    primeWindow N A B = (range (N+1)).filter
      (fun p : ℕ => p.Prime ∧ p.Coprime N ∧ A ≤ (p:ℝ) ∧ (p:ℝ) < B) := by
  ext p
  simp only [mem_primeWindow, mem_filter, mem_range]
  constructor
  · intro hp
    have hn : p ≤ N := by exact_mod_cast hp.2.2.2.le.trans hB
    exact ⟨by omega,hp⟩
  · tauto

/-- A complete-label reindexing; no quotient by the product is taken. -/
theorem rect_sum {i : ℕ} (N : ℕ) (δ : ℝ) (W : Fin i → Finset ℕ)
    (A B C D : ℝ) (F : Gamma5ClassicalLabel → ℝ)
    (hB : ∀ d ∈ boxConvolutionSupport W, ((N:ℝ)^(1/2-δ)/d)^B ≤ N)
    (hD : ∀ d ∈ boxConvolutionSupport W, ((N:ℝ)^(1/2-δ)/d)^D ≤ N) :
    (∑ x ∈ rectLabels N δ W A B C D, F x) =
    ∑ d ∈ boxConvolutionSupport W,
      ∑ p ∈ primeWindow N (((N:ℝ)^(1/2-δ)/d)^A) (((N:ℝ)^(1/2-δ)/d)^B),
      ∑ q ∈ primeWindow N (((N:ℝ)^(1/2-δ)/d)^C) (((N:ℝ)^(1/2-δ)/d)^D),
        if p < q then F (d,p,q) else 0 := by
  simp only [rectLabels, sum_filter, sum_product]
  apply sum_congr rfl
  intro d hd
  rw [window_range N (hB d hd), window_range N (hD d hd)]
  simp only [sum_filter]
  apply sum_congr rfl
  intro p _
  by_cases hp : p.Prime ∧ p.Coprime N ∧
      ((N:ℝ)^(1/2-δ)/d)^A ≤ (p:ℝ) ∧ (p:ℝ) < ((N:ℝ)^(1/2-δ)/d)^B
  · rw [if_pos hp]
    apply sum_congr rfl
    intro q _
    split_ifs <;> first | rfl | (exfalso; tauto)
  · rw [if_neg hp]
    apply sum_eq_zero
    intro q _
    split_ifs with h
    · exact False.elim (hp ⟨h.1,h.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩)
    · rfl

 theorem cutoff_le_N {i k N : ℕ} {δ Δ x : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) (hx : x ≤ 1)
    {d : ℕ} (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V)) :
    ((N:ℝ)^(1/2-δ)/d)^x ≤ N := by
  have hg := gamma5Mass_support_geometry hN hδ hδhi hb hd
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hg.1
  have hQN : (N:ℝ)^(1/2-δ) ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hN1
      (show 1/2-δ ≤ 1 by linarith)
  have hRN : (N:ℝ)^(1/2-δ)/d ≤ N := by
    apply (div_le_iff₀ (by linarith : (0:ℝ) < d)).mpr
    nlinarith
  have hp : ((N:ℝ)^(1/2-δ)/d)^x ≤ (N:ℝ)^(1/2-δ)/d := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hg.2.2.1.le hx
  exact hp.trans hRN

/-- All four literal shared label counts equal the original mother source.
No parity assumption is needed; the finite range bounds follow from the source box. -/
theorem termCount_eq_original (P : SecondFunctionalParameters) (hP : AnalyticParameters P)
    (j : Term) {i k N : ℕ} {δ Δ : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (hb : wuSourceBox k δ N i Δ V) :
    termCount P j N δ (convolutionWuWindows N Δ V)
      (termLabels P j N δ (convolutionWuWindows N Δ V)) =
    secondFunctionalMotherGammaSum P N δ (convolutionWuWindows N Δ V) j.index := by
  obtain ⟨_,_,hbc,hce,hef,hf⟩ := parameter_order hP
  have hb1 : 1/P.kappa1 ≤ 1 := by linarith
  have hc1 : 1/P.kappa2 ≤ 1 := by linarith
  have he1 : 1/P.kappa3 ≤ 1 := by linarith
  have hB := fun d hd => cutoff_le_N hN hδ hδhi hb hb1 (d := d) hd
  have hC := fun d hd => cutoff_le_N hN hδ hδhi hb hc1 (d := d) hd
  have hE := fun d hd => cutoff_le_N hN hδ hδhi hb he1 (d := d) hd
  cases j with
  | gammaFive =>
    simp only [termCount, termLabels, fixedCount, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hC hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma, fourthRowMotherPair, sum_comm]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaSix =>
    simp only [termCount, termLabels, fixedCount, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hE]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d _
    rw [secondFunctionalMotherGamma, fourthRowMotherPair, sum_comm]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaSeven =>
    simp only [termCount, termLabels, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hB]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hd
    obtain ⟨_,_,_,hbc,hce,hef⟩ := secondFunctionalMother_source_cutoffs P hP.mother
      hN hδ hδhi hb hd
    rw [raw_seven N d N (hbc.trans (hce.trans hef))]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]
  | gammaEight =>
    simp only [termCount, termLabels, Term.index]
    rw [rect_sum N δ _ _ _ _ _ _ hB hC]
    unfold secondFunctionalMotherGammaSum
    apply sum_congr rfl
    intro d hd
    obtain ⟨_,_,hab,hbc,hce,hef⟩ := secondFunctionalMother_source_cutoffs P hP.mother
      hN hδ hδhi hb hd
    rw [raw_eight N d N hab (hbc.trans (hce.trans hef)) (hce.trans hef)]
    simp only [mul_sum, mul_ite, mul_zero, wuLocalCutoff, gamma5ClassicalProduct]

end Wu2008DoubleSieve.MotherPair
