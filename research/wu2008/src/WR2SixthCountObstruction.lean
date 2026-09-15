import WR2SixthCountWindows

noncomputable section
namespace WuPaper.R2SixthCount
open Real Finset Filter Wu2008DoubleSieve
open scoped Classical Topology

theorem high_pair_weight_separation {N p q m : ℕ} {l u v w delta : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v) (hp : p ∈ window N l u) (hq : q ∈ window N v w)
    (hhigh : (N : ℝ) ^ (1 / 4 : ℝ) < q) (hd : 0 ≤ delta)
    (k i : Fin m → ℕ) (D c : Fin m → ℝ) (V : (r : Fin m) → Fin (i r) → ℝ)
    (hb : ∀ r, wuSourceBox (k r) delta N (i r) (D r) (V r)) :
    convolutionCoeff (pairWindows N l u v w) (p * q) = 1 ∧
      (∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) (p * q) : ℝ)) = 0 := by
  refine ⟨separated_coefficient_one hN huv hp hq, ?_⟩
  exact Wu08G6HighActual.finite_source_combination_zero k i D c V hN hd hb
    (mem_window.mp hq).1 (dvd_mul_left q p) hhigh

theorem high_rectangle_not_source_combination {N p q m : ℕ} {l u v w delta : ℝ}
    (hN : 1 ≤ N) (huv : u ≤ v) (hp : p ∈ window N l u) (hq : q ∈ window N v w)
    (hhigh : (N : ℝ) ^ (1 / 4 : ℝ) < q) (hd : 0 ≤ delta)
    (k i : Fin m → ℕ) (D c : Fin m → ℝ) (V : (r : Fin m) → Fin (i r) → ℝ)
    (hb : ∀ r, wuSourceBox (k r) delta N (i r) (D r) (V r)) :
    (fun d => (convolutionCoeff (pairWindows N l u v w) d : ℝ)) ≠
      (fun d => ∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) d : ℝ)) := by
  intro he
  have hs := high_pair_weight_separation hN huv hp hq hhigh hd k i D c V hb
  have hv := congrFun he (p * q)
  rw [hs.1, hs.2] at hv
  norm_num at hv

theorem eventually_ab_source_separation :
    ∀ᶠ N : ℕ in atTop,
      ∃ pA qA pB qB : ℕ,
        (pA ∈ window N alpha beta ∧ qA ∈ window N beta aCeiling ∧
          (N : ℝ) ^ (1 / 4 : ℝ) < qA) ∧
        (pB ∈ window N alpha bCut ∧ qB ∈ window N aCeiling sigma ∧
          (N : ℝ) ^ (1 / 4 : ℝ) < qB) ∧
        convolutionCoeff (pairWindows N alpha beta beta aCeiling) (pA * qA) = 1 ∧
        convolutionCoeff (pairWindows N alpha bCut aCeiling sigma) (pB * qB) = 1 ∧
        ∀ delta : ℝ, 0 ≤ delta → ∀ m : ℕ,
          ∀ k i : Fin m → ℕ, ∀ D c : Fin m → ℝ,
          ∀ V : (r : Fin m) → Fin (i r) → ℝ,
          (∀ r, wuSourceBox (k r) delta N (i r) (D r) (V r)) →
          (∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) (pA * qA) : ℝ)) = 0 ∧
          (∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) (pB * qB) : ℝ)) = 0 := by
  filter_upwards [eventually_original_high_pairs, eventually_ge_atTop (1 : ℕ)] with N hpairs hN
  obtain ⟨⟨pA, qA, hpA, hqA, hhighA⟩, ⟨pB, qB, hpB, hqB, hhighB⟩⟩ := hpairs
  have hb : bCut ≤ aCeiling :=
    (parameter_order.2.2.1.trans (parameter_order.2.2.2.1.trans
      parameter_order.2.2.2.2.1)).le
  refine ⟨pA, qA, pB, qB, ⟨hpA, hqA, hhighA⟩, ⟨hpB, hqB, hhighB⟩,
    separated_coefficient_one hN le_rfl hpA hqA,
    separated_coefficient_one hN hb hpB hqB, ?_⟩
  intro delta hd m k i D c V hboxes
  exact ⟨(high_pair_weight_separation hN le_rfl hpA hqA hhighA hd k i D c V hboxes).2,
    (high_pair_weight_separation hN hb hpB hqB hhighB hd k i D c V hboxes).2⟩

theorem eventually_original_rectangles_not_source_combinations :
    ∀ᶠ N : ℕ in atTop, ∀ delta : ℝ, 0 ≤ delta → ∀ m : ℕ,
      ∀ k i : Fin m → ℕ, ∀ D c : Fin m → ℝ,
      ∀ V : (r : Fin m) → Fin (i r) → ℝ,
      (∀ r, wuSourceBox (k r) delta N (i r) (D r) (V r)) →
      (fun d => (convolutionCoeff (pairWindows N alpha beta beta aCeiling) d : ℝ)) ≠
        (fun d => ∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) d : ℝ)) ∧
      (fun d => (convolutionCoeff (pairWindows N alpha bCut aCeiling sigma) d : ℝ)) ≠
        (fun d => ∑ r, c r * (convolutionCoeff (convolutionWuWindows N (D r) (V r)) d : ℝ)) := by
  filter_upwards [eventually_ab_source_separation] with N hN
  obtain ⟨pA, qA, pB, qB, _, _, hA, hB, hz⟩ := hN
  intro delta hd m k i D c V hb
  have hzero := hz delta hd m k i D c V hb
  constructor
  · intro he
    have h := congrFun he (pA * qA)
    rw [hA, hzero.1] at h
    norm_num at h
  · intro he
    have h := congrFun he (pB * qB)
    rw [hB, hzero.2] at h
    norm_num at h

#check @WuPaper.R2SixthCount.high_pair_weight_separation
#check @WuPaper.R2SixthCount.high_rectangle_not_source_combination
#check @WuPaper.R2SixthCount.eventually_ab_source_separation
#check @WuPaper.R2SixthCount.eventually_original_rectangles_not_source_combinations
#print axioms WuPaper.R2SixthCount.high_pair_weight_separation
#print axioms WuPaper.R2SixthCount.high_rectangle_not_source_combination
#print axioms WuPaper.R2SixthCount.eventually_ab_source_separation
#print axioms WuPaper.R2SixthCount.eventually_original_rectangles_not_source_combinations
end WuPaper.R2SixthCount
