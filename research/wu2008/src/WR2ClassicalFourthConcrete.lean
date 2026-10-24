import WR2ClassicalFourthConditions

noncomputable section
namespace WuPaper.ClassicalFourthConditions
open Real Set ClassicalFourthRecurrence

/-- Monotone numerator replacement uses the exact positive outer weight. -/
theorem kernel_le_numeric {f : ℝ → ℝ} {s A : ℝ}
    (hs : 3 ≤ s) (hr : s ≤ ClassicalFourth.R-1) (hf : f s ≤ A) :
    ClassicalFourth.kernel f s ≤ A/(s*((1:ℝ)/2-(100/1327)*s)) := by
  have hs0 : 0 < s := by linarith
  have hr0 : 0 < ClassicalFourth.R-s := by linarith
  have hw : 0 ≤ ClassicalFourth.weight s := by unfold ClassicalFourth.weight; positivity
  have h := mul_le_mul_of_nonneg_left hf hw
  unfold ClassicalFourth.kernel
  apply h.trans
  rw [ClassicalFourth.weight_literal hs0.ne' hr0.ne']
  exact le_of_eq (by ring)

/-- The only remaining hypotheses are finite, generated integer/logarithm checks. -/
theorem fourth_upper_of_certificates
    (hlog : ∀ i < 10541, ClassicalB.splitUpper (node 2 i) ≤ val ClassicalFourthData.Bq i)
    (hB : ∀ i < 10540, BPay i)
    (hC : ∀ i < 2540, CPay i)
    (hD : ∀ i < 2540, DPay i)
    (hO : ∀ i < 10540, OuterPay i)
    (hQ : ∀ i < 10541, OuterPoint i) :
    Wu08TerminalAlignment.fourthMain ≤ (1964373:ℝ)/100000 := by
  have hb0 : val ClassicalFourthData.B 0 = 0 := by
    have he : ClassicalFourthData.B 0 = 0 := rfl
    simp only [val,he,Nat.cast_zero,zero_div]
  have hc0 : val ClassicalFourthData.C 0 = 0 := by
    have he : ClassicalFourthData.C 0 = 0 := rfl
    simp only [val,he,Nat.cast_zero,zero_div]
  have hd0 : val ClassicalFourthData.D 0 = 0 := by
    have he : ClassicalFourthData.D 0 = 0 := rfl
    simp only [val,he,Nat.cast_zero,zero_div]
  have ho0 : val ClassicalFourthData.outer 0 = 0 := by
    have he : ClassicalFourthData.outer 0 = 0 := rfl
    simp only [val,he,Nat.cast_zero,zero_div]
  have hb (i : ℕ) (hi : i ≤ 10540) : Wu08OriginalFirstSteps.B (node 3 i) ≤ val ClassicalFourthData.B i :=
    B_node_upper _ _ hb0 (fun j hj => hlog j (by omega)) (fun j hj => B_payment (hB j hj)) hi
  have hc (i : ℕ) (hi : i ≤ 2540) : Wu08OriginalFirstSteps.C (node 4 i) ≤ val ClassicalFourthData.C i :=
    C_node_upper _ _ hc0 (fun j hj => hb j (by omega)) (fun j hj => C_payment (hC j hj)) hi
  have hd (i : ℕ) (hi : i ≤ 2540) : Wu08OriginalFirstSteps.D (node 5 i) ≤ val ClassicalFourthData.D i :=
    D_node_upper _ _ hd0 hc (fun j hj => D_payment (hD j hj)) hi
  have hqi (i : ℕ) (hi : i ≤ 8000) :
      ClassicalFourth.kernel ClassicalFourth.initial (node 3 i) ≤ val ClassicalFourthData.outerq i := by
    have hs := node_bounds (3:ℝ) hi
    have hsr : node 3 i ≤ ClassicalFourth.R-1 := by norm_num [ClassicalFourth.R] at hs ⊢; linarith [hs.2]
    have hn : ClassicalFourth.initial (node 3 i) ≤ 1+val ClassicalFourthData.B i+val tail i := by
      have ht : 0 ≤ val tail i := by positivity
      unfold ClassicalFourth.initial
      linarith only [hb i (by omega),ht]
    exact (kernel_le_numeric hs.1 hsr hn).trans (outer_point (by omega) (hQ i (by omega)))
  have hqt (i : ℕ) (hi : i ≤ 2540) :
      ClassicalFourth.kernel ClassicalFourth.terminal (node 5 i) ≤ val ClassicalFourthData.outerq (8000+i) := by
    have he : node 3 (8000+i) = node 5 i := by simp [node]; ring
    have ht : tail (8000+i) = ClassicalFourthData.D i := by simp [tail]
    have hbi := hb (8000+i) (by omega)
    rw [he] at hbi
    have hs := node_bounds (5:ℝ) hi
    have hsr : node 5 i ≤ ClassicalFourth.R-1 := by norm_num [ClassicalFourth.R] at hs ⊢; exact hs.2
    have hn : ClassicalFourth.terminal (node 5 i) ≤
        1+val ClassicalFourthData.B (8000+i)+val tail (8000+i) := by
      simp only [val,ht]
      unfold ClassicalFourth.terminal
      have hdi := hd i hi
      dsimp only [val] at hbi hdi
      linarith only [hbi,hdi]
    have hq := outer_point (by omega : 8000+i ≤ 10540) (hQ (8000+i) (by omega))
    rw [he] at hq
    exact (kernel_le_numeric (by linarith [hs.1]) hsr hn).trans hq
  have h := fourth_upper_of_table _ _ ho0 hqi hqt (fun i hi => outer_payment (hO i hi))
  apply h.trans
  have hv : val ClassicalFourthData.outer 10540 = (4910932051664422:ℝ)/1000000000000000 := rfl
  rw [hv]
  norm_num

end WuPaper.ClassicalFourthConditions
#print axioms WuPaper.ClassicalFourthConditions.fourth_upper_of_certificates
