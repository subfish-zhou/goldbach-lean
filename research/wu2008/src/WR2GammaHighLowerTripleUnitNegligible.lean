import WR2GammaHighLowerTripleUnitPower

noncomputable section
namespace WuPaper.R2GammaHigh.LowerTriple
open Wu2008DoubleSieve LowerTripleGroupedFinite HighBoxRecovery Real Finset Filter
open scoped Classical Topology

/-- The genuine three-coordinate power cap pays the full unit mass, including all endpoints. -/
theorem unitMass_six_negligible {δ ε : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1/100) (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∀ k : Fin 6, unitMass j N δ k ≤ (ε/6)*((N:ℝ)/log N)*
        boxConvolutionReciprocalMass (windows j N)) ∧
      (∑ k : Fin 6, unitMass j N δ k) ≤ ε*((N:ℝ)/log N)*
        boxConvolutionReciprocalMass (windows j N) := by
  obtain ⟨T0,hT0,h0⟩ := high_slab_mass hδ hδhi
  have ha : 0 < (10*highEta)/2 := by norm_num [highEta]
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    ((unit_power_log_decay ha).eventually (gt_mem_nhds (show (0:ℝ) < ε/(6*5^3) by positivity)))
  refine ⟨max T0 T1,hT0.trans (le_max_left _ _),?_⟩
  intro N hN j
  have hN0 := (le_max_left T0 T1).trans hN
  have hN4 := hT0.trans hN0
  have hl : 0 < log (N:ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hsmall := (h1 N ((le_max_right T0 T1).trans hN)).le
  have hn : (N:ℝ)^(-(10*highEta)/2) ≤ ε/(6*5^3)/log N := by
    apply (le_div_iff₀ hl).mpr
    simpa only [neg_div, mul_comm] using hsmall
  let W := boxConvolutionReciprocalMass (windows j N)
  have hW : 0 ≤ W := sum_nonneg (fun _ _ => by positivity)
  have hj (k : Fin 6) : unitMass j N δ k ≤
      (ε/6) * ((N:ℝ)/log N) * W := by
    apply (unitMass_power_le j (by omega) hδ hδhi k (h0 N hN0 j)).trans
    calc
      _ ≤ 5^3 * (N:ℝ) * (ε/(6*5^3)/log N) * W :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by positivity)) hW
      _ = _ := by ring
  constructor
  · exact hj
  · have hh := sum_le_sum (s := (univ : Finset (Fin 6))) (fun k _ => hj k)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat] at hh
    calc
      _ ≤ 6 * ((ε/6) * ((N:ℝ)/log N) * W) := hh
      _ = _ := by dsimp only [W]; ring

end WuPaper.R2GammaHigh.LowerTriple
#print axioms WuPaper.R2GammaHigh.LowerTriple.unitMass_six_negligible
