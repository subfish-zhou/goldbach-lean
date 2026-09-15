import SrcFifthGainAnalyticWeights

namespace WuSource.SrcFifthGain.Analytic
open Wu2008DoubleSieve WuTarget.Wu08FifthSource SharpMassBalance
open MeasureTheory Set Real
open scoped Interval
noncomputable section

def rationalGain (h : ℕ → ℝ) : ℝ := directedGain h realWeight
def massGain (h : ℕ → ℝ) : ℝ := directedGain h analyticMass

theorem rational_gain_literal (h : ℕ → ℝ) :
    rationalGain h =
      (135*h 15+520*h 16+940*h 17+1390*h 18+1890*h 19+2430*h 20+
        2770*h 21+2440*h 22+2040*h 23+1600*h 24+1110*h 25+540*h 26+42*h 27)/12500 := by
  norm_num [rationalGain, directedGain, realWeight, rationalWeight, weightNumerator,
    Finset.sum_range_succ]
  ring

theorem rational_gain_le_mass {h : ℕ → ℝ} (hn : ∀ j < 13, 0 ≤ h (15+j)) :
    rationalGain h ≤ massGain h := by
  unfold rationalGain massGain directedGain
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Finset.sum_le_sum (fun j hj => mul_le_mul_of_nonneg_right
    (rational_weight_le_mass (Finset.mem_range.mp hj)) (hn j (Finset.mem_range.mp hj)))

theorem mass_gain_le_grid {h : ℕ → ℝ} (hn : ∀ j < 13, 0 ≤ h (15+j)) :
    massGain h ≤ gridGain h :=
  directed_gain_le_grid hn (fun _j hj => analytic_mass_le hj)

theorem rational_gain_le_grid {h : ℕ → ℝ} (hn : ∀ j < 13, 0 ≤ h (15+j)) :
    rationalGain h ≤ gridGain h :=
  (rational_gain_le_mass hn).trans (mass_gain_le_grid hn)

theorem rational_gain_nonneg {h : ℕ → ℝ} (hn : ∀ j < 13, 0 ≤ h (15+j)) :
    0 ≤ rationalGain h := by
  unfold rationalGain directedGain
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun j hj =>
    mul_nonneg (thirteen_positive_weights (Finset.mem_range.mp hj)).1.le
      (hn j (Finset.mem_range.mp hj)))

theorem rational_gain_source {h : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j))) :
    rationalGain h ≤ sourceGain (wuImprovementLimit false δ) :=
  (rational_gain_le_grid hn).trans (grid_le_actual_source hδ hd hc)

theorem rational_gain_moving {h : ℕ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hd : δ ≤ 1/1000)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j))) :
    rationalGain h ≤ fifthHOnlyIntegral δ :=
  (rational_gain_source hδ hd hn hc).trans (actual_source_le_moving hδ hd)

theorem mass_gain_count {h : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 → δ ≤ d →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+massGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) :=
  certified_g5_count hd hn hc (fun _j hj => analytic_mass_le hj) le_rfl hε

theorem rational_gain_count {h : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hn : ∀ j < 13, 0 ≤ h (15+j))
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 → δ ≤ d →
      ∀ j < 13, h (15+j) ≤ wuImprovementLimit false δ (node (15+j)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+rationalGain h-ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤
        (fifthPairCount N : ℝ) :=
  certified_g5_count hd hn hc (fun _j hj => thirteen_rational_weights hj) le_rfl hε

theorem parameter_nodes_count {h : ℕ → ℝ} {d : ℝ} (hd : 0 < d)
    (hn : ∀ i ∈ Finset.Ico 15 28, 0 ≤ h i)
    (hc : ∀ δ : ℝ, 0 < δ → δ ≤ 1/1000 → δ ≤ d →
      ∀ i ∈ Finset.Ico 15 28, h i ≤ wuImprovementLimit false δ (node i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (fifthPairFlin+
        (135*h 15+520*h 16+940*h 17+1390*h 18+1890*h 19+2430*h 20+
          2770*h 21+2440*h 22+2040*h 23+1600*h 24+1110*h 25+540*h 26+42*h 27)/12500
        -ε)*wuSingularSeries N*N/log N^(2 : ℕ) ≤ (fifthPairCount N : ℝ) := by
  rw [← rational_gain_literal]
  apply rational_gain_count hd _ _ hε
  · intro j hj
    exact hn (15+j) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)
  · intro δ hδ hδhi hδd j hj
    exact hc δ hδ hδhi hδd (15+j) (Finset.mem_Ico.mpr ⟨by omega, by omega⟩)

theorem rational_gain_replaces_fixed (h : ℕ → ℝ) (base : ℝ) :
    (base+PositiveCoreResume.fifthGain)/4+
      (rationalGain h-PositiveCoreResume.fifthGain)/4 = (base+rationalGain h)/4 :=
  replacement_quarter base (rationalGain h)

end
end WuSource.SrcFifthGain.Analytic
