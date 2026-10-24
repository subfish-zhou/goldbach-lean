import WR2GammaHighFourUnitPower

noncomputable section
namespace WuPaper.R2GammaHigh.FourUnit
open Wu2008DoubleSieve FourPrimeUnit Real Finset Filter
open scoped Classical Topology

/-- Pay all four original unit sources by their genuine N^(20/23) power cap. -/
theorem unit_four_paid {δ ε : ℝ} (hd : 0 < δ) (hh : δ ≤ 1/100) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ j : Fin 3,
      (∑ k : Fin 4, actualSource N δ (Wu04RemainingCore.row j) (windows j N) k) ≤
        ε*truncatedSixthMassScale N := by
  obtain ⟨T0,hT0,h0⟩ := HighSix.Omega3Upper.power_log_scale_paid 1
    (by positivity : 0 < ε/4) (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ)<3/23)
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    ((tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (1:ℝ)))
  refine ⟨max T0 T1,by omega,?_⟩
  intro N hN j
  have hl := h1 N (by omega)
  dsimp only [Function.comp_apply] at hl
  have hn : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have heq : (N:ℝ)^(20/23:ℝ) = (N:ℝ)/(N:ℝ)^(3/23:ℝ) := by
    calc
      _ = (N:ℝ)^((1:ℝ)-3/23) := by norm_num
      _ = (N:ℝ)^1/(N:ℝ)^(3/23:ℝ) := rpow_sub hn _ _
      _ = _ := by rw [rpow_one]
  have hs (k : Fin 4) : actualSource N δ (Wu04RemainingCore.row j) (windows j N) k ≤
      (ε/4)*truncatedSixthMassScale N := by
    calc
      _ ≤ (N:ℝ)^(20/23:ℝ)*(1+log N) := source_power_bound j k (by omega) hd hh
      _ ≤ (N:ℝ)^(20/23:ℝ)*(2*log N) := by gcongr; linarith
      _ = 2*N*log N^1/(N:ℝ)^(3/23:ℝ) := by rw [heq]; ring
      _ ≤ _ := h0 N (by omega)
  have hs' := sum_le_sum (s := (univ : Finset (Fin 4))) (fun k _ => hs k)
  simpa only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    show (4:ℝ)*((ε/4)*truncatedSixthMassScale N) = ε*truncatedSixthMassScale N by ring] using hs'

end WuPaper.R2GammaHigh.FourUnit
#print axioms WuPaper.R2GammaHigh.FourUnit.unit_four_paid
