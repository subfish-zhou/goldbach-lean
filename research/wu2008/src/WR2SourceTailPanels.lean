import WR2SourceLogPanels
import W02Tail

noncomputable section
namespace WuPaper.SourceTailPanels
open Real Set MeasureTheory NodeExtension WuTarget.W02 Finset
open scoped Interval

def grid (a b : ℝ) (i : ℕ) : ℝ := a+(b-a)*(i:ℝ)/8

def panels (S : ℝ) (k : Fin 9) : ℝ :=
  let a := tailLeft S k
  let b := upperNode k
  if a < b then ∑ i ∈ range 8,
    SourceLogChord.cell (grid a b i) (grid a b (i+1))
      (SourceLogRational.lower ((grid a b i+1)/(S-1)))
      (SourceLogRational.lower ((grid a b (i+1)+1)/(S-1)))
  else 0

theorem panels_le_logMoment {S : ℝ} (hS : 3 ≤ S) (hS5 : S ≤ 5) (k : Fin 9) :
    panels S k ≤ logMoment (nodeBasis k) S := by
  rw [logMoment_basis_eq hS hS5]
  unfold panels tailIntegral
  dsimp only
  by_cases hab : tailLeft S k < upperNode k
  · rw [if_pos hab, if_pos hab.le]
    let a := tailLeft S k
    let b := upperNode k
    have haS : S-2 ≤ a := le_max_right _ _
    have ha : 0 < a := by linarith
    have hx (i : ℕ) (hi : i ≤ 8) : a ≤ grid a b i ∧ grid a b i ≤ b := by
      have h0 : (0:ℝ) ≤ i := Nat.cast_nonneg _
      have h8 : (i:ℝ) ≤ 8 := by exact_mod_cast hi
      dsimp [grid]
      change a < b at hab
      constructor <;> nlinarith
    have hp := SourceLogChord.rational_panels_le_integral (n := 8)
      (x := grid a b) (c := S-1) (by linarith)
      (fun i hi => ha.trans_le (hx i hi).1) (fun i _ => by
        simp only [grid, Nat.cast_add, Nat.cast_one]
        change a < b at hab
        linarith) (fun i hi => by linarith [(hx i hi).1])
    simpa only [grid, Nat.cast_zero, mul_zero, zero_div, add_zero, Nat.cast_ofNat,
      mul_div_cancel_right₀ _ (by norm_num : (8:ℝ) ≠ 0), add_sub_cancel] using hp
  · rw [if_neg hab]
    by_cases he : tailLeft S k ≤ upperNode k
    · rw [if_pos he]
      have heq := le_antisymm he (le_of_not_gt hab)
      rw [heq, intervalIntegral.integral_same]
    · rw [if_neg he]

end WuPaper.SourceTailPanels
#print axioms WuPaper.SourceTailPanels.panels_le_logMoment
