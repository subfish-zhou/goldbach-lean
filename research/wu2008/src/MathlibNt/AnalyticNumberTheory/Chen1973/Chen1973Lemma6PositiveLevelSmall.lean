import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation19BetaSmall
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20AlphaSmall
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20BetaSmall

noncomputable section
open Classical Complex Finset MeasureTheory Set
namespace AnalyticNumberTheory.LargeSieve

/-- Both actual complementary-cell integrals are paid at the same printed height.
The cutoff is source geometry, not an analytic moment hypothesis. -/
theorem chen1973Lemma6_equation20_actual_cell_small
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
      ∀ L B lastD level k m : ℕ,
      Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k →
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  obtain ⟨Cα, hCα, Xα, hXα⟩ := chen1973Lemma6_equation20_small_alpha_actual_beta
  obtain ⟨Xβ, hXβ⟩ := eq20small_actual_beta_paid ε hε hεu
  refine ⟨Cα+1, by positivity, max Xα Xβ, ?_⟩
  intro x hx L B lastD level k m P hcut
  have hcap : (chen1973Lemma6Eq20SourceQ L level : ℝ) ≤ 2*(x:ℝ)^((1:ℝ)/2) := by
    have hq := eq20small_source_Q_cut P ε hcut
    have hx1 : (1:ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by have := P.hx; omega)
    have hp := Real.rpow_le_rpow_of_exponent_le hx1
      (show (1:ℝ)/2-ε ≤ 1/2 by linarith)
    linarith
  have ha := hXα x ((le_max_left Xα Xβ).trans hx) L B lastD level k m
    ε hε.le hεu.le P hcap
  have hb := hXβ x ((le_max_right Xα Xβ).trans hx) L B lastD level k m P hcut
  calc
    _ ≤ Cα*x/Real.log x^20 + 2*(x:ℝ)^((1:ℝ)/2)*
        chen1973Lemma6Eq20CorrectedSecondIntegral x L level B k m
          (chen1973Lemma6Equation20H x level k ε) := ha
    _ ≤ Cα*x/Real.log x^20 + x/Real.log x^20 := add_le_add le_rfl hb
    _ = _ := by ring

/-- Uniform corrected-kernel estimate over every positive-level source cell.
The branch split and Perron-order condition are derived internally. This does
not cover the level-zero contour or assert the literal printed radial comparison. -/
theorem chen1973Lemma6_positive_level_actual_cell_small
    (ε : ℝ) (hε : 0 < ε) (hεu : ε < 1/10) :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) →
      ∀ L B lastD level k m : ℕ,
      0 < L → 0 < B → 1 ≤ level →
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) → Real.log x ^ (100 : ℕ) < L+1 →
      (B : ℝ) ≤ (x : ℝ)^((13:ℝ)/30) → (x : ℝ)^((13:ℝ)/30) < B+1 →
      L * 2^level ≤ 2*lastD →
      (lastD : ℝ) ≤ (x : ℝ)^((1:ℝ)/2-ε) →
      chen1973Lemma6NmBlockActual x L level B k m ≤ C*x/Real.log x^20 := by
  obtain ⟨C₁, hC₁, X₁, hX₁⟩ := chen1973Lemma6_equation19_actual_cell_small ε hε hεu
  obtain ⟨C₂, hC₂, X₂, hX₂⟩ := chen1973Lemma6_equation20_actual_cell_small ε hε hεu
  refine ⟨max C₁ C₂, hC₁.trans_le (le_max_left _ _),
    max (max X₁ X₂) (max 3 (Real.exp 3)), ?_⟩
  intro x hx L B lastD level k m hL hB hlevel hLl hLu hBl hBu hLast hcut
  rcases max_le_iff.mp hx with ⟨hx₁₂, hxlarge⟩
  rcases max_le_iff.mp hx₁₂ with ⟨hx₁, hx₂⟩
  rcases max_le_iff.mp hxlarge with ⟨hx3real, hxexp⟩
  have hx3 : 3 ≤ x := by exact_mod_cast hx3real
  have hlog3 : (3:ℝ) ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hlog1 : (1:ℝ) ≤ Real.log x := by linarith
  have horder : 4 ≤ chen1973PerronOrder (x:ℝ)+1 := by
    unfold chen1973PerronOrder
    have hf : 3 ≤ ⌊Real.log (x:ℝ)⌋₊ := Nat.le_floor hlog3
    omega
  have budget_mono : Monotone (fun C : ℝ => C*x/Real.log x^20) := by
    intro C D hCD
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCD (Nat.cast_nonneg x)) (by positivity)
  rcases chen1973Lemma6_eq19_or_eq20 (x := x) hlevel hLast with h19 | h20
  · let P : Chen1973Lemma6Eq19SourceParameters x L B lastD level k :=
      ⟨hx3, hL, hB, hlevel, hlog1, hLl, hLu, hBl, hBu, h19⟩
    have hh := hX₁ x hx₁ L B lastD level k m P hcut hLast
    exact hh.trans (budget_mono (le_max_left C₁ C₂))
  · let P : Chen1973Lemma6Eq20ComplementarySourceParameters x L B lastD level k :=
      ⟨hx3, horder, hL, hB, hlevel, hlog1, hLl, hLu, hBl, hBu, h20⟩
    have hh := hX₂ x hx₂ L B lastD level k m P hcut
    exact hh.trans (budget_mono (le_max_right C₁ C₂))

end AnalyticNumberTheory.LargeSieve
