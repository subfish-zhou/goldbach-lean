import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation18Weight
import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation20CorrectedFinal

noncomputable section
open Classical Finset
namespace AnalyticNumberTheory.LargeSieve
set_option maxRecDepth 4096

/-- The printed equation-(19) height uses the exponential I, not the legacy maximum W. -/
def chen1973Lemma6Eq19PrintedHeightReal (x level : ℕ) : ℝ :=
  (2 : ℝ) ^ level * Real.log x ^ (200 : ℕ) * chen1973Lemma6Equation20Ilx x level

def chen1973Lemma6Eq19PrintedHeight (x level : ℕ) : ℕ :=
  ⌈chen1973Lemma6Eq19PrintedHeightReal x level⌉₊

/-- Bind directly to the already public exponential I used by equation (20). -/
theorem chen1973Lemma6_actual_W_sq_le_Ilx_eventually :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L level : ℕ,
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) →
      chen1973Lemma6Eq19I x L level ^ 2 ≤ chen1973Lemma6Equation20Ilx x level := by
  obtain ⟨X₀, hX₀⟩ := chenEq18_actual_W_sq_le_source_I
  refine ⟨X₀, ?_⟩
  intro x hx L level hL
  simpa only [chen1973Lemma6Equation20Ilx, Real.rpow_natCast] using hX₀ x hx L level hL

/-- The original height pays the square of the actual arithmetic weight uniformly.
The statement is about the exact natural ceiling, not an assumed real cutoff. -/
theorem chen1973Lemma6_eq19_printedHeight_weight_payment :
    ∃ X₀ : ℝ, ∀ x : ℕ, X₀ ≤ (x : ℝ) → ∀ L level : ℕ,
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) →
      (((L * 2 ^ level : ℕ) : ℝ) * Real.log x ^ (100 : ℕ) *
        chen1973Lemma6Eq19I x L level ^ 2 ≤ chen1973Lemma6Eq19PrintedHeight x level) ∧
      chen1973Lemma6Eq19Height x L level ≤ chen1973Lemma6Eq19PrintedHeight x level := by
  obtain ⟨X₀, hX₀⟩ := chen1973Lemma6_actual_W_sq_le_Ilx_eventually
  refine ⟨X₀, ?_⟩
  intro x hx L level hL
  have hW := hX₀ x hx L level hL
  have hW1 : 1 ≤ chen1973Lemma6Eq19I x L level := by
    unfold chen1973Lemma6Eq19I
    exact Finset.le_max' _ 1 (by simp)
  have hWI : chen1973Lemma6Eq19I x L level ≤ chen1973Lemma6Equation20Ilx x level := by
    have hh : chen1973Lemma6Eq19I x L level ≤ chen1973Lemma6Eq19I x L level ^ 2 := by nlinarith
    exact hh.trans hW
  constructor
  · calc
      _ ≤ (Real.log x ^ (100 : ℕ) * (2 : ℝ) ^ level) * Real.log x ^ (100 : ℕ) *
          chen1973Lemma6Equation20Ilx x level := by
        push_cast
        gcongr
      _ = chen1973Lemma6Eq19PrintedHeightReal x level := by
        unfold chen1973Lemma6Eq19PrintedHeightReal
        ring
      _ ≤ chen1973Lemma6Eq19PrintedHeight x level := Nat.le_ceil _
  · unfold chen1973Lemma6Eq19Height chen1973Lemma6Eq19PrintedHeight
    apply Nat.ceil_mono
    unfold chen1973Lemma6Eq19PrintedHeightReal
    exact mul_le_mul_of_nonneg_left hWI (by positivity)

end AnalyticNumberTheory.LargeSieve
