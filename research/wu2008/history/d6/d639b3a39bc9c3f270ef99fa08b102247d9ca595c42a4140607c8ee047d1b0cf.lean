import MathlibNt.Wu2004MeanValue.OriginalLargeTransport
import MathlibNt.Wu2004MeanValue.OriginalTailAsymptotics
import MathlibNt.Wu2004MeanValue.OriginalCountPayment

/-!
# The unconditional large-product upper bound

The actual divisor-exception cardinality is at most `floor (sqrt N) + 1`.
The accepted power-saving payment, using the universal positive lower bound
for the Liu singular series, absorbs it. The integral is left unevaluated.
-/

namespace Wu2004MeanValue

open Filter Finset
open MathlibNt.SieveTheory.SingularSeries
noncomputable section

theorem originalLargeExceptionalBudget_le {N : ℕ} (hN : 1 ≤ N) :
    ((⌊Real.sqrt N⌋₊ + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) ^ (1 / 2 : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs1 : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hN1
  have hs := Nat.floor_le (Real.sqrt_nonneg (N : ℝ))
  rw [← Real.sqrt_eq_rpow]
  push_cast
  linarith

theorem eventually_originalLargeExceptionalBudget_paid (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((⌊Real.sqrt N⌋₊ + 1 : ℕ) : ℝ) ≤
        ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  filter_upwards [eventually_powerSaving_le_singular_margin 2 (1 / 2) ε
    (by norm_num) (by norm_num) hε, eventually_ge_atTop (1 : ℕ)] with N hp hN
  exact (originalLargeExceptionalBudget_le hN).trans hp

theorem eventually_originalLargeTriplesExceptional_paid (a η ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((originalLargeTriplesExceptional N a η).card : ℝ) ≤
        ε * liuSingularSeries N * N / Real.log N ^ 2 := by
  filter_upwards [eventually_originalLargeExceptionalBudget_paid ε hε] with N hp
  have hcard : ((originalLargeTriplesExceptional N a η).card : ℝ) ≤
      ((⌊Real.sqrt N⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast originalLargeTriplesExceptional_card_le N a η
  exact hcard.trans hp

/-- The literal strict large-product count. All parameters are fixed before
the eventual even integer, and no analytic estimate is an input hypothesis. -/
theorem originalLargeTripleCount_upper (a η ε : ℝ)
    (ha : 3 / 2 < a) (ha2 : a < 2) (hη : 0 < η) (hηh : η < 1 / 2)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      (originalLargeTripleCount N a η : ℝ) ≤
        (8 * (∫ u in ((a - 1) / a)..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε) *
          liuSingularSeries N * N / Real.log N ^ 2 := by
  have ha1 : 1 < a := by linarith
  have ha0 : 0 < a := by linarith
  have hτ : 1 / 3 < (a - 1) / a := by
    apply (lt_div_iff₀ ha0).mpr
    linarith
  have hτh : (a - 1) / a < 1 / 2 := by
    apply (div_lt_iff₀ ha0).mpr
    linarith
  obtain ⟨M, hM⟩ := tailOriginalSum_sharp_upper
    (η ^ ((a - 1) / a)) ((a - 1) / a) η (ε / 2)
    (Real.rpow_pos_of_pos hη _) hτ hτh hη hηh (by positivity)
  refine eventually_atTop.mp ?_
  filter_upwards [eventually_originalLargeExceptionalBudget_paid (ε / 2) (by positivity),
    eventually_ge_atTop M] with N hp hNM hEven
  have hfinite : (originalLargeTripleCount N a η : ℝ) ≤
      (tailOriginalSum N (η ^ ((a - 1) / a)) ((a - 1) / a) η : ℝ) +
        ((⌊Real.sqrt N⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast originalLargeTripleCount_le_tail_add_sqrt (N := N) ha1 hη.le
  calc
    _ ≤ _ := hfinite
    _ ≤ (8 * (∫ u in ((a - 1) / a)..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε / 2) *
        liuSingularSeries N * N / Real.log N ^ 2 +
        (ε / 2) * liuSingularSeries N * N / Real.log N ^ 2 :=
      add_le_add (hM N hNM hEven) hp
    _ = _ := by ring

end
end Wu2004MeanValue
