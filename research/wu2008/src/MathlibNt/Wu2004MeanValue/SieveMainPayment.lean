import MathlibNt.Wu2004MeanValue.TailMass
import MathlibNt.Wu2004MeanValue.BlockMass
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# Main-mass budgets for the actual upper-sieve consumers

The tail reserves a positive margin for both the sieve factor and the actual
sequence remainder. The block keeps the distinct logarithms at `H` and `2H`.
These inequalities concern the literal masses, not a replacement model mass.
-/

namespace Wu2004MeanValue

open Filter
open MathlibNt.SieveTheory.SingularSeries

private theorem exists_upperSieve_margin (I ε : ℝ) (hI : 0 ≤ I) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (I + δ) * (8 + δ) + δ ≤ 8 * I + ε := by
  let δ := min 1 (ε / (2 * (I + 10)))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hpay : δ * (2 * (I + 10)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (I + 10))).mp (min_le_right _ _)
  refine ⟨δ, hδ, ?_⟩
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1), mul_nonneg hδ.le hI]

/-- A single fixed positive margin pays the near-eight sieve factor and
the normalized remainder without changing the sharp integral coefficient. -/
theorem tailMass_sieve_budget (c τ η ε : ℝ) (hc : 0 < c)
    (hτ : 1 / 3 < τ) (hτh : τ < 1 / 2) (hη : 0 < η) (hη1 : η < 1)
    (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      0 ≤ tailMass N c τ η ∧
      tailMass N c τ η * ((8 + δ) * liuSingularSeries N / Real.log N) +
        δ * liuSingularSeries N * N / Real.log N ^ 2 ≤
      (8 * (∫ u in τ..(1 / 2 : ℝ), 1 / (u * (1 - u))) + ε) *
        liuSingularSeries N * N / Real.log N ^ 2 := by
  obtain ⟨δ, hδ, hmargin⟩ := exists_upperSieve_margin (tailIntegral τ) ε
    (tailIntegral_nonneg (by linarith) hτh.le) hε
  obtain ⟨M, hM⟩ := tailMass_sharp_upper c τ η hc hτ hτh hη hη1 δ hδ
  refine ⟨δ, hδ, max M 2, ?_⟩
  intro N hN
  have hNM := (le_max_left M 2).trans hN
  have hN2 := (le_max_right M 2).trans hN
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hf : 0 ≤ (8 + δ) * liuSingularSeries N / Real.log N := by
    positivity [liuSingularSeries_pos N]
  obtain ⟨hm0, hm⟩ := hM N hNM
  refine ⟨hm0, ?_⟩
  calc
    _ ≤ ((tailIntegral τ + δ) * ((N : ℝ) / Real.log N)) *
        ((8 + δ) * liuSingularSeries N / Real.log N) +
        δ * liuSingularSeries N * N / Real.log N ^ 2 :=
      add_le_add (mul_le_mul_of_nonneg_right hm hf) le_rfl
    _ = ((tailIntegral τ + δ) * (8 + δ) + δ) *
        (liuSingularSeries N * N / Real.log N ^ 2) := by ring
    _ ≤ (8 * tailIntegral τ + ε) *
        (liuSingularSeries N * N / Real.log N ^ 2) :=
      mul_le_mul_of_nonneg_right hmargin
        (by positivity [liuSingularSeries_pos N])
    _ = _ := by unfold tailIntegral; ring

/-- One constant bounds the actual block's complete main-plus-error budget,
uniformly in the later integer and endpoint parameters. -/
theorem blockMass_sieve_budget :
    ∃ K : ℝ, 0 < K ∧ ∀ H : ℝ, 4 ≤ H →
      ∀ (N : ℕ) (a η : ℝ), 3 / 2 < a →
      blockMass H N a η * (9 * liuSingularSeries N / Real.log (2 * H)) +
        liuSingularSeries N * H / Real.log H ^ 2 ≤
      K * liuSingularSeries N * H / Real.log H ^ 2 := by
  obtain ⟨M, hM, hmass⟩ := blockMass_uniform_bound
  refine ⟨9 * M + 1, by positivity, ?_⟩
  intro H hH N a η ha
  have hl : 0 < Real.log H := Real.log_pos (by linarith)
  have hlogs : Real.log H ≤ Real.log (2 * H) :=
    Real.log_le_log (by linarith) (by linarith)
  have hl2 : 0 < Real.log (2 * H) := hl.trans_le hlogs
  have hV : 9 * liuSingularSeries N / Real.log (2 * H) ≤
      9 * liuSingularSeries N / Real.log H :=
    div_le_div_of_nonneg_left (by positivity [liuSingularSeries_pos N]) hl hlogs
  have hm := hmass H hH N a η ha
  calc
    _ ≤ (M * H / Real.log H) * (9 * liuSingularSeries N / Real.log H) +
        liuSingularSeries N * H / Real.log H ^ 2 := by
      apply add_le_add _ le_rfl
      exact mul_le_mul hm.2 hV
        (by positivity [liuSingularSeries_pos N])
        (by positivity)
    _ = _ := by ring

end Wu2004MeanValue
