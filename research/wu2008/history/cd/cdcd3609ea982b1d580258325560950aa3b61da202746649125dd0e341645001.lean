import MathlibNt.Wu2008DoubleSieve.TruncatedSixthMassPrime
import MathlibNt.Wu2008DoubleSieve.ReboxingGeometric

/-!
# Inner shrinking partitions of fixed exponent intervals

The terminal interval is omitted, not enlarged. The existing exact
geometric prime partition retains all prime labels in the other cells.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def truncatedSixthMassDelta (N : ℕ) : ℝ :=
  1 + log (N : ℝ) ^ (-4 : ℝ)

noncomputable def truncatedSixthMassStep (N : ℕ) : ℝ :=
  log (truncatedSixthMassDelta N) / log N

noncomputable def truncatedSixthMassGridSize (N : ℕ) (a b : ℝ) : ℕ :=
  ⌊(b - a) / truncatedSixthMassStep N⌋₊

noncomputable def truncatedSixthMassGridPoint (N : ℕ) (a : ℝ) (j : ℕ) : ℝ :=
  a + j * truncatedSixthMassStep N

noncomputable def truncatedSixthMassTerminal (N : ℕ) (a b : ℝ) : ℝ :=
  truncatedSixthMassGridPoint N a (truncatedSixthMassGridSize N a b)

theorem truncatedSixthMass_delta_legal {N : ℕ} (hN : 1 < N) :
    1 < truncatedSixthMassDelta N ∧
      1 + log (N : ℝ) ^ (-4 : ℝ) ≤ truncatedSixthMassDelta N ∧
      truncatedSixthMassDelta N < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) := by
  have hp := rpow_pos_of_pos (log_pos (by exact_mod_cast hN : (1 : ℝ) < N)) (-4 : ℝ)
  unfold truncatedSixthMassDelta
  exact ⟨by linarith, le_rfl, by linarith⟩

theorem truncatedSixthMass_step_pos {N : ℕ} (hN : 1 < N) :
    0 < truncatedSixthMassStep N :=
  div_pos (log_pos (truncatedSixthMass_delta_legal hN).1)
    (log_pos (by exact_mod_cast hN))

theorem truncatedSixthMass_step_tendsto :
    Tendsto truncatedSixthMassStep atTop (𝓝 0) := by
  have hlog := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hp : Tendsto (fun N : ℕ => log (N : ℝ) ^ (-4 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 4)).comp hlog
  have hΔ : Tendsto truncatedSixthMassDelta atTop (𝓝 1) := by
    change Tendsto (fun N : ℕ => 1 + log (N : ℝ) ^ (-4 : ℝ)) atTop (𝓝 1)
    simpa only [add_zero] using hp.const_add 1
  have hld : Tendsto (fun N => log (truncatedSixthMassDelta N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, log_one] using
      (continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hΔ
  exact hld.div_atTop hlog

theorem truncatedSixthMass_grid_terminal_bounds {N : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a ≤ b) :
    a ≤ truncatedSixthMassTerminal N a b ∧
      truncatedSixthMassTerminal N a b ≤ b ∧
      b < truncatedSixthMassTerminal N a b + truncatedSixthMassStep N := by
  have hh := truncatedSixthMass_step_pos hN
  have hf := Nat.floor_le (div_nonneg (sub_nonneg.mpr hab) hh.le)
  have hhi := Nat.lt_floor_add_one ((b - a) / truncatedSixthMassStep N)
  have hlo := (le_div_iff₀ hh).mp hf
  have hup := (div_lt_iff₀ hh).mp hhi
  unfold truncatedSixthMassTerminal truncatedSixthMassGridPoint truncatedSixthMassGridSize
  refine ⟨le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hh.le), ?_, ?_⟩ <;> linarith

theorem truncatedSixthMass_grid_point_mono {N : ℕ} (hN : 1 < N) (a : ℝ) :
    StrictMono (truncatedSixthMassGridPoint N a) := by
  intro i j hij
  unfold truncatedSixthMassGridPoint
  exact add_lt_add_right
    (mul_lt_mul_of_pos_right (by exact_mod_cast hij : (i : ℝ) < j)
      (truncatedSixthMass_step_pos hN)) _

theorem truncatedSixthMass_grid_point_bounds {N j : ℕ} {a b : ℝ}
    (hN : 1 < N) (hab : a ≤ b) (hj : j < truncatedSixthMassGridSize N a b) :
    a ≤ truncatedSixthMassGridPoint N a j ∧
      truncatedSixthMassGridPoint N a (j + 1) ≤ b := by
  have hm := (truncatedSixthMass_grid_point_mono hN a).monotone
  have hz : truncatedSixthMassGridPoint N a 0 = a := by
    simp [truncatedSixthMassGridPoint]
  exact ⟨by simpa only [hz] using hm (Nat.zero_le j),
    (hm (show j + 1 ≤ truncatedSixthMassGridSize N a b by omega)).trans
      (truncatedSixthMass_grid_terminal_bounds hN hab).2.1⟩

theorem truncatedSixthMass_terminal_tendsto {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun N => truncatedSixthMassTerminal N a b) atTop (𝓝 b) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (show Tendsto (fun N => b - truncatedSixthMassStep N) atTop (𝓝 b) by
      simpa using tendsto_const_nhds.sub truncatedSixthMass_step_tendsto)
    tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    have h := (truncatedSixthMass_grid_terminal_bounds (N := N) (by omega) hab).2.2
    linarith
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
    exact (truncatedSixthMass_grid_terminal_bounds (by omega) hab).2.1

theorem truncatedSixthMass_grid_power {N : ℕ} (hN : 1 < N) (a : ℝ) (j : ℕ) :
    (N : ℝ) ^ truncatedSixthMassGridPoint N a j =
      reboxingAlpha ((N : ℝ) ^ a) (truncatedSixthMassDelta N) 1 j := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : log (N : ℝ) ≠ 0 := (log_pos (by exact_mod_cast hN)).ne'
  have hD : 0 < truncatedSixthMassDelta N := by
    linarith [(truncatedSixthMass_delta_legal hN).1]
  have hh : (N : ℝ) ^ truncatedSixthMassStep N = truncatedSixthMassDelta N := by
    rw [rpow_def_of_pos hN0, truncatedSixthMassStep, mul_div_cancel₀ _ hl, exp_log hD]
  rw [truncatedSixthMassGridPoint, rpow_add hN0, mul_comm (j : ℝ),
    rpow_mul hN0.le, hh]
  simp [reboxingAlpha]

theorem truncatedSixthMass_grid_lower_endpoint {N : ℕ} (hN : 1 < N) (a : ℝ) (j : ℕ) :
    (N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1) / truncatedSixthMassDelta N =
      (N : ℝ) ^ truncatedSixthMassGridPoint N a j := by
  rw [truncatedSixthMass_grid_power hN, truncatedSixthMass_grid_power hN]
  push_cast
  rw [reboxingAlpha_step (by linarith [(truncatedSixthMass_delta_legal hN).1]),
    mul_div_cancel_right₀ _ (by linarith [(truncatedSixthMass_delta_legal hN).1])]

theorem truncatedSixthMass_grid_sum {N : ℕ} (hN : 1 < N) (a b : ℝ) (f : ℕ → ℝ) :
    (∑ p ∈ primeWindow N ((N : ℝ) ^ a) ((N : ℝ) ^ truncatedSixthMassTerminal N a b), f p) =
      ∑ j ∈ range (truncatedSixthMassGridSize N a b),
        ∑ p ∈ primeWindow N
          ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1) / truncatedSixthMassDelta N)
          ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1)), f p := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp_rw [truncatedSixthMass_grid_lower_endpoint hN]
  simp_rw [truncatedSixthMass_grid_power hN]
  have h := reboxingAlpha_sum_partition (rpow_pos_of_pos hN0 a)
    (truncatedSixthMass_delta_legal hN).1 N (truncatedSixthMassGridSize N a b) f (t := 1)
  simpa [truncatedSixthMassTerminal, reboxingAlpha_zero, truncatedSixthMass_grid_power hN] using h

theorem truncatedSixthMass_grid_disjoint {N : ℕ} (hN : 1 < N) (a : ℝ) :
    Pairwise (fun i j : ℕ => Disjoint
      (primeWindow N
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (i + 1) / truncatedSixthMassDelta N)
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (i + 1)))
      (primeWindow N
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1) / truncatedSixthMassDelta N)
        ((N : ℝ) ^ truncatedSixthMassGridPoint N a (j + 1)))) := by
  intro i j hij
  simp_rw [truncatedSixthMass_grid_lower_endpoint hN]
  have hmono := (truncatedSixthMass_grid_point_mono hN a).monotone
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN.le
  apply Finset.disjoint_left.mpr
  intro p hi hj
  have hi' := mem_primeWindow.mp hi
  have hj' := mem_primeWindow.mp hj
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hpow := rpow_le_rpow_of_exponent_le hNR (hmono (show i + 1 ≤ j by omega))
    exact (not_lt_of_ge hj'.2.2.1) (hi'.2.2.2.trans_le hpow)
  · have hpow := rpow_le_rpow_of_exponent_le hNR (hmono (show j + 1 ≤ i by omega))
    exact (not_lt_of_ge hi'.2.2.1) (hj'.2.2.2.trans_le hpow)

theorem truncatedSixthMass_trimmed_prime_tendsto {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N => truncatedSixthMassPrimeSum N a (truncatedSixthMassTerminal N a b))
      atTop (𝓝 (log (b / a))) := by
  have he : Tendsto (fun N =>
      truncatedSixthMassPrimeSum N a (truncatedSixthMassTerminal N a b) -
        log (truncatedSixthMassTerminal N a b / a)) atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨T, hT⟩ := eventually_atTop.mp (truncatedSixthMass_prime_uniform ha hε)
    refine ⟨max 2 T, ?_⟩
    intro N hN
    have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
    simpa [Real.dist_eq] using hT N ((le_max_right _ _).trans hN)
      a (truncatedSixthMassTerminal N a b) le_rfl
      (truncatedSixthMass_grid_terminal_bounds (by omega) hab).1
  have hl := ((truncatedSixthMass_terminal_tendsto hab).div_const a).log
    (div_ne_zero (ha.trans_le hab).ne' ha.ne')
  simpa using he.add hl

end Wu2008DoubleSieve
