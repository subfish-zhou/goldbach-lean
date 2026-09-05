import MathlibNt.AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducerHighAggregate
import MathlibNt.AnalyticNumberTheory.LargeSieve.PanWangDingLowEndpoint
import MathlibNt.AnalyticNumberTheory.LargeSieve.DirectConductorWeight

/-! Uniform logarithmic payment for the complete nonprincipal Liu source.
The cofactor remains free after the common threshold; conductor one is omitted
before applying the low-conductor estimate. -/

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiuWeight

namespace AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

theorem sum_inv_totient_le_four_log_sq {N D : ℕ}
    (hlog : 1 ≤ Real.log (N : ℝ)) (hD : D ≤ N) :
    (∑ m ∈ Icc 1 D, (m.totient : ℝ)⁻¹) ≤ 4 * Real.log (N : ℝ) ^ 2 := by
  calc
    _ ≤ conductorHarmonicFactor D ^ 2 := sum_inv_totient_le_harmonic_sq D
    _ ≤ conductorHarmonicFactor N ^ 2 :=
      pow_le_pow_left₀ (conductorHarmonicFactor_nonneg D)
        (conductorHarmonicFactor_mono hD) 2
    _ ≤ (1 + Real.log (N : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (conductorHarmonicFactor_nonneg N)
        (conductorHarmonicFactor_le N) 2
    _ ≤ _ := by nlinarith

theorem eventually_high_remainder_le (s : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      6984 * Real.log (N : ℝ) ^ 2 / N ≤
        6984 * N / Real.log (N : ℝ) ^ s := by
  have he := (isLittleO_log_rpow_rpow_atTop (s + 2)
    (show (0 : ℝ) < 1 by norm_num)).bound (show (0 : ℝ) < 1 by norm_num)
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually he, hl,
    eventually_ge_atTop (1 : ℕ)] with N he hlog hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hpow : Real.log (N : ℝ) ^ (s + 2) ≤ (N : ℝ) := by
    simpa only [Real.norm_eq_abs, Real.rpow_one, one_mul,
      abs_of_nonneg (Real.rpow_nonneg hLp.le _), abs_of_nonneg hNp.le] using he
  apply (div_le_div_iff₀ hNp (Real.rpow_pos_of_pos hLp s)).mpr
  have hmul : Real.log (N : ℝ) ^ 2 * Real.log (N : ℝ) ^ s ≤ (N : ℝ) := by
    rw [show s + 2 = 2 + s by ring, Real.rpow_add hLp, Real.rpow_two] at hpow
    exact hpow
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  nlinarith

/-- Both analytic means are paid, with one threshold before the changing
Liu source and the cofactor. The cutoff exponent is explicitly `s + 6`. -/
theorem nonprincipal_liu_source_log_saving (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ Real.sqrt N →
      PanLow.nonprincipalLow
          (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
          (panSourceD m) N (liuPanSourceIntervalLower N (s + 6))
          (liuPanSourceIntervalUpper N) ⌊lowConductor N (s + 6)⌋₊ +
        panIymHigh
          (panSourceG (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)) m)
          (panSourceD m) N (liuPanSourceIntervalLower N (s + 6))
          (liuPanSourceIntervalUpper N) ⌊lowConductor N (s + 6)⌋₊
          ⌊upperConductor N (s + 6)⌋₊ ≤ C * N / Real.log (N : ℝ) ^ s := by
  obtain ⟨CL, hCL, NL, hlow⟩ :=
    PanLow.nonprincipalLow_liuSource_endpoint s (s + 6) hs (by linarith)
  obtain ⟨CH, hCH, hhigh⟩ := chosen_high_source_log_saving
  obtain ⟨NH, hhigh⟩ := hhigh (s + 6) (1 / 3) (by linarith) (by norm_num)
  refine ⟨CL + CH + 6984, by positivity, ?_⟩
  apply eventually_atTop.mp
  have hl : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop NL, eventually_ge_atTop NH,
    eventually_ge_atTop (2 : ℕ), hl, eventually_high_remainder_le s]
    with N hNL hNH hN hlog hrem
  intro m hm hmN
  have hLp : 0 < Real.log (N : ℝ) := by linarith
  have hlow' := hlow N hNL (s + 6) m ⌊lowConductor N (s + 6)⌋₊ hm hmN
    (Nat.floor_le (Real.rpow_nonneg hLp.le _))
  have hA : (liuPanSourceIntervalUpper N : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hAN : liuPanSourceIntervalUpper N ≤ N := by
    exact_mod_cast hA.trans (Real.rpow_le_self_of_one_le
      (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num))
  have hf : ∀ a, ‖(liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ)‖ ≤ 1 := by
    intro a
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_liuWeight] using
      liuWeight_le_one N (liuSourceZ10 N) (liuSourceY3 N) a
  have hhigh' := hhigh N hNH m (liuPanSourceIntervalLower N (s + 6))
    (liuPanSourceIntervalUpper N)
    (fun a => (liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a : ℂ))
    hAN (by convert hA using 1; norm_num)
    (log_rpow_lt_liuPanSourceIntervalLower N (s + 6)).le hf
  have hmain : CH * (N : ℝ) * Real.log (N : ℝ) ^ (6 - (s + 6)) =
      CH * N / Real.log (N : ℝ) ^ s := by
    rw [show 6 - (s + 6) = -s by ring, Real.rpow_neg hLp.le, div_eq_mul_inv]
  rw [hmain] at hhigh'
  have hD : panSourceD m =
      (fun n => if n.Prime ∧ n.Coprime m then (1 : ℂ) else 0) := by
    funext n
    simp only [panSourceD, and_comm]
  calc
    _ ≤ CL * N / Real.log (N : ℝ) ^ s +
        (CH * N / Real.log (N : ℝ) ^ s + 6984 * Real.log (N : ℝ) ^ 2 / N) := by
      refine add_le_add ?_ hhigh'
      rw [hD]
      exact hlow'
    _ ≤ CL * N / Real.log (N : ℝ) ^ s +
        (CH * N / Real.log (N : ℝ) ^ s + 6984 * N / Real.log (N : ℝ) ^ s) :=
      add_le_add le_rfl (add_le_add le_rfl hrem)
    _ = _ := by ring

end AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer
