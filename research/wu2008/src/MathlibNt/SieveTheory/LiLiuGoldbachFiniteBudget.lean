import MathlibNt.SieveTheory.LiLiuGoldbachBadBound
import MathlibNt.SieveTheory.LiLiuGoldbachRepeatBound
import MathlibNt.SieveTheory.LiLiuGoldbachEndpointBound

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The actual four error counts, with all component bounds supplied by proofs.
The carrier is the actual prime-difference carrier, not an arbitrary count. -/
theorem goldbachFiniteError_le_446_of_growth (N : ℕ) (ε κ y : ℝ)
    (hN : 1 ≤ N) (hlarge : 1 < ε * N)
    (hκ : (1 : ℝ) / 21 < κ) (hκupper : κ ≤ (1 : ℝ) / 3)
    (hz : 2 ≤ (N : ℝ) ^ κ) (hzy : (N : ℝ) ^ κ ≤ y) :
    (goldbachFiniteError (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) y : ℝ) ≤
      446 * (N : ℝ) ^ (1 - κ) := by
  let A := goldbachDifferenceCarrier N ε
  have hA : ∀ n ∈ A, 1 ≤ n ∧ n < N := by
    intro n hn
    have hb := goldbachDifferenceCarrier_bounds hlarge hn
    exact ⟨by omega, hb.2⟩
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hz0 : 0 < (N : ℝ)^κ := Real.rpow_pos_of_pos hN0 _
  have hzN : ((N : ℝ)^κ)^2 ≤ (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    calc
      (N : ℝ) ^ (κ * (2 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
      _ = N := Real.rpow_one _
  have hX := goldbachBadCount_twice_le_four_div N ε ((N : ℝ)^κ) hN hz0 hzN
  have hQ : (goldbachQ A N ((N : ℝ)^κ) y : ℝ) ≤
      2 * (N : ℝ) / ((N : ℝ)^κ) :=
    (Int.cast_le.mpr (goldbachQ_le_goldbachQA A N ((N : ℝ)^κ) y hA)).trans
      (goldbachQA_real_le_two_mul_div A N ((N : ℝ)^κ) hA hz)
  have hR := goldbachR_real_le_forty_mul_div A N κ y hA hκ hz
  have hB := goldbachB6_le_four_hundred_mul_div_z A N hN hA hκ rfl hzy
  calc
    (goldbachFiniteError (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) y : ℝ) =
        ((2 * goldbachBadCount A N : ℤ) : ℝ) +
          (goldbachQ A N ((N : ℝ)^κ) y : ℝ) +
          (goldbachR A N ((N : ℝ)^κ) y : ℝ) +
          (goldbachB6 A N ((N : ℝ)^κ) y : ℝ) := by
            simp only [goldbachFiniteError, Int.cast_add, A]
    _ ≤ 446 * (N : ℝ) / ((N : ℝ)^κ) := by
      change ((2 * goldbachBadCount A N : ℤ) : ℝ) ≤ _ at hX
      exact (add_le_add (add_le_add (add_le_add hX hQ) hR) hB).trans_eq (by ring)
    _ = 446 * (N : ℝ) ^ (1 - κ) := by
      rw [Real.rpow_sub hN0, Real.rpow_one]
      ring

/-- A single epsilon-dependent threshold controls the actual error uniformly
in kappa and sigma. No evenness or analytic distribution input is needed. -/
theorem goldbachFiniteError_446_eventually (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ κ σ : ℝ,
      (1 : ℝ) / 21 < κ → κ < σ → σ ≤ (1 : ℝ) / 3 →
      0 ≤ goldbachFiniteError (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^κ) ((N : ℝ)^σ) ∧
      (goldbachFiniteError (goldbachDifferenceCarrier N ε) N
        ((N : ℝ)^κ) ((N : ℝ)^σ) : ℝ) ≤ 446 * (N : ℝ) ^ (1 - κ) := by
  obtain ⟨Ng, hg⟩ := exists_goldbachBasic_growth_cutoff ε hε
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Ng, eventually_ge_atTop (1 : ℕ), hpowers]
    with N hNg hN1 hpow
  intro κ σ hκ hκσ hσ
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hz : 2 ≤ (N : ℝ)^κ :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase hκ.le)
  have hzy : (N : ℝ)^κ ≤ (N : ℝ)^σ :=
    Real.rpow_le_rpow_of_exponent_le hbase hκσ.le
  exact ⟨goldbachFiniteError_nonneg _ _ _ _,
    goldbachFiniteError_le_446_of_growth N ε κ ((N : ℝ)^σ) hN1
      (hg N hNg).1 hκ (hκσ.le.trans hσ) hz hzy⟩

/-- Finite Goldbachbig with the actual D19 count and a proved explicit error.
This is a signed sieve lower bound, not positivity or the final 1+1.9 theorem. -/
theorem goldbachbig_finite_lower_bound_eventually (ε : ℝ) (hε : 0 < ε)
    (hεupper : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ κ σ : ℝ,
      (1 : ℝ) / 21 < κ → κ < σ → σ ≤ (1 : ℝ) / 3 →
      (((2 * goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) -
        2 * goldbachS2 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^((9 : ℝ)/19 - ε)) -
        goldbachS3Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^κ) ((N : ℝ)^σ) -
        2 * goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ)^σ) -
        goldbachS5Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^κ) ((N : ℝ)^σ) +
        goldbachS6Closed (goldbachDifferenceCarrier N ε) N
          ((N : ℝ)^κ) ((N : ℝ)^σ)) : ℤ) : ℝ) -
        446 * (N : ℝ) ^ (1 - κ) ≤ 2 * (D19 N : ℝ) := by
  obtain ⟨Nb, hb⟩ := goldbach_closed_sieve_lower_bound_eventually ε hε hεupper
  obtain ⟨Ne, he⟩ := goldbachFiniteError_446_eventually ε hε
  refine ⟨max Nb Ne, ?_⟩
  intro N hN hEven κ σ hκ hκσ hσ
  have hlo := hb N (le_trans (le_max_left Nb Ne) hN) hEven κ σ hκ hκσ hσ
  have herr := (he N (le_trans (le_max_right Nb Ne) hN) κ σ hκ hκσ hσ).2
  have hloR := (Int.cast_le (R := ℝ)).mpr hlo
  push_cast at hloR ⊢
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig