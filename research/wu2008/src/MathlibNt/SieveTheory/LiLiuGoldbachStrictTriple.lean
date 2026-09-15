import MathlibNt.SieveTheory.LiLiuGoldbachTwoBasic
import MathlibNt.SieveTheory.LiLiuGoldbachS4Split
import MathlibNt.SieveTheory.LiLiuGoldbachDoubleDifference

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Two actual basic estimates followed by H1, H2 and H3. The triple sum
is still strict; diagonal Q and noncoprime X remain actual counts. No
analytic positive-main-term estimate, repeated-triple or endpoint payment
is asserted here. The threshold is uniform in kappa and sigma. -/
theorem goldbach_strict_triple_lower_bound_eventually (ε : ℝ) (hε : 0 < ε)
    (hεupper : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ κ σ : ℝ,
      (1 : ℝ) / 21 < κ → κ < σ → σ ≤ (1 : ℝ) / 3 →
      2 * goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ κ) -
        2 * goldbachS2 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) -
        goldbachS3HalfOpen (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) -
        2 * goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ σ) -
        goldbachS5HalfOpen (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) +
        goldbachWStrict (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ κ) ((N : ℝ) ^ σ) -
        (2 * goldbachBadCount (goldbachDifferenceCarrier N ε) N +
          goldbachQ (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ κ) ((N : ℝ) ^ σ)) ≤
        2 * (D19 N : ℤ) := by
  obtain ⟨Nb,hb⟩ := goldbach_two_basic_sieve_eventually ε hε hεupper
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Nb, eventually_ge_atTop (1 : ℕ), hpowers]
    with N hNb hN1 hpow
  intro hEven κ σ hκ hκσ hσ
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hzy : (N : ℝ)^κ ≤ (N : ℝ)^σ :=
    Real.rpow_le_rpow_of_exponent_le hbase hκσ.le
  have hy2 : (2 : ℝ) ≤ (N : ℝ)^σ :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase (hκ.le.trans hκσ.le))
  have hyN : ((N : ℝ)^σ)^3 ≤ (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ N)]
    calc
      (N : ℝ) ^ (σ * (3 : ℕ)) ≤ (N : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase (by norm_num; linarith)
      _ = N := Real.rpow_one _
  have hB := hb N hNb hEven κ σ hκ hκσ hσ
  have h1 := goldbachS4_split_exact (goldbachDifferenceCarrier N ε) N hzy hy2 hyN
  have h2 := goldbachS1_two_buchstab_exact (goldbachDifferenceCarrier N ε) N hzy
  have h3 := goldbachDoubleDifference_eq_goldbachWStrict_sub_goldbachQ
    (goldbachDifferenceCarrier N ε) N ((N : ℝ)^κ) ((N : ℝ)^σ)
  omega

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig