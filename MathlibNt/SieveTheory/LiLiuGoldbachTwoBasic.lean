import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve

open Filter
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Every actual difference is at least two and strictly below N once the
uniform epsilon growth condition holds. No coprimality is assumed. -/
theorem goldbachDifferenceCarrier_bounds {N n : ℕ} {ε : ℝ}
    (hlarge : 1 < ε * N) (hn : n ∈ goldbachDifferenceCarrier N ε) :
    2 ≤ n ∧ n < N := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hn
  obtain ⟨hpN, hpPrime, hcut⟩ := Finset.mem_filter.mp hp
  have hpN' : p ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hpN)
  have hdiff : ε * N < ((N - p : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpN']
    linarith
  have hn1 : (1 : ℝ) < ((N - p : ℕ) : ℝ) := hlarge.trans hdiff
  have hnNat : 1 < N - p := by exact_mod_cast hn1
  constructor
  · omega
  · have hpPos := hpPrime.pos
    omega

/-- Li--Liu's two actual basic inequalities, before the subsequent Buchstab
expansions. The one threshold precedes N, kappa and sigma; the bad count is
retained, not assumed negligible. This does not assert positivity of D19. -/
theorem goldbach_two_basic_sieve_eventually (ε : ℝ) (hε : 0 < ε)
    (hεupper : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N → ∀ κ σ : ℝ,
      (1 : ℝ) / 21 < κ → κ < σ → σ ≤ (1 : ℝ) / 3 →
      goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ κ) +
        goldbachS1 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ σ) -
        2 * goldbachS2 (goldbachDifferenceCarrier N ε) N
          ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) -
        goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ κ) -
        goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ σ) -
        2 * goldbachBadCount (goldbachDifferenceCarrier N ε) N ≤
          2 * (D19 N : ℤ) := by
  obtain ⟨Nb, hb⟩ := goldbachBasic_finite_le_D19 ε hε
  obtain ⟨Ng, hg⟩ := exists_goldbachBasic_growth_cutoff ε hε
  have hpowers : ∀ᶠ N : ℕ in atTop, 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 21) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 21)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  apply Filter.Eventually.exists_forall_of_atTop
  filter_upwards [eventually_ge_atTop Nb, eventually_ge_atTop Ng,
    eventually_ge_atTop (1 : ℕ), hpowers] with N hNb hNg hN1 hpow
  intro hEven κ σ hκ hκσ hσ
  have hbase : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hκT : κ ≤ (9 : ℝ) / 19 - ε := by linarith
  have hσT : σ ≤ (9 : ℝ) / 19 - ε := by linarith
  have huκ : (2 : ℝ) ≤ (N : ℝ) ^ κ :=
    hpow.trans (Real.rpow_le_rpow_of_exponent_le hbase hκ.le)
  have huσ : (2 : ℝ) ≤ (N : ℝ) ^ σ :=
    huκ.trans (Real.rpow_le_rpow_of_exponent_le hbase hκσ.le)
  have hA : ∀ ⦃n : ℕ⦄, n ∈ goldbachDifferenceCarrier N ε → 2 ≤ n ∧ n < N :=
    fun _ hn => goldbachDifferenceCarrier_bounds (hg N hNg).1 hn
  have hk := goldbachBasicFiniteRHS_ge_S1_sub_S2_sub_S4_sub_X
    (goldbachDifferenceCarrier N ε) hEven hA huκ
    (Real.rpow_le_rpow_of_exponent_le hbase hκT)
  have hs := goldbachBasicFiniteRHS_ge_S1_sub_S2_sub_S4_sub_X
    (goldbachDifferenceCarrier N ε) hEven hA huσ
    (Real.rpow_le_rpow_of_exponent_le hbase hσT)
  have hbk := hb N hNb κ
  have hbs := hb N hNb σ
  simp only [goldbachPowerCutoff] at hbk hbs
  linarith

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig