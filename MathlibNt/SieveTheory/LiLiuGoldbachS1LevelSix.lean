import MathlibNt.SieveTheory.LiLiuGoldbachB10FibreSieve
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The fixed lower-sieve endpoint from the original `α = 4 / 53` geometry. -/
noncomputable def S1LevelSixZ (N : ℕ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ (4 / 53 : ℝ))

/-- The corresponding `s = 6` sieve level `D = Z^6`. -/
def S1LevelSixD (N : ℕ) : ℕ :=
  S1LevelSixZ N ^ 6

theorem S1LevelSix_two_le_Z {N : ℕ} (hN : 2 ≤ N) :
    2 ≤ S1LevelSixZ N := by
  unfold S1LevelSixZ
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hpow : (1 : ℝ) < (N : ℝ) ^ (4 / 53 : ℝ) :=
    Real.one_lt_rpow hN1 (by norm_num)
  have hpow' : ((1 : ℕ) : ℝ) < (N : ℝ) ^ (4 / 53 : ℝ) := by simpa using hpow
  have hceil : 1 < Nat.ceil ((N : ℝ) ^ (4 / 53 : ℝ)) := Nat.lt_ceil.mpr hpow'
  omega

theorem S1LevelSix_two_le_D {N : ℕ} (hN : 2 ≤ N) :
    2 ≤ S1LevelSixD N := by
  have hZ : 2 ≤ S1LevelSixZ N := S1LevelSix_two_le_Z hN
  unfold S1LevelSixD
  have hZpos : 0 < S1LevelSixZ N := by omega
  have hpow : S1LevelSixZ N ≤ S1LevelSixZ N ^ 6 := by
    simpa using
      (Nat.pow_le_pow_right hZpos (show (1 : ℕ) ≤ 6 by omega) :
        S1LevelSixZ N ^ 1 ≤ S1LevelSixZ N ^ 6)
  exact hZ.trans hpow

private theorem S1LevelSix_D_le_sixtyFour_mul_rpow {N : ℕ} (hN : 1 ≤ N) :
    (S1LevelSixD N : ℝ) ≤ 64 * (N : ℝ) ^ (24 / 53 : ℝ) := by
  let x : ℝ := (N : ℝ) ^ (4 / 53 : ℝ)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by norm_num)
  have hceil : (S1LevelSixZ N : ℝ) ≤ 2 * x := by
    unfold S1LevelSixZ
    have hlt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have hsum : x + 1 ≤ 2 * x := by linarith
    exact hlt.le.trans hsum
  have hpow : (S1LevelSixZ N : ℝ) ^ 6 ≤ (2 * x) ^ 6 := by
    exact pow_le_pow_left₀ (by positivity) hceil 6
  calc
    (S1LevelSixD N : ℝ) = (S1LevelSixZ N : ℝ) ^ 6 := by simp [S1LevelSixD]
    _ ≤ (2 * x) ^ 6 := hpow
    _ = 64 * (N : ℝ) ^ (24 / 53 : ℝ) := by
      dsimp [x]
      rw [mul_pow]
      norm_num
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
      norm_num

private theorem S1LevelSix_eventually_cutoff_dominates (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      2 ≤ N ∧
      2 ≤ S1LevelSixZ N ∧
      2 ≤ S1LevelSixD N ∧
      S1LevelSixD N ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
  have hlog :
      ∀ᶠ N : ℕ in atTop,
        Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ (5 / 212 : ℝ) :=
    MathlibNt.SieveTheory.LiuWeight.eventually_pan_log_rpow_le_rpow B (5 / 212)
      (by norm_num)
  have hconst :
      ∀ᶠ N : ℕ in atTop, (64 : ℝ) ≤ (N : ℝ) ^ (5 / 212 : ℝ) := by
    exact ((tendsto_rpow_atTop (show 0 < (5 / 212 : ℝ) by norm_num)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (64 : ℝ))
  filter_upwards [eventually_ge_atTop (2 : ℕ), hlog, hconst] with N hN hlogN hconstN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogPos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogPowPos : 0 < Real.log (N : ℝ) ^ B := Real.rpow_pos_of_pos hlogPos B
  have hgap :
      64 * Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ (5 / 106 : ℝ) := by
    calc
      64 * Real.log (N : ℝ) ^ B
        ≤ (N : ℝ) ^ (5 / 212 : ℝ) * (N : ℝ) ^ (5 / 212 : ℝ) := by
          gcongr
      _ = (N : ℝ) ^ (5 / 106 : ℝ) := by
          rw [← Real.rpow_add hN0]
          congr 1
          norm_num
  have hupper :
      64 * (N : ℝ) ^ (24 / 53 : ℝ) ≤
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := by
    apply (le_div_iff₀ hlogPowPos).2
    have hmul :=
      mul_le_mul_of_nonneg_right hgap
        (Real.rpow_nonneg hN0.le (24 / 53 : ℝ))
    calc
      64 * (N : ℝ) ^ (24 / 53 : ℝ) * Real.log (N : ℝ) ^ B
        = 64 * Real.log (N : ℝ) ^ B * (N : ℝ) ^ (24 / 53 : ℝ) := by ring
      _ ≤ (N : ℝ) ^ (5 / 106 : ℝ) * (N : ℝ) ^ (24 / 53 : ℝ) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [← Real.rpow_add hN0]
          congr 1
          norm_num
  have hcut :
      S1LevelSixD N ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    rw [MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_eq_upper]
    apply Nat.le_floor
    calc
      (S1LevelSixD N : ℝ) ≤ 64 * (N : ℝ) ^ (24 / 53 : ℝ) :=
        S1LevelSix_D_le_sixtyFour_mul_rpow hN1
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := hupper
      _ = AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor N B := by
          rw [AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor,
            AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.lowConductor,
            Real.sqrt_eq_rpow]
  exact ⟨hN, S1LevelSix_two_le_Z hN, S1LevelSix_two_le_D hN, hcut⟩

theorem S1LevelSix_panModulusCutoff_eventually (B : ℝ) (_hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 ≤ S1LevelSixZ N ∧
      2 ≤ S1LevelSixD N ∧
      S1LevelSixD N ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B + 1 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (S1LevelSix_eventually_cutoff_dominates B)
  refine ⟨max 2 N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hN₀N : N₀ ≤ N := (le_max_right _ _).trans hN
  rcases hN₀ N hN₀N with ⟨_, hZ, hD, hcut⟩
  exact ⟨hZ, hD, le_trans hcut (Nat.le_succ _)⟩

theorem S1LevelSix_ceil_rootD_eq_Z (N : ℕ) :
    Nat.ceil (((S1LevelSixD N : ℕ) : ℝ) ^ (1 / 6 : ℝ)) = S1LevelSixZ N := by
  have hz0 : 0 ≤ (S1LevelSixZ N : ℝ) := by positivity
  have hroot :
      (((S1LevelSixD N : ℕ) : ℝ) ^ (1 / 6 : ℝ)) = (S1LevelSixZ N : ℝ) := by
    unfold S1LevelSixD
    rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hz0]
    norm_num
  rw [hroot, Nat.ceil_natCast]

theorem S1LevelSix_logD_div_logZ_eq_six {N : ℕ} (hZ : 2 ≤ S1LevelSixZ N) :
    Real.log (S1LevelSixD N : ℝ) / Real.log (S1LevelSixZ N : ℝ) = 6 := by
  have hz0 : 0 < (S1LevelSixZ N : ℝ) := by
    exact_mod_cast (show 0 < S1LevelSixZ N by omega)
  have hlogZ : 0 < Real.log (S1LevelSixZ N : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (show 1 < S1LevelSixZ N by omega))
  have hlog :
      Real.log (S1LevelSixD N : ℝ) = 6 * Real.log (S1LevelSixZ N : ℝ) := by
    unfold S1LevelSixD
    rw [Nat.cast_pow, ← Real.rpow_natCast, Real.log_rpow hz0]
    norm_num
  apply (div_eq_iff hlogZ.ne').2
  linarith

theorem S1LevelSix_lt_Z_of_lt_rpow {N ℓ : ℕ}
    (hℓ : (ℓ : ℝ) < (N : ℝ) ^ (4 / 53 : ℝ)) :
    ℓ < S1LevelSixZ N := by
  unfold S1LevelSixZ
  exact Nat.lt_ceil.mpr hℓ

theorem S1LevelSix_lt_powSix_of_lt {Z p : ℕ} (hZ : 2 ≤ Z) (hp : p < Z) :
    p < Z ^ 6 := by
  have hpow : Z ≤ Z ^ 6 := by
    simpa using
      (Nat.pow_le_pow_right (show 0 < Z by omega) (show (1 : ℕ) ≤ 6 by omega) :
        Z ^ 1 ≤ Z ^ 6)
  exact lt_of_lt_of_le hp hpow

theorem S1LevelSix_lt_D_of_lt_Z {N p : ℕ}
    (hZ : 2 ≤ S1LevelSixZ N) (hp : p < S1LevelSixZ N) :
    p < S1LevelSixD N := by
  simpa [S1LevelSixD] using S1LevelSix_lt_powSix_of_lt hZ hp

theorem S1LevelSix_primeFactor_lt_D
    {N p : ℕ} (hN : 2 ≤ N) (hp : p.Prime)
    (hpP : p ∣ goldbachB10ProdPrimes N ((N : ℝ) ^ (4 / 53 : ℝ))) :
    p < S1LevelSixD N := by
  have hpZ : p < S1LevelSixZ N :=
    S1LevelSix_lt_Z_of_lt_rpow (prime_dvd_goldbachB10ProdPrimes_lt hp hpP)
  exact S1LevelSix_lt_D_of_lt_Z (S1LevelSix_two_le_Z hN) hpZ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig