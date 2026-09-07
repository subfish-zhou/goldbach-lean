import MathlibNt.SieveTheory.LiLiuGoldbachS1Carrier
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The natural lower-sieve level attached to the fixed `beta = 4 / 33`
and arbitrary fixed `4 ≤ s < 33 / 8`. -/
noncomputable def S1BetaGeometryD (N : ℕ) (s : ℝ) : ℕ :=
  Nat.ceil ((N : ℝ) ^ ((4 / 33 : ℝ) * s))

/-- The genuine real Suzuki endpoint attached to `S1BetaGeometryD`. -/
noncomputable def S1BetaGeometryZeta (N : ℕ) (s : ℝ) : ℝ :=
  (S1BetaGeometryD N s : ℝ) ^ (1 / s)

/-- The natural Suzuki endpoint obtained by transporting the genuine real root
through `Nat.ceil`. -/
noncomputable def S1BetaGeometryZ (N : ℕ) (s : ℝ) : ℕ :=
  Nat.ceil (S1BetaGeometryZeta N s)

private theorem S1BetaGeometry_s_pos {s : ℝ} (hs4 : 4 ≤ s) : 0 < s := by
  linarith

private theorem S1BetaGeometry_s_one_le {s : ℝ} (hs4 : 4 ≤ s) : 1 ≤ s := by
  linarith

private theorem S1BetaGeometry_gap_pos {s : ℝ} (hslt : s < (33 / 8 : ℝ)) :
    0 < (1 / 2 : ℝ) - (4 / 33 : ℝ) * s := by
  linarith

theorem S1BetaGeometry_two_le_D {N : ℕ} {s : ℝ} (hN : 2 ≤ N) (hs : 0 < s) :
    2 ≤ S1BetaGeometryD N s := by
  unfold S1BetaGeometryD
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (show 1 < N by omega)
  have hexp : 0 < (4 / 33 : ℝ) * s := by positivity
  have hpow : (1 : ℝ) < (N : ℝ) ^ ((4 / 33 : ℝ) * s) :=
    Real.one_lt_rpow hN1 hexp
  have hpow' : ((1 : ℕ) : ℝ) < (N : ℝ) ^ ((4 / 33 : ℝ) * s) := by
    simpa using hpow
  have hceil : 1 < Nat.ceil ((N : ℝ) ^ ((4 / 33 : ℝ) * s)) := Nat.lt_ceil.mpr hpow'
  omega

theorem S1BetaGeometry_one_lt_zeta {N : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs : 0 < s) :
    1 < S1BetaGeometryZeta N s := by
  unfold S1BetaGeometryZeta
  have hD1 : (1 : ℝ) < (S1BetaGeometryD N s : ℝ) := by
    exact_mod_cast (show 1 < S1BetaGeometryD N s by omega)
  exact Real.one_lt_rpow hD1 (one_div_pos.mpr hs)

theorem S1BetaGeometry_two_le_Z {N : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs : 0 < s) :
    2 ≤ S1BetaGeometryZ N s := by
  unfold S1BetaGeometryZ
  have hzeta : ((1 : ℕ) : ℝ) < S1BetaGeometryZeta N s := by
    simpa using S1BetaGeometry_one_lt_zeta hD hs
  have hceil : 1 < Nat.ceil (S1BetaGeometryZeta N s) := Nat.lt_ceil.mpr hzeta
  omega

theorem S1BetaGeometry_rpow_le_zeta {N : ℕ} {s : ℝ} (hs : 0 < s) :
    (N : ℝ) ^ (4 / 33 : ℝ) ≤ S1BetaGeometryZeta N s := by
  have hceil :
      (N : ℝ) ^ ((4 / 33 : ℝ) * s) ≤ (S1BetaGeometryD N s : ℝ) := by
    exact Nat.le_ceil _
  have hroot :
      ((N : ℝ) ^ ((4 / 33 : ℝ) * s)) ^ (1 / s) ≤
        ((S1BetaGeometryD N s : ℝ)) ^ (1 / s) := by
    exact Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg N) _) hceil (by positivity)
  have hmul : ((4 / 33 : ℝ) * s) * (1 / s) = (4 / 33 : ℝ) := by
    field_simp [hs.ne']
  calc
    (N : ℝ) ^ (4 / 33 : ℝ) = ((N : ℝ) ^ ((4 / 33 : ℝ) * s)) ^ (1 / s) := by
      rw [← Real.rpow_mul (Nat.cast_nonneg N), hmul]
    _ ≤ (S1BetaGeometryD N s : ℝ) ^ (1 / s) := hroot

private theorem S1BetaGeometry_D_le_two_mul_rpow {N : ℕ} {s : ℝ}
    (hN : 1 ≤ N) (hs : 0 < s) :
    (S1BetaGeometryD N s : ℝ) ≤ 2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s) := by
  let x : ℝ := (N : ℝ) ^ ((4 / 33 : ℝ) * s)
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hx1 : 1 ≤ x := by
    dsimp [x]
    exact Real.one_le_rpow (by exact_mod_cast hN) (by positivity)
  have hceil : (S1BetaGeometryD N s : ℝ) ≤ 2 * x := by
    unfold S1BetaGeometryD
    have hlt : (Nat.ceil x : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
    have hsum : x + 1 ≤ 2 * x := by linarith
    exact hlt.le.trans hsum
  simpa [x] using hceil

theorem S1BetaGeometry_zeta_le_rpow_eventually
    (s η : ℝ) (hs4 : 4 ≤ s) (hη : 0 < η) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      S1BetaGeometryZeta N s ≤ (N : ℝ) ^ ((4 / 33 : ℝ) + η) := by
  let C : ℝ := (2 : ℝ) ^ (1 / s)
  have hs : 0 < s := S1BetaGeometry_s_pos hs4
  have hconst : ∀ᶠ N : ℕ in atTop, C ≤ (N : ℝ) ^ η := by
    exact ((tendsto_rpow_atTop hη).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop C)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hconst
  refine ⟨max 2 N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hDle :
      (S1BetaGeometryD N s : ℝ) ≤ 2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s) :=
    S1BetaGeometry_D_le_two_mul_rpow hN1 hs
  have hzeta :
      S1BetaGeometryZeta N s ≤ C * (N : ℝ) ^ (4 / 33 : ℝ) := by
    unfold S1BetaGeometryZeta
    calc
      (S1BetaGeometryD N s : ℝ) ^ (1 / s) ≤
          (2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s)) ^ (1 / s) := by
            exact Real.rpow_le_rpow (by positivity) hDle (by positivity)
      _ = (2 : ℝ) ^ (1 / s) * (((N : ℝ) ^ ((4 / 33 : ℝ) * s)) ^ (1 / s)) := by
            rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
      _ = C * (N : ℝ) ^ (4 / 33 : ℝ) := by
            dsimp [C]
            congr 1
            have hmul : ((4 / 33 : ℝ) * s) * (1 / s) = (4 / 33 : ℝ) := by
              field_simp [hs.ne']
            rw [← Real.rpow_mul (Nat.cast_nonneg N), hmul]
  have hmul :
      C * (N : ℝ) ^ (4 / 33 : ℝ) ≤
        (N : ℝ) ^ η * (N : ℝ) ^ (4 / 33 : ℝ) := by
    exact mul_le_mul_of_nonneg_right (hN₀ N hNN₀) (Real.rpow_nonneg hN0.le _)
  calc
    S1BetaGeometryZeta N s ≤ C * (N : ℝ) ^ (4 / 33 : ℝ) := hzeta
    _ ≤ (N : ℝ) ^ η * (N : ℝ) ^ (4 / 33 : ℝ) := hmul
    _ = (N : ℝ) ^ ((4 / 33 : ℝ) + η) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

theorem S1BetaGeometry_eventually_ge_constant
    (s R : ℝ) (hs : 0 < s) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      R ≤ (S1BetaGeometryD N s : ℝ) := by
  have hpow : ∀ᶠ N : ℕ in atTop, R ≤ (N : ℝ) ^ ((4 / 33 : ℝ) * s) := by
    exact ((tendsto_rpow_atTop (by positivity : 0 < (4 / 33 : ℝ) * s)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop R)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hpow
  refine ⟨max 2 N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hNN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  exact (hN₀ N hNN₀).trans (Nat.le_ceil _)

private theorem S1BetaGeometry_zeta_le_D_real {N : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs1 : 1 ≤ s) :
    S1BetaGeometryZeta N s ≤ (S1BetaGeometryD N s : ℝ) := by
  have hs : 0 < s := by linarith
  have hD1 : (1 : ℝ) ≤ (S1BetaGeometryD N s : ℝ) := by
    exact_mod_cast (show 1 ≤ S1BetaGeometryD N s by omega)
  unfold S1BetaGeometryZeta
  exact Real.rpow_le_self_of_one_le hD1 ((div_le_one hs).2 hs1)

private theorem S1BetaGeometry_eventually_cutoff_dominates
    (s B : ℝ) (hs4 : 4 ≤ s) (hslt : s < 33 / 8) :
    ∀ᶠ N : ℕ in atTop,
      4 ≤ N ∧
      S1BetaGeometryD N s ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
  let gap : ℝ := (1 / 2 : ℝ) - (4 / 33 : ℝ) * s
  have hs : 0 < s := S1BetaGeometry_s_pos hs4
  have hgap : 0 < gap := S1BetaGeometry_gap_pos hslt
  have hlog :
      ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ (gap / 2) :=
    MathlibNt.SieveTheory.LiuWeight.eventually_pan_log_rpow_le_rpow B (gap / 2)
      (by positivity)
  have hconst : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (gap / 2) := by
    exact ((tendsto_rpow_atTop (by positivity : 0 < gap / 2)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (2 : ℝ))
  filter_upwards [eventually_ge_atTop (4 : ℕ), hlog, hconst] with N hN hlogN hconstN
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogPos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogPowPos : 0 < Real.log (N : ℝ) ^ B := Real.rpow_pos_of_pos hlogPos B
  have hgapBound :
      2 * Real.log (N : ℝ) ^ B ≤ (N : ℝ) ^ gap := by
    calc
      2 * Real.log (N : ℝ) ^ B
        ≤ (N : ℝ) ^ (gap / 2) * (N : ℝ) ^ (gap / 2) := by
            gcongr
      _ = (N : ℝ) ^ gap := by
            rw [← Real.rpow_add hN0]
            congr 1
            dsimp [gap]
            ring
  have hupper :
      2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s) ≤
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := by
    apply (le_div_iff₀ hlogPowPos).2
    have hmul := mul_le_mul_of_nonneg_right hgapBound
      (Real.rpow_nonneg hN0.le ((4 / 33 : ℝ) * s))
    calc
      2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s) * Real.log (N : ℝ) ^ B
        = 2 * Real.log (N : ℝ) ^ B * (N : ℝ) ^ ((4 / 33 : ℝ) * s) := by ring
      _ ≤ (N : ℝ) ^ gap * (N : ℝ) ^ ((4 / 33 : ℝ) * s) := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      _ = (N : ℝ) ^ ((1 : ℝ) / 2) := by
            rw [← Real.rpow_add hN0]
            congr 1
            dsimp [gap]
            ring
  have hcut :
      S1BetaGeometryD N s ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    rw [MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_eq_upper]
    apply Nat.le_floor
    calc
      (S1BetaGeometryD N s : ℝ) ≤ 2 * (N : ℝ) ^ ((4 / 33 : ℝ) * s) :=
        S1BetaGeometry_D_le_two_mul_rpow hN1 hs
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := hupper
      _ = AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor N B := by
            rw [AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.upperConductor,
              AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer.lowConductor,
              Real.sqrt_eq_rpow]
  exact ⟨hN, hcut⟩

theorem S1BetaGeometry_panModulusCutoff_eventually
    (s B : ℝ) (hs4 : 4 ≤ s) (hslt : s < 33 / 8) (_hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 ≤ S1BetaGeometryD N s ∧
      1 < S1BetaGeometryZeta N s ∧
      2 ≤ S1BetaGeometryZ N s ∧
      S1BetaGeometryD N s ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B + 1 := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (S1BetaGeometry_eventually_cutoff_dominates s B hs4 hslt)
  refine ⟨max 4 N₀, le_max_left _ _, ?_⟩
  intro N hN
  have hNN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hs : 0 < s := S1BetaGeometry_s_pos hs4
  have hDcut : S1BetaGeometryD N s ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B :=
    (hN₀ N hNN₀).2
  have hD : 2 ≤ S1BetaGeometryD N s := S1BetaGeometry_two_le_D (by omega) hs
  have hzeta : 1 < S1BetaGeometryZeta N s := S1BetaGeometry_one_lt_zeta hD hs
  have hZ : 2 ≤ S1BetaGeometryZ N s := S1BetaGeometry_two_le_Z hD hs
  exact ⟨hD, hzeta, hZ, le_trans hDcut (Nat.le_succ _)⟩

@[simp] theorem S1BetaGeometry_ceil_zeta_eq_Z (N : ℕ) (s : ℝ) :
    Nat.ceil (S1BetaGeometryZeta N s) = S1BetaGeometryZ N s := rfl

theorem S1BetaGeometry_logD_div_logZeta_eq_s {N : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs : 0 < s) :
    Real.log (S1BetaGeometryD N s : ℝ) / Real.log (S1BetaGeometryZeta N s) = s := by
  have hzetaLogPos : 0 < Real.log (S1BetaGeometryZeta N s) := by
    exact Real.log_pos (S1BetaGeometry_one_lt_zeta hD hs)
  have hDpos : 0 < (S1BetaGeometryD N s : ℝ) := by
    exact_mod_cast (show 0 < S1BetaGeometryD N s by omega)
  have hlog :
      Real.log (S1BetaGeometryZeta N s) =
        (1 / s) * Real.log (S1BetaGeometryD N s : ℝ) := by
    unfold S1BetaGeometryZeta
    rw [Real.log_rpow hDpos]
  apply (div_eq_iff hzetaLogPos.ne').2
  calc
    Real.log (S1BetaGeometryD N s : ℝ)
      = s * ((1 / s) * Real.log (S1BetaGeometryD N s : ℝ)) := by
          field_simp [hs.ne']
    _ = s * Real.log (S1BetaGeometryZeta N s) := by rw [hlog]

theorem S1BetaGeometry_Z_le_D {N : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs1 : 1 ≤ s) :
    S1BetaGeometryZ N s ≤ S1BetaGeometryD N s := by
  unfold S1BetaGeometryZ S1BetaGeometryZeta
  exact Nat.ceil_le.mpr (S1BetaGeometry_zeta_le_D_real hD hs1)

theorem S1BetaGeometry_lt_D_of_lt_zeta {N p : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs1 : 1 ≤ s)
    (hp : (p : ℝ) < S1BetaGeometryZeta N s) :
    p < S1BetaGeometryD N s := by
  have hpD : (p : ℝ) < (S1BetaGeometryD N s : ℝ) :=
    hp.trans_le (S1BetaGeometry_zeta_le_D_real hD hs1)
  exact_mod_cast hpD

theorem S1BetaGeometry_lt_D_of_lt_Z {N p : ℕ} {s : ℝ}
    (hD : 2 ≤ S1BetaGeometryD N s) (hs1 : 1 ≤ s)
    (hp : p < S1BetaGeometryZ N s) :
    p < S1BetaGeometryD N s := by
  exact lt_of_lt_of_le hp (S1BetaGeometry_Z_le_D hD hs1)

theorem S1BetaGeometry_primeFactor_lt_D
    {N p : ℕ} {s : ℝ} (hN : 2 ≤ N) (hs4 : 4 ≤ s) (hp : p.Prime)
    (hpP : p ∣ goldbachS1ProdPrimes N (S1BetaGeometryZeta N s)) :
    p < S1BetaGeometryD N s := by
  have hs : 0 < s := S1BetaGeometry_s_pos hs4
  have hs1 : 1 ≤ s := S1BetaGeometry_s_one_le hs4
  have hpz : (p : ℝ) < S1BetaGeometryZeta N s :=
    (prime_dvd_goldbachS1ProdPrimes_iff hp).mp hpP |>.1
  exact S1BetaGeometry_lt_D_of_lt_zeta (S1BetaGeometry_two_le_D hN hs) hs1 hpz

theorem S1BetaGeometry_threshold
    (s B η : ℝ) (hs4 : 4 ≤ s) (hslt : s < 33 / 8) (hB : 0 ≤ B) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 ≤ S1BetaGeometryD N s ∧
      1 < S1BetaGeometryZeta N s ∧
      2 ≤ S1BetaGeometryZ N s ∧
      (N : ℝ) ^ (4 / 33 : ℝ) ≤ S1BetaGeometryZeta N s ∧
      S1BetaGeometryZeta N s ≤ (N : ℝ) ^ ((4 / 33 : ℝ) + η) ∧
      S1BetaGeometryD N s ≤ MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B + 1 ∧
      Real.log (S1BetaGeometryD N s : ℝ) / Real.log (S1BetaGeometryZeta N s) = s ∧
      ∀ p : ℕ, p < S1BetaGeometryZ N s → p < S1BetaGeometryD N s := by
  obtain ⟨Ncut, hNcut, hcut⟩ :=
    S1BetaGeometry_panModulusCutoff_eventually s B hs4 hslt hB
  obtain ⟨Nup, _hNup, hup⟩ := S1BetaGeometry_zeta_le_rpow_eventually s η hs4 hη
  refine ⟨max Ncut Nup, le_trans hNcut (le_max_left _ _), ?_⟩
  intro N hN
  have hNcut' : Ncut ≤ N := (le_max_left _ _).trans hN
  have hNup' : Nup ≤ N := (le_max_right _ _).trans hN
  have hs : 0 < s := S1BetaGeometry_s_pos hs4
  have hs1 : 1 ≤ s := S1BetaGeometry_s_one_le hs4
  rcases hcut N hNcut' with ⟨hD, hzeta, hZ, hcutoff⟩
  refine ⟨hD, hzeta, hZ, S1BetaGeometry_rpow_le_zeta hs, hup N hNup', hcutoff,
    S1BetaGeometry_logD_div_logZeta_eq_s hD hs, ?_⟩
  intro p hp
  exact S1BetaGeometry_lt_D_of_lt_Z hD hs1 hp

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig