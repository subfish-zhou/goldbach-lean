import MathlibNt.SieveTheory.LiLiuGoldbachB10EndpointScale
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import MathlibNt.SieveTheory.LiuPanWangDingSource
import Mathlib.Analysis.SpecialFunctions.Sqrt

open Filter

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The common upper Pan window used to consume the actual `C10` support at both
`x = N` and `x = ⌊εN⌋`. -/
noncomputable def B10PanGeometryUpperWindow (N : ℕ) (γ : ℝ) : ℕ :=
  Nat.floor ((N : ℝ) ^ ((1 + γ) / 2))

private theorem B10PanGeometry_scaled_floor_half_mul_le
    (ε : ℝ) (hε : 0 < ε) (N : ℕ)
    (hN : ⌈2 / ε⌉₊ ≤ N) :
    ε / 2 * (N : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) := by
  have hc : 2 / ε ≤ (N : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have hprod : 2 ≤ ε * (N : ℝ) := by
    have := (div_le_iff₀ hε).mp hc
    nlinarith
  have hfloor := Nat.lt_floor_add_one (ε * (N : ℝ))
  nlinarith

private theorem B10PanGeometry_le_scaled_floor_of_ceil
    (ε : ℝ) (hε : 0 < ε) {L N : ℕ} (hL : 1 ≤ L)
    (hN : ⌈2 * (L : ℝ) / ε⌉₊ ≤ N) :
    L ≤ ⌊ε * (N : ℝ)⌋₊ := by
  have hLN : (L : ℝ) ≤ ε / 2 * (N : ℝ) := by
    have hc : 2 * (L : ℝ) / ε ≤ (N : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hN)
    calc
      (L : ℝ) = ε / 2 * (2 * (L : ℝ) / ε) := by
        field_simp [hε.ne']
      _ ≤ ε / 2 * (N : ℝ) := by
        gcongr
  have hhalf :
      ε / 2 * (N : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) := by
    apply B10PanGeometry_scaled_floor_half_mul_le ε hε N
    have htwo : (2 / ε : ℝ) ≤ 2 * (L : ℝ) / ε := by
      have hLreal : (1 : ℝ) ≤ L := by exact_mod_cast hL
      calc
        (2 / ε : ℝ) = 1 * (2 / ε) := by ring
        _ ≤ L * (2 / ε) := by gcongr
        _ = 2 * (L : ℝ) / ε := by ring
    exact (Nat.ceil_mono htwo).trans hN
  exact_mod_cast hLN.trans hhalf

private theorem B10PanGeometry_two_le_of_support
    {N : ℕ} {β γ : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    2 ≤ N := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, _⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, hsize⟩
  have htwo : 2 ≤ rs.1 * rs.2 ^ 2 := by
    calc
      2 ≤ rs.1 := hrPrime.two_le
      _ ≤ rs.1 * rs.2 ^ 2 := by
        have hsone : 1 ≤ rs.2 ^ 2 := by
          exact pow_pos hsPrime.pos 2
        exact Nat.le_mul_of_pos_right _ hsone
  exact le_trans htwo hsize

/-- Every actual support point lies below the common upper window. -/
theorem B10PanGeometry_support_le_upperWindow
    {N : ℕ} {β γ : ℝ} {m : ℕ}
    (hN : 2 ≤ N) (hγ : γ < (1 : ℝ) / 3)
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    m ≤ B10PanGeometryUpperWindow N γ := by
  unfold B10PanGeometryUpperWindow
  rw [Nat.le_floor_iff (Real.rpow_nonneg (Nat.cast_nonneg N) _)]
  exact (goldbachC10ProductSupport_le_rpow_half_and_lt_two_thirds hN hγ hm).1

/-- The common upper window is admissible for the original `x = N` scale. -/
theorem B10PanGeometry_upperWindow_le_rpow_two_thirds
    {N : ℕ} (hN : 1 ≤ N) {γ : ℝ} (hγ : γ < (1 : ℝ) / 3) :
    (B10PanGeometryUpperWindow N γ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  unfold B10PanGeometryUpperWindow
  refine (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans ?_
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by linarith)

/-- The common upper window is eventually admissible for the smaller
endpoint `x = ⌊εN⌋`. -/
theorem B10PanGeometry_upperWindow_le_scaled_floor_rpow_eventually
    (ε γ : ℝ) (hε : 0 < ε) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (B10PanGeometryUpperWindow N γ : ℝ) ≤
        (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ ((2 : ℝ) / 3) := by
  obtain ⟨N₀, hN₀, hscale⟩ :=
    eventually_rpow_le_scaled_floor_rpow ε ((1 + γ) / 2) ((2 : ℝ) / 3)
      hε (by norm_num) (by linarith)
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  unfold B10PanGeometryUpperWindow
  exact (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)).trans (hscale N hN)

private theorem B10PanGeometry_support_rpow_two_beta_le
    {N : ℕ} {β γ : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    (N : ℝ) ^ (2 * β) ≤ m := by
  rcases mem_goldbachC10ProductSupport_iff.mp hm with ⟨rs, hrs, rfl⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, _, _, hβr, hrγ, hγs, hsize⟩
  have hNnat : 0 < N := by
    rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, hsize⟩
    have hpos : 0 < rs.1 * rs.2 ^ 2 := Nat.mul_pos hrPrime.pos (pow_pos hsPrime.pos 2)
    exact lt_of_lt_of_le hpos hsize
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNnat
  have hβs : (N : ℝ) ^ β ≤ (rs.2 : ℝ) := (hβr.trans hrγ).trans hγs
  have hmul :
      (N : ℝ) ^ β * (N : ℝ) ^ β ≤ (rs.1 : ℝ) * (rs.2 : ℝ) :=
    mul_le_mul hβr hβs (by positivity) (by positivity)
  calc
    (N : ℝ) ^ (2 * β) = (N : ℝ) ^ β * (N : ℝ) ^ β := by
      rw [show (2 * β : ℝ) = β + β by ring, Real.rpow_add hNpos]
    _ ≤ (rs.1 : ℝ) * (rs.2 : ℝ) := hmul
    _ = goldbachC10Prod rs := by simp [goldbachC10Prod]

private theorem B10PanGeometry_support_rpow_one_ninth_lt
    {N : ℕ} {β γ : ℝ} {m : ℕ}
    (hβ : (1 : ℝ) / 18 < β)
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ)) :
    (N : ℝ) ^ (1 / 9 : ℝ) < m := by
  have hN2 : 2 ≤ N := B10PanGeometry_two_le_of_support hm
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact (Real.rpow_lt_rpow_of_exponent_lt hN1 (by linarith)).trans_le
    (B10PanGeometry_support_rpow_two_beta_le hm)

private theorem B10PanGeometry_support_lowerWindow_eventually
    (B : ℝ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ, (1 : ℝ) / 18 < β →
      ∀ γ : ℝ, ∀ m : ℕ,
      m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) →
        MathlibNt.SieveTheory.LiuWeight.liuPanSourceIntervalLower N B < m := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp
    (MathlibNt.SieveTheory.LiuWeight.eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B)
  refine ⟨N₀, ?_⟩
  intro N hN β hβ γ m hm
  have hlower := hN₀ N hN
  have hm' :
      MathlibNt.SieveTheory.LiuWeight.liuSourceZ10 N < m := by
    unfold MathlibNt.SieveTheory.LiuWeight.liuSourceZ10
    refine (Nat.floor_lt (Real.rpow_nonneg (Nat.cast_nonneg N) _)).2 ?_
    exact (Real.rpow_lt_rpow_of_exponent_lt
      (by exact_mod_cast (show 1 < N by
        have hN2 : 2 ≤ N := B10PanGeometry_two_le_of_support hm
        omega))
      (by norm_num : (1 / 10 : ℝ) < 1 / 9)).trans
      (B10PanGeometry_support_rpow_one_ninth_lt hβ hm)
  exact hlower.trans hm'

/-- The original lower Pan window also covers the smaller endpoint `x = ⌊εN⌋`,
and together with the common upper window it contains every actual support
point. -/
theorem B10PanGeometry_support_mem_commonWindow_eventually
    (ε γ B : ℝ)
    (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3)
    (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let A₁ := MathlibNt.SieveTheory.LiuWeight.liuPanSourceIntervalLower N B
      let A₂ := B10PanGeometryUpperWindow N γ
      Real.log (N : ℝ) ^ (2 * B) ≤ A₁ ∧
      Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ (2 * B) ≤ A₁ ∧
      (A₂ : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ ((2 : ℝ) / 3) ∧
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧
      ∀ β : ℝ, (1 : ℝ) / 18 < β → ∀ m : ℕ,
        m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) →
          m ∈ Finset.Ioc A₁ A₂ := by
  obtain ⟨Nup, hNup2, hupperScaled⟩ :=
    B10PanGeometry_upperWindow_le_scaled_floor_rpow_eventually ε γ hε hγ
  obtain ⟨Nlow, hlow⟩ := B10PanGeometry_support_lowerWindow_eventually B
  obtain ⟨Nsqrt, hNsqrt2, hsqrt⟩ :=
    eventually_rpow_le_scaled_floor_rpow ε ((1 : ℝ) / 2) 1 hε (by norm_num) (by norm_num)
  refine ⟨max Nup (max Nlow (max Nsqrt 2)), le_trans hNup2 (le_max_left _ _), ?_⟩
  intro N hN
  dsimp
  have hNup : Nup ≤ N := (le_max_left _ _).trans hN
  have hNrest : max Nlow (max Nsqrt 2) ≤ N := (le_max_right _ _).trans hN
  have hNlow : Nlow ≤ N := (le_max_left _ _).trans hNrest
  have hNsqrt : Nsqrt ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNrest)
  have hN2 : 2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNrest)
  have hN1 : 1 ≤ N := by omega
  have hMge1 :
      1 ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) := by
    have hsqrt1 : 1 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    exact hsqrt1.trans (by simpa using hsqrt N hNsqrt)
  have hMpos : 0 < (⌊ε * (N : ℝ)⌋₊ : ℝ) := by linarith
  have hMleN :
      (⌊ε * (N : ℝ)⌋₊ : ℝ) ≤ N := by
    calc
      (⌊ε * (N : ℝ)⌋₊ : ℝ) ≤ ε * (N : ℝ) := Nat.floor_le (by positivity)
      _ ≤ N := by nlinarith
  have hlogScaled :
      Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log hMpos hMleN
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
  have hlogScaledNonneg : 0 ≤ Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) :=
    Real.log_nonneg hMge1
  have hA1N :
      Real.log (N : ℝ) ^ (2 * B) ≤
        MathlibNt.SieveTheory.LiuWeight.liuPanSourceIntervalLower N B :=
    (MathlibNt.SieveTheory.LiuWeight.log_rpow_lt_liuPanSourceIntervalLower N B).le
  have hA1Scaled :
      Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ (2 * B) ≤
        MathlibNt.SieveTheory.LiuWeight.liuPanSourceIntervalLower N B :=
    (Real.rpow_le_rpow hlogScaledNonneg hlogScaled (by linarith)).trans hA1N
  refine ⟨hA1N, hA1Scaled, hupperScaled N hNup,
    B10PanGeometry_upperWindow_le_rpow_two_thirds hN1 hγ, ?_⟩
  intro β hβ m hm
  refine Finset.mem_Ioc.mpr ?_
  constructor
  · exact hlow N hNlow β hβ γ m hm
  · exact B10PanGeometry_support_le_upperWindow hN2 hγ hm

/-- The smaller-endpoint modulus cutoff with exponent `B` eventually dominates
the original-scale cutoff with exponent `B + 1`; the latter is also bounded by
the original cutoff with exponent `B`. -/
theorem B10PanGeometry_panModulusCutoff_comparison_eventually
    (ε B : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff (⌊ε * (N : ℝ)⌋₊) B ∧
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
  have he : ∀ᶠ N : ℕ in atTop,
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff (⌊ε * (N : ℝ)⌋₊) B ∧
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B := by
    have hconst :
        ∀ᶠ N : ℕ in atTop,
          ((2 / ε : ℝ) ^ ((1 : ℝ) / 2)) ≤ Real.log (N : ℝ) := by
      exact (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
        (eventually_ge_atTop ((2 / ε : ℝ) ^ ((1 : ℝ) / 2)))
    obtain ⟨Nsqrt, _, hsqrt⟩ :=
      eventually_rpow_le_scaled_floor_rpow ε ((1 : ℝ) / 2) 1 hε (by norm_num) (by norm_num)
    filter_upwards [hconst, eventually_ge_atTop (max Nsqrt (max ⌈2 / ε⌉₊ 4))] with N hconstN hN
    have hNsqrt : Nsqrt ≤ N := (le_max_left _ _).trans hN
    have hNrest : max ⌈2 / ε⌉₊ 4 ≤ N := (le_max_right _ _).trans hN
    have hNceil : ⌈2 / ε⌉₊ ≤ N := (le_max_left _ _).trans hNrest
    have hN4 : 4 ≤ N := (le_max_right _ _).trans hNrest
    have hN2 : 2 ≤ N := by omega
    let M : ℕ := ⌊ε * (N : ℝ)⌋₊
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1 : 1 ≤ N := by omega
    have hM2 : 2 ≤ M := by
      have hsqrt4 : (2 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
        have h4 : (4 : ℝ) ≤ N := by exact_mod_cast hN4
        calc
          (2 : ℝ) = (4 : ℝ) ^ ((1 : ℝ) / 2) := by norm_num [Real.sqrt_eq_rpow]
          _ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_le_rpow (by positivity) h4 (by norm_num)
      have hMge : (2 : ℝ) ≤ M := hsqrt4.trans (by simpa using hsqrt N hNsqrt)
      exact_mod_cast hMge
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hlogMpos : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
    have hlogNge1 : 1 ≤ Real.log (N : ℝ) := by
      have hconst1 : (1 : ℝ) ≤ (2 / ε : ℝ) ^ ((1 : ℝ) / 2) := by
        have hεle2 : ε ≤ 2 := by linarith
        have : (1 : ℝ) ≤ 2 / ε := by
          calc
            (1 : ℝ) = ε * (1 / ε) := by field_simp [hε.ne']
            _ ≤ 2 * (1 / ε) := by gcongr
            _ = 2 / ε := by ring
        exact Real.one_le_rpow this (by norm_num)
      exact hconst1.trans hconstN
    have hMhalf : ε / 2 * (N : ℝ) ≤ M :=
      B10PanGeometry_scaled_floor_half_mul_le ε hε N hNceil
    have hMlin : (N : ℝ) ≤ (2 / ε : ℝ) * M := by
      calc
        (N : ℝ) = (2 / ε : ℝ) * (ε / 2 * (N : ℝ)) := by
          field_simp [hε.ne']
        _ ≤ (2 / ε : ℝ) * M := by
          gcongr
    have hsqrtCompare :
        (N : ℝ) ^ ((1 : ℝ) / 2) ≤ ((2 / ε : ℝ) * M) ^ ((1 : ℝ) / 2) := by
      exact Real.rpow_le_rpow (by positivity) hMlin (by norm_num)
    have hsqrtFactor :
        (N : ℝ) ^ ((1 : ℝ) / 2) ≤
          (2 / ε : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 2) := by
      calc
        (N : ℝ) ^ ((1 : ℝ) / 2) ≤ ((2 / ε : ℝ) * M) ^ ((1 : ℝ) / 2) := hsqrtCompare
        _ = (2 / ε : ℝ) ^ ((1 : ℝ) / 2) * (M : ℝ) ^ ((1 : ℝ) / 2) := by
          rw [Real.mul_rpow (by positivity : 0 ≤ (2 / ε : ℝ))
            (by exact_mod_cast (show 0 ≤ M by omega))]
    have hsqrtLog :
        (N : ℝ) ^ ((1 : ℝ) / 2) ≤ Real.log (N : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 2) := by
      exact hsqrtFactor.trans <|
        mul_le_mul_of_nonneg_right hconstN
          (Real.rpow_nonneg (by exact_mod_cast (show 0 ≤ M by omega)) _)
    have hpowNBpos : 0 < Real.log (N : ℝ) ^ B := Real.rpow_pos_of_pos hlogNpos B
    have hpowMBpos : 0 < Real.log (M : ℝ) ^ B := Real.rpow_pos_of_pos hlogMpos B
    have hpowMleN :
        Real.log (M : ℝ) ^ B ≤ Real.log (N : ℝ) ^ B := by
      exact Real.rpow_le_rpow hlogMpos.le
        (Real.log_le_log hMpos (by
          have hMleN : (M : ℝ) ≤ N := by
            calc
              (M : ℝ) ≤ ε * (N : ℝ) := Nat.floor_le (by positivity)
              _ ≤ N := by nlinarith [hεlt]
          exact hMleN))
        hB
    have hrootDiv :
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1) ≤
          (M : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := by
      calc
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
            = (N : ℝ) ^ ((1 : ℝ) / 2) /
                (Real.log (N : ℝ) ^ B * Real.log (N : ℝ)) := by
                  rw [Real.rpow_add hlogNpos, Real.rpow_one]
        _ ≤ (Real.log (N : ℝ) * (M : ℝ) ^ ((1 : ℝ) / 2)) /
              (Real.log (N : ℝ) ^ B * Real.log (N : ℝ)) := by
                exact div_le_div_of_nonneg_right hsqrtLog
                  (mul_pos hpowNBpos hlogNpos).le
        _ = (M : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := by
              field_simp [hpowNBpos.ne', hlogNpos.ne']
    have hrootDivScaled :
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1) ≤
          (M : ℝ) ^ ((1 : ℝ) / 2) / Real.log (M : ℝ) ^ B := by
      calc
        (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1) ≤
            (M : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ B := hrootDiv
        _ = (M : ℝ) ^ ((1 : ℝ) / 2) * (1 / Real.log (N : ℝ) ^ B) := by
              simp [div_eq_mul_inv]
        _ ≤ (M : ℝ) ^ ((1 : ℝ) / 2) * (1 / Real.log (M : ℝ) ^ B) := by
              gcongr
        _ = (M : ℝ) ^ ((1 : ℝ) / 2) / Real.log (M : ℝ) ^ B := by
              simp [div_eq_mul_inv]
    have hpowShift :
        Real.log (N : ℝ) ^ B ≤ Real.log (N : ℝ) ^ (B + 1) := by
      rw [Real.rpow_add hlogNpos, Real.rpow_one]
      exact le_mul_of_one_le_right (Real.rpow_nonneg hlogNpos.le _) hlogNge1
    constructor
    · unfold MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
      apply Nat.floor_le_floor
      simpa using hrootDivScaled
    · unfold MathlibNt.SieveTheory.LiuWeight.panModulusCutoff
      apply Nat.floor_le_floor
      rw [div_eq_mul_inv, div_eq_mul_inv]
      have hinv :
          (Real.log (N : ℝ) ^ (B + 1))⁻¹ ≤ (Real.log (N : ℝ) ^ B)⁻¹ := by
        simpa [one_div] using one_div_le_one_div_of_le hpowNBpos hpowShift
      exact mul_le_mul_of_nonneg_left hinv (Real.rpow_nonneg hNpos.le _)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp he
  exact ⟨max 2 N₀, le_max_left _ _, fun N hN => hN₀ N ((le_max_right _ _).trans hN)⟩

/-- The smaller endpoint carries at most the original `N / log(N)^U` scale up
to the explicit factor `2^U`. -/
theorem B10PanGeometry_scaled_div_log_rpow_le_eventually
    (ε U : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hU : 0 ≤ U) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      (⌊ε * (N : ℝ)⌋₊ : ℝ) / Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ U ≤
        (2 : ℝ) ^ U * N / Real.log (N : ℝ) ^ U := by
  obtain ⟨Nsqrt, hNsqrt2, hsqrt⟩ :=
    eventually_rpow_le_scaled_floor_rpow ε ((1 : ℝ) / 2) 1 hε (by norm_num) (by norm_num)
  refine ⟨max Nsqrt 2, le_trans hNsqrt2 (le_max_left _ _), ?_⟩
  intro N hN
  let M : ℕ := ⌊ε * (N : ℝ)⌋₊
  have hNsqrt : Nsqrt ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : 1 ≤ N := by omega
  have hMleN : (M : ℝ) ≤ N := by
    calc
      (M : ℝ) ≤ ε * (N : ℝ) := Nat.floor_le (by positivity)
      _ ≤ N := by nlinarith
  have hMsqrt : Real.sqrt N ≤ M := by
    simpa [M, Real.sqrt_eq_rpow] using hsqrt N hNsqrt
  have hMpos : (0 : ℝ) < M := by
    exact lt_of_lt_of_le (Real.sqrt_pos.2 hNpos) hMsqrt
  have hlogHalf :
      Real.log (N : ℝ) / 2 ≤ Real.log (M : ℝ) := by
    have hlog := Real.log_le_log (Real.sqrt_pos.2 hNpos) hMsqrt
    rw [Real.log_sqrt hNpos.le] at hlog
    simpa [two_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hlog
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogHalfPos : 0 < Real.log (N : ℝ) / 2 := by positivity
  have hpowHalf :
      (Real.log (N : ℝ) / 2) ^ U ≤ Real.log (M : ℝ) ^ U :=
    Real.rpow_le_rpow hlogHalfPos.le hlogHalf hU
  have hinv :
      1 / Real.log (M : ℝ) ^ U ≤ 1 / (Real.log (N : ℝ) / 2) ^ U :=
    one_div_le_one_div_of_le (Real.rpow_pos_of_pos hlogHalfPos U) hpowHalf
  have hlogNnonneg : 0 ≤ Real.log (N : ℝ) := hlogNpos.le
  have hlogPowPos : 0 < Real.log (N : ℝ) ^ U := Real.rpow_pos_of_pos hlogNpos U
  have htwoPowPos : 0 < (2 : ℝ) ^ U := Real.rpow_pos_of_pos (by norm_num) U
  calc
    (M : ℝ) / Real.log (M : ℝ) ^ U
        = (M : ℝ) * (1 / Real.log (M : ℝ) ^ U) := by
            rw [div_eq_mul_inv, one_div]
    _ ≤ (M : ℝ) * (1 / (Real.log (N : ℝ) / 2) ^ U) := by
          gcongr
    _ = (M : ℝ) * ((2 : ℝ) ^ U / Real.log (N : ℝ) ^ U) := by
          rw [Real.div_rpow hlogNnonneg (by norm_num : (0 : ℝ) ≤ 2)]
          field_simp [hlogPowPos.ne', htwoPowPos.ne']
    _ ≤ N * ((2 : ℝ) ^ U / Real.log (N : ℝ) ^ U) := by
          gcongr
    _ = (2 : ℝ) ^ U * N / Real.log (N : ℝ) ^ U := by
          ring

private theorem B10PanGeometry_scaled_floor_threshold
    (ε : ℝ) (hε : 0 < ε) (K : ℕ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      K ≤ N ∧ K ≤ ⌊ε * (N : ℝ)⌋₊ ∧ 2 ≤ ⌊ε * (N : ℝ)⌋₊ := by
  let L := max K 2
  let N₀ := max 2 (max K ⌈2 * (L : ℝ) / ε⌉₊)
  refine ⟨N₀, by
    dsimp [N₀, L]
    exact le_max_left _ _, ?_⟩
  intro N hN
  have hNrest : max K ⌈2 * (L : ℝ) / ε⌉₊ ≤ N := (le_max_right _ _).trans hN
  have hKN : K ≤ N := (le_max_left _ _).trans hNrest
  have hceilN : ⌈2 * (L : ℝ) / ε⌉₊ ≤ N := (le_max_right _ _).trans hNrest
  have hLN : L ≤ ⌊ε * (N : ℝ)⌋₊ :=
    B10PanGeometry_le_scaled_floor_of_ceil ε hε (by
      dsimp [L]
      exact le_trans (show 1 ≤ 2 by omega) (le_max_right _ _)) hceilN
  exact ⟨hKN, (le_max_left _ _).trans hLN, (le_max_right _ _).trans hLN⟩

/-- Threshold form of the combined B10 Pan-geometry packet. -/
theorem B10PanGeometry_consumer_threshold
    (ε γ B U : ℝ) (K : ℕ)
    (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3)
    (hB : 0 ≤ B) (hU : 0 ≤ U) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      K ≤ N ∧ K ≤ ⌊ε * (N : ℝ)⌋₊ ∧ 2 ≤ ⌊ε * (N : ℝ)⌋₊ ∧
      let A₁ := MathlibNt.SieveTheory.LiuWeight.liuPanSourceIntervalLower N B
      let A₂ := B10PanGeometryUpperWindow N γ
      Real.log (N : ℝ) ^ (2 * B) ≤ A₁ ∧
      Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ (2 * B) ≤ A₁ ∧
      (A₂ : ℝ) ≤ (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ ((2 : ℝ) / 3) ∧
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff (⌊ε * (N : ℝ)⌋₊) B ∧
      MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N (B + 1) ≤
        MathlibNt.SieveTheory.LiuWeight.panModulusCutoff N B ∧
      (⌊ε * (N : ℝ)⌋₊ : ℝ) / Real.log (⌊ε * (N : ℝ)⌋₊ : ℝ) ^ U ≤
        (2 : ℝ) ^ U * N / Real.log (N : ℝ) ^ U ∧
      ∀ β : ℝ, (1 : ℝ) / 18 < β → ∀ m : ℕ,
        m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) →
          m ∈ Finset.Ioc A₁ A₂ := by
  obtain ⟨Ngeo, hNgeo2, hgeo⟩ :=
    B10PanGeometry_support_mem_commonWindow_eventually ε γ B hε hεlt hγ hB
  obtain ⟨Ncut, hNcut2, hcut⟩ :=
    B10PanGeometry_panModulusCutoff_comparison_eventually ε B hε hεlt hB
  obtain ⟨Nratio, hNratio2, hratio⟩ :=
    B10PanGeometry_scaled_div_log_rpow_le_eventually ε U hε hεlt hU
  obtain ⟨Nthr, hNthr2, hthr⟩ := B10PanGeometry_scaled_floor_threshold ε hε K
  refine ⟨max Ngeo (max Ncut (max Nratio Nthr)), le_trans hNgeo2 (le_max_left _ _), ?_⟩
  intro N hN
  have hNgeo : Ngeo ≤ N := (le_max_left _ _).trans hN
  have hNrest : max Ncut (max Nratio Nthr) ≤ N := (le_max_right _ _).trans hN
  have hNcut : Ncut ≤ N := (le_max_left _ _).trans hNrest
  have hNrest' : max Nratio Nthr ≤ N := (le_max_right _ _).trans hNrest
  have hNratio : Nratio ≤ N := (le_max_left _ _).trans hNrest'
  have hNthr : Nthr ≤ N := (le_max_right _ _).trans hNrest'
  rcases hthr N hNthr with ⟨hKN, hKfloor, h2floor⟩
  have hgeo' := hgeo N hNgeo
  dsimp at hgeo'
  rcases hgeo' with ⟨hA1N, hA1M, hA2M, hA2N, hsupp⟩
  rcases hcut N hNcut with ⟨hcutM, hcutN⟩
  refine ⟨hKN, hKfloor, h2floor, hA1N, hA1M, hA2M, hA2N, hcutM, hcutN,
    hratio N hNratio, hsupp⟩

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig