import MathlibNt.SieveTheory.LiLiuGoldbachB9PaidUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB8NormalizedMainMass
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import MathlibNt.SieveTheory.LiLiuGoldbachS5CountTransport

open Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- The production identity only identifies the density at primes in the strict product. -/
theorem goldbachB9PlusBoundingSieve_product_eq_goldbachPrimeProduct
    (N : ℕ) (hEven : Even N) (Z : ℝ) :
    sieveProductPrimeFactors
      (goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)) =
      goldbachB10PrimeProduct N Z :=
  (goldbachB10PrimeProduct_eq_sieveProductPrimeFactors N hEven 0
    ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
    Z (goldbachB9PlusMainMass N)).symm

theorem goldbachB9PlusBoundingSieve_product_log_le_liuSingularSeries
    (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ N : ℕ, 4 ≤ N → ∀ hEven : Even N,
      ∀ Z : ℝ, Z₀ ≤ Z →
        sieveProductPrimeFactors
          (goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) Z (goldbachB9PlusMainMass N)) * Real.log Z ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
  obtain ⟨Z₀, hZ₀, hprod⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries η hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N hN hEven Z hZ
  rw [goldbachB9PlusBoundingSieve_product_eq_goldbachPrimeProduct]
  exact hprod N hN hEven Z hZ

/-- Reuse the public scalar geometry, without imposing the B8 carrier window on B9. -/
theorem goldbachB9Plus_normalized_cutoff_geometry
    (B K τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Real.sqrt Δ
      max 2 K ≤ Z ∧ Z ≤ (N : ℝ) ^ (1 / 4 : ℝ) ∧
        Z ≤ Real.sqrt (N : ℝ) ∧ Real.log Δ / Real.log Z = 2 ∧
        0 < Real.log Z ∧ Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
  obtain ⟨N₀, hN₀, hg⟩ := goldbachB8Plus_normalized_cutoff_geometry B K τ hB hτ hτ1
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  obtain ⟨hlarge, hquarter, _hB8, hsqrt, hs, hlog, hratio⟩ := hg N hN
  exact ⟨hlarge, hquarter, hsqrt, hs, hlog, hratio⟩

private theorem B9NormalizedMainMass_coefficient
    {τ δ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτδ : 56 * τ ≤ δ) :
    8 * (1 + τ) ^ 3 ≤ 8 + δ := by
  have hτ2 : τ ^ 2 ≤ τ := by nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hτ1)]
  have hτ3 : τ ^ 3 ≤ τ := by
    have hmul := mul_le_mul_of_nonneg_left hτ2 hτ0
    nlinarith
  nlinarith

private theorem B9NormalizedMainMass_paid_error (C η : ℝ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        η * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  have hηU : 0 < η * SingularSeries.liuUniversalProduct :=
    mul_pos hη SingularSeries.liuUniversalProduct_pos
  have hlogs := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (C / (η * SingularSeries.liuUniversalProduct))))
  filter_upwards [hlogs] with N hN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hN)
  have hC : C ≤ η * SingularSeries.liuUniversalProduct * Real.log (N : ℝ) := by
    simpa [mul_comm] using
      (div_le_iff₀ hηU).mp ((le_max_right _ _).trans hN)
  have hCdiv : C / Real.log (N : ℝ) ≤ η * SingularSeries.liuUniversalProduct :=
    (div_le_iff₀ hlogpos).2 hC
  calc
    C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) =
        (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      rw [Real.rpow_ofNat]
      field_simp
    _ ≤ (η * SingularSeries.liuUniversalProduct) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hCdiv (by positivity)
    _ ≤ (η * SingularSeries.liuSingularSeries N) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hη.le) (by positivity)
    _ = _ := by ring

/-- Independent main-term and error tolerances keep the final S5 budget exact. -/
theorem goldbachB9PlusSiftedCount_normalized_mainMass
    (δ η : ℝ) (hδ : 0 < δ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ _hEven : Even N,
        let Z := Real.sqrt ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1))
        2 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
          (goldbachB10SiftedCount N 0 ((N : ℝ) ^ (4 / 53 : ℝ))
            ((N : ℝ) ^ (1 / 3 : ℝ)) Z : ℝ) ≤
              (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB9PlusMainMass N /
                Real.log (N : ℝ) +
              η * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  let τ : ℝ := min (δ / 56) 1
  have hτ : 0 < τ := lt_min (by positivity) zero_lt_one
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτδ : 56 * τ ≤ δ := by
    have h := min_le_left (δ / 56) (1 : ℝ)
    dsimp [τ]
    linarith
  obtain ⟨C, _hC, B, hB, Npaid, _hNpaid, hpaid⟩ :=
    goldbachB9PlusSiftedCount_upper_paid 3 (by norm_num)
  obtain ⟨z₀, hpaidN⟩ := hpaid (τ * Real.exp Real.eulerMascheroniConstant)
    (mul_pos hτ (Real.exp_pos _))
  obtain ⟨Z₀, _hZ₀, hprod⟩ :=
    goldbachB9PlusBoundingSieve_product_log_le_liuSingularSeries τ hτ
  obtain ⟨Ng, hNg, hgeom⟩ :=
    goldbachB9Plus_normalized_cutoff_geometry B (max z₀ Z₀) τ hB hτ hτ1
  obtain ⟨Ne, herr⟩ := eventually_atTop.mp (B9NormalizedMainMass_paid_error C η hη)
  obtain ⟨Nx, _hNx, hx⟩ := goldbachB9PlusMainMass_nonneg_eventually
  refine ⟨B, hB, max Ng (max Npaid (max Ne Nx)), hNg.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hgN : Ng ≤ N := (le_max_left _ _).trans hN
  have hpN : Npaid ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hexN : max Ne Nx ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have heN : Ne ≤ N := (le_max_left _ _).trans hexN
  have hxN : Nx ≤ N := (le_max_right _ _).trans hexN
  have hN4 : 4 ≤ N := hNg.trans hgN
  let Δ := (N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1)
  let Z := Real.sqrt Δ
  let X := goldbachB9PlusMainMass N
  let S := goldbachB10BoundingSieve N hEven 0 ((N : ℝ) ^ (4 / 53 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ)) Z X
  obtain ⟨hZbig, _hZquarter, hZsqrt, hs, hlogZpos, hratio⟩ := hgeom N hgN
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hz₀ : z₀ ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZbig)
  have hZ₀ : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZbig)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg : 0 ≤ X := hx N hxN
  have hpaidBound := hpaidN N hpN hEven Z 2 hz₀ hZ2
    hs.symm (by norm_num) (by norm_num)
  have hV : sieveProductPrimeFactors S ≤
      2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
        SingularSeries.liuSingularSeries N / Real.log Z :=
    (le_div_iff₀ hlogZpos).2 (hprod N hN4 hEven Z hZ₀)
  have hfactor :
      jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant =
        Real.exp Real.eulerMascheroniConstant * (1 + τ) := by
    norm_num [jurkatRichertUpperLinearSieveFactor]
    ring
  have hInvLogZ : 1 / Real.log Z ≤ (4 * (1 + τ)) / Real.log (N : ℝ) := by
    calc
      _ = (Real.log (N : ℝ) / Real.log Z) / Real.log (N : ℝ) := by
        field_simp [hlogNpos.ne', hlogZpos.ne']
      _ ≤ _ := div_le_div_of_nonneg_right hratio hlogNpos.le
  have hCoeff : 2 * (1 + τ) ^ 2 / Real.log Z ≤ (8 + δ) / Real.log (N : ℝ) := by
    calc
      _ = 2 * (1 + τ) ^ 2 * (1 / Real.log Z) := by ring
      _ ≤ 2 * (1 + τ) ^ 2 * ((4 * (1 + τ)) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hInvLogZ (by positivity)
      _ = (8 * (1 + τ) ^ 3) / Real.log (N : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (B9NormalizedMainMass_coefficient hτ.le hτ1 hτδ) hlogNpos.le
  have hMain :
      X * (jurkatRichertUpperLinearSieveFactor (2 : ℝ) +
          τ * Real.exp Real.eulerMascheroniConstant) * sieveProductPrimeFactors S ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) := by
    rw [hfactor]
    calc
      _ ≤ X * (Real.exp Real.eulerMascheroniConstant * (1 + τ)) *
          (2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + τ) *
            SingularSeries.liuSingularSeries N / Real.log Z) :=
        mul_le_mul_of_nonneg_left hV (by positivity)
      _ = (SingularSeries.liuSingularSeries N * X) *
          (2 * (1 + τ) ^ 2 / Real.log Z) := by
        have hexp : Real.exp Real.eulerMascheroniConstant *
            Real.exp (-Real.eulerMascheroniConstant) = 1 := by
          rw [← Real.exp_add]
          norm_num
        calc
          _ = (Real.exp Real.eulerMascheroniConstant *
              Real.exp (-Real.eulerMascheroniConstant)) *
              ((SingularSeries.liuSingularSeries N * X) *
                (2 * (1 + τ) ^ 2 / Real.log Z)) := by ring
          _ = _ := by rw [hexp, one_mul]
      _ ≤ (SingularSeries.liuSingularSeries N * X) *
          ((8 + δ) / Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hCoeff
          (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le hXnonneg)
      _ = _ := by ring
  exact ⟨hZ2, hZsqrt, hpaidBound.trans (add_le_add hMain (herr N heN))⟩

/-- Actual S5Closed on the original epsilon carrier; no free sieve parameter remains. -/
theorem goldbachS5Closed_normalized_upper_mainMass
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (_hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS5Closed (goldbachDifferenceCarrier N ε) N
        ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) ≤
          (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB9PlusMainMass N /
            Real.log (N : ℝ) +
          δ * (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by
  obtain ⟨B, _hB, Ns, hNs, hs⟩ :=
    goldbachB9PlusSiftedCount_normalized_mainMass δ (δ / 2) hδ (by positivity)
  obtain ⟨Nt, _hNt, ht⟩ :=
    goldbachS5Closed_le_B10ZeroPrefix_normalized ε (δ / 2) hε (by positivity)
  refine ⟨max Ns Nt, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have htN : Nt ≤ N := (le_max_right _ _).trans hN
  let Z := Real.sqrt ((N : ℝ) ^ (1 / 2 : ℝ) / Real.log (N : ℝ) ^ (B + 1))
  obtain ⟨hZ2, hZsqrt, hbound⟩ := hs N hsN hEven
  have htransport := ht N htN Z (by linarith) hZsqrt
  dsimp [Z] at htransport
  linarith only [hbound, htransport]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig