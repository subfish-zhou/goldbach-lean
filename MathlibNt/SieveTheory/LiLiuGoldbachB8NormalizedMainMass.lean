import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import MathlibNt.SieveTheory.LiLiuGoldbachB8PaidUpper
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import MathlibNt.SieveTheory.LiLiuGoldbachS4CountTransport

noncomputable section

open Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.SwitchingPrinciple

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableB8NormalizedMainMass (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Only the prime values of the actual B8 density enter this identity. -/
theorem goldbachB8PlusBoundingSieve_product_eq_goldbachPrimeProduct
    (N : ℕ) (hEven : Even N) (Z : ℝ) :
    sieveProductPrimeFactors (goldbachB8PlusBoundingSieve N hEven Z) =
      goldbachB10PrimeProduct N Z := by
  unfold goldbachB10PrimeProduct MertensTheorem.goldbachSieveProduct
  unfold sieveProductPrimeFactors goldbachB8PlusBoundingSieve
  rw [goldbachB10ProdPrimes_primeFactors]
  apply Finset.prod_congr rfl
  intro p hp
  have hpPrime : p.Prime := (Finset.mem_filter.mp hp).2.1
  rw [goldbachB8PlusNu_eq_goldbachNu_of_squarefree hpPrime.squarefree,
    goldbachNu_apply_prime hpPrime]

theorem goldbachB8PlusBoundingSieve_product_log_le_liuSingularSeries
    (η : ℝ) (hη : 0 < η) :
    ∃ Z₀ : ℝ, 2 ≤ Z₀ ∧ ∀ N : ℕ, 4 ≤ N → ∀ hEven : Even N,
      ∀ Z : ℝ, Z₀ ≤ Z →
        sieveProductPrimeFactors (goldbachB8PlusBoundingSieve N hEven Z) * Real.log Z ≤
          2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
            SingularSeries.liuSingularSeries N := by
  obtain ⟨Z₀, hZ₀, hprod⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries η hη
  refine ⟨Z₀, hZ₀, ?_⟩
  intro N hN hEven Z hZ
  rw [goldbachB8PlusBoundingSieve_product_eq_goldbachPrimeProduct]
  exact hprod N hN hEven Z hZ

private theorem B8NormalizedMainMass_cutoff_large (B K : ℝ) (hK : 0 < K) :
    ∀ᶠ N : ℕ in atTop,
      K ≤ Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (B + 1) (by norm_num : (0 : ℝ) < 1 / 2)).bound
      (show (0 : ℝ) < 1 / K ^ 2 by positivity)
  have hsmall' : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (B + 1) ≤ (1 / K ^ 2) * x ^ ((1 : ℝ) / 2) := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hx1) _),
      Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using hx
  filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall',
    eventually_ge_atTop (4 : ℕ)] with N hsmallN hN4
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hmul : K ^ 2 * Real.log (N : ℝ) ^ (B + 1) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    have htmp := mul_le_mul_of_nonneg_left hsmallN (sq_nonneg K)
    simpa [mul_assoc, hK.ne'] using htmp
  have hlevel : K ^ 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1) :=
    (le_div_iff₀ (Real.rpow_pos_of_pos hlogpos _)).2 hmul
  simpa [Real.sqrt_sq_eq_abs, abs_of_nonneg hK.le] using Real.sqrt_le_sqrt hlevel

private theorem B8NormalizedMainMass_loglog_ratio :
    Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ))
      atTop (nhds 0) := by
  have hreal : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) := by
    simpa [Real.rpow_one] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero
  exact hreal.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- The real paid level gives ratio exactly two, with both production cutoff windows. -/
theorem goldbachB8Plus_normalized_cutoff_geometry
    (B K τ : ℝ) (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Real.sqrt Δ
      max 2 K ≤ Z ∧ Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4) ∧
        (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((3 : ℝ) / 11) ∧
        Z ≤ Real.sqrt (N : ℝ) ∧
        Real.log Δ / Real.log Z = 2 ∧
        0 < Real.log Z ∧ Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
  have hB1 : 0 < B + 1 := by linarith
  let κ : ℝ := τ / (4 * (B + 1))
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hsmall := B8NormalizedMainMass_loglog_ratio.eventually (Metric.ball_mem_nhds 0 hκ)
  have hlogs := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (1 : ℝ))
  have hlarge := B8NormalizedMainMass_cutoff_large B (max 2 K) (by positivity)
  have hall : ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ max 2 K ≤
      Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)) ∧
      1 ≤ Real.log (N : ℝ) ∧
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) ∈ Metric.ball (0 : ℝ) κ := by
    filter_upwards [eventually_ge_atTop (4 : ℕ), hlarge, hlogs, hsmall] with N hN hZ hL hS
    exact ⟨hN, hZ, hL, hS⟩
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hall
  refine ⟨max 4 N₁, le_max_left _ _, ?_⟩
  intro N hN
  obtain ⟨hN4, hZbig, hlog1, hsmallN⟩ := hN₁ N ((le_max_right _ _).trans hN)
  let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z := Real.sqrt Δ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hΔnonneg : 0 ≤ Δ := by dsimp [Δ]; positivity
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hlogZpos : 0 < Real.log Z := Real.log_pos (by linarith)
  have hlogZ : Real.log Z = Real.log Δ / 2 := Real.log_sqrt hΔnonneg
  have hs : Real.log Δ / Real.log Z = 2 := by
    have hlogΔ : Real.log Δ ≠ 0 := by rw [hlogZ] at hlogZpos; linarith
    rw [hlogZ]
    field_simp [hlogΔ]
  have hden1 : 1 ≤ Real.log (N : ℝ) ^ (B + 1) :=
    Real.one_le_rpow hlog1 hB1.le
  have hΔupper : Δ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    exact div_le_self (Real.rpow_nonneg hNpos.le _) hden1
  have hZquarter : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    calc
      Z ≤ Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2)) := Real.sqrt_le_sqrt hΔupper
      _ = (N : ℝ) ^ ((1 : ℝ) / 4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos.le]
        norm_num
  have hquarter : (N : ℝ) ^ ((1 : ℝ) / 4) ≤ (N : ℝ) ^ ((3 : ℝ) / 11) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hZsqrt : Z ≤ Real.sqrt (N : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact hZquarter.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))
  have hratioAbs : |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| < κ := by
    simpa [Real.dist_eq, abs_div] using hsmallN
  have hsmallTerm :
      (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) ≤ τ / 4 := by
    calc
      _ ≤ (B + 1) * |Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hB1.le
      _ ≤ (B + 1) * κ := mul_le_mul_of_nonneg_left hratioAbs.le hB1.le
      _ = τ / 4 := by dsimp [κ]; field_simp [hB1.ne']
  have hΔratio :
      Real.log Δ / Real.log (N : ℝ) =
        (1 / 2 : ℝ) - (B + 1) * (Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ)) := by
    dsimp [Δ]
    rw [Real.log_div (by positivity)
      (ne_of_gt (Real.rpow_pos_of_pos hlogpos _)),
      Real.log_rpow hNpos, Real.log_rpow hlogpos]
    field_simp [hlogpos.ne']
  have hZlower : (1 / 4 : ℝ) - τ / 8 ≤ Real.log Z / Real.log (N : ℝ) := by
    rw [hlogZ, div_right_comm, hΔratio]
    linarith
  have hquarterPos : 0 < (1 / 4 : ℝ) - τ / 8 := by linarith
  have hrecip : 1 / (Real.log Z / Real.log (N : ℝ)) ≤ 4 * (1 + τ) := by
    calc
      _ ≤ 1 / ((1 / 4 : ℝ) - τ / 8) := one_div_le_one_div_of_le hquarterPos hZlower
      _ ≤ 4 * (1 + τ) := by
        apply (div_le_iff₀ hquarterPos).2
        nlinarith [mul_nonneg hτ.le (sub_nonneg.mpr hτ1)]
  have hratio : Real.log (N : ℝ) / Real.log Z ≤ 4 * (1 + τ) := by
    simpa only [one_div_div, div_one] using hrecip
  exact ⟨hZbig, hZquarter, hquarter, hZsqrt, hs, hlogZpos, hratio⟩

private theorem B8NormalizedMainMass_coefficient
    {τ δ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hτδ : 56 * τ ≤ δ) :
    8 * (1 + τ) ^ 3 ≤ 8 + δ := by
  have hτ2 : τ ^ 2 ≤ τ := by nlinarith [mul_nonneg hτ0 (sub_nonneg.mpr hτ1)]
  have hτ3 : τ ^ 3 ≤ τ := by
    have hmul := mul_le_mul_of_nonneg_left hτ2 hτ0
    nlinarith
  nlinarith

private theorem B8NormalizedMainMass_paid_error (C δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop,
      C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) ≤
        δ * SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  have hδU : 0 < δ * SingularSeries.liuUniversalProduct :=
    mul_pos hδ SingularSeries.liuUniversalProduct_pos
  have hlogs := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (C / (δ * SingularSeries.liuUniversalProduct))))
  filter_upwards [hlogs] with N hN
  have hlogpos : 0 < Real.log (N : ℝ) :=
    lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hN)
  have hC : C ≤ δ * SingularSeries.liuUniversalProduct * Real.log (N : ℝ) := by
    simpa [mul_comm] using
      (div_le_iff₀ hδU).mp ((le_max_right _ _).trans hN)
  have hCdiv : C / Real.log (N : ℝ) ≤ δ * SingularSeries.liuUniversalProduct :=
    (div_le_iff₀ hlogpos).2 hC
  calc
    C * (N : ℝ) / Real.log (N : ℝ) ^ (3 : ℝ) =
        (C / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      rw [Real.rpow_ofNat]
      field_simp
    _ ≤ (δ * SingularSeries.liuUniversalProduct) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hCdiv (by positivity)
    _ ≤ (δ * SingularSeries.liuSingularSeries N) *
        ((N : ℝ) / Real.log (N : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ.le) (by positivity)
    _ = _ := by ring

/-- The selected B8 sieve, normalized on its unchanged sum of logarithmic integrals. -/
theorem goldbachB8PlusSiftedCount_normalized_mainMass (δ : ℝ) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ _hEven : Even N,
        let Z := Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1))
        2 ≤ Z ∧ Z ≤ Real.sqrt (N : ℝ) ∧
          ((goldbachB8PlusSiftedAtoms N Z).card : ℝ) ≤
            (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB8PlusMainMass N /
                Real.log (N : ℝ) +
              δ * SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  let τ : ℝ := min (δ / 56) 1
  have hτ : 0 < τ := lt_min (by positivity) zero_lt_one
  have hτ1 : τ ≤ 1 := min_le_right _ _
  have hτδ : 56 * τ ≤ δ := by
    have h := min_le_left (δ / 56) (1 : ℝ)
    dsimp [τ]
    linarith
  obtain ⟨C, _hC, B, hB, Npaid, _hNpaid, hpaid⟩ :=
    goldbachB8PlusSiftedCount_upper_paid 3 (by norm_num)
  obtain ⟨z₀, hpaidN⟩ := hpaid (τ * Real.exp Real.eulerMascheroniConstant)
    (mul_pos hτ (Real.exp_pos _))
  obtain ⟨Z₀, _hZ₀, hprod⟩ :=
    goldbachB8PlusBoundingSieve_product_log_le_liuSingularSeries τ hτ
  obtain ⟨Ng, hNg, hgeom⟩ :=
    goldbachB8Plus_normalized_cutoff_geometry B (max z₀ Z₀) τ hB hτ hτ1
  obtain ⟨Ne, herr⟩ := eventually_atTop.mp (B8NormalizedMainMass_paid_error C δ hδ)
  refine ⟨B, hB, max Ng (max Npaid Ne), hNg.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hgN : Ng ≤ N := (le_max_left _ _).trans hN
  have hpN : Npaid ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have heN : Ne ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN4 : 4 ≤ N := hNg.trans hgN
  let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z := Real.sqrt Δ
  let X := goldbachB8PlusMainMass N
  let S := goldbachB8PlusBoundingSieve N hEven Z
  obtain ⟨hZbig, hZquarter, hquarter, hZsqrt, hs, hlogZpos, hratio⟩ := hgeom N hgN
  have hZ2 : 2 ≤ Z := (le_max_left _ _).trans hZbig
  have hz₀ : z₀ ≤ Z := (le_max_left _ _).trans ((le_max_right _ _).trans hZbig)
  have hZ₀ : Z₀ ≤ Z := (le_max_right _ _).trans ((le_max_right _ _).trans hZbig)
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg : 0 ≤ X := goldbachB8PlusMainMass_nonneg N
  have hpaidBound := hpaidN N hpN hEven Z 2 hz₀ hZ2 (hZquarter.trans hquarter)
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
        (B8NormalizedMainMass_coefficient hτ.le hτ1 hτδ) hlogNpos.le
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

/-- The actual S4 consumer: no cutoff, level, free mass, or unpaid error remains. -/
theorem goldbachS4_normalized_upper_mainMass
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N →
      (goldbachS4 (goldbachDifferenceCarrier N ε) N ((N : ℝ) ^ ((3 : ℝ) / 11)) : ℝ) ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * goldbachB8PlusMainMass N /
            Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  obtain ⟨B, _hB, Ns, hNs, hs⟩ :=
    goldbachB8PlusSiftedCount_normalized_mainMass (δ / 2) (by positivity)
  obtain ⟨Nt, _hNt, ht⟩ :=
    goldbachS4_le_sifted_B8Plus_with_paid_finite_error (δ / 2) ε (by positivity) hε hεu
  refine ⟨max Ns Nt, hNs.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hsN : Ns ≤ N := (le_max_left _ _).trans hN
  have htN : Nt ≤ N := (le_max_right _ _).trans hN
  let Z := Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1))
  obtain ⟨hZ2, hZsqrt, hbound⟩ := hs N hsN hEven
  have htransport := ht N htN Z (by linarith) hZsqrt
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by
    have hN4 : 4 ≤ N := hNs.trans hsN
    exact_mod_cast (show 1 < N by omega))
  have hmass : 0 ≤ SingularSeries.liuSingularSeries N * goldbachB8PlusMainMass N /
      Real.log (N : ℝ) :=
    div_nonneg (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le
      (goldbachB8PlusMainMass_nonneg N)) hlogpos.le
  have hbudget := mul_nonneg hδ.le hmass
  dsimp [Z] at htransport
  simp only [div_eq_mul_inv] at hbudget hbound htransport ⊢
  nlinarith only [hbound, htransport, hbudget]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig