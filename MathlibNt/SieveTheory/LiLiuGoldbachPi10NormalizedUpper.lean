import MathlibNt.SieveTheory.LiLiuGoldbachB10MainWeight
import MathlibNt.SieveTheory.LiLiuGoldbachB10NormalizedUpper
import MathlibNt.SieveTheory.LiLiuGoldbachPi10Sifted
import MathlibNt.SieveTheory.LiLiuGoldbachWeightLogScale
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import MathlibNt.SieveTheory.LiuSingularSeries

noncomputable section

open Filter
open AnalyticNumberTheory.LargeSieve.ChenLiuCoprimeProducer

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem Pi10NormalizedUpper_Z_ge_one_eventually
    (B : ℝ) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Δ ^ ((1 : ℝ) / 2)
      1 ≤ Z := by
  have hB1 : 0 ≤ B + 1 := by linarith
  obtain ⟨Ncond, hcond⟩ := eventually_atTop.mp
    (MathlibNt.SieveTheory.LiuWeight.eventually_pan_conductor_bounds (B + 1) hB1)
  refine ⟨max 4 Ncond, le_max_left _ _, ?_⟩
  intro N hN
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  have hNcond : Ncond ≤ N := (le_max_right _ _).trans hN
  rcases hcond N hNcond with ⟨hlogN, hlow1, hlowUpper, _, _⟩
  have hlow : 1 ≤ lowConductor N (B + 1) := lowConductor_ge_one hlogN hB1
  have hupperFloor : 1 ≤ ⌊upperConductor N (B + 1)⌋₊ := by
    have hlowUpper' : ⌊lowConductor N (B + 1)⌋₊ ≤ ⌊upperConductor N (B + 1)⌋₊ := by
      simpa [MathlibNt.SieveTheory.LiuWeight.panModulusCutoff_eq_upper] using hlowUpper
    exact hlow1.trans hlowUpper'
  have hupperNonneg : 0 ≤ upperConductor N (B + 1) := by
    exact div_nonneg (Real.sqrt_nonneg _) (show 0 ≤ lowConductor N (B + 1) by linarith)
  have hΔge : 1 ≤ Δ := by
    have hupperGe : 1 ≤ upperConductor N (B + 1) := by
      have hcast : (1 : ℝ) ≤ ⌊upperConductor N (B + 1)⌋₊ := by
        exact_mod_cast hupperFloor
      exact hcast.trans (Nat.floor_le hupperNonneg)
    simpa [Δ, upperConductor, lowConductor, Real.sqrt_eq_rpow] using hupperGe
  have hΔnonneg : 0 ≤ Δ := by
    simpa [Δ, upperConductor, lowConductor, Real.sqrt_eq_rpow] using hupperNonneg
  have hsqrt : 1 ≤ Real.sqrt Δ := by
    have hsqrt' : Real.sqrt 1 ≤ Real.sqrt Δ := Real.sqrt_le_sqrt hΔge
    simpa using hsqrt'
  simpa [Δ, Z, Real.sqrt_eq_rpow] using hsqrt

private theorem Pi10NormalizedUpper_Z_le_quarter_power
    {N : ℕ} {B : ℝ} (hlogN : 1 ≤ Real.log (N : ℝ)) (hB : 0 ≤ B) :
    let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
    let Z := Δ ^ ((1 : ℝ) / 2)
    Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
  have hB1 : 0 ≤ B + 1 := by linarith
  have hNnonneg : 0 ≤ (N : ℝ) := by positivity
  have hpowLog : 1 ≤ Real.log (N : ℝ) ^ (B + 1) := Real.one_le_rpow hlogN hB1
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  have hΔle : Δ ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
    dsimp [Δ]
    exact div_le_self (by positivity) hpowLog
  have hΔnonneg : 0 ≤ Δ := by
    dsimp [Δ]
    positivity
  dsimp [Z]
  calc
    Δ ^ ((1 : ℝ) / 2) = Real.sqrt Δ := by rw [← Real.sqrt_eq_rpow]
    _ ≤ Real.sqrt ((N : ℝ) ^ ((1 : ℝ) / 2)) := Real.sqrt_le_sqrt hΔle
    _ = (N : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNnonneg]
      norm_num

private theorem Pi10NormalizedUpper_fourHundred_floor_pay_eventually
    (δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      let Δ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
      let Z := Δ ^ ((1 : ℝ) / 2)
      400 * (⌊Z⌋₊ : ℝ) ≤
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
  have hδU : 0 < (δ / 2) * SingularSeries.liuUniversalProduct := by
    exact mul_pos (by positivity) SingularSeries.liuUniversalProduct_pos
  obtain ⟨Npow, hNpow2, hpow⟩ :=
    goldbach_power_error_le_log_scale_eventually
      400 ((3 : ℝ) / 4) ((δ / 2) * SingularSeries.liuUniversalProduct)
      (by norm_num) (by norm_num) hδU
  have hB1 : 0 ≤ B + 1 := by linarith
  obtain ⟨Ncond, hcond⟩ := eventually_atTop.mp
    (MathlibNt.SieveTheory.LiuWeight.eventually_pan_conductor_bounds (B + 1) hB1)
  refine ⟨max 4 (max Npow Ncond), le_max_left _ _, ?_⟩
  intro N hN
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  have hNrest : max Npow Ncond ≤ N := (le_max_right _ _).trans hN
  have hNpow : Npow ≤ N := (le_max_left _ _).trans hNrest
  have hNcond : Ncond ≤ N := (le_max_right _ _).trans hNrest
  rcases hcond N hNcond with ⟨hlogN, _, _, _, _⟩
  have hZnonneg : 0 ≤ Z := by
    dsimp [Z, Δ]
    positivity
  have hfloor :
      (⌊Z⌋₊ : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 4) := by
    exact (Nat.floor_le hZnonneg).trans
      (by simpa [Δ, Z] using Pi10NormalizedUpper_Z_le_quarter_power hlogN hB)
  have hpowQuarter :
      400 * (N : ℝ) ^ ((1 : ℝ) / 4) ≤
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hpow' := hpow N hNpow ((3 : ℝ) / 4) le_rfl
    simpa [show (1 : ℝ) - (3 : ℝ) / 4 = (1 : ℝ) / 4 by norm_num] using hpow'
  calc
    400 * (⌊Z⌋₊ : ℝ) ≤ 400 * (N : ℝ) ^ ((1 : ℝ) / 4) := by
      gcongr
    _ ≤ (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
        Real.log (N : ℝ) ^ (2 : ℝ) := hpowQuarter

/-- Exact normalized upper bound for the actual integer-valued `Pi10` count.
The auxiliary cutoff is eliminated from the statement and the full
`400 * floor Z` loss is paid into the final `δ * 𝔖_Liu(N) * N / log(N)^2`
remainder. -/
theorem goldbachPi10_normalized_upper
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ ε γ : ℝ, 0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → Even N → ∀ β : ℝ,
        (1 : ℝ) / 18 < β →
        (goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) : ℝ) ≤
          (8 + δ) * SingularSeries.liuSingularSeries N *
              goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) /
            Real.log (N : ℝ) +
            δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
              Real.log (N : ℝ) ^ (2 : ℝ) := by
  have hδ2 : 0 < δ / 2 := by linarith
  obtain ⟨B, hB, hB10⟩ := goldbachB10SiftedCount_normalized_upper (δ / 2) hδ2
  intro ε γ hε hεlt hγ
  obtain ⟨Nmass, hNmass2, hmass⟩ := goldbachB10MainMass_nonneg_eventually ε γ hε hεlt hγ
  obtain ⟨NB10, hNB104, hB10N⟩ := hB10 ε γ hε hεlt hγ
  obtain ⟨NZ1, hNZ14, hZ1⟩ := Pi10NormalizedUpper_Z_ge_one_eventually B hB
  obtain ⟨Npay, hNpay4, hpay⟩ := Pi10NormalizedUpper_fourHundred_floor_pay_eventually δ B hδ hB
  let N₀ := max 4 (max Nmass (max NB10 (max NZ1 Npay)))
  refine ⟨N₀, le_max_left _ _, ?_⟩
  intro N hN hEven β hβ
  let Δ : ℝ := (N : ℝ) ^ ((1 : ℝ) / 2) / Real.log (N : ℝ) ^ (B + 1)
  let Z : ℝ := Δ ^ ((1 : ℝ) / 2)
  let X : ℝ := goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)
  have hNmass : Nmass ≤ N := by
    exact (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNrest : max NB10 (max NZ1 Npay) ≤ N := by
    exact (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNB10 : NB10 ≤ N := (le_max_left _ _).trans hNrest
  have hNrest' : max NZ1 Npay ≤ N := (le_max_right _ _).trans hNrest
  have hNZ1 : NZ1 ≤ N := (le_max_left _ _).trans hNrest'
  have hNpay : Npay ≤ N := (le_max_right _ _).trans hNrest'
  have hN2 : 2 ≤ N := by omega
  have hlogNpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXnonneg : 0 ≤ X := by
    dsimp [X]
    exact hmass N hNmass β hβ
  have hZ1N : 1 ≤ Z := by
    simpa [Δ, Z] using hZ1 N hNZ1
  have hPi :=
    (Int.cast_le (R := ℝ)).mpr
      (goldbachPi10_le_goldbachB10SiftedCount_add_fourHundred_floor
        (c := (N : ℝ) ^ γ) (Z := Z) hN2 hε hβ hZ1N)
  push_cast at hPi
  have hB10bound :
      (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) ≤
        (8 + δ / 2) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
    simpa [Δ, Z, X] using hB10N N hNB10 hEven β hβ
  have hpayU :
      400 * (⌊Z⌋₊ : ℝ) ≤
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    simpa [Δ, Z] using hpay N hNpay
  have hpayS :
      400 * (⌊Z⌋₊ : ℝ) ≤
        (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ) := by
    have hseries :
        (δ / 2) * SingularSeries.liuUniversalProduct ≤
          (δ / 2) * SingularSeries.liuSingularSeries N := by
      exact mul_le_mul_of_nonneg_left
        (SingularSeries.liuUniversalProduct_le_liuSingularSeries N) hδ2.le
    have hmassNonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) ^ (2 : ℝ) := by
      positivity
    have hscale :
        (δ / 2) * SingularSeries.liuUniversalProduct * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) ≤
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_le_mul_of_nonneg_right hseries hmassNonneg)
    exact hpayU.trans hscale
  have hmainWiden :
      (8 + δ / 2) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) ≤
        (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) := by
    have hcoeff :
        (8 + δ / 2) * (SingularSeries.liuSingularSeries N * X) ≤
          (8 + δ) * (SingularSeries.liuSingularSeries N * X) := by
      exact mul_le_mul_of_nonneg_right (by linarith : 8 + δ / 2 ≤ 8 + δ)
        (mul_nonneg (SingularSeries.liuSingularSeries_pos N).le hXnonneg)
    exact div_le_div_of_nonneg_right
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hcoeff) hlogNpos.le
  calc
    (goldbachPi10 N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) : ℝ)
      ≤ (goldbachB10SiftedCount N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) Z : ℝ) +
          400 * (⌊Z⌋₊ : ℝ) := hPi
    _ ≤ ((8 + δ / 2) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
          (δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ)) +
        ((δ / 2) * SingularSeries.liuSingularSeries N * (N : ℝ) /
          Real.log (N : ℝ) ^ (2 : ℝ)) := by
            exact add_le_add hB10bound hpayS
    _ = (8 + δ / 2) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
              ring
    _ ≤ (8 + δ) * SingularSeries.liuSingularSeries N * X / Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
              exact add_le_add hmainWiden le_rfl
    _ = (8 + δ) * SingularSeries.liuSingularSeries N *
          goldbachB10MainMass N ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ) / Real.log (N : ℝ) +
          δ * SingularSeries.liuSingularSeries N * (N : ℝ) /
            Real.log (N : ℝ) ^ (2 : ℝ) := by
              rfl

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig