import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import MathlibNt.SieveTheory.LiLiuGoldbachBasicToSieve
import MathlibNt.SieveTheory.LiuLogarithmicIntegral
import MathlibNt.SieveTheory.LiuWeightMainSum
import MathlibNt.SieveTheory.MertensTheorem

open scoped BigOperators
open Filter Finset
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable local instance instDecidableS2MainMassUpper (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The literal `S2` main-mass sum at the genuine single-endpoint carrier
`r ∈ R(N,N^τ)`. -/
noncomputable def goldbachS2MainMassUpperSum (N : ℕ) (τ : ℝ) : ℝ :=
  ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (r : ℝ))

private noncomputable def S2MainMassLogKernel (u : ℝ) : ℝ :=
  ((1 : ℝ) - u)⁻¹

private noncomputable def S2MainMassWindowWeight (N : ℕ) (r : ℕ) : ℝ :=
  S2MainMassLogKernel (Real.log (r : ℝ) / Real.log (N : ℝ)) / (r : ℝ)

private theorem S2MainMass_prime_le_rpow_half_of_sq_le
    {N r : ℕ} (hrSq : r ^ 2 ≤ N) :
    (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) := by
  have hrsq : (r : ℝ) ^ 2 ≤ (N : ℝ) := by exact_mod_cast hrSq
  have hsqrt : (r : ℝ) ≤ Real.sqrt (N : ℝ) := Real.le_sqrt_of_sq_le hrsq
  simpa [Real.sqrt_eq_rpow] using hsqrt

private theorem S2MainMass_sqrt_le_div_of_le_rpow_half
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hrle : (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) :
    Real.sqrt (N : ℝ) ≤ (N : ℝ) / (r : ℝ) := by
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hr0 : 0 ≤ (r : ℝ) := by positivity
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hsqrt0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  apply (le_div_iff₀ hrpos).2
  calc
    Real.sqrt (N : ℝ) * (r : ℝ)
      ≤ Real.sqrt (N : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 2)) := by
          gcongr
    _ = (Real.sqrt (N : ℝ)) ^ 2 := by
          rw [Real.sqrt_eq_rpow]
          ring
    _ = N := by
          rw [Real.sq_sqrt hN0]

private theorem S2MainMass_logKernel_continuousOn
    {τ : ℝ} (_hτ : τ < (1 : ℝ) / 2) :
    ContinuousOn S2MainMassLogKernel (Set.Icc τ (1 / 2 : ℝ)) := by
  unfold S2MainMassLogKernel
  apply (continuousOn_const.sub continuousOn_id).inv₀
  intro u hu
  have hu2 : u ≤ (1 / 2 : ℝ) := hu.2
  have hne : ((1 : ℝ) - u) ≠ 0 := by
    linarith
  simpa using hne

private theorem S2MainMass_logKernel_integral
    {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < (1 : ℝ) / 2) :
    (∫ u in τ..(1 / 2 : ℝ), S2MainMassLogKernel u / u) =
      Real.log ((1 - τ) / τ) := by
  have hcongr :
      (∫ u in τ..(1 / 2 : ℝ), S2MainMassLogKernel u / u) =
        ∫ u in τ..(1 / 2 : ℝ), (1 / u) + 1 / (1 - u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (le_of_lt hτ)] at hu
    have hu0 : u ≠ 0 := ne_of_gt (hτ0.trans_le hu.1)
    have hu1 : 1 - u ≠ 0 := by
      linarith [hu.2]
    have hterm : S2MainMassLogKernel u / u = (1 / u) + 1 / (1 - u) := by
      unfold S2MainMassLogKernel
      field_simp [hu0, hu1]
      ring
    simpa using hterm
  rw [hcongr]
  have hintLeft :
      IntervalIntegrable (fun u : ℝ => 1 / u) MeasureTheory.volume τ (1 / 2 : ℝ) := by
    have hleftInv :
        IntervalIntegrable (fun u : ℝ => u⁻¹) MeasureTheory.volume τ (1 / 2 : ℝ) :=
      (continuousOn_id.inv₀ (fun u hu => ne_of_gt (hτ0.trans_le hu.1))).intervalIntegrable_of_Icc
        (μ := MeasureTheory.volume) (le_of_lt hτ)
    simpa [one_div] using hleftInv
  have hintRight :
      IntervalIntegrable (fun u : ℝ => 1 / (1 - u)) MeasureTheory.volume τ (1 / 2 : ℝ) := by
    have hright : ContinuousOn (fun u : ℝ => ((1 : ℝ) - u)⁻¹) (Set.Icc τ (1 / 2 : ℝ)) := by
      apply (continuousOn_const.sub continuousOn_id).inv₀
      intro u hu
      have hu2 : u ≤ (1 / 2 : ℝ) := hu.2
      have hne : ((1 : ℝ) - u) ≠ 0 := by
        linarith
      simpa using hne
    have hrightInv :
        IntervalIntegrable (fun u : ℝ => ((1 : ℝ) - u)⁻¹) MeasureTheory.volume τ (1 / 2 : ℝ) :=
      hright.intervalIntegrable_of_Icc (μ := MeasureTheory.volume) (le_of_lt hτ)
    simpa [one_div] using hrightInv
  have hsum :
      (∫ u in τ..(1 / 2 : ℝ), 1 / u + 1 / (1 - u)) =
        (∫ u in τ..(1 / 2 : ℝ), 1 / u) + ∫ u in τ..(1 / 2 : ℝ), 1 / (1 - u) := by
    simpa using (intervalIntegral.integral_add hintLeft hintRight)
  have hleft := integral_one_div_of_pos hτ0 (by norm_num : (0 : ℝ) < 1 / 2)
  have hrightDeriv :
      ∀ u ∈ Set.uIcc τ (1 / 2 : ℝ),
        HasDerivAt (-Real.log ∘ fun x : ℝ => 1 - x) (1 / (1 - u)) u := by
    intro u hu
    rw [Set.uIcc_of_le (le_of_lt hτ)] at hu
    have hu1 : 1 - u ≠ 0 := by
      linarith [hu.2]
    have hsub0 : HasDerivAt ((fun x : ℝ => (1 : ℝ)) - fun x : ℝ => x) (0 - 1) u :=
      (hasDerivAt_const u (1 : ℝ)).sub (hasDerivAt_id u)
    have hlog :
        HasDerivAt (Real.log ∘ fun x : ℝ => 1 - x) ((1 - u)⁻¹ * (0 - 1)) u :=
      (Real.hasDerivAt_log hu1).comp u hsub0
    simpa [Function.comp, one_div] using hlog.neg
  have hright :
      (∫ u in τ..(1 / 2 : ℝ), 1 / (1 - u)) =
        Real.log ((1 - τ) / (1 / 2 : ℝ)) := by
    have hraw := intervalIntegral.integral_eq_sub_of_hasDerivAt hrightDeriv hintRight
    have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
    have h1τne : 1 - τ ≠ 0 := by linarith
    calc
      (∫ u in τ..(1 / 2 : ℝ), 1 / (1 - u))
        = -Real.log (1 - (1 / 2 : ℝ)) - (-Real.log (1 - τ)) := by simpa using hraw
      _ = Real.log (1 - τ) - Real.log (1 / 2 : ℝ) := by ring_nf
      _ = Real.log ((1 - τ) / (1 / 2 : ℝ)) := by
            symm
            exact Real.log_div h1τne hhalf
  calc
    ∫ u in τ..(1 / 2 : ℝ), 1 / u + 1 / (1 - u)
      = Real.log ((1 / 2 : ℝ) / τ) + Real.log ((1 - τ) / (1 / 2 : ℝ)) := by
          rw [hsum, hleft, hright]
    _ = Real.log ((1 - τ) / τ) := by
      have hhalf : (1 / 2 : ℝ) ≠ 0 := by norm_num
      have hτne : τ ≠ 0 := ne_of_gt hτ0
      have h1τne : 1 - τ ≠ 0 := by linarith
      rw [← Real.log_mul (div_ne_zero hhalf hτne) (div_ne_zero h1τne hhalf)]
      field_simp [hhalf, hτne]

private theorem S2MainMass_logDifference_continuousAt
    {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < (1 : ℝ) / 2) :
    ContinuousAt (fun u : ℝ => Real.log (1 - u) - Real.log u) τ := by
  have hleft : ContinuousAt (fun u : ℝ => Real.log (1 - u)) τ := by
    have h1τne : 1 - τ ≠ 0 := by linarith
    have hraw :=
      (Real.continuousAt_log h1τne).comp
        (continuousAt_const.sub continuousAt_id)
    convert hraw using 1
    · funext u
      rfl
  have hright : ContinuousAt (fun u : ℝ => Real.log u) τ :=
    Real.continuousAt_log hτ0.ne'
  exact hleft.sub hright

private theorem S2MainMass_choose_lowerExponent
    {τ η : ℝ} (hτ0 : 0 < τ) (hτ : τ < (1 : ℝ) / 2) (hη : 0 < η) :
    ∃ τ₀ : ℝ, 0 < τ₀ ∧ τ₀ < τ ∧
      Real.log ((1 - τ₀) / τ₀) ≤ Real.log ((1 - τ) / τ) + η := by
  have hcont := S2MainMass_logDifference_continuousAt hτ0 hτ
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδpos, hδ⟩ := hcont η hη
  let ε : ℝ := min (δ / 2) (τ / 2)
  have hεpos : 0 < ε := by
    dsimp [ε]
    positivity
  have hεltδ : ε < δ := by
    calc
      ε ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  refine ⟨τ - ε, ?_, ?_, ?_⟩
  · have hεle : ε ≤ τ / 2 := min_le_right _ _
    nlinarith
  · linarith
  · have hdist : dist (τ - ε) τ < δ := by
      rw [Real.dist_eq]
      have hεnonneg : 0 ≤ ε := le_of_lt hεpos
      calc
        |(τ - ε) - τ| = |(-ε : ℝ)| := by ring_nf
        _ = ε := by simpa using abs_of_nonneg hεnonneg
        _ < δ := hεltδ
    have hclose := hδ hdist
    have hτ₀ne : τ - ε ≠ 0 := by
      have hεle : ε ≤ τ / 2 := min_le_right _ _
      nlinarith
    have h1τ₀ne : 1 - (τ - ε) ≠ 0 := by
      have hεnonneg : 0 ≤ ε := le_of_lt hεpos
      linarith
    have hτne : τ ≠ 0 := ne_of_gt hτ0
    have h1τne : 1 - τ ≠ 0 := by linarith
    rw [Real.dist_eq] at hclose
    have hupper :
        (Real.log (1 - (τ - ε)) - Real.log (τ - ε)) -
            (Real.log (1 - τ) - Real.log τ) < η := (abs_lt.mp hclose).2
    rw [Real.log_div h1τ₀ne hτ₀ne, Real.log_div h1τne hτne]
    linarith

private theorem S2MainMass_carrier_subset_window
    {N : ℕ} {τ₀ τ : ℝ}
    (hN : 1 < N) (hτ : τ₀ < τ) :
    goldbachS2Primes N ((N : ℝ) ^ τ) ⊆
      ((Finset.Ioc (MertensTheorem.rpowFloor N τ₀)
        (MertensTheorem.rpowFloor N ((1 : ℝ) / 2))).filter Nat.Prime) := by
  intro r hr
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, hrLower, hrSq⟩
  apply Finset.mem_filter.mpr
  constructor
  · have hNreal : (1 : ℝ) < N := by exact_mod_cast hN
    have hlower : (N : ℝ) ^ τ₀ < (r : ℝ) := by
      have hpow : (N : ℝ) ^ τ₀ < (N : ℝ) ^ τ :=
        Real.rpow_lt_rpow_of_exponent_lt hNreal hτ
      exact hpow.trans_le hrLower
    have hupper : (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
      S2MainMass_prime_le_rpow_half_of_sq_le hrSq
    exact (MertensTheorem.mem_Ioc_rpowFloor_iff).2 ⟨hlower, hupper⟩
  · exact hrPrime

private theorem S2MainMass_window_weight_nonneg
    {N r : ℕ} {τ : ℝ} (hN : 2 ≤ N)
    (hr : r ∈ ((Finset.Ioc (MertensTheorem.rpowFloor N τ)
      (MertensTheorem.rpowFloor N ((1 : ℝ) / 2))).filter Nat.Prime)) :
    0 ≤ S2MainMassWindowWeight N r := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hrIoc : r ∈ Finset.Ioc (MertensTheorem.rpowFloor N τ)
      (MertensTheorem.rpowFloor N ((1 : ℝ) / 2)) := (Finset.mem_filter.mp hr).1
  have hrPrime : r.Prime := (Finset.mem_filter.mp hr).2
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrPrime.pos
  have hrltN : (r : ℝ) < N := by
    have hupper := (MertensTheorem.mem_Ioc_rpowFloor_iff.mp hrIoc).2
    have hpowlt : (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_lt_rpow_of_exponent_lt hNreal (by norm_num : (1 : ℝ) / 2 < 1))
    exact hupper.trans_lt hpowlt
  have hden : 0 < 1 - Real.log (r : ℝ) / Real.log (N : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hlogN).mpr (Real.log_lt_log hrpos hrltN))
  unfold S2MainMassWindowWeight S2MainMassLogKernel
  positivity

private theorem S2MainMass_proxy_term_identity
    {N r : ℕ} (hN : 2 ≤ N) (hr : 0 < r)
    (hrle : (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2)) :
    ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ)) =
      ((N : ℝ) / Real.log (N : ℝ)) * S2MainMassWindowWeight N r := by
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hNpos : (0 : ℝ) < N := by positivity
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hrltN : (r : ℝ) < N := by
    have hpowlt : (N : ℝ) ^ ((1 : ℝ) / 2) < (N : ℝ) := by
      simpa only [Real.rpow_one] using
        (Real.rpow_lt_rpow_of_exponent_lt hNreal (by norm_num : (1 : ℝ) / 2 < 1))
    exact hrle.trans_lt hpowlt
  have hden : 0 < 1 - Real.log (r : ℝ) / Real.log (N : ℝ) := by
    exact sub_pos.mpr ((div_lt_one hlogN).mpr (Real.log_lt_log hrpos hrltN))
  have hdiff : 0 < Real.log (N : ℝ) - Real.log (r : ℝ) := by
    have hh := (div_lt_one hlogN).mp (sub_pos.mp hden)
    linarith
  rw [Real.log_div hNpos.ne' hrpos.ne']
  unfold S2MainMassWindowWeight S2MainMassLogKernel
  field_simp [hlogN.ne', hden.ne', hdiff.ne', hrpos.ne']

private theorem S2MainMass_remainder_term_le
    {N r : ℕ} {τ : ℝ} (C : ℝ) (hC : 0 ≤ C) (hN : 4 ≤ N)
    (hr : r ∈ goldbachS2Primes N ((N : ℝ) ^ τ))
    (hpoint :
      |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))| ≤
        C * ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ)) ^ 2) :
    |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))| ≤
      (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) * ((1 : ℝ) / (r : ℝ)) := by
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, hrSq⟩
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hrposNat : 0 < r := hrPrime.pos
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hrposNat
  have hrle : (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
    S2MainMass_prime_le_rpow_half_of_sq_le hrSq
  have hxSqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) / (r : ℝ) :=
    S2MainMass_sqrt_le_div_of_le_rpow_half (show 0 < N by omega) hrposNat hrle
  have hxLogLower :
      (1 / 2 : ℝ) * Real.log (N : ℝ) ≤ Real.log ((N : ℝ) / (r : ℝ)) := by
    have hN0 : 0 ≤ (N : ℝ) := by positivity
    have hxpos : 0 < (N : ℝ) / (r : ℝ) := by positivity
    calc
      (1 / 2 : ℝ) * Real.log (N : ℝ) = Real.log (Real.sqrt (N : ℝ)) := by
        rw [Real.log_sqrt hN0]
        ring
      _ ≤ Real.log ((N : ℝ) / (r : ℝ)) :=
        Real.log_le_log (Real.sqrt_pos.2 (by positivity)) hxSqrt
  have hxLogPos : 0 < Real.log ((N : ℝ) / (r : ℝ)) := by
    linarith
  have hinv :
      1 / Real.log ((N : ℝ) / (r : ℝ)) ^ 2 ≤ 4 / Real.log (N : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hxLogPos) (sq_pos_of_pos hlogN)]
    nlinarith [sq_nonneg (Real.log ((N : ℝ) / (r : ℝ)))]
  calc
    |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))|
      ≤ C * ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ)) ^ 2 := hpoint
    _ = C * (((N : ℝ) / (r : ℝ)) * (1 / Real.log ((N : ℝ) / (r : ℝ)) ^ 2)) := by
          ring
    _ ≤ C * (((N : ℝ) / (r : ℝ)) * (4 / Real.log (N : ℝ) ^ 2)) := by
          gcongr
    _ = (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) * ((1 : ℝ) / (r : ℝ)) := by
          field_simp [hrpos.ne', (sq_pos_of_pos hlogN).ne']

/-- For every fixed `1/3 < τ < 1/2`, the literal single-endpoint `S2`
main-mass sum is eventually bounded by the exact logarithmic kernel
`log ((1-τ)/τ)`. The finite carrier is the actual `goldbachS2Primes`
carrier, with no switched source predicate. -/
theorem goldbachS2MainMassUpper
    (τ η : ℝ) (hτ : (1 : ℝ) / 3 < τ) (hτu : τ < (1 : ℝ) / 2)
    (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachS2MainMassUpperSum N τ ≤
        (Real.log ((1 - τ) / τ) + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
  have hτ0 : 0 < τ := by linarith
  obtain ⟨τ₀, hτ₀0, hτ₀τ, hkernelτ₀⟩ :=
    S2MainMass_choose_lowerExponent (τ := τ) (η := η / 3) hτ0 hτu (by positivity)
  have hτ₀u : τ₀ < (1 : ℝ) / 2 := hτ₀τ.trans hτu
  have hmainLim :=
    MertensTheorem.tendsto_weightedPrimeReciprocalLogSum
      hτ₀0 hτ₀u (S2MainMass_logKernel_continuousOn hτ₀u)
  have hmainEventually :
      ∀ᶠ N : ℕ in atTop,
        MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) ≤
          Real.log ((1 - τ₀) / τ₀) + η / 3 := by
    have hclose := (Metric.tendsto_nhds.1 hmainLim) (η / 3) (by positivity)
    filter_upwards [hclose] with N hN
    rw [S2MainMass_logKernel_integral hτ₀0 hτ₀u, Real.dist_eq] at hN
    have hupper :
        MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) -
            Real.log ((1 - τ₀) / τ₀) < η / 3 := (abs_lt.mp hN).2
    linarith
  obtain ⟨Nmain, hNmain⟩ := eventually_atTop.mp hmainEventually
  have hconstLim :=
    MertensTheorem.tendsto_weightedPrimeReciprocalLogSum_const
      (c := 1) hτ₀0 hτ₀u
  have hconstEventually :
      ∀ᶠ N : ℕ in atTop,
        MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1) N τ₀ (1 / 2 : ℝ) ≤
          Real.log (((1 / 2 : ℝ) / τ₀)) + 1 := by
    have hclose := (Metric.tendsto_nhds.1 (by simpa using hconstLim)) 1 zero_lt_one
    filter_upwards [hclose] with N hN
    rw [Real.dist_eq] at hN
    have hupper :
        MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1) N τ₀ (1 / 2 : ℝ) -
            Real.log (((1 / 2 : ℝ) / τ₀)) < 1 := by
              simpa using (abs_lt.mp hN).2
    linarith
  obtain ⟨Nconst, hNconst⟩ := eventually_atTop.mp hconstEventually
  obtain ⟨C, hC, hCrest⟩ :=
    eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hCrest
  have hsqrtTendsto : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop := by
    have hpow :
        Tendsto (fun N : ℕ => (N : ℝ) ^ ((1 : ℝ) / 2)) atTop atTop :=
      (tendsto_rpow_atTop (show 0 < (1 : ℝ) / 2 by norm_num)).comp
        tendsto_natCast_atTop_atTop
    simpa [Real.sqrt_eq_rpow] using hpow
  obtain ⟨Nsqrt, hNsqrt⟩ := eventually_atTop.mp
    (hsqrtTendsto.eventually (eventually_ge_atTop (max x₀ 2)))
  let K : ℝ := Real.log (((1 / 2 : ℝ) / τ₀)) + 1
  have hKpos : 0 < K := by
    have hratio : 1 < ((1 / 2 : ℝ) / τ₀) := (one_lt_div hτ₀0).2 hτ₀u
    dsimp [K]
    nlinarith [Real.log_pos hratio]
  have hlogTendsto : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    (hlogTendsto.eventually (eventually_ge_atTop (12 * C * K / η)))
  let M : ℕ := max Nmain (max Nconst (max Nsqrt Nlog))
  refine ⟨max 4 M,
    le_max_left _ _, ?_⟩
  intro N hN
  let S := goldbachS2Primes N ((N : ℝ) ^ τ)
  let proxySum : ℝ :=
    ∑ r ∈ S, ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ))
  let remSum : ℝ :=
    ∑ r ∈ S, |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))|
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 < N := by omega
  have hM : M ≤ N := (le_max_right 4 M).trans hN
  have hNmain' : Nmain ≤ N := (le_max_left _ _).trans hM
  have hMconst : max Nconst (max Nsqrt Nlog) ≤ N := (le_max_right _ _).trans hM
  have hNconst' : Nconst ≤ N := (le_max_left _ _).trans hMconst
  have hMsqrt : max Nsqrt Nlog ≤ N := (le_max_right _ _).trans hMconst
  have hNsqrt' : Nsqrt ≤ N := (le_max_left _ _).trans hMsqrt
  have hNlog' : Nlog ≤ N := (le_max_right _ _).trans hMsqrt
  have hNreal : (1 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hNreal
  have hNdivNonneg : 0 ≤ (N : ℝ) / Real.log (N : ℝ) := by positivity
  have hsubset :=
    S2MainMass_carrier_subset_window (N := N) hN1 hτ₀τ
  have hsplit :
      goldbachS2MainMassUpperSum N τ ≤ proxySum + remSum := by
    unfold goldbachS2MainMassUpperSum proxySum remSum S
    calc
      ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
          liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (r : ℝ))
        ≤ ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
            (((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ)) +
              |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))|) := by
                refine Finset.sum_le_sum ?_
                intro r hr
                have hdecomp :
                    liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / (r : ℝ)) =
                      ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ)) +
                        liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ)) := by
                  unfold liuLogarithmicIntegralRemainder
                  ring
                rw [hdecomp]
                nlinarith [le_abs_self
                  (liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ)))]
      _ = proxySum + remSum := by
            rw [Finset.sum_add_distrib]
  have hweightSubset :
      ∑ r ∈ S, S2MainMassWindowWeight N r ≤
        MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) := by
    simpa [MertensTheorem.weightedPrimeReciprocalLogSum, S, S2MainMassWindowWeight] using
      (Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun r hr _ => S2MainMass_window_weight_nonneg (τ := τ₀) hN2 hr))
  have hproxy :
      proxySum ≤
        ((N : ℝ) / Real.log (N : ℝ)) *
          MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) := by
    unfold proxySum S
    calc
      ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
          ((N : ℝ) / (r : ℝ)) / Real.log ((N : ℝ) / (r : ℝ))
        = ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
            ((N : ℝ) / Real.log (N : ℝ)) * S2MainMassWindowWeight N r := by
              apply Finset.sum_congr rfl
              intro r hr
              rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, hrSq⟩
              exact S2MainMass_proxy_term_identity hN2 hrPrime.pos
                (S2MainMass_prime_le_rpow_half_of_sq_le hrSq)
      _ = ((N : ℝ) / Real.log (N : ℝ)) *
            ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ), S2MainMassWindowWeight N r := by
              rw [Finset.mul_sum]
      _ ≤ ((N : ℝ) / Real.log (N : ℝ)) *
            MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) := by
              gcongr
  have hmainBound' :
      MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) ≤
        Real.log ((1 - τ₀) / τ₀) + η / 3 := hNmain N hNmain'
  have hconstBound :
      MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1) N τ₀ (1 / 2 : ℝ) ≤ K := by
    simpa [K] using hNconst N hNconst'
  have hsqrtLarge : max x₀ 2 ≤ Real.sqrt (N : ℝ) := hNsqrt N hNsqrt'
  have hrem :
      remSum ≤ (η / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    have hconstSubset :
        ∑ r ∈ S, ((1 : ℝ) / (r : ℝ)) ≤
          MertensTheorem.weightedPrimeReciprocalLogSum (fun _ : ℝ => 1) N τ₀ (1 / 2 : ℝ) := by
      simpa [MertensTheorem.weightedPrimeReciprocalLogSum, S] using
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun r hr _ => by
            have hrPrime : r.Prime := (Finset.mem_filter.mp hr).2
            positivity))
    have hsumK : ∑ r ∈ S, ((1 : ℝ) / (r : ℝ)) ≤ K := hconstSubset.trans hconstBound
    have hremRaw :
        remSum ≤
          (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) *
            ∑ r ∈ S, ((1 : ℝ) / (r : ℝ)) := by
      unfold remSum S
      calc
        ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
            |liuLogarithmicIntegralRemainder (2 / Real.log 2) ((N : ℝ) / (r : ℝ))|
          ≤ ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ),
              (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) * ((1 : ℝ) / (r : ℝ)) := by
                refine Finset.sum_le_sum ?_
                intro r hr
                rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, hrSq⟩
                have hrle : (r : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 2) :=
                  S2MainMass_prime_le_rpow_half_of_sq_le hrSq
                have hx0le : x₀ ≤ (N : ℝ) / (r : ℝ) := by
                  have hsqrtle :=
                    S2MainMass_sqrt_le_div_of_le_rpow_half
                      (show 0 < N by omega) hrPrime.pos hrle
                  exact ((le_max_left _ _).trans hsqrtLarge).trans hsqrtle
                have hx2 : 2 ≤ (N : ℝ) / (r : ℝ) := by
                  have hsqrtle :=
                    S2MainMass_sqrt_le_div_of_le_rpow_half
                      (show 0 < N by omega) hrPrime.pos hrle
                  exact ((le_max_right _ _).trans hsqrtLarge).trans hsqrtle
                exact S2MainMass_remainder_term_le (τ := τ) C hC hN4 hr (hx₀ _ hx0le hx2)
        _ = (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) *
              ∑ r ∈ goldbachS2Primes N ((N : ℝ) ^ τ), ((1 : ℝ) / (r : ℝ)) := by
                rw [Finset.mul_sum]
    calc
      remSum
        ≤ (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) *
            ∑ r ∈ S, ((1 : ℝ) / (r : ℝ)) := hremRaw
      _ ≤ (4 * C * ((N : ℝ) / Real.log (N : ℝ) ^ 2)) * K := by
            exact mul_le_mul_of_nonneg_left hsumK (by positivity)
      _ = ((4 * C * K) / Real.log (N : ℝ)) * ((N : ℝ) / Real.log (N : ℝ)) := by
            field_simp [hlogN.ne']
      _ ≤ (η / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
            have hlogLower : 12 * C * K / η ≤ Real.log (N : ℝ) := hNlog N hNlog'
            have hcoeff :
                (4 * C * K) / Real.log (N : ℝ) ≤ η / 3 := by
              apply (div_le_iff₀ hlogN).2
              have htmp : 12 * C * K ≤ η * Real.log (N : ℝ) := by
                simpa [mul_comm] using (div_le_iff₀ hη).mp hlogLower
              nlinarith
            exact mul_le_mul_of_nonneg_right hcoeff hNdivNonneg
  have hproxyFinal :
      proxySum ≤
        (Real.log ((1 - τ) / τ) + 2 * η / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
    calc
      proxySum
        ≤ ((N : ℝ) / Real.log (N : ℝ)) *
            MertensTheorem.weightedPrimeReciprocalLogSum S2MainMassLogKernel N τ₀ (1 / 2 : ℝ) :=
          hproxy
      _ ≤ ((N : ℝ) / Real.log (N : ℝ)) * (Real.log ((1 - τ₀) / τ₀) + η / 3) := by
            gcongr
      _ ≤ ((N : ℝ) / Real.log (N : ℝ)) *
            (Real.log ((1 - τ) / τ) + 2 * η / 3) := by
            have hcoef :
                Real.log ((1 - τ₀) / τ₀) + η / 3 ≤
                  Real.log ((1 - τ) / τ) + 2 * η / 3 := by
              linarith
            gcongr
      _ = (Real.log ((1 - τ) / τ) + 2 * η / 3) * ((N : ℝ) / Real.log (N : ℝ)) := by
            ring
  calc
    goldbachS2MainMassUpperSum N τ ≤ proxySum + remSum := hsplit
    _ ≤ (Real.log ((1 - τ) / τ) + 2 * η / 3) * ((N : ℝ) / Real.log (N : ℝ)) +
          (η / 3) * ((N : ℝ) / Real.log (N : ℝ)) := add_le_add hproxyFinal hrem
    _ = (Real.log ((1 - τ) / τ) + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
          ring

/-- Specialization of `goldbachS2MainMassUpper` to
`τ = 9 / 19 - ε` under the task-local constraint `0 < ε < 2 / 15`. -/
theorem goldbachS2MainMassUpper_nine_nineteen_sub
    (η ε : ℝ) (hη : 0 < η) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      goldbachS2MainMassUpperSum N ((9 : ℝ) / 19 - ε) ≤
        (Real.log ((1 - ((9 : ℝ) / 19 - ε)) / ((9 : ℝ) / 19 - ε)) + η) *
          ((N : ℝ) / Real.log (N : ℝ)) := by
  have hτ : (1 : ℝ) / 3 < (9 : ℝ) / 19 - ε := by
    nlinarith
  have hτu : (9 : ℝ) / 19 - ε < (1 : ℝ) / 2 := by
    nlinarith
  simpa using goldbachS2MainMassUpper ((9 : ℝ) / 19 - ε) η hτ hτu hη

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig