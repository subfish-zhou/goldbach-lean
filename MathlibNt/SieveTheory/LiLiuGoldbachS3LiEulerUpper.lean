import MathlibNt.SieveTheory.LiLiuGoldbachS1MainScale
import MathlibNt.SieveTheory.LiLiuGoldbachB10SieveProduct
import MathlibNt.SieveTheory.LiuWeightMainSum
import MathlibNt.SieveTheory.LiLiuGoldbachS3Carrier

open Filter
open MathlibNt.SieveTheory.BombieriVinogradov
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.Sieve

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

private theorem S3LiEulerUpper_endpoint_large (ε X : ℝ) (hεu : ε < 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      2 ≤ goldbachS1Endpoint N ε ∧
      X ≤ (goldbachS1Endpoint N ε : ℝ) ∧
      (1 - ε) * (N : ℝ) / 2 ≤ (goldbachS1Endpoint N ε : ℝ) ∧
      (goldbachS1Endpoint N ε : ℝ) < (1 - ε) * (N : ℝ) := by
  have ha : 0 < 1 - ε := sub_pos.mpr hεu
  obtain ⟨k, hk⟩ := exists_nat_ge (2 * max 3 X / (1 - ε))
  refine ⟨max 4 k, le_max_left _ _, ?_⟩
  intro N hN
  have hkN : (k : ℝ) ≤ N := by
    exact_mod_cast ((le_max_right 4 k).trans hN)
  have hcut : 2 * max 3 X ≤ (1 - ε) * (N : ℝ) := by
    have hh := (div_le_iff₀ ha).mp (hk.trans hkN)
    nlinarith
  have hx6 : 6 ≤ (1 - ε) * (N : ℝ) := by
    linarith [le_max_left (3 : ℝ) X]
  have hceil3 : 3 ≤ Nat.ceil ((1 - ε) * (N : ℝ)) := by
    exact_mod_cast (show (3 : ℝ) ≤ (Nat.ceil ((1 - ε) * (N : ℝ)) : ℝ) by
      linarith [Nat.le_ceil ((1 - ε) * (N : ℝ))])
  have hmcast : (goldbachS1Endpoint N ε : ℝ) =
      (Nat.ceil ((1 - ε) * (N : ℝ)) : ℝ) - 1 := by
    unfold goldbachS1Endpoint
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hmlower : (1 - ε) * (N : ℝ) - 1 ≤
      (goldbachS1Endpoint N ε : ℝ) := by
    rw [hmcast]
    linarith [Nat.le_ceil ((1 - ε) * (N : ℝ))]
  have hmhalf : (1 - ε) * (N : ℝ) / 2 ≤
      (goldbachS1Endpoint N ε : ℝ) := by
    linarith
  refine ⟨by unfold goldbachS1Endpoint; omega, ?_, hmhalf, ?_⟩
  · linarith [le_max_right (3 : ℝ) X]
  · rw [hmcast]
    have hh := Nat.ceil_lt_add_one (show 0 ≤ (1 - ε) * (N : ℝ) by linarith)
    linarith

/-- The genuine mass at the strict endpoint retains its factor `1 - epsilon`.
The rounding, logarithm transport, and genuine-minus-proxy remainder are paid
before choosing the uniform natural-number threshold. -/
theorem goldbachS3_strictEndpoint_mainMass_upper (ε η : ℝ)
    (hε : 0 < ε) (hεu : ε < 1) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      trueLogarithmicIntegral (goldbachS1Endpoint N ε) ≤
        (1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ)) := by
  let t : ℝ := min (η / 3) 1
  have ht : 0 < t := lt_min (by positivity) zero_lt_one
  have ht1 : t ≤ 1 := min_le_right _ _
  have htη : 3 * t ≤ η := by
    have hh : t ≤ η / 3 := min_le_left _ _
    linarith
  have ha : 0 < 1 - ε := sub_pos.mpr hεu
  obtain ⟨C, _hC, hrest⟩ :=
    eventually_abs_liuLogarithmicIntegralRemainder_le (2 / Real.log 2)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hrest
  let X : ℝ := max x₀
    (max (Real.exp (C / t)) (Real.exp (Real.log (2 / (1 - ε)) / t)))
  obtain ⟨N₀, hN₀, hlarge⟩ := S3LiEulerUpper_endpoint_large ε X hεu
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN
  rcases hlarge N hN with ⟨hm2, hXm, hmhalf, hmupper⟩
  let m : ℕ := goldbachS1Endpoint N ε
  have hm2R : (2 : ℝ) ≤ m := by exact_mod_cast hm2
  have hmpos : (0 : ℝ) < m := by linarith
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hXrest : max (Real.exp (C / t))
      (Real.exp (Real.log (2 / (1 - ε)) / t)) ≤ (m : ℝ) :=
    (le_max_right _ _).trans hXm
  have hCexp : Real.exp (C / t) ≤ (m : ℝ) :=
    (le_max_left _ _).trans hXrest
  have hDexp : Real.exp (Real.log (2 / (1 - ε)) / t) ≤ (m : ℝ) :=
    (le_max_right _ _).trans hXrest
  have hClog : C ≤ t * Real.log (m : ℝ) := by
    have hh : C / t ≤ Real.log (m : ℝ) := by
      simpa using Real.log_le_log (Real.exp_pos _) hCexp
    exact (div_le_iff₀ ht).mp hh |>.trans_eq (mul_comm _ _)
  have hDlog : Real.log (2 / (1 - ε)) ≤ t * Real.log (m : ℝ) := by
    have hh : Real.log (2 / (1 - ε)) / t ≤ Real.log (m : ℝ) := by
      simpa using Real.log_le_log (Real.exp_pos _) hDexp
    exact (div_le_iff₀ ht).mp hh |>.trans_eq (mul_comm _ _)
  have hNle : (N : ℝ) ≤ (2 / (1 - ε)) * (m : ℝ) := by
    calc
      (N : ℝ) = (2 / (1 - ε)) * ((1 - ε) * (N : ℝ) / 2) := by
        field_simp
      _ ≤ (2 / (1 - ε)) * (m : ℝ) :=
        mul_le_mul_of_nonneg_left hmhalf (by positivity)
  have hlogTransport : Real.log (N : ℝ) ≤ (1 + t) * Real.log (m : ℝ) := by
    have hh := Real.log_le_log hNpos hNle
    rw [Real.log_mul (by positivity) hmpos.ne'] at hh
    linarith
  have hrestm : trueLogarithmicIntegral (m : ℝ) - (m : ℝ) / Real.log (m : ℝ) ≤
      C * (m : ℝ) / Real.log (m : ℝ) ^ 2 := by
    exact (le_abs_self _).trans (hx₀ (m : ℝ) ((le_max_left _ _).trans hXm) hm2R)
  have herr : C * (m : ℝ) / Real.log (m : ℝ) ^ 2 ≤
      t * ((m : ℝ) / Real.log (m : ℝ)) := by
    calc
      C * (m : ℝ) / Real.log (m : ℝ) ^ 2 ≤
          (t * Real.log (m : ℝ)) * (m : ℝ) / Real.log (m : ℝ) ^ 2 := by
        gcongr
      _ = t * ((m : ℝ) / Real.log (m : ℝ)) := by
        field_simp
  have hmass : trueLogarithmicIntegral (m : ℝ) ≤
      (1 + t) * ((m : ℝ) / Real.log (m : ℝ)) := by
    linarith
  have hproxy : (m : ℝ) / Real.log (m : ℝ) ≤
      ((1 - ε) * (N : ℝ)) / Real.log (m : ℝ) :=
    div_le_div_of_nonneg_right hmupper.le hlogm.le
  have hlogRatio : ((1 - ε) * (N : ℝ)) / Real.log (m : ℝ) ≤
      (1 + t) * ((1 - ε) * ((N : ℝ) / Real.log (N : ℝ))) := by
    apply (div_le_iff₀ hlogm).mpr
    have hh := mul_le_mul_of_nonneg_left hlogTransport
      (show 0 ≤ (1 - ε) * (N : ℝ) / Real.log (N : ℝ) by positivity)
    convert hh using 1 <;> field_simp
  have hcoef : (1 + t) ^ 2 * (1 - ε) ≤ 1 - ε + η := by
    have htSq : t ^ 2 ≤ t := by nlinarith
    have herror : 0 ≤ 2 * t + t ^ 2 := by positivity
    have hh := mul_le_mul_of_nonneg_right (show 1 - ε ≤ 1 by linarith) herror
    nlinarith
  calc
    trueLogarithmicIntegral (goldbachS1Endpoint N ε)
      ≤ (1 + t) * ((m : ℝ) / Real.log (m : ℝ)) := hmass
    _ ≤ (1 + t) * ((1 + t) * ((1 - ε) * ((N : ℝ) / Real.log (N : ℝ)))) :=
      mul_le_mul_of_nonneg_left (hproxy.trans hlogRatio) (by positivity)
    _ = ((1 + t) ^ 2 * (1 - ε)) * ((N : ℝ) / Real.log (N : ℝ)) := by ring
    _ ≤ (1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)

/-- Conditioning the carrier does not change either `nu` or `prodPrimes`. -/
theorem goldbachS3BoundingSieve_sieveProduct_eq_S1
    (N : ℕ) (hEven : Even N) (ε z : ℝ) (p : ℕ) :
    sieveProductPrimeFactors (goldbachS3BoundingSieve N hEven ε z p) =
      sieveProductPrimeFactors (goldbachS1BoundingSieve N hEven ε z) := by
  rfl

/-- The strict S3 Li prefactor times the actual Euler product at `N^(4/53)`,
with a fully paid additive budget on the genuine Liu singular-series scale. -/
theorem goldbachS3_li_mul_eulerProduct_upper (δ ε : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hεu : ε < (2 : ℝ) / 15) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N,
      trueLogarithmicIntegral (goldbachS1Endpoint N ε) *
        sieveProductPrimeFactors
          (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ ((4 : ℝ) / 53))) ≤
        ((1 - ε) * (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant) + δ) *
          SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2 := by
  let K : ℝ := (53 / 2 : ℝ) * Real.exp (-Real.eulerMascheroniConstant)
  have hK : 0 < K := by dsimp [K]; positivity
  let η : ℝ := min (δ / (3 * K)) 1
  have hη : 0 < η := lt_min (by positivity) zero_lt_one
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηδ : 3 * K * η ≤ δ := by
    have hh : η ≤ δ / (3 * K) := min_le_left _ _
    have hmul := (le_div_iff₀ (show 0 < 3 * K by positivity)).mp hh
    nlinarith
  obtain ⟨Nm, hNm4, hmass⟩ :=
    goldbachS3_strictEndpoint_mainMass_upper ε η hε (by linarith) hη
  obtain ⟨Z₀, _hZ₀, hproduct⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries η hη
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ ((4 : ℝ) / 53)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 53)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨Nz, hNz⟩ := eventually_atTop.mp (hpow.eventually (eventually_ge_atTop Z₀))
  refine ⟨max Nm Nz, hNm4.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hNm : Nm ≤ N := (le_max_left _ _).trans hN
  have hNzN : Nz ≤ N := (le_max_right _ _).trans hN
  have hN4 : 4 ≤ N := hNm4.trans hNm
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hC : 0 < SingularSeries.liuSingularSeries N :=
    SingularSeries.liuSingularSeries_pos N
  let V : ℝ := sieveProductPrimeFactors
    (goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ ((4 : ℝ) / 53)))
  have hV0 : 0 ≤ V := by
    let S := goldbachS1BoundingSieve N hEven ε ((N : ℝ) ^ ((4 : ℝ) / 53))
    change 0 ≤ sieveProductPrimeFactors S
    unfold sieveProductPrimeFactors
    apply Finset.prod_nonneg
    intro p hp
    have hpDvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact sub_nonneg.mpr
      (S.nu_lt_one_of_prime p (Nat.prime_of_mem_primeFactors hp) hpDvd).le
  have hVlog := hproduct N hN4 hEven ((N : ℝ) ^ ((4 : ℝ) / 53)) (hNz N hNzN)
  change MertensTheorem.goldbachSieveProduct N
    (Nat.ceil ((N : ℝ) ^ ((4 : ℝ) / 53))) * _ ≤ _ at hVlog
  rw [← goldbachS1BoundingSieve_sieveProduct_eq N hEven ε,
    Real.log_rpow hNpos] at hVlog
  have hV : V ≤ K * (1 + η) * SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
    have hh := (le_div_iff₀ (show 0 < (4 / 53 : ℝ) * Real.log (N : ℝ) by positivity)).mpr hVlog
    calc
      V ≤ 2 * Real.exp (-Real.eulerMascheroniConstant) * (1 + η) *
          SingularSeries.liuSingularSeries N / ((4 / 53 : ℝ) * Real.log (N : ℝ)) := hh
      _ = K * (1 + η) * SingularSeries.liuSingularSeries N / Real.log (N : ℝ) := by
        dsimp [K]
        ring
  have hcoef : (1 - ε + η) * (1 + η) * K ≤ (1 - ε) * K + δ := by
    have hηSq : η ^ 2 ≤ η := by nlinarith
    have hεη : 0 ≤ ε * η := mul_nonneg hε.le hη.le
    have hh : (1 - ε + η) * (1 + η) ≤ 1 - ε + 3 * η := by nlinarith
    have hmul := mul_le_mul_of_nonneg_right hh hK.le
    nlinarith
  have hmul := mul_le_mul (hmass N hNm) hV hV0
    (show 0 ≤ (1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ)) by
      have : 0 < 1 - ε + η := by linarith
      positivity)
  calc
    trueLogarithmicIntegral (goldbachS1Endpoint N ε) * V
      ≤ ((1 - ε + η) * ((N : ℝ) / Real.log (N : ℝ))) *
          (K * (1 + η) * SingularSeries.liuSingularSeries N / Real.log (N : ℝ)) := hmul
    _ = ((1 - ε + η) * (1 + η) * K) *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) := by ring
    _ ≤ ((1 - ε) * K + δ) *
        (SingularSeries.liuSingularSeries N * (N : ℝ) / Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by dsimp [K]; ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig