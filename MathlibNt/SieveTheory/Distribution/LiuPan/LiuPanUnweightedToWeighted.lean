import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanModernWeightTransfer

noncomputable section
open Finset
open scoped BigOperators
namespace MathlibNt.SieveTheory.LiuWeight

private theorem liu_log_add_two_le_two_log {N : ℕ} (hN : 2 ≤ N) :
    Real.log ((N : ℝ) + 2) ≤ 2 * Real.log N := by
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN
  calc
    _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) (by nlinarith)
    _ = _ := by rw [Real.log_pow]; norm_num

/-- Modern Cauchy weight payment for Pan's actual unweighted convolution
specialization. The only analytic premise is `hPan`; κ and B are unchanged.
Nine logarithms pay 9^ω/q and two pay the proved actual pointwise envelope. -/
theorem LiuPanUnweightedTheorem2Specialization.to_corollary230
    (hPan : LiuPanUnweightedTheorem2Specialization) : LiuPanWangDingCorollary230 := by
  obtain ⟨κ, hPan⟩ := hPan
  obtain ⟨C₉, hC₉, hfinite⟩ := exists_liuPanWeightedSum_sq_le_unweighted
  refine ⟨κ, ?_⟩
  intro A hA
  -- The second moment spends nine logarithms on the weight and two on the envelope.
  let U : ℝ := 2 * A + 11
  obtain ⟨K, hK, B, hB, Nsrc, hsrc⟩ := hPan U (by dsimp [U]; linarith)
  let D : ℝ := C₉ * (2 ^ (11 : ℕ) : ℝ) * liuActualEnvelopeConstant κ * K
  let C : ℝ := Real.sqrt D + 1
  have henvC := liuActualEnvelopeConstant_pos κ
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, B, hB, max Nsrc 3, ?_⟩
  intro N hN
  have hsrcN := hsrc N ((le_max_left _ _).trans hN)
  have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hlog1 : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    exact ((Real.lt_log_iff_exp_lt (by exact_mod_cast (by omega : 0 < N))).2
      (he1.trans_le (by exact_mod_cast hN3))).le
  have hlog : 0 < Real.log (N : ℝ) := lt_of_lt_of_le zero_lt_one hlog1
  have hlog2 := liu_log_add_two_le_two_log hN2
  have hlog2nonneg : 0 ≤ Real.log ((N : ℝ) + 2) :=
    Real.log_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg _; linarith)
  have hone : 1 + Real.log (N : ℝ) ≤ 2 * Real.log N := by linarith
  have hfactor : 0 ≤ K * (N : ℝ) / Real.log N ^ U := by positivity
  have hsquare : liuPanWangDingCorollary230Sum κ N B ^ 2 ≤
      (C₉ * Real.log (N + 2) ^ (9 : ℝ)) *
        ((liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2) *
          (K * N / Real.log N ^ U)) := by
    refine (hfinite κ N B hN2 hlog1 hB).trans ?_
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hsrcN (by positivity)) (by positivity)
  have hmajor : liuPanWangDingCorollary230Sum κ N B ^ 2 ≤
      D * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
    calc
      _ ≤ (C₉ * Real.log (N + 2) ^ (9 : ℝ)) *
          ((liuActualEnvelopeConstant κ * N * (1 + Real.log N) ^ 2) *
            (K * N / Real.log N ^ U)) := hsquare
      _ ≤ (C₉ * (2 * Real.log N) ^ (9 : ℝ)) *
          ((liuActualEnvelopeConstant κ * N * (2 * Real.log N) ^ 2) *
            (K * N / Real.log N ^ U)) := by
        have hfirst : C₉ * Real.log ((N : ℝ) + 2) ^ (9 : ℝ) ≤
            C₉ * (2 * Real.log N) ^ (9 : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow hlog2nonneg hlog2 (by norm_num)) hC₉.le
        have hsecond : liuActualEnvelopeConstant κ * (N : ℝ) * (1 + Real.log N) ^ 2 ≤
            liuActualEnvelopeConstant κ * N * (2 * Real.log N) ^ 2 := by
          gcongr
        exact mul_le_mul hfirst (mul_le_mul_of_nonneg_right hsecond hfactor)
          (by positivity) (by positivity)
      _ = D * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
        have hpowU : Real.log N ^ U =
            (Real.log N ^ A) ^ (2 : ℝ) * Real.log N ^ (11 : ℝ) := by
          dsimp [U]
          rw [show 2 * A + 11 = A * 2 + 11 by ring,
            Real.rpow_add hlog, Real.rpow_mul hlog.le]
        rw [hpowU]
        rw [show (Real.log N ^ A) ^ (2 : ℝ) = (Real.log N ^ A) ^ (2 : ℕ) from
          Real.rpow_natCast _ 2]
        rw [show Real.log N ^ (11 : ℝ) = Real.log N ^ (11 : ℕ) from
          Real.rpow_natCast _ 11]
        rw [show (2 * Real.log N) ^ (9 : ℝ) = (2 * Real.log N) ^ (9 : ℕ) from
          Real.rpow_natCast _ 9]
        dsimp [D]
        field_simp [hlog.ne']
  -- Recover the nonnegative sum from its second-moment bound.
  have hleft : 0 ≤ liuPanWangDingCorollary230Sum κ N B := by
    unfold liuPanWangDingCorollary230Sum
    exact sum_nonneg fun q _ => mul_nonneg (by positivity)
      (liuMainPanCoprimeIntervalMaxL_nonneg ..)
  have htarget : 0 ≤ C * (N : ℝ) / Real.log N ^ A := by positivity
  have hDsquare : D ≤ C ^ 2 := by
    dsimp [C]
    nlinarith only [Real.sq_sqrt hD, Real.sqrt_nonneg D]
  apply (sq_le_sq₀ hleft htarget).mp
  calc
    _ ≤ D * ((N : ℝ) / Real.log N ^ A) ^ 2 := hmajor
    _ ≤ C ^ 2 * ((N : ℝ) / Real.log N ^ A) ^ 2 :=
      mul_le_mul_of_nonneg_right hDsquare (sq_nonneg _)
    _ = _ := by ring

end MathlibNt.SieveTheory.LiuWeight