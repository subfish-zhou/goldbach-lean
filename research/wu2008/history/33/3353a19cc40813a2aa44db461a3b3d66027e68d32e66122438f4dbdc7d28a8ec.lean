import RMapMDebitSubstitution

noncomputable section
open Real Set MeasureTheory Wu2008DoubleSieve
open scoped Interval

namespace WuPaper.RMapMDebit

theorem C8_eq_small_large :
    C8 = 8 * U8CanonicalMother.I + 8 * U8MotherInsertion.largeIntegral := by
  rw [C8_eq_existing]
  unfold Wu08TerminalAlignment.eighthMain
  rw [U8MotherInsertion.J8_split, U8CanonicalMother.L_eq_oldSmallIntegral]
  ring

theorem physical_eighth_original_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((SeventhEighth.physicalT8 N).card : ℝ) ≤ (C8 + ε) * U8CanonicalMother.M N := by
  obtain ⟨Ts, hs⟩ :=
    OriginalU8.Weighted.physicalSmall_original_integral (ε / 2) (half_pos hε)
  obtain ⟨Tl, hTl, hl⟩ := U8MotherInsertion.large_integral_upper (half_pos hε)
  refine ⟨max Ts Tl, hTl.trans (le_max_right _ _), ?_⟩
  intro N hN he
  have hNs := (le_max_left Ts Tl).trans hN
  have hNl := (le_max_right Ts Tl).trans hN
  have hpos : 0 < N := by have := hTl.trans hNl; omega
  have hsN := hs N hNs he
  have hlN := hl N hNl he
  have hsM : ((U8MotherInsertion.small N).card : ℝ) ≤
      (8 * U8CanonicalMother.I + ε / 2) * U8CanonicalMother.M N := by
    rw [U8CanonicalMother.small_eq_physicalSmall, U8CanonicalMother.scale_eq_liu hpos]
    convert hsN using 1
    ring
  have hlM : ((U8MotherInsertion.large N).card : ℝ) ≤
      (8 * U8MotherInsertion.largeIntegral + ε / 2) * U8CanonicalMother.M N := by
    convert hlN using 1
    dsimp [U8CanonicalMother.M]
    ring
  rw [U8MotherInsertion.physicalT8_card_split, Nat.cast_add, C8_eq_small_large]
  linarith only [hsM, hlM]

theorem physical_seventh_original_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ((SeventhEighth.physicalT7 N).card : ℝ) ≤ (C7 + ε) * U8CanonicalMother.M N := by
  obtain ⟨T, hT, h⟩ := SeventhEighth.seventh_eighth_physical_classical_upper hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  rw [C7_eq_existing]
  convert (h N hN he).1 using 1
  dsimp [Wu08TerminalAlignment.seventhMain, U8CanonicalMother.M]
  ring

theorem ninth_original_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (variableS3Main N (ninthProfileW N) (ninthProfileU N) : ℝ) ≤
        (C9 + ε) * U8CanonicalMother.M N := by
  obtain ⟨T, hT, h⟩ := variableS3Main_upper_F9 hε
  refine ⟨T, hT, ?_⟩
  intro N hN he
  rw [C9_eq_existing]
  convert h N hN he using 1
  dsimp [Wu08TerminalAlignment.ninthMain, U8CanonicalMother.M]
  ring

theorem switching_errors_paid {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (lowerS2 N (SeventhEighth.w N) (SeventhEighth.u N) : ℝ) ≤
        ((SeventhEighth.physicalT7 N).card : ℝ) + ε * U8CanonicalMother.M N ∧
      (lowerS3 N (SeventhEighth.z N) (SeventhEighth.v N) : ℝ) ≤
        ((SeventhEighth.physicalT8 N).card : ℝ) + ε * U8CanonicalMother.M N := by
  have hC : 0 < wuSingularSeries 1 := wuSingularSeries_pos 1 (by norm_num)
  obtain ⟨Tc, hc⟩ := SeventhEighth.exists_fixed_cutoff
  obtain ⟨Tp, hTp, hp⟩ := ninth_power_log_error_budget 0
    (by norm_num [alpha, SeventhEighth.alpha] : 0 < 5 / alpha^2)
    parameters.1 (show 0 < ε * wuSingularSeries 1 by positivity)
  refine ⟨max Tc Tp, hTp.trans (le_max_right _ _), ?_⟩
  intro N hN he
  have hNc := (le_max_left Tc Tp).trans hN
  have hNp := (le_max_right Tc Tp).trans hN
  have h512 := hTp.trans hNp
  have hNpos : 0 < N := by omega
  have h7 := SeventhEighth.lowerS2_fixed_le_physicalT7 (by omega : 4 ≤ N) he (hc N hNc)
  have h8 := SeventhEighth.lowerS3_fixed_le_physicalT8 (by omega : 4 ≤ N) he (hc N hNc)
  have herr := hp N hNp
  have heq : (5 / alpha^2) * (N : ℝ) ^ (1 - alpha) =
      (5 / alpha^2) * N * log N ^ (0 : ℕ) / (N : ℝ) ^ alpha := by
    rw [rpow_sub (by positivity : (0 : ℝ) < N), rpow_one, pow_zero]
    ring
  rw [← heq] at herr
  have hClow := wuSingularSeries_le_of_dvd (by norm_num : 0 < (1 : ℕ)) hNpos (one_dvd N)
  have hscale := mul_le_mul_of_nonneg_left hClow
    (show 0 ≤ ε * N / log N ^ (2 : ℕ) by positivity)
  have hpaid : ε * wuSingularSeries 1 * N / log N ^ (2 : ℕ) ≤
      ε * U8CanonicalMother.M N := by
    dsimp [U8CanonicalMother.M]
    nlinarith only [hscale]
  exact ⟨by linarith only [h7, herr, hpaid], by linarith only [h8, herr, hpaid]⟩

theorem original_three_count_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (lowerS2 N (SeventhEighth.w N) (SeventhEighth.u N) : ℝ) ≤
        (C7 + ε) * U8CanonicalMother.M N ∧
      (lowerS3 N (SeventhEighth.z N) (SeventhEighth.v N) : ℝ) ≤
        (C8 + ε) * U8CanonicalMother.M N ∧
      (variableS3Main N (ninthProfileW N) (ninthProfileU N) : ℝ) ≤
        (C9 + ε) * U8CanonicalMother.M N := by
  obtain ⟨T7, hT7, h7⟩ := physical_seventh_original_upper (half_pos hε)
  obtain ⟨T8, _, h8⟩ := physical_eighth_original_upper (half_pos hε)
  obtain ⟨T9, _, h9⟩ := ninth_original_upper hε
  obtain ⟨Te, _, herr⟩ := switching_errors_paid (half_pos hε)
  refine ⟨max T7 (max T8 (max T9 Te)), hT7.trans (le_max_left _ _), ?_⟩
  intro N hN he
  have hN7 := (le_max_left T7 (max T8 (max T9 Te))).trans hN
  have hN89e := (le_max_right T7 (max T8 (max T9 Te))).trans hN
  have hN8 := (le_max_left T8 (max T9 Te)).trans hN89e
  have hN9e := (le_max_right T8 (max T9 Te)).trans hN89e
  have hN9 := (le_max_left T9 Te).trans hN9e
  have hNe := (le_max_right T9 Te).trans hN9e
  obtain ⟨he7, he8⟩ := herr N hNe he
  exact ⟨by linarith only [he7, h7 N hN7 he],
    by linarith only [he8, h8 N hN8 he], h9 N hN9 he⟩

theorem weighted_original_count_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℕ, 512 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      (2 * (lowerS2 N (SeventhEighth.w N) (SeventhEighth.u N) : ℝ) +
        (lowerS3 N (SeventhEighth.z N) (SeventhEighth.v N) : ℝ) +
        (variableS3Main N (ninthProfileW N) (ninthProfileU N) : ℝ)) ≤
          (2 * C7 + C8 + C9 + ε) * U8CanonicalMother.M N := by
  obtain ⟨T, hT, h⟩ := original_three_count_upper (show 0 < ε / 4 by positivity)
  refine ⟨T, hT, ?_⟩
  intro N hN he
  obtain ⟨h7, h8, h9⟩ := h N hN he
  linarith only [h7, h8, h9]

end WuPaper.RMapMDebit
