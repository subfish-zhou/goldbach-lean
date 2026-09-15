import Wu18938Campaign.M4.HighNonunitDensity

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh WuSource.SrcSingle Finset Real
open scoped Classical

private theorem positive_card_le_real {P : Finset ℕ} {B : ℝ} (hB : 0 ≤ B)
    (hP : ∀ p ∈ P, 0 < p ∧ (p : ℝ) ≤ B) : (P.card : ℝ) ≤ B := by
  have hs : P ⊆ Icc 1 ⌊B⌋₊ := by
    intro p hp
    exact mem_Icc.mpr ⟨(hP p hp).1, (Nat.le_floor_iff hB).mpr (hP p hp).2⟩
  have hc : P.card ≤ ⌊B⌋₊ := by simpa using card_le_card hs
  exact (Nat.cast_le.mpr hc).trans (Nat.floor_le hB)

theorem mother_tuple_card_le (P : Finset ℕ) (n : ℕ) :
    (secondFunctionalMotherTuples P n).card ≤ P.card ^ n := by
  induction n generalizing P with
  | zero => simp [secondFunctionalMotherTuples]
  | succ n ih =>
    rw [secondFunctionalMotherTuples]
    calc
      _ ≤ ∑ p ∈ P,
          ((secondFunctionalMotherTuples (P.filter (fun q => p < q)) n).image (List.cons p)).card :=
        card_biUnion_le
      _ ≤ ∑ _p ∈ P, P.card ^ n := sum_le_sum (fun p _ =>
        card_image_le.trans ((ih _).trans
          (pow_le_pow_left₀ (Nat.zero_le _) (card_le_card (filter_subset _ _)) n)))
      _ = P.card ^ (n + 1) := by simp [pow_succ, mul_comm]

theorem unit_prefix_le_tuple_power (N d : ℕ) (a b c e f : ℝ) (cs : List ℕ) :
    FourPrimeUnit.prefixTerm true N d a b c e f cs ≤
      ((primeWindow N a f).card : ℝ) ^ cs.length := by
  have hunit (l : List ℕ) : (secondFunctionalFourPrimeUnitCarrier N d l).card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact secondFunctionalFourPrimeUnit_unique hx hy
      (FourPrimeUnit.carrier_le hx) (FourPrimeUnit.carrier_le hy)
  calc
    _ ≤ ∑ _l ∈ secondFunctionalMotherTuples (primeWindow N a f) cs.length, (1 : ℝ) := by
      apply sum_le_sum
      intro l _
      change (if l.map (secondFunctionalMotherColour b c e) = cs then
        ((secondFunctionalFourPrimeUnitCarrier N d l).card : ℝ) else 0) ≤ 1
      split_ifs
      · exact_mod_cast hunit l
      · norm_num
    _ = ((secondFunctionalMotherTuples (primeWindow N a f) cs.length).card : ℝ) := by simp
    _ ≤ _ := by exact_mod_cast mother_tuple_card_le (primeWindow N a f) cs.length

theorem original_unit_word_bound {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) (cs : List ℕ) (hlen : cs.length ≤ 6) :
    FourPrimeUnit.source N (windows j N)
      (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
      (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
      (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2)
      (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
      (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) cs ≤
        (N : ℝ) ^ (3127 / 3981 : ℝ) := by
  let B := (N : ℝ) ^ (100 / 1327 : ℝ)
  have hNpos : (0 : ℝ) < N := by positivity
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hB1 : 1 ≤ B := one_le_rpow hN1 (by norm_num)
  have houter : ((psiPrimes (j.castAdd 4) N).card : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by
    apply positive_card_le_real (rpow_nonneg hNpos.le _)
    intro d hdm
    have hm := mem_primeWindow.mp hdm
    exact ⟨hm.1.pos, hm.2.2.2.le.trans (rpow_le_rpow_of_exponent_le hN1
      (seven_parameter_geometry (j.castAdd 4)).2.2.2.2.2.2.2.2.2.1)⟩
  have hinner (d : ℕ) (hdm : d ∈ psiPrimes (j.castAdd 4) N) :
      FourPrimeUnit.prefixTerm true N d
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) cs ≤ B ^ 6 := by
    have hc : ((primeWindow N
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)).card : ℝ) ≤ B := by
      apply positive_card_le_real (le_trans zero_le_one hB1)
      intro q hq
      have h := original_label_bounds j hN hd hh hdm hq
      exact ⟨h.1, h.2.2⟩
    exact (unit_prefix_le_tuple_power N d _ _ _ _ _ cs).trans
      ((pow_le_pow_left₀ (Nat.cast_nonneg _) hc _).trans (pow_le_pow_right₀ hB1 hlen))
  unfold FourPrimeUnit.source
  rw [support_eq]
  calc
    _ ≤ ∑ _d ∈ psiPrimes (j.castAdd 4) N, B ^ 6 := by
      apply sum_le_sum
      intro d hdm
      have hc : convolutionCoeff (windows j N) d = 1 := by
        exact (SingleUpperCounts.single_coeff (psiPrimes (j.castAdd 4) N) d).trans
          (if_pos hdm)
      rw [hc, Nat.cast_one, one_mul]
      exact hinner d hdm
    _ = ((psiPrimes (j.castAdd 4) N).card : ℝ) * B ^ 6 := by simp [mul_comm]
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * B ^ 6 := mul_le_mul_of_nonneg_right houter (by positivity)
    _ = (N : ℝ) ^ (3127 / 3981 : ℝ) := by
      dsimp only [B]
      rw [← rpow_natCast, ← rpow_mul hNpos.le, ← rpow_add hNpos]
      norm_num

theorem original_unit_word_paid {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 → ∀ N : ℕ, T ≤ N →
      ∀ j : Fin 3, ∀ cs : List ℕ, cs.length ≤ 6 →
      FourPrimeUnit.source N (windows j N)
        (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
        (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
        (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2)
        (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa3)
        (fun d => wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) cs ≤
          ε * truncatedSixthMassScale N := by
  obtain ⟨T, hT, hp⟩ := HighSix.Omega3Upper.power_log_scale_paid 0 heps
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) < 854 / 3981 by norm_num)
  refine ⟨T, hT, ?_⟩
  intro δ hd hh N hN j cs hlen
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  calc
    _ ≤ (N : ℝ) ^ (3127 / 3981 : ℝ) := original_unit_word_bound j (by omega) hd hh cs hlen
    _ = (N : ℝ) ^ (1 - (854 / 3981 : ℝ)) := by norm_num
    _ = (N : ℝ) ^ (1 : ℝ) / (N : ℝ) ^ (854 / 3981 : ℝ) := rpow_sub hNpos _ _
    _ = 1 * N * log N ^ (0 : ℕ) / (N : ℝ) ^ (854 / 3981 : ℝ) := by rw [rpow_one]; ring
    _ ≤ _ := hp N hN

theorem original_high_gamma_nonunit_density {δ ρ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (hrho : 0 < ρ) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, ∀ high : Bool,
      gamma j N δ (if high then 21 else 20) ≤
        (originalNonunitFamily j N δ high).coprimePart.mass *
          (HighO3.densityFactor δ ρ * wuSingularSeries N / log N) +
            ε * truncatedSixthMassScale N := by
  obtain ⟨T0, hT04, hmain⟩ := original_high_gamma_density hd hh hrho (half_pos heps)
  obtain ⟨T1, _, hunit⟩ := original_unit_word_paid (half_pos heps)
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven j high
  have hm := hmain N (by omega) hEven j high
  have hu := hunit δ hd hh N (by omega) j (HighNonunit.word high)
    (by cases high <;> simp [HighNonunit.word, HighUnitSource.word20, HighUnitSource.word21])
  change HighNonunit.actualUnit N δ (Wu04RemainingCore.row j) (windows j N) high ≤
    (ε / 2) * truncatedSixthMassScale N at hu
  linarith only [hm, hu]

end Wu18938Campaign.M4
