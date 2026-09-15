import Wu18938Campaign.M4.Gamma9Consumer
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalZeroWidthFinite

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh WuSource.SrcSingle WuPaper.R2PsiCosts Finset
open scoped Classical

theorem original_gamma_zero_width (j : Fin 3) (hj : j ≠ 0) (N : ℕ) (δ : ℝ) {i : ℕ}
    (hi : i ∈ ({12, 15, 17, 18, 19, 20, 21} : Finset ℕ)) :
    gamma j N δ i = 0 := by
  have he : (Wu04RemainingCore.row j).kappa3 = (Wu04RemainingCore.row j).s := by
    fin_cases j
    · exact False.elim (hj rfl)
    · rfl
    · rfl
  unfold gamma secondFunctionalMotherGammaSum
  apply sum_eq_zero
  intro d _
  rw [he]
  have hz (cs : List ℕ) (hcs : 3 ∈ cs) :
      secondFunctionalMotherPrefixTerm N d N
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).S)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa1)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).kappa2)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s)
        (wuLocalCutoff N δ d (Wu04RemainingCore.row j).s) cs = 0 :=
    SecondFunctionalZeroWidth.prefix_zero N d N _ _ _ _ cs hcs
  simp only [mem_insert, mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [secondFunctionalMotherGamma, secondFunctionalMotherGammaWords,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero] <;>
    rw [hz _ (by simp), mul_zero]

def unpaidFive (j : Fin 3) (N : ℕ) (δ : ℝ) : ℝ :=
  ∑ i ∈ ({10, 11, 13, 14, 16} : Finset ℕ), gamma j N δ i

theorem unpaidTwelve_eq_five (j : Fin 3) (hj : j ≠ 0) (N : ℕ) (δ : ℝ) :
    unpaidTwelve j N δ = unpaidFive j N δ := by
  have h12 := original_gamma_zero_width j hj N δ (i := 12) (by decide)
  have h15 := original_gamma_zero_width j hj N δ (i := 15) (by decide)
  have h17 := original_gamma_zero_width j hj N δ (i := 17) (by decide)
  have h18 := original_gamma_zero_width j hj N δ (i := 18) (by decide)
  have h19 := original_gamma_zero_width j hj N δ (i := 19) (by decide)
  have h20 := original_gamma_zero_width j hj N δ (i := 20) (by decide)
  have h21 := original_gamma_zero_width j hj N δ (i := 21) (by decide)
  norm_num [unpaidTwelve, unpaidFive, Finset.sum_Icc_succ_top,
    h12, h15, h17, h18, h19, h20, h21]
  ring

theorem actual_count_five_pending {ε : ℝ} (heps : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 100 ∧ ∀ δ : ℝ, 0 < δ → δ < r →
      ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N → ∀ j : Fin 3, j ≠ 0 →
      psiCount (j.castAdd 4) N ≤
        (8 * psiLogWeight (j.castAdd 4) *
          (1 - classicalGain j + (2 / 5) * I9 (Wu04RemainingCore.row j)) + ε) *
            truncatedSixthMassScale N + unpaidFive j N δ / 5 := by
  obtain ⟨r, hr, hrhi, hb⟩ := actual_count_twelve_pending heps
  refine ⟨r, hr, hrhi, ?_⟩
  intro δ hd hdr
  obtain ⟨T, hT, hc⟩ := hb δ hd hdr
  refine ⟨T, hT, ?_⟩
  intro N hN hEven j hj
  simpa only [unpaidTwelve_eq_five j hj] using hc N hN hEven j

end Wu18938Campaign.M4
