import WR2OmegaHighPrime
import WR2OmegaHighMother

noncomputable section
namespace WuPaper.R2OmegaHigh
open Wu2008DoubleSieve WuSource.SrcSingle
open Finset Real Filter
open scoped Classical Topology Interval BigOperators

def fixedCoefficient (j : Fin 4) (δ : ℝ) : ℝ :=
  4 * (1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))) * outerIntegral j δ

theorem theta_exact {N : ℕ} (j : Fin 4) (δ : ℝ) (hN : 2 ≤ N) (he : Even N) :
    theta j N δ = 4 * HighSix.liRatio N * subTwoMain j N δ * truncatedSixthMassScale N := by
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  change boxTheta N ((N : ℝ) ^ (1 / 2 - δ)) (fun _ : Fin 1 => psiPrimes (index j) N) = _
  rw [SingleUpperNormalization.theta_single_exact (δ := δ) hN (psiPrimes (index j) N) (by
    intro p hp
    have hpp := (mem_primeWindow.mp hp).1
    have hcop := (mem_primeWindow.mp hp).2.1
    have hp2 : 2 < p := by
      have hdiv : 2 ∣ N := even_iff_two_dvd.mp he
      have hpne : p ≠ 2 := by
        intro h; subst p
        exact hpp.coprime_iff_not_dvd.mp hcop hdiv
      have := hpp.two_le
      omega
    exact ⟨hpp, hp2, hcop⟩)]
  have hs : (∑ p ∈ psiPrimes (index j) N,
      1 / (((p : ℝ) - 2) * ((1 / 2 - δ) - log p / log N))) = subTwoMain j N δ := by
    apply sum_congr rfl
    intro p _
    simp only [HighSix.primeWeight, div_eq_mul_inv, mul_inv_rev, one_mul]
  rw [hs]
  unfold HighSix.liRatio truncatedSixthMassScale
  field_simp

theorem theta_integral_error (j : Fin 4) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      |theta j N δ - 4 * outerIntegral j δ * truncatedSixthMassScale N| ≤
        ε * truncatedSixthMassScale N := by
  let e := ε / (16 * (|outerIntegral j δ| + 1))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨T0, hT04, hq⟩ := subTwo_integral hd.le hh he
  obtain ⟨T1, _, hl⟩ := HighSix.trueLi_relative he
  obtain ⟨T2, _, hl1⟩ := HighSix.trueLi_relative (show (0 : ℝ) < 1 by norm_num)
  refine ⟨max T0 (max T1 T2), hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := by omega
  have hscale := scale_nonneg hN2
  have hq' := hq N (by omega) j
  have hl' := hl N (by omega)
  have hl1' := hl1 N (by omega)
  have hr : |HighSix.liRatio N| ≤ 2 :=
    abs_le.mpr ⟨by linarith [(abs_le.mp hl1').1], by linarith [(abs_le.mp hl1').2]⟩
  have hb : |4 * HighSix.liRatio N * subTwoMain j N δ - 4 * outerIntegral j δ| ≤ ε := by
    rw [show 4 * HighSix.liRatio N * subTwoMain j N δ - 4 * outerIntegral j δ =
      4 * HighSix.liRatio N * (subTwoMain j N δ - outerIntegral j δ) +
        4 * outerIntegral j δ * (HighSix.liRatio N - 1) by ring]
    apply (abs_add_le _ _).trans
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    have ha := mul_le_mul (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 4)) hq'
      (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 * 2)
    have hc := mul_le_mul_of_nonneg_left hl' (show 0 ≤ 4 * |outerIntegral j δ| by positivity)
    have heq : 16 * (|outerIntegral j δ| + 1) * e = ε := by dsimp [e]; field_simp
    have hn := mul_nonneg (abs_nonneg (outerIntegral j δ)) he.le
    nlinarith only [ha, hc, heq, hn, he.le]
  rw [theta_exact j δ hN2 hEven, ← sub_mul, abs_mul, abs_of_nonneg hscale]
  exact mul_le_mul_of_nonneg_right hb hscale

theorem raw_fixed_integral_upper (j : Fin 4) {δ ε : ℝ}
    (hd : 0 < δ) (hh : δ ≤ 1 / 100) (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      sevenRawSource N δ (index j) ≤
        (fixedCoefficient j δ + ε) * truncatedSixthMassScale N := by
  let c := 1 - firstFunctionalGainPsi δ (psiNode (index j)) (psiTop (index j))
  let e := ε / (2 * (|c| + 1))
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨T0, hT04, hr⟩ := raw_mother_upper hd hh (half_pos heps)
  obtain ⟨T1, _, ht⟩ := theta_integral_error j hd hh he
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN hEven
  have hN2 : 2 ≤ N := by omega
  have hraw := hr N (by omega) hEven j
  have htheta := ht N (by omega) hEven
  have hbudget : |c| * e ≤ ε / 2 := by
    have heq : 2 * (|c| + 1) * e = ε := by dsimp [e]; field_simp
    nlinarith [he.le]
  have hc : c * (theta j N δ - 4 * outerIntegral j δ * truncatedSixthMassScale N) ≤
      (ε / 2) * truncatedSixthMassScale N := by
    calc
      _ ≤ |c * (theta j N δ - 4 * outerIntegral j δ * truncatedSixthMassScale N)| := le_abs_self _
      _ = |c| * |theta j N δ - 4 * outerIntegral j δ * truncatedSixthMassScale N| := abs_mul _ _
      _ ≤ |c| * (e * truncatedSixthMassScale N) :=
        mul_le_mul_of_nonneg_left htheta (abs_nonneg _)
      _ = (|c| * e) * truncatedSixthMassScale N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hbudget (scale_nonneg hN2)
  change sevenRawSource N δ (index j) ≤ c * theta j N δ + _ at hraw
  change sevenRawSource N δ (index j) ≤ (4 * c * outerIntegral j δ + ε) * _
  nlinarith only [hraw, hc]

#check @WuPaper.R2OmegaHigh.fixedCoefficient
#check @WuPaper.R2OmegaHigh.theta_exact
#check @WuPaper.R2OmegaHigh.theta_integral_error
#check @WuPaper.R2OmegaHigh.raw_fixed_integral_upper
#print axioms WuPaper.R2OmegaHigh.fixedCoefficient
#print axioms WuPaper.R2OmegaHigh.theta_exact
#print axioms WuPaper.R2OmegaHigh.theta_integral_error
#print axioms WuPaper.R2OmegaHigh.raw_fixed_integral_upper
end WuPaper.R2OmegaHigh
