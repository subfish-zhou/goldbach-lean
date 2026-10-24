import WR2XiPieceDomain
import WR2XiClippedPanels

/-! Factorwise logarithm payments on the two original product pieces. -/
noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory Wu2008DoubleSieve MotherPair
open scoped Interval BigOperators

theorem scaled_product_kernel_panel {n : ℕ} {q : Fin n → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hq : ∀ j, 0 < q j ∧ q j ≤ a+1)
    (hi : IntervalIntegrable (fun t => log ((t+1)^n / ∏ j, q j)/(5*t)) volume a b) :
    (b-a) * (productLogLower q a/(5*b)) ≤
      ∫ t in a..b, log ((t+1)^n / ∏ j, q j)/(5*t) := by
  have hp (t : ℝ) (ht : t ∈ Icc a b) :
      productLogLower q a/(5*b) ≤ log ((t+1)^n / ∏ j, q j)/(5*t) := by
    have htpos : 0 < 5*t := by linarith [ht.1]
    exact (div_le_div_of_nonneg_left (productLogLower_nonneg hq) htpos
      (by linarith [ht.2])).trans (div_le_div_of_nonneg_right
        (productLogLower_le (by linarith) ht.1 hq) htpos.le)
  have h := intervalIntegral.integral_mono_on hab
    (intervalIntegrable_const (c := productLogLower q a/(5*b))) hi hp
  simpa only [intervalIntegral.integral_const, smul_eq_mul] using h

theorem original_five_factor_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 0).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 0).2) :
    (b-a) * (productLogLower (xi2Factors (gamma5OriginalRow r)) a/(5*b)) ≤
      ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t 0 := by
  have hs := original_piece_support_bounds r 0
  have hap : 0 < a := by linarith [hs.1]
  have hd := original_piece_domain r 0 ⟨ha, hab.trans hb⟩
  have hq : ∀ j, 0 < xi2Factors (gamma5OriginalRow r) j ∧
      xi2Factors (gamma5OriginalRow r) j ≤ a+1 := hd
  have hi := original_subinterval_integrable r 0 hab ha hb
  have he : (fun t => log ((t+1)^5 / ∏ j, xi2Factors (gamma5OriginalRow r) j)/(5*t)) =
      (fun t => xi2PieceKernel (gamma5OriginalRow r) t 0) := by
    simp only [xi2Factors_prod]
    rfl
  have h := scaled_product_kernel_panel hap hab hq (he.symm ▸ hi)
  rwa [he] at h

def middleFactors (p : SecondFunctionalParameters) : Fin 2 → ℝ := ![p.kappa1-1,p.kappa2-1]

theorem original_two_factor_panel (r : Fin 4) {a b : ℝ} (hab : a ≤ b)
    (ha : (xi2PieceInterval (gamma5OriginalRow r) 4).1 ≤ a)
    (hb : b ≤ (xi2PieceInterval (gamma5OriginalRow r) 4).2) :
    (b-a) * (productLogLower (middleFactors (gamma5OriginalRow r)) a/(5*b)) ≤
      ∫ t in a..b, xi2PieceKernel (gamma5OriginalRow r) t 4 := by
  have hs := original_piece_support_bounds r 4
  have hap : 0 < a := by linarith [hs.1]
  have hd := original_piece_domain r 4 ⟨ha, hab.trans hb⟩
  have hq : ∀ j, 0 < middleFactors (gamma5OriginalRow r) j ∧
      middleFactors (gamma5OriginalRow r) j ≤ a+1 := by
    simpa [middleFactors, Fin.forall_fin_succ, xi2PieceDomain, and_assoc] using hd
  have hi := original_subinterval_integrable r 4 hab ha hb
  have he : (fun t => log ((t+1)^2 / ∏ j, middleFactors (gamma5OriginalRow r) j)/(5*t)) =
      (fun t => xi2PieceKernel (gamma5OriginalRow r) t 4) := by
    simp [middleFactors, Fin.prod_univ_succ, xi2PieceKernel]
  have h := scaled_product_kernel_panel hap hab hq (he.symm ▸ hi)
  rwa [he] at h

end WuPaper.R2Xi
#print axioms WuPaper.R2Xi.original_five_factor_panel
#print axioms WuPaper.R2Xi.original_two_factor_panel
