import WR2GammaHighPairGeometry
import Wu18938Campaign.M4.Gamma9Geometric

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve WuPaper.R2GammaHigh Finset
open scoped Classical

theorem gamma9_eq_omega3 {N : ℕ} {δ : ℝ} (j : Fin 3)
    (hN : 2 ≤ N) (hd : 0 < δ) (hh : δ ≤ 1 / 100) :
    gamma j N δ 9 =
      wuOmega3Sum N δ (Wu04RemainingCore.row j).kappa3
        (Wu04RemainingCore.row j).kappa1 (windows j N) := by
  exact gamma9_eq_omega3_of_local_level (windows j N) (Wu04RemainingCore.row j)
    (row_analytic j).mother (fun d hdm => (support_local j hN hd hh hdm).2.2.2.le)

end Wu18938Campaign.M4
