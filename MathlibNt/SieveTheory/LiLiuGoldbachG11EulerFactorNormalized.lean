import MathlibNt.SieveTheory.LiLiuGoldbachG11SieveParameters
import MathlibNt.SieveTheory.LiLiuGoldbachG11EulerProduct

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
noncomputable section

/-- Actual uniform square-root-level Euler/JR factor. This does not assert the
paper's stronger low-band coefficient. -/
theorem goldbachG11EulerFactor_normalized (B τ : ℝ)
    (hB : 0 ≤ B) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ _hEven : Even N,
      (Real.exp Real.eulerMascheroniConstant + τ*Real.exp Real.eulerMascheroniConstant)*
        goldbachB10PrimeProduct N (goldbachG11SieveCutoff B N) ≤
      8*(1+τ)^3*SingularSeries.liuSingularSeries N/Real.log (N : ℝ) := by
  obtain ⟨Z₀,_,hprod⟩ := goldbachB10PrimeProduct_log_le_liuSingularSeries τ hτ
  obtain ⟨N₀,hN₀,hgeom⟩ := goldbachG11SieveParameters_eventually B Z₀ τ hB hτ hτ1
  refine ⟨N₀,hN₀,?_⟩
  intro N hN hEven
  have hN4 := hN₀.trans hN
  let Z := goldbachG11SieveCutoff B N
  obtain ⟨hZbig,_,_,_,_,hlogZ,hratio⟩ := hgeom N hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hV : goldbachB10PrimeProduct N Z ≤
      2*Real.exp (-Real.eulerMascheroniConstant)*(1+τ)*SingularSeries.liuSingularSeries N/Real.log Z :=
    (le_div_iff₀ hlogZ).mpr (hprod N hN4 hEven Z ((le_max_right _ _).trans hZbig))
  have hInv : 1/Real.log Z ≤ 4*(1+τ)/Real.log (N : ℝ) := by
    calc
      _ = (Real.log (N : ℝ)/Real.log Z)/Real.log (N : ℝ) := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hratio hlogN.le
  have hCoeff : 2*(1+τ)^2/Real.log Z ≤ 8*(1+τ)^3/Real.log (N : ℝ) := by
    calc
      _ = 2*(1+τ)^2*(1/Real.log Z) := by ring
      _ ≤ 2*(1+τ)^2*(4*(1+τ)/Real.log (N : ℝ)) :=
        mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = _ := by ring
  have hExp : Real.exp Real.eulerMascheroniConstant * Real.exp (-Real.eulerMascheroniConstant) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hf : Real.exp Real.eulerMascheroniConstant+τ*Real.exp Real.eulerMascheroniConstant =
      Real.exp Real.eulerMascheroniConstant*(1+τ) := by ring
  rw [hf]
  change Real.exp Real.eulerMascheroniConstant*(1+τ)*goldbachB10PrimeProduct N Z ≤ _
  calc
    _ ≤ Real.exp Real.eulerMascheroniConstant*(1+τ)*
        (2*Real.exp (-Real.eulerMascheroniConstant)*(1+τ)*SingularSeries.liuSingularSeries N/Real.log Z) :=
      mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (Real.exp Real.eulerMascheroniConstant*Real.exp (-Real.eulerMascheroniConstant))*
        (SingularSeries.liuSingularSeries N*(2*(1+τ)^2/Real.log Z)) := by ring
    _ = SingularSeries.liuSingularSeries N*(2*(1+τ)^2/Real.log Z) := by rw [hExp,one_mul]
    _ ≤ SingularSeries.liuSingularSeries N*(8*(1+τ)^3/Real.log (N : ℝ)) :=
      mul_le_mul_of_nonneg_left hCoeff (SingularSeries.liuSingularSeries_pos N).le
    _ = _ := by ring

end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig