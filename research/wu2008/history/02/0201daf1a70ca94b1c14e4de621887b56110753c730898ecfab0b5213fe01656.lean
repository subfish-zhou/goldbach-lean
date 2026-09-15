import RMapMMatrixGeometry

noncomputable section
namespace WuPaper.RMapMMatrix
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Interval

theorem original_kappa2_lt_three (i : Fin 4) : (coupledRow i).kappa2 < 3 := by
  fin_cases i <;>
    norm_num [coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem original_reciprocal_gap (i : Fin 4) : 1 / 3 < 1 / (coupledRow i).kappa2 := by
  fin_cases i <;>
    norm_num [coupledRow, SecondFunctionalPositive.parameters,
      SecondFunctionalParameters.row1, SecondFunctionalParameters.row2,
      SecondFunctionalParameters.row3, SecondFunctionalParameters.row4]

theorem original_open_triangle_nonempty (i : Fin 4) :
    ∃ t u : ℝ, 1 / 3 < t ∧ t < u ∧ u < 1 / (coupledRow i).kappa2 := by
  obtain ⟨u, hu, huk⟩ := exists_between (original_reciprocal_gap i)
  obtain ⟨t, ht, htu⟩ := exists_between hu
  exact ⟨t, u, ht, htu, huk⟩

theorem original_open_triangle_excluded (i : Fin 4) {t u : ℝ}
    (ht : 1 / 3 < t) (htu : t < u) (hu : u < 1 / (coupledRow i).kappa2) :
    MotherPair.PairRegion (coupledRow i) .gammaFive t u ∧
      (coupledRow i).S * (1 - t - u) ∈ Icc 1 3 ∧
      ¬ gamma5GainLegal t u ∧
      (t, u) ∉ MotherPair.gainRegion (coupledRow i) .gammaFive := by
  let p := coupledRow i
  have hp := original_four_rows_qualified i
  have hS : 3 ≤ p.S := hp.2.2.1
  have hS0 : 0 < p.S := by linarith
  have hinv : 1 / p.S ≤ 1 / 3 :=
    one_div_le_one_div_of_le (by norm_num) hS
  have htS : 1 / p.S ≤ t := hinv.trans ht.le
  have htk : t ≤ 1 / p.kappa2 := htu.le.trans hu.le
  have hb := source66_rectangle_bounds hS0 ⟨htS, htk⟩ ⟨htu.le, hu.le⟩
  have ha6 : 1 ≤ alpha6 p := (hp.2.2.2.2.2.2.2.2.2.1 5).1
  have ha2 : alpha2 p ≤ 3 := (hp.2.2.2.2.2.2.2.2.2.1 1).2
  have hlegal : ¬ gamma5GainLegal t u := by
    intro h
    have h' := h.2
    linarith
  refine ⟨⟨htS, htk, htu.le, hu.le⟩, ⟨ha6.trans hb.1, hb.2.trans ha2⟩,
    hlegal, ?_⟩
  exact fun h => hlegal h.2

theorem original_open_triangle_mask_zero (i : Fin 4) (δ : ℝ) {t u : ℝ}
    (ht : 1 / 3 < t) (htu : t < u) (hu : u < 1 / (coupledRow i).kappa2) :
    MotherPair.gainLiteral (coupledRow i) .gammaFive δ t u = 0 := by
  exact if_neg (original_open_triangle_excluded i ht htu hu).2.2.1

theorem original_domain_not_gainRegion (i : Fin 4) :
    {v : ℝ × ℝ | MotherPair.PairRegion (coupledRow i) .gammaFive v.1 v.2} ≠
      MotherPair.gainRegion (coupledRow i) .gammaFive := by
  obtain ⟨t, u, ht, htu, hu⟩ := original_open_triangle_nonempty i
  have h := original_open_triangle_excluded i ht htu hu
  intro he
  apply h.2.2.2
  rw [← he]
  exact h.1

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.RMapMMatrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.RMapMMatrix
