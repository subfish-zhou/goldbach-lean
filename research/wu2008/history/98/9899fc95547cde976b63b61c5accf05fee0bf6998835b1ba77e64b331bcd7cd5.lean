import R2XiEquation67

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix WuPaper.RMapMSigma
open scoped Interval

theorem strip_fubini_measurable {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {l u : ℝ → ℝ} (hs : MeasurableSet (strip a b l u))
    (hb : ∀ x ∈ Icc a b, c ≤ l x ∧ l x ≤ u x ∧ u x ≤ d)
    {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F (strip a b l u)) :
    (∫ x in a..b, ∫ v in (l x)..(u x), F (x, v)) =
      ∫ v in c..d, ∫ x in a..b,
        (Icc (l x) (u x)).indicator (fun v => F (x, v)) v := by
  let G := (strip a b l u).indicator F
  have hi : Integrable G ((volume.restrict (Icc a b)).prod
      (volume.restrict (Icc c d))) := by
    rw [Measure.prod_restrict]
    exact ((integrable_indicator_iff hs).mpr hF).integrableOn
  have he (x v : ℝ) (hx : x ∈ Icc a b) :
      G (x, v) = (Icc (l x) (u x)).indicator (fun v => F (x, v)) v := by
    by_cases hv : v ∈ Icc (l x) (u x)
    · exact (indicator_of_mem (show (x, v) ∈ strip a b l u from ⟨hx, hv⟩) F).trans
        (indicator_of_mem hv (fun v => F (x, v))).symm
    · exact (indicator_of_notMem (show (x, v) ∉ strip a b l u from fun h => hv h.2) F).trans
        (indicator_of_notMem hv (fun v => F (x, v))).symm
  rw [integral_Icc hab, integral_Icc hcd]
  calc
    _ = ∫ x in Icc a b, ∫ v in Icc c d, G (x, v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro x hx
      have hbx := hb x hx
      dsimp only
      rw [← integral_Icc hcd,
        intervalIntegral.integral_congr (fun v _ => he x v hx),
        indicator_interval_integral hbx.1 hbx.2.1 hbx.2.2]
    _ = ∫ v in Icc c d, ∫ x in Icc a b, G (x, v) := integral_integral_swap hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _
      dsimp only
      rw [integral_Icc hab]
      exact setIntegral_congr_fun measurableSet_Icc (fun x hx => he x v hx)

theorem selected_section_iff {b x v : ℝ} (hx : 0 < x) (hv : 0 < v) :
    v ∈ Icc ((1 - x - b) / x) (1 / x - 2) ↔
      x ∈ Icc ((1 - b) / (v + 1)) (1 / (v + 2)) := by
  have hv1 : 0 < v + 1 := by linarith
  have hv2 : 0 < v + 2 := by linarith
  constructor
  · intro h
    have hl := (div_le_iff₀ hx).mp h.1
    have hu := (le_div_iff₀ hx).mp (show v + 2 ≤ 1 / x by linarith [h.2])
    exact ⟨(div_le_iff₀ hv1).mpr (by nlinarith only [hl]),
      (le_div_iff₀ hv2).mpr (by nlinarith only [hu])⟩
  · intro h
    have hl := (div_le_iff₀ hv1).mp h.1
    have hu := (le_div_iff₀ hv2).mp h.2
    have hu' := (le_div_iff₀ hx).mpr (show (v + 2) * x ≤ 1 by nlinarith only [hu])
    exact ⟨(div_le_iff₀ hx).mpr (by nlinarith only [hl]), by linarith⟩

theorem source68_strip_bounds {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    ∀ x ∈ Icc (1 / p.S) (1 / p.kappa1),
      1 ≤ (1 - x - 1 / p.kappa2) / x ∧
      (1 - x - 1 / p.kappa2) / x ≤ 1 / x - 2 ∧ 1 / x - 2 ≤ 3 := by
  have hb := second_parameter_bounds hp
  have ha := (second_alpha_bounds hp).1
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk1 : 0 < p.kappa1 := by linarith [hb.2.2.2.1]
  have hk2 : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have h21 : p.kappa2 < p.kappa1 := hp.2.2.2.2.2.2.1
  intro x hx
  have hx0 : 0 < x := (one_div_pos.mpr hS).trans_le hx.1
  have hx2 := hx.2.trans (one_div_le_one_div_of_le hk2 h21.le)
  have hl := source68_rectangle_bounds hS hk1 (by linarith : 1 ≤ p.kappa2) hx
    (show (1 / p.kappa2) ∈ Icc x (1 / p.kappa2) from ⟨hx2, le_rfl⟩)
  have hu := source68_rectangle_bounds hS hk1 (by linarith : 1 ≤ p.kappa2) hx
    (show x ∈ Icc x (1 / p.kappa2) from ⟨le_rfl, hx2⟩)
  have he : (1 - x - x) / x = 1 / x - 2 := by field_simp; ring
  rw [he] at hu
  refine ⟨(show 1 ≤ alpha9 p from (ha 8).1).trans hl.1, ?_, hu.2.trans (ha 1).2⟩
  rw [← he]
  exact div_le_div_of_nonneg_right (by linarith) hx0.le

theorem source68_strip_compact {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    IsCompact (strip (1 / p.S) (1 / p.kappa1)
      (fun x => (1 - x - 1 / p.kappa2) / x) (fun x => 1 / x - 2)) := by
  have hS : 0 < p.S := by linarith [(second_parameter_bounds hp).2.1]
  have he : strip (1 / p.S) (1 / p.kappa1)
      (fun x => (1 - x - 1 / p.kappa2) / x) (fun x => 1 / x - 2) =
      {z : ℝ × ℝ | z.1 ∈ Icc (1 / p.S) (1 / p.kappa1) ∧
        1 - z.1 - 1 / p.kappa2 ≤ z.2 * z.1 ∧ (z.2 + 2) * z.1 ≤ 1} := by
    ext z
    constructor
    · intro hz
      have hx0 : 0 < z.1 := (one_div_pos.mpr hS).trans_le hz.1.1
      exact ⟨hz.1, (div_le_iff₀ hx0).mp hz.2.1,
        (le_div_iff₀ hx0).mp (by linarith [hz.2.2])⟩
    · intro hz
      have hx0 : 0 < z.1 := (one_div_pos.mpr hS).trans_le hz.1.1
      have h := (le_div_iff₀ hx0).mpr hz.2.2
      exact ⟨hz.1, (div_le_iff₀ hx0).mpr hz.2.1, by linarith⟩
  have hclosed : IsClosed (strip (1 / p.S) (1 / p.kappa1)
      (fun x => (1 - x - 1 / p.kappa2) / x) (fun x => 1 / x - 2)) := by
    rw [he]
    exact (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (by fun_prop) (by fun_prop)).inter
        (isClosed_le (by fun_prop) continuous_const))
  apply (isCompact_Icc.prod (isCompact_Icc (a := (1 : ℝ)) (b := 3))).of_isClosed_subset hclosed
  intro z hz
  have h := source68_strip_bounds hp z.1 hz.1
  exact ⟨hz.1, h.1.trans hz.2.1, hz.2.2.trans h.2.2⟩

theorem source68_fubini {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (∫ v in ((1 - x - 1 / p.kappa2) / x)..(1 / x - 2),
        f v / (v * (1 - x - v * x))) / x) =
      ∫ v in (1 : ℝ)..3, ∫ x in (1 / p.S)..(1 / p.kappa1),
        (Icc ((1 - x - 1 / p.kappa2) / x) (1 / x - 2)).indicator
          (fun v => (f v / (v * (1 - x - v * x))) / x) v := by
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk1 : 0 < p.kappa1 := by linarith [hb.2.2.2.1]
  have hkS : p.kappa1 ≤ p.S := hp.2.2.2.2.2.2.2.1
  have hab := one_div_le_one_div_of_le hk1 hkS
  let T := strip (1 / p.S) (1 / p.kappa1)
    (fun x => (1 - x - 1 / p.kappa2) / x) (fun x => 1 / x - 2)
  have hcompact : IsCompact T := source68_strip_compact hp
  have hbase : IntegrableOn (fun z : ℝ × ℝ => f z.2)
      (Icc (1 / p.S) (1 / p.kappa1) ×ˢ Icc 1 3) := by
    change Integrable _ ((volume.prod volume).restrict _)
    rw [← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (1 / p.S) (1 / p.kappa1))) :=
      integrable_const 1
    simpa only [one_mul] using h1.mul_prod
      ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3)).mp hf)
  have hsub : T ⊆ Icc (1 / p.S) (1 / p.kappa1) ×ˢ Icc 1 3 := by
    intro z hz
    have h := source68_strip_bounds hp z.1 hz.1
    exact ⟨hz.1, h.1.trans hz.2.1, hz.2.2.trans h.2.2⟩
  have hw : ContinuousOn (fun z : ℝ × ℝ => 1 / (z.2 * (1 - z.1 - z.2 * z.1)) / z.1) T := by
    intro z hz
    have hx0 : 0 < z.1 := (one_div_pos.mpr hS).trans_le hz.1.1
    have hv0 : 0 < z.2 := by linarith [(hsub hz).2.1]
    have hmul := (le_div_iff₀ hx0).mp (show z.2 + 2 ≤ 1 / z.1 by linarith [hz.2.2])
    have hden : 0 < 1 - z.1 - z.2 * z.1 := by nlinarith
    apply ContinuousAt.continuousWithinAt
    fun_prop (disch := positivity)
  have hi := (hbase.mono_set hsub).mul_continuousOn hw hcompact
  have hi' : IntegrableOn (fun z : ℝ × ℝ => f z.2 / (z.2 * (1 - z.1 - z.2 * z.1)) / z.1) T := by
    convert hi using 1
    ext z
    ring
  have hswap := strip_fubini_measurable hab (by norm_num : (1 : ℝ) ≤ 3)
    hcompact.measurableSet (source68_strip_bounds hp) hi'
  simpa only [intervalIntegral.integral_div] using hswap

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
