import R2XiSecondAssembly

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension
open WuPaper.RMapMSigma
open scoped Interval

def strip (a b : ℝ) (l u : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Icc a b ∧ z.2 ∈ Icc (l z.1) (u z.1)}

theorem strip_compact {a b c d : ℝ} {l u : ℝ → ℝ}
    (hl : Continuous l) (hu : Continuous u)
    (hb : ∀ x ∈ Icc a b, c ≤ l x ∧ l x ≤ u x ∧ u x ≤ d) :
    IsCompact (strip a b l u) := by
  have hc : IsClosed (strip a b l u) :=
    (isClosed_Icc.preimage continuous_fst).inter
      ((isClosed_le (hl.comp continuous_fst) continuous_snd).inter
        (isClosed_le continuous_snd (hu.comp continuous_fst)))
  apply (isCompact_Icc.prod isCompact_Icc).of_isClosed_subset hc
  intro z hz
  exact ⟨hz.1, (hb z.1 hz.1).1.trans hz.2.1, hz.2.2.trans (hb z.1 hz.1).2.2⟩

theorem strip_profile_integrable {f : ℝ → ℝ}
    {a b c d : ℝ} (_hab : a ≤ b) (hcd : c ≤ d)
    (hf : IntervalIntegrable f volume c d) {l u : ℝ → ℝ}
    (hl : Continuous l) (hu : Continuous u)
    (hb : ∀ x ∈ Icc a b, c ≤ l x ∧ l x ≤ u x ∧ u x ≤ d)
    {w : ℝ × ℝ → ℝ} (hw : ContinuousOn w (strip a b l u)) :
    IntegrableOn (fun z => f z.2 * w z) (strip a b l u) := by
  have hi : IntegrableOn (fun z : ℝ × ℝ => f z.2) (Icc a b ×ˢ Icc c d) := by
    change Integrable _ ((volume.prod volume).restrict (Icc a b ×ˢ Icc c d))
    rw [← Measure.prod_restrict]
    have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc a b)) :=
      integrable_const 1
    simpa only [one_mul] using h1.mul_prod
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hcd).mp hf)
  have hs : strip a b l u ⊆ Icc a b ×ˢ Icc c d := by
    intro z hz
    exact ⟨hz.1, (hb z.1 hz.1).1.trans hz.2.1, hz.2.2.trans (hb z.1 hz.1).2.2⟩
  exact (hi.mono_set hs).mul_continuousOn hw (strip_compact hl hu hb)

theorem strip_fubini {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {l u : ℝ → ℝ} (hl : Continuous l) (hu : Continuous u)
    (hb : ∀ x ∈ Icc a b, c ≤ l x ∧ l x ≤ u x ∧ u x ≤ d)
    {F : ℝ × ℝ → ℝ} (hF : IntegrableOn F (strip a b l u)) :
    (∫ x in a..b, ∫ v in (l x)..(u x), F (x, v)) =
      ∫ v in c..d, ∫ x in a..b,
        (Icc (l x) (u x)).indicator (fun v => F (x, v)) v := by
  let G := (strip a b l u).indicator F
  have hs := (strip_compact hl hu hb).measurableSet
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
    _ = ∫ v in Icc c d, ∫ x in Icc a b, G (x, v) :=
      integral_integral_swap hi
    _ = _ := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _
      dsimp only
      rw [integral_Icc hab]
      exact setIntegral_congr_fun measurableSet_Icc (fun x hx => he x v hx)

theorem strip_section {a b m n v : ℝ} {l u : ℝ → ℝ}
    (ham : a ≤ m) (hmn : m ≤ n) (hnb : n ≤ b)
    (he : ∀ x ∈ Icc a b, v ∈ Icc (l x) (u x) ↔ x ∈ Icc m n)
    (F : ℝ × ℝ → ℝ) :
    (∫ x in a..b, (Icc (l x) (u x)).indicator (fun v => F (x, v)) v) =
      ∫ x in m..n, F (x, v) := by
  rw [← indicator_interval_integral ham hmn hnb (fun x => F (x, v))]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le (ham.trans (hmn.trans hnb))] at hx
  dsimp only
  by_cases hv : v ∈ Icc (l x) (u x)
  · rw [indicator_of_mem hv, indicator_of_mem ((he x hx).mp hv)]
  · rw [indicator_of_notMem hv, indicator_of_notMem (fun h => hv ((he x hx).mpr h))]

theorem strip_section_empty {a b v : ℝ} (hab : a ≤ b) {l u : ℝ → ℝ}
    (he : ∀ x ∈ Icc a b, v ∉ Icc (l x) (u x))
    (F : ℝ × ℝ → ℝ) :
    (∫ x in a..b, (Icc (l x) (u x)).indicator (fun v => F (x, v)) v) = 0 := by
  calc
    _ = ∫ _x in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le hab] at hx
      exact indicator_of_notMem (he x hx) _
    _ = 0 := by simp

theorem fixed_section_primitive {S v a b : ℝ} (hS : 0 < S) (hv : 0 < v)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < 1 - v / S) (f : ℝ → ℝ) :
    (∫ x in a..b, (S * f v / (v * (S - S * x - v))) / x) =
      f v / (v * (1 - v / S)) *
        log (((1 - v / S) - a) * b / (a * ((1 - v / S) - b))) := by
  have hc : 0 < 1 - v / S := (ha.trans_le hab).trans hbc
  rw [← rationalWeight_primitive ha hab hbc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hcx : 1 - v / S - x ≠ 0 := by linarith [hx.2]
  have he : S - S * x - v = S * (1 - v / S - x) := by field_simp; ring
  dsimp only
  rw [he]
  dsimp [rationalWeight]
  have hSv : S - v ≠ 0 := by
    have h := (div_lt_one hS).mp (show v / S < 1 by linarith)
    linarith
  field_simp [hS.ne', hv.ne', hc.ne', hx0, hcx]

theorem selected_section_primitive {v a b : ℝ} (hv : 0 < v)
    (ha : 0 < a) (hab : a ≤ b) (hbc : b < 1 / (v + 1)) (f : ℝ → ℝ) :
    (∫ x in a..b, (f v / (v * (1 - x - v * x))) / x) =
      f v / v *
        log ((1 / (v + 1) - a) * b / (a * (1 / (v + 1) - b))) := by
  have hv1 : v + 1 ≠ 0 := by linarith
  have hc : 0 < 1 / (v + 1) := by positivity
  rw [← rationalWeight_primitive ha hab hbc, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x hx
  rw [uIcc_of_le hab] at hx
  have hx0 : x ≠ 0 := (ha.trans_le hx.1).ne'
  have hcx : 1 / (v + 1) - x ≠ 0 := by linarith [hx.2]
  have he : 1 - x - v * x = (v + 1) * (1 / (v + 1) - x) := by field_simp; ring
  dsimp only
  rw [he]
  dsimp [rationalWeight]
  field_simp [hv.ne', hv1, hc.ne', hx0, hcx]

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
