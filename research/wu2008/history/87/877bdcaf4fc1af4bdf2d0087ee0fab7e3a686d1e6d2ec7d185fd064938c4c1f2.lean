import R2XiKernelRegularity

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem fixed_triangle_section_iff {S b x v : ℝ} (hS : 0 < S) :
    v ∈ Icc (S * (1 - b - x)) (S * (1 - 2 * x)) ↔
      x ∈ Icc (1 - v / S - b) ((1 - v / S) / 2) := by
  constructor
  · intro h
    have hl : 1 - b - x ≤ v / S :=
      (le_div_iff₀ hS).mpr (by nlinarith only [h.1])
    have hu : v / S ≤ 1 - 2 * x :=
      (div_le_iff₀ hS).mpr (by nlinarith only [h.2])
    exact ⟨by linarith, by linarith⟩
  · intro h
    have hl := (le_div_iff₀ hS).mp (show 1 - b - x ≤ v / S by linarith [h.1])
    have hu := (div_le_iff₀ hS).mp (show v / S ≤ 1 - 2 * x by linarith [h.2])
    exact ⟨by nlinarith only [hl], by nlinarith only [hu]⟩

theorem source66_strip_bounds {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    ∀ x ∈ Icc (1 / p.S) (1 / p.kappa2),
      1 ≤ p.S * (1 - 1 / p.kappa2 - x) ∧
      p.S * (1 - 1 / p.kappa2 - x) ≤ p.S * (1 - 2 * x) ∧
      p.S * (1 - 2 * x) ≤ 3 := by
  have hb := second_parameter_bounds hp
  have ha := (second_alpha_bounds hp).1
  have hS : 0 < p.S := by linarith [hb.2.1]
  intro x hx
  have hlo := mul_le_mul_of_nonneg_left hx.1 hS.le
  have hhi := mul_le_mul_of_nonneg_left hx.2 hS.le
  simp only [mul_one_div, div_self hS.ne'] at hlo hhi
  have h6 : 1 ≤ p.S - 2 * p.S / p.kappa2 := (ha 5).1
  have h2 : p.S - 2 ≤ 3 := (ha 1).2
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem source66_fubini {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa2),
      (∫ v in (p.S * (1 - 1 / p.kappa2 - x))..(p.S * (1 - 2 * x)),
        p.S * f v / (v * (p.S - p.S * x - v))) / x) =
      ∫ v in (1 : ℝ)..3, ∫ x in (1 / p.S)..(1 / p.kappa2),
        (Icc (p.S * (1 - 1 / p.kappa2 - x)) (p.S * (1 - 2 * x))).indicator
          (fun v => (p.S * f v / (v * (p.S - p.S * x - v))) / x) v := by
  have hb := second_parameter_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have hkS : p.kappa2 ≤ p.S := hb.2.2.2.2.2.2.2.1.le
  have hab := one_div_le_one_div_of_le hk hkS
  have hbounds := source66_strip_bounds hp
  have hi := strip_profile_integrable hab (by norm_num : (1 : ℝ) ≤ 3) hf
    (l := fun x => p.S * (1 - 1 / p.kappa2 - x))
    (u := fun x => p.S * (1 - 2 * x))
    (by fun_prop) (by fun_prop) hbounds
    (w := fun z => p.S / (z.2 * (p.S - p.S * z.1 - z.2)) / z.1) (by
      intro z hz
      have hx0 : 0 < z.1 := (one_div_pos.mpr hS).trans_le hz.1.1
      have hv0 : 0 < z.2 := by linarith [(hbounds z.1 hz.1).1, hz.2.1]
      have hden : 0 < p.S - p.S * z.1 - z.2 := by
        nlinarith [hz.2.2, mul_pos hS hx0]
      apply ContinuousAt.continuousWithinAt
      fun_prop (disch := positivity))
  have hi' : IntegrableOn (fun z : ℝ × ℝ =>
      (p.S * f z.2 / (z.2 * (p.S - p.S * z.1 - z.2))) / z.1)
      (strip (1 / p.S) (1 / p.kappa2)
        (fun x => p.S * (1 - 1 / p.kappa2 - x)) (fun x => p.S * (1 - 2 * x))) := by
    convert hi using 1
    ext z
    ring
  have hswap := strip_fubini hab (by norm_num : (1 : ℝ) ≤ 3)
    (by fun_prop) (by fun_prop) hbounds hi'
  simpa only [intervalIntegral.integral_div] using hswap

theorem source66_section {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    (f : ℝ → ℝ) {v : ℝ} (hv : v ∈ Icc 1 3) (hne : v ≠ alpha4 p) :
    (∫ x in (1 / p.S)..(1 / p.kappa2),
      (Icc (p.S * (1 - 1 / p.kappa2 - x)) (p.S * (1 - 2 * x))).indicator
        (fun v => (p.S * f v / (v * (p.S - p.S * x - v))) / x) v) =
      f v * K66 p v := by
  have hb := second_parameter_bounds hp
  have ha := second_alpha_bounds hp
  have hS : 0 < p.S := by linarith [hb.2.1]
  have hk : 0 < p.kappa2 := by linarith [hb.2.2.2.2.1]
  have hkS : p.kappa2 ≤ p.S := hb.2.2.2.2.2.2.2.1.le
  have hab := one_div_le_one_div_of_le hk hkS
  have ha0 : 0 < 1 / p.S := one_div_pos.mpr hS
  have hb0 : 0 < 1 / p.kappa2 := one_div_pos.mpr hk
  have hv0 : 0 < v := by linarith [hv.1]
  have e6 : alpha6 p = p.S * (1 - 2 * (1 / p.kappa2)) := by dsimp [alpha6]; ring
  have e4 : alpha4 p = p.S * (1 - 1 / p.kappa2 - 1 / p.S) := by
    dsimp [alpha4]
    field_simp
    ring
  have e2 : alpha2 p = p.S * (1 - 2 * (1 / p.S)) := by
    dsimp [alpha2]
    field_simp
    ring
  by_cases hlow : v ∈ Icc (alpha6 p) (alpha4 p)
  · have hc1 : 1 / p.S + 1 / p.kappa2 ≤ 1 - v / p.S := by
      have h := (div_le_iff₀ hS).mpr (show v ≤ (1 - 1 / p.kappa2 - 1 / p.S) * p.S by
        rw [mul_comm, ← e4]; exact hlow.2)
      linarith
    have hc2 : 1 - v / p.S ≤ 2 * (1 / p.kappa2) := by
      have h := (le_div_iff₀ hS).mpr (show (1 - 2 * (1 / p.kappa2)) * p.S ≤ v by
        rw [mul_comm, ← e6]; exact hlow.1)
      linarith
    have hc0 : 0 < 1 - v / p.S := by linarith
    have hsec := strip_section (show 1 / p.S ≤ 1 - v / p.S - 1 / p.kappa2 by linarith)
      (show 1 - v / p.S - 1 / p.kappa2 ≤ (1 - v / p.S) / 2 by linarith)
      (show (1 - v / p.S) / 2 ≤ 1 / p.kappa2 by linarith)
      (fun x _ => fixed_triangle_section_iff hS)
      (fun z : ℝ × ℝ => (p.S * f z.2 / (z.2 * (p.S - p.S * z.1 - z.2))) / z.1)
    rw [hsec, fixed_section_primitive hS hv0 (by linarith : 0 < 1 - v / p.S - 1 / p.kappa2)
      (by linarith) (by linarith)]
    have hother : v ∉ Icc (alpha4 p) (alpha2 p) :=
      fun h => hne (le_antisymm hlow.2 h.1)
    simp only [K66, indicator_of_mem hlow, indicator_of_notMem hother, zero_div, zero_mul, add_zero]
    have hratio :
        ((1 - v / p.S) - (1 - v / p.S - 1 / p.kappa2)) * ((1 - v / p.S) / 2) /
          ((1 - v / p.S - 1 / p.kappa2) * ((1 - v / p.S) - (1 - v / p.S) / 2)) =
        p.S / (p.kappa2 * p.S - p.S - p.kappa2 * v) := by
      have hcne : 1 - v / p.S - 1 / p.kappa2 ≠ 0 := by linarith
      have hD := source_denominator_pos (S := p.S) (t := v) hk (by
        have h := hlow.2; dsimp [alpha4] at h; linarith)
      field_simp
      <;> ring
    rw [hratio]
    ring
  · by_cases hhigh : v ∈ Icc (alpha4 p) (alpha2 p)
    · have hc1 : 2 * (1 / p.S) ≤ 1 - v / p.S := by
        have h := (div_le_iff₀ hS).mpr (show v ≤ (1 - 2 * (1 / p.S)) * p.S by
          rw [mul_comm, ← e2]; exact hhigh.2)
        linarith
      have hc2 : 1 - v / p.S ≤ 1 / p.S + 1 / p.kappa2 := by
        have h := (le_div_iff₀ hS).mpr (show (1 - 1 / p.kappa2 - 1 / p.S) * p.S ≤ v by
          rw [mul_comm, ← e4]; exact hhigh.1)
        linarith
      have hsec := strip_section (le_refl (1 / p.S))
        (show 1 / p.S ≤ (1 - v / p.S) / 2 by linarith)
        (show (1 - v / p.S) / 2 ≤ 1 / p.kappa2 by linarith)
        (l := fun x => p.S * (1 - 1 / p.kappa2 - x)) (u := fun x => p.S * (1 - 2 * x))
        (v := v) (by
          intro x hx
          rw [fixed_triangle_section_iff hS]
          constructor
          · intro h; exact ⟨hx.1, h.2⟩
          · intro h; exact ⟨by linarith [h.1], h.2⟩)
        (fun z : ℝ × ℝ => (p.S * f z.2 / (z.2 * (p.S - p.S * z.1 - z.2))) / z.1)
      rw [hsec, fixed_section_primitive hS hv0 ha0 (by linarith) (by linarith)]
      simp only [K66, indicator_of_notMem hlow, indicator_of_mem hhigh, zero_div, zero_mul, zero_add]
      have hratio :
          ((1 - v / p.S) - 1 / p.S) * ((1 - v / p.S) / 2) /
            ((1 / p.S) * ((1 - v / p.S) - (1 - v / p.S) / 2)) =
          p.S - 1 - v := by
        have hcne : 1 - v / p.S ≠ 0 := by linarith
        field_simp
        <;> ring
      rw [hratio]
      ring
    · have hnot : v < alpha6 p ∨ alpha2 p < v := by
        have h64 := alpha6_le_alpha4 hk hkS
        have h42 := ha.2.2.2.2.1
        simp only [mem_Icc, not_and_or, not_le] at hlow hhigh
        rcases hlow with h | h <;> rcases hhigh with h' | h'
        · exact Or.inl h
        · exact Or.inl h
        · exfalso; linarith
        · exact Or.inr h'
      rw [strip_section_empty hab (by
        intro x hx hz
        have hxlo := mul_le_mul_of_nonneg_left hx.1 hS.le
        have hxhi := mul_le_mul_of_nonneg_left hx.2 hS.le
        simp only [mul_one_div, div_self hS.ne'] at hxlo hxhi
        rcases hnot with h | h
        · dsimp [alpha6] at h; nlinarith [hz.1]
        · dsimp [alpha2] at h; nlinarith [hz.2])]
      simp only [K66, indicator_of_notMem hlow, indicator_of_notMem hhigh,
        zero_div, zero_mul, add_zero, mul_zero]

theorem equation66 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa2),
      (∫ u in x..(1 / p.kappa2),
        f (p.S - p.S * x - p.S * u) / (u * (1 - x - u))) / x) =
      ∫ v in (1 : ℝ)..3, f v * K66 p v := by
  rw [source66_change_of_variables f hp, source66_fubini hf hp]
  apply intervalIntegral.integral_congr_ae
  have hne : ∀ᵐ v : ℝ ∂volume, v ≠ alpha4 p := by rw [ae_iff]; simp
  filter_upwards [hne] with v hv hmem
  apply source66_section hp f _ hv
  have h := uIoc_subset_uIcc hmem
  rwa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at h

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
