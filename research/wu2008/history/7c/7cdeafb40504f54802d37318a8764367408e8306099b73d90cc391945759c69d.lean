import WR2XiRectangleFubini

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem source67_section {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    (f : ℝ → ℝ) {v : ℝ} (hv : v ∈ Icc 1 3)
    (hne5 : v ≠ alpha5 p) (hne8 : v ≠ alpha8 p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (Icc (p.S * (1 - 1 / p.kappa3 - x)) (p.S * (1 - 1 / p.kappa2 - x))).indicator
        (fun v => (p.S * f v / (v * (p.S - p.S * x - v))) / x) v) =
      f v * K67 p v := by
  rcases second_parameter_bounds hp with ⟨_, hS3, _, hk13, hk22, hk32, _⟩
  have hS : 0 < p.S := by linarith
  have hk1 : 0 < p.kappa1 := by linarith
  have hk2 : 0 < p.kappa2 := by linarith
  have hk3 : 0 < p.kappa3 := by linarith
  have hkS : p.kappa1 ≤ p.S := hp.2.2.2.2.2.2.2.1
  have h32 : p.kappa3 < p.kappa2 := hp.2.2.2.2.2.1
  have hab := one_div_le_one_div_of_le hk1 hkS
  have hde := one_div_le_one_div_of_le hk3 h32.le
  have ha0 : 0 < 1 / p.S := one_div_pos.mpr hS
  have hb0 : 0 < 1 / p.kappa1 := one_div_pos.mpr hk1
  have hd0 : 0 < 1 / p.kappa2 := one_div_pos.mpr hk2
  have he0 : 0 < 1 / p.kappa3 := one_div_pos.mpr hk3
  have hv0 : 0 < v := by linarith [hv.1]
  rcases source67_endpoint_identities hp with ⟨e7, e5, e8, e4⟩
  have ha := second_alpha_bounds hp
  have h58 := ha.2.2.1
  have hcross : 1 / p.kappa1 + 1 / p.kappa2 < 1 / p.S + 1 / p.kappa3 := by
    rw [e5, e8] at h58
    have h := (mul_lt_mul_iff_right₀ hS).mp h58
    linarith
  have h75 : alpha7 p ≤ alpha5 p := by
    rw [e7, e5]
    exact mul_le_mul_of_nonneg_left (by linarith : 1 - 1 / p.kappa3 - 1 / p.kappa1 ≤
      1 - 1 / p.kappa3 - 1 / p.S) hS.le
  have h84 := ha.2.2.2.2.2.2
  let F := fun z : ℝ × ℝ => (p.S * f z.2 / (z.2 * (p.S - p.S * z.1 - z.2))) / z.1
  by_cases hlow : v ∈ Icc (alpha7 p) (alpha5 p)
  · have hc1 : 1 / p.S + 1 / p.kappa3 ≤ 1 - v / p.S := by
      have h := hlow.2
      rw [e5, fixed_cut_upper hS] at h
      linarith
    have hc2 : 1 - v / p.S ≤ 1 / p.kappa1 + 1 / p.kappa3 := by
      have h := hlow.1
      rw [e7, fixed_cut_lower hS] at h
      linarith
    have hsec := strip_section
      (show 1 / p.S ≤ 1 - v / p.S - 1 / p.kappa3 by linarith)
      (show 1 - v / p.S - 1 / p.kappa3 ≤ 1 / p.kappa1 by linarith) le_rfl
      (l := fun x => p.S * (1 - 1 / p.kappa3 - x))
      (u := fun x => p.S * (1 - 1 / p.kappa2 - x)) (v := v) (by
        intro x hx
        rw [fixed_rectangle_section_iff hS]
        constructor
        · intro h; exact ⟨h.1, hx.2⟩
        · intro h; exact ⟨h.1, by linarith [h.2]⟩) F
    rw [hsec]
    dsimp only [F]
    rw [fixed_section_primitive hS hv0
      (by linarith : 0 < 1 - v / p.S - 1 / p.kappa3)
      (by linarith) (by linarith)]
    have hmid : v ∉ Icc (alpha5 p) (alpha8 p) := fun h => hne5 (le_antisymm hlow.2 h.1)
    have hhigh : v ∉ Icc (alpha8 p) (alpha4 p) := by
      intro h; have := hlow.2; linarith [h.1]
    simp only [K67, indicator_of_mem hlow, indicator_of_notMem hmid, indicator_of_notMem hhigh,
      zero_div, zero_mul, add_zero]
    have hD1 := source_denominator_pos (S := p.S) (r := p.kappa1) (t := v) hk1 (by
      have h := hlow.2.trans ha.2.2.1.le
      dsimp [alpha8] at h
      linarith [div_pos hS hk2])
    have hD3 := source_denominator_pos (S := p.S) (r := p.kappa3) (t := v) hk3 (by
      have h := hlow.2
      dsimp [alpha5] at h
      linarith)
    have hratio :
        ((1 - v / p.S) - (1 - v / p.S - 1 / p.kappa3)) * (1 / p.kappa1) /
          ((1 - v / p.S - 1 / p.kappa3) * ((1 - v / p.S) - 1 / p.kappa1)) =
        p.S ^ 2 / ((p.kappa1 * p.S - p.S - p.kappa1 * v) *
          (p.kappa3 * p.S - p.S - p.kappa3 * v)) := by
      field_simp
      ring
    rw [hratio]
    ring
  · by_cases hmid : v ∈ Icc (alpha5 p) (alpha8 p)
    · have hc1 : 1 / p.kappa1 + 1 / p.kappa2 ≤ 1 - v / p.S := by
        have h := hmid.2
        rw [e8, fixed_cut_upper hS] at h
        linarith
      have hc2 : 1 - v / p.S ≤ 1 / p.S + 1 / p.kappa3 := by
        have h := hmid.1
        rw [e5, fixed_cut_lower hS] at h
        linarith
      have hsec := strip_section (le_refl (1 / p.S)) hab (le_refl (1 / p.kappa1))
        (l := fun x => p.S * (1 - 1 / p.kappa3 - x))
        (u := fun x => p.S * (1 - 1 / p.kappa2 - x)) (v := v) (by
          intro x hx
          rw [fixed_rectangle_section_iff hS]
          constructor
          · intro _; exact hx
          · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩) F
      rw [hsec]
      dsimp only [F]
      rw [fixed_section_primitive hS hv0 ha0 hab (by linarith)]
      have hhigh : v ∉ Icc (alpha8 p) (alpha4 p) := fun h => hne8 (le_antisymm hmid.2 h.1)
      simp only [K67, indicator_of_notMem hlow, indicator_of_mem hmid, indicator_of_notMem hhigh,
        zero_div, zero_mul, zero_add, add_zero]
      have hD1 := source_denominator_pos (S := p.S) (r := p.kappa1) (t := v) hk1 (by
        have h := hmid.2; dsimp [alpha8] at h; linarith [div_pos hS hk2])
      have hratio :
          ((1 - v / p.S) - 1 / p.S) * (1 / p.kappa1) /
            ((1 / p.S) * ((1 - v / p.S) - 1 / p.kappa1)) =
          p.S * (p.S - 1 - v) / (p.kappa1 * p.S - p.S - p.kappa1 * v) := by
        field_simp
        ring
      rw [hratio]
      ring
    · by_cases hhigh : v ∈ Icc (alpha8 p) (alpha4 p)
      · have hc1 : 1 / p.S + 1 / p.kappa2 ≤ 1 - v / p.S := by
          have h := hhigh.2
          rw [e4, fixed_cut_upper hS] at h
          linarith
        have hc2 : 1 - v / p.S ≤ 1 / p.kappa1 + 1 / p.kappa2 := by
          have h := hhigh.1
          rw [e8, fixed_cut_lower hS] at h
          linarith
        have hsec := strip_section (le_refl (1 / p.S))
          (show 1 / p.S ≤ 1 - v / p.S - 1 / p.kappa2 by linarith)
          (show 1 - v / p.S - 1 / p.kappa2 ≤ 1 / p.kappa1 by linarith)
          (l := fun x => p.S * (1 - 1 / p.kappa3 - x))
          (u := fun x => p.S * (1 - 1 / p.kappa2 - x)) (v := v) (by
            intro x hx
            rw [fixed_rectangle_section_iff hS]
            constructor
            · intro h; exact ⟨hx.1, h.2⟩
            · intro h; exact ⟨by linarith [h.1], h.2⟩) F
        rw [hsec]
        dsimp only [F]
        rw [fixed_section_primitive hS hv0 ha0 (by linarith) (by linarith)]
        simp only [K67, indicator_of_notMem hlow, indicator_of_notMem hmid, indicator_of_mem hhigh,
          zero_div, zero_mul, zero_add]
        have hratio :
            ((1 - v / p.S) - 1 / p.S) * (1 - v / p.S - 1 / p.kappa2) /
              ((1 / p.S) * ((1 - v / p.S) - (1 - v / p.S - 1 / p.kappa2))) =
            (p.S - 1 - v) * (p.kappa2 * p.S - p.S - p.kappa2 * v) / p.S := by
          field_simp
          field_simp [hS.ne']
          ring
        rw [hratio]
        ring
      · have hnot : v < alpha7 p ∨ alpha4 p < v := by
          simp only [mem_Icc, not_and_or, not_le] at hlow hmid hhigh
          rcases hlow with h | h <;> rcases hmid with h' | h' <;> rcases hhigh with h'' | h''
          all_goals first | exact Or.inl h | exact Or.inr h'' | (exfalso; linarith)
        rw [strip_section_empty (l := fun x => p.S * (1 - 1 / p.kappa3 - x))
          (u := fun x => p.S * (1 - 1 / p.kappa2 - x)) (v := v) hab (by
            intro x hx hz
            have h := (fixed_rectangle_section_iff hS).mp hz
            rcases hnot with hnot | hnot
            · have hn : 1 - v / p.S ≤ 1 / p.kappa3 + 1 / p.kappa1 := by linarith [hx.2, h.1]
              have hv7 := (fixed_cut_lower hS).mpr hn
              rw [← e7] at hv7
              linarith
            · have hn : 1 / p.kappa2 + 1 / p.S ≤ 1 - v / p.S := by linarith [hx.1, h.2]
              have hv4 := (fixed_cut_upper hS).mpr hn
              rw [← e4] at hv4
              linarith) F]
        simp only [K67, indicator_of_notMem hlow, indicator_of_notMem hmid, indicator_of_notMem hhigh,
          zero_div, zero_mul, zero_add, mul_zero]

theorem equation67 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (∫ u in (1 / p.kappa2)..(1 / p.kappa3),
        f (p.S - p.S * x - p.S * u) / (u * (1 - x - u))) / x) =
      ∫ v in (1 : ℝ)..3, f v * K67 p v := by
  rw [source67_change_of_variables f hp, source67_fubini hf hp]
  apply intervalIntegral.integral_congr_ae
  have hne (a : ℝ) : ∀ᵐ v : ℝ ∂volume, v ≠ a := by rw [ae_iff]; simp
  filter_upwards [hne (alpha5 p), hne (alpha8 p)] with v hv5 hv8 hmem
  apply source67_section hp f _ hv5 hv8
  have h := uIoc_subset_uIcc hmem
  rwa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at h

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
