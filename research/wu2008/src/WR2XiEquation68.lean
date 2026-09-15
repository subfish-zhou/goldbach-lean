import WR2XiSelectedFubini

noncomputable section
namespace WuPaper.R2Xi
open Real Set MeasureTheory NodeExtension Wu2008DoubleSieve
open WuPaper.RMapMMatrix
open scoped Interval

theorem selected_lower_le {r k v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    (1 - 1 / k) / (v + 1) ≤ 1 / r ↔ r - r / k - 1 ≤ v := by
  rw [div_le_div_iff₀ (by linarith : 0 < v + 1) hr]
  simp only [div_eq_mul_inv]
  constructor <;> intro h <;> nlinarith only [h]

theorem le_selected_lower {r k v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    1 / r ≤ (1 - 1 / k) / (v + 1) ↔ v ≤ r - r / k - 1 := by
  rw [div_le_div_iff₀ hr (by linarith : 0 < v + 1)]
  simp only [div_eq_mul_inv]
  constructor <;> intro h <;> nlinarith only [h]

theorem selected_upper_le {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    1 / (v + 2) ≤ 1 / r ↔ r - 2 ≤ v := by
  rw [div_le_div_iff₀ (by linarith : 0 < v + 2) hr]
  constructor <;> intro h <;> linarith

theorem le_selected_upper {r v : ℝ} (hr : 0 < r) (hv : 0 < v) :
    1 / r ≤ 1 / (v + 2) ↔ v ≤ r - 2 := by
  rw [div_le_div_iff₀ hr (by linarith : 0 < v + 2)]
  constructor <;> intro h <;> linarith

theorem selected_lower_le_upper {k v : ℝ} (hk : 0 < k) (hv : 0 < v)
    (hkv : k - 2 ≤ v) :
    (1 - 1 / k) / (v + 1) ≤ 1 / (v + 2) := by
  rw [div_le_div_iff₀ (by linarith : 0 < v + 1) (by linarith : 0 < v + 2)]
  have h := (one_le_div hk).mpr (show k ≤ v + 2 by linarith)
  simp only [div_eq_mul_inv] at *
  nlinarith

theorem source68_section {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p)
    (f : ℝ → ℝ) {v : ℝ} (hv : v ∈ Icc 1 3)
    (hne1 : v ≠ alpha1 p) (hne4 : v ≠ alpha4 p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (Icc ((1 - x - 1 / p.kappa2) / x) (1 / x - 2)).indicator
        (fun v => f v / (v * (1 - x - v * x)) / x) v) =
      f v * K68 p v := by
  rcases second_parameter_bounds hp with ⟨_, hS3, _, hk13, hk22, _⟩
  have hS : 0 < p.S := by linarith
  have hk1 : 0 < p.kappa1 := by linarith
  have hk2 : 0 < p.kappa2 := by linarith
  have hkS : p.kappa1 ≤ p.S := hp.2.2.2.2.2.2.2.1
  have h21 : p.kappa2 < p.kappa1 := hp.2.2.2.2.2.2.1
  have hab := one_div_le_one_div_of_le hk1 hkS
  have ha0 : 0 < 1 / p.S := one_div_pos.mpr hS
  have hb0 : 0 < 1 / p.kappa1 := one_div_pos.mpr hk1
  have hv0 : 0 < v := by linarith [hv.1]
  have hv1 : 0 < v + 1 := by linarith
  have hv2 : 0 < v + 2 := by linarith
  have hbn : 0 < 1 - 1 / p.kappa2 := by
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hk22
    linarith
  have hm0 : 0 < (1 - 1 / p.kappa2) / (v + 1) := div_pos hbn hv1
  have hnc : 1 / (v + 2) < 1 / (v + 1) :=
    one_div_lt_one_div_of_lt hv1 (by linarith)
  have ha := second_alpha_bounds hp
  have h14 := ha.2.1
  have h42 := ha.2.2.2.2.1
  have h91 : alpha9 p ≤ alpha1 p := by
    have h := (one_le_div hk2).mpr h21.le
    dsimp [alpha9, alpha1]
    linarith
  let F := fun z : ℝ × ℝ => f z.2 / (z.2 * (1 - z.1 - z.2 * z.1)) / z.1
  by_cases hlow : v ∈ Icc (alpha9 p) (alpha1 p)
  · have ham : 1 / p.S ≤ (1 - 1 / p.kappa2) / (v + 1) :=
      (le_selected_lower hS hv0).mpr (hlow.2.trans h14.le)
    have hmb : (1 - 1 / p.kappa2) / (v + 1) ≤ 1 / p.kappa1 :=
      (selected_lower_le hk1 hv0).mpr hlow.1
    have hbn' : 1 / p.kappa1 ≤ 1 / (v + 2) :=
      (le_selected_upper hk1 hv0).mpr hlow.2
    have hsec := strip_section ham hmb le_rfl
      (l := fun x => (1 - x - 1 / p.kappa2) / x) (u := fun x => 1 / x - 2) (v := v) (by
        intro x hx
        rw [selected_section_iff (ha0.trans_le hx.1) hv0]
        constructor
        · intro h; exact ⟨h.1, hx.2⟩
        · intro h; exact ⟨h.1, h.2.trans hbn'⟩) F
    rw [hsec]
    dsimp only [F]
    rw [selected_section_primitive hv0 hm0 hmb (hbn'.trans_lt hnc)]
    have hmid : v ∉ Icc (alpha1 p) (alpha4 p) := fun h => hne1 (le_antisymm hlow.2 h.1)
    have hhigh : v ∉ Icc (alpha4 p) (alpha2 p) := by intro h; linarith [hlow.2, h.1]
    simp only [K68, indicator_of_mem hlow, indicator_of_notMem hmid, indicator_of_notMem hhigh,
      zero_div, zero_mul, add_zero]
    have hD : p.kappa1 - 1 - v ≠ 0 := by
      have h := hlow.2
      dsimp [alpha1] at h
      linarith
    have hk21 : p.kappa2 - 1 ≠ 0 := by linarith
    have hratio :
        (1 / (v + 1) - (1 - 1 / p.kappa2) / (v + 1)) * (1 / p.kappa1) /
          (((1 - 1 / p.kappa2) / (v + 1)) * (1 / (v + 1) - 1 / p.kappa1)) =
        (v + 1) / ((p.kappa2 - 1) * (p.kappa1 - 1 - v)) := by
      field_simp
      ring_nf
      field_simp [show -1 + p.kappa1 - v ≠ 0 by intro h; apply hD; linarith]
      ring
    rw [hratio]
    ring
  · by_cases hmid : v ∈ Icc (alpha1 p) (alpha4 p)
    · have ham : 1 / p.S ≤ (1 - 1 / p.kappa2) / (v + 1) :=
        (le_selected_lower hS hv0).mpr hmid.2
      have hmn := selected_lower_le_upper hk2 hv0 (show p.kappa2 - 2 ≤ v by
        have h := hmid.1; dsimp [alpha1] at h; linarith)
      have hnb : 1 / (v + 2) ≤ 1 / p.kappa1 :=
        (selected_upper_le hk1 hv0).mpr hmid.1
      have hsec := strip_section ham hmn hnb
        (l := fun x => (1 - x - 1 / p.kappa2) / x) (u := fun x => 1 / x - 2) (v := v)
        (fun x hx => selected_section_iff (ha0.trans_le hx.1) hv0) F
      rw [hsec]
      dsimp only [F]
      rw [selected_section_primitive hv0 hm0 hmn hnc]
      have hhigh : v ∉ Icc (alpha4 p) (alpha2 p) := fun h => hne4 (le_antisymm hmid.2 h.1)
      simp only [K68, indicator_of_notMem hlow, indicator_of_mem hmid, indicator_of_notMem hhigh,
        zero_div, zero_mul, zero_add, add_zero]
      have hk21 : p.kappa2 - 1 ≠ 0 := by linarith
      have hratio :
          (1 / (v + 1) - (1 - 1 / p.kappa2) / (v + 1)) * (1 / (v + 2)) /
            (((1 - 1 / p.kappa2) / (v + 1)) * (1 / (v + 1) - 1 / (v + 2))) =
          (v + 1) / (p.kappa2 - 1) := by
        field_simp
        ring
      rw [hratio]
      ring
    · by_cases hhigh : v ∈ Icc (alpha4 p) (alpha2 p)
      · have hma : (1 - 1 / p.kappa2) / (v + 1) ≤ 1 / p.S :=
          (selected_lower_le hS hv0).mpr hhigh.1
        have han : 1 / p.S ≤ 1 / (v + 2) :=
          (le_selected_upper hS hv0).mpr hhigh.2
        have hnb : 1 / (v + 2) ≤ 1 / p.kappa1 :=
          (selected_upper_le hk1 hv0).mpr (h14.le.trans hhigh.1)
        have hsec := strip_section (le_refl (1 / p.S)) han hnb
          (l := fun x => (1 - x - 1 / p.kappa2) / x) (u := fun x => 1 / x - 2) (v := v) (by
            intro x hx
            rw [selected_section_iff (ha0.trans_le hx.1) hv0]
            constructor
            · intro h; exact ⟨hx.1, h.2⟩
            · intro h; exact ⟨hma.trans h.1, h.2⟩) F
        rw [hsec]
        dsimp only [F]
        rw [selected_section_primitive hv0 ha0 han hnc]
        simp only [K68, indicator_of_notMem hlow, indicator_of_notMem hmid, indicator_of_mem hhigh,
          zero_div, zero_mul, zero_add]
        have hratio :
            (1 / (v + 1) - 1 / p.S) * (1 / (v + 2)) /
              ((1 / p.S) * (1 / (v + 1) - 1 / (v + 2))) =
            p.S - 1 - v := by
          field_simp
          ring
        rw [hratio]
        ring
      · have hnot : v < alpha9 p ∨ alpha2 p < v := by
          simp only [mem_Icc, not_and_or, not_le] at hlow hmid hhigh
          rcases hlow with h | h <;> rcases hmid with h' | h' <;> rcases hhigh with h'' | h''
          all_goals first | exact Or.inl h | exact Or.inr h'' | (exfalso; linarith)
        rw [strip_section_empty (l := fun x => (1 - x - 1 / p.kappa2) / x)
          (u := fun x => 1 / x - 2) (v := v) hab (by
            intro x hx hz
            have h := (selected_section_iff (ha0.trans_le hx.1) hv0).mp hz
            rcases hnot with hn | hn
            · have h9 := (selected_lower_le hk1 hv0).mp (h.1.trans hx.2)
              change alpha9 p ≤ v at h9
              linarith
            · have h2 := (le_selected_upper hS hv0).mp (hx.1.trans h.2)
              change v ≤ alpha2 p at h2
              linarith) F]
        simp only [K68, indicator_of_notMem hlow, indicator_of_notMem hmid, indicator_of_notMem hhigh,
          zero_div, zero_mul, zero_add, mul_zero]

theorem equation68 {f : ℝ → ℝ} (hf : IntervalIntegrable f volume 1 3)
    {p : SecondFunctionalParameters} (hp : PropositionFourGeometry p) :
    (∫ x in (1 / p.S)..(1 / p.kappa1),
      (∫ u in x..(1 / p.kappa2),
        f ((1 - x - u) / x) / (u * (1 - x - u))) / x) =
      ∫ v in (1 : ℝ)..3, f v * K68 p v := by
  rw [source68_change_of_variables f hp, source68_fubini hf hp]
  apply intervalIntegral.integral_congr_ae
  have hne (a : ℝ) : ∀ᵐ v : ℝ ∂volume, v ≠ a := by rw [ae_iff]; simp
  filter_upwards [hne (alpha1 p), hne (alpha4 p)] with v hv1 hv4 hmem
  apply source68_section hp f _ hv1 hv4
  have h := uIoc_subset_uIcc hmem
  rwa [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at h

end WuPaper.R2Xi

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.R2Xi then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))
