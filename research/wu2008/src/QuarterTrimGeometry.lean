import QuarterTrimIntegral

open Set MeasureTheory

namespace QuarterTrim

noncomputable def beta : ℝ := 25 / 206

def regionA : Set (ℝ × ℝ) :=
  Icc alpha beta ×ˢ Icc beta (1 / 2 - 2 * beta)
def regionB : Set (ℝ × ℝ) :=
  Icc alpha (3 * alpha / 2) ×ˢ Icc (1 / 2 - 2 * beta) (1 / 2 - 3 * alpha)
def originalP : Set (ℝ × ℝ) := (regionA ∪ regionB) ∩ {v | 2 ≤ u v.1 v.2}
def clippedP : Set (ℝ × ℝ) :=
  {v | alpha ≤ v.1 ∧ v.1 ≤ beta ∧ beta ≤ v.2 ∧ v.1 + v.2 ≤ 1 / 2 - 2 * alpha}
def goodP : Set (ℝ × ℝ) := originalP ∩ {v | v.2 ≤ 1 / 4}
def excessP : Set (ℝ × ℝ) := originalP ∩ {v | 1 / 4 < v.2}

theorem fixed_geometry :
    3 * alpha / 2 < beta ∧ beta < 7 * alpha / 4 ∧
    beta < (1 / 4 : ℝ) ∧ alpha + d < beta := by
  norm_num [alpha, beta, d]

theorem originalP_eq_clippedP : originalP = clippedP := by
  ext v
  rcases v with ⟨x, y⟩
  simp only [originalP, regionA, regionB, clippedP, mem_inter_iff, mem_union,
    mem_prod, mem_Icc, mem_ofPred_eq]
  have hf := fixed_geometry
  have hu : 2 ≤ u x y ↔ x + y ≤ 1 / 2 - 2 * alpha := by
    unfold u
    rw [le_div_iff₀ alpha_pos]
    constructor <;> intro h <;> linarith
  rw [hu]
  constructor
  · rintro ⟨h | h, hxy⟩
    · exact ⟨h.1.1, h.1.2, h.2.1, hxy⟩
    · refine ⟨h.1.1, ?_, ?_, hxy⟩
      · linarith [h.1.2, hf.1]
      · have hbb : beta ≤ 1 / 2 - 2 * beta := by norm_num [beta]
        linarith [h.2.1]
  · rintro ⟨hx, hxb, hy, hxy⟩
    refine ⟨?_, hxy⟩
    by_cases hya : y ≤ 1 / 2 - 2 * beta
    · exact Or.inl ⟨⟨hx, hxb⟩, ⟨hy, hya⟩⟩
    · apply Or.inr
      refine ⟨⟨hx, ?_⟩, ⟨le_of_lt (lt_of_not_ge hya), ?_⟩⟩
      · linarith [hf.2.1]
      · linarith

/-- Closed excess is precisely the triangle. The strict excess below keeps its boundary explicit. -/
theorem closed_excess_iff (x y : ℝ) :
    ((x, y) ∈ originalP ∧ (1 / 4 : ℝ) ≤ y) ↔ triangle x y := by
  rw [originalP_eq_clippedP]
  simp only [clippedP, mem_ofPred_eq, triangle, mem_Icc]
  have hf := fixed_geometry
  dsimp [top, d] at *
  constructor
  · rintro ⟨⟨hx, _hxb, _hyb, hxy⟩, hy⟩
    exact ⟨⟨hx, by linarith⟩, ⟨hy, by linarith⟩⟩
  · rintro ⟨⟨hx, hxd⟩, ⟨hy, hyt⟩⟩
    exact ⟨⟨hx, by linarith [hf.2.2.2], by linarith [hf.2.2.1], by linarith⟩, hy⟩

theorem excess_iff (x y : ℝ) :
    (x, y) ∈ excessP ↔ triangle x y ∧ (1 / 4 : ℝ) < y := by
  change ((x, y) ∈ originalP ∧ (1 / 4 : ℝ) < y) ↔ _
  constructor
  · rintro ⟨hP, hy⟩
    exact ⟨(closed_excess_iff x y).1 ⟨hP, le_of_lt hy⟩, hy⟩
  · rintro ⟨hT, hy⟩
    exact ⟨((closed_excess_iff x y).2 hT).1, hy⟩

theorem good_excess_partition : goodP ∪ excessP = originalP ∧ Disjoint goodP excessP := by
  constructor
  · ext v
    simp only [goodP, excessP, mem_union, mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro h
      by_cases hy : v.2 ≤ 1 / 4
      · exact Or.inl ⟨h, hy⟩
      · exact Or.inr ⟨h, lt_of_not_ge hy⟩
  · rw [Set.disjoint_left]
    intro v hv hw
    have hle : v.2 ≤ (1 / 4 : ℝ) := hv.2
    have hlt : (1 / 4 : ℝ) < v.2 := hw.2
    exact (not_lt_of_ge hle) hlt

theorem excess_fibre {x : ℝ} (hx : x ∈ Icc alpha (alpha + d)) :
    {y : ℝ | (x, y) ∈ excessP} = Ioc (1 / 4) (top x) := by
  ext y
  rw [mem_ofPred_eq, excess_iff]
  simp only [triangle, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨⟨_, hy⟩, hy'⟩
    exact ⟨hy', hy.2⟩
  · rintro ⟨hy, hyt⟩
    exact ⟨⟨hx, ⟨le_of_lt hy, hyt⟩⟩, hy⟩

/-- The inner integral is over the actual strict excess fibre, not an assumed area.
The outer `Ioc` only omits the endpoint x = alpha. -/
theorem loss_as_excess_fibres (p : ℝ → ℝ) :
    loss p = 4 * ∫ x in Ioc alpha (alpha + d),
      ∫ y in {y : ℝ | (x, y) ∈ excessP}, kernel p x y := by
  unfold loss
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [d_pos] : alpha ≤ alpha + d)]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro x hx
  have hxc : x ∈ Icc alpha (alpha + d) := ⟨le_of_lt hx.1, hx.2⟩
  dsimp only
  rw [excess_fibre hxc, intervalIntegral.integral_of_le (top_ge hxc)]

noncomputable def coefficientLoss : ℝ := q * (d / alpha) ^ 2
noncomputable def printedSum : ℝ := 90713 / 100000

/-- A printed rational, not an assertion that the specified staircase achieves it. -/
noncomputable def staircaseTarget : ℝ := 60469 / 1000000

theorem exact_coefficient_loss : coefficientLoss = 3403880289 / 1600000000000 := by
  norm_num [coefficientLoss, q, d, alpha]

theorem exact_margin :
    printedSum - coefficientLoss - 899 / 1000 = 9604119711 / 1600000000000 := by
  rw [exact_coefficient_loss]
  norm_num [printedSum]

theorem rectangle_margin : (899 / 1000 : ℝ) < printedSum - 2 * coefficientLoss := by
  rw [exact_coefficient_loss]
  norm_num [printedSum]

/-- Pure algebra, conditional on the printed-sum lower certificate and a debit budget. -/
theorem conditional_coefficient (base debit : ℝ)
    (hb : printedSum ≤ base) (hd : debit ≤ coefficientLoss) :
    (899 / 1000 : ℝ) < base - debit := by
  have hm := exact_margin
  have hr : (0 : ℝ) < 9604119711 / 1600000000000 := by norm_num
  linarith

/-- The analytic loss bound supplies the debit budget; no input claims the loss bound itself. -/
theorem conditional_coefficient_of_integral (p : ℝ → ℝ) (base : ℝ)
    (hb : printedSum ≤ base)
    (hp : ∀ x y, triangle x y → 0 ≤ p (u x y) ∧ p (u x y) ≤ q)
    (hi : ∀ x ∈ Icc alpha (alpha + d),
      IntervalIntegrable (kernel p x) volume (1 / 4) (top x))
    (ho : IntervalIntegrable
      (fun x => ∫ y in (1 / 4)..top x, kernel p x y) volume alpha (alpha + d)) :
    (899 / 1000 : ℝ) < base - loss p / 4 := by
  apply conditional_coefficient base (loss p / 4) hb
  have hh := (loss_bounds p hp hi ho).2
  unfold coefficientLoss
  linarith

end QuarterTrim
