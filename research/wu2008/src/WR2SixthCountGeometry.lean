import Wu08G6HighActual

noncomputable section
namespace WuPaper.R2SixthCount
open Real Set

abbrev alpha : ℝ := QuarterTrim.alpha
abbrev beta : ℝ := QuarterTrim.beta
def aCeiling : ℝ := 1 / 2 - 2 * beta
def bCut : ℝ := 3 * alpha / 2
def sigma : ℝ := 1 / 2 - 3 * alpha

def fullDomain : Set (ℝ × ℝ) := Ico alpha beta ×ˢ Ico beta sigma
def domainA : Set (ℝ × ℝ) := Ico alpha beta ×ˢ Ico beta aCeiling
def domainB : Set (ℝ × ℝ) := Ico alpha bCut ×ˢ Ico aCeiling sigma
def domainC : Set (ℝ × ℝ) := Ico bCut beta ×ˢ Ico aCeiling sigma

theorem parameter_order :
    0 < alpha ∧ alpha < bCut ∧ bCut < beta ∧ beta < 1 / 4 ∧
      (1 / 4 : ℝ) < aCeiling ∧ aCeiling < sigma ∧ sigma < 1 := by
  norm_num [alpha, beta, QuarterTrim.alpha, QuarterTrim.beta, aCeiling, bCut, sigma]

theorem full_domain_partition :
    fullDomain = domainA ∪ domainB ∪ domainC := by
  ext v
  simp only [fullDomain, domainA, domainB, domainC, mem_union, mem_prod, mem_Ico]
  have h := parameter_order
  constructor
  · rintro ⟨hx, hy⟩
    by_cases ha : v.2 < aCeiling
    · exact Or.inl (Or.inl ⟨hx, hy.1, ha⟩)
    · by_cases hb : v.1 < bCut
      · exact Or.inl (Or.inr ⟨⟨hx.1, hb⟩, le_of_not_gt ha, hy.2⟩)
      · exact Or.inr ⟨⟨le_of_not_gt hb, hx.2⟩, le_of_not_gt ha, hy.2⟩
  · rintro ((⟨hx, hy⟩ | ⟨hx, hy⟩) | ⟨hx, hy⟩)
    · exact ⟨hx, hy.1, hy.2.trans h.2.2.2.2.2.1⟩
    · exact ⟨⟨hx.1, hx.2.trans h.2.2.1⟩,
        (h.2.2.2.1.trans h.2.2.2.2.1).le.trans hy.1, hy.2⟩
    · exact ⟨⟨h.2.1.le.trans hx.1, hx.2⟩,
        (h.2.2.2.1.trans h.2.2.2.2.1).le.trans hy.1, hy.2⟩

theorem three_blocks_disjoint :
    Disjoint domainA domainB ∧ Disjoint domainA domainC ∧ Disjoint domainB domainC := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro v ha hb
    exact (not_lt_of_ge hb.2.1) ha.2.2
  · intro v ha hc
    exact (not_lt_of_ge hc.2.1) ha.2.2
  · intro v hb hc
    exact (not_lt_of_ge hc.1.1) hb.1.2

theorem a_high_open_rectangle :
    Ioo alpha beta ×ˢ Ioo (1 / 4 : ℝ) aCeiling ⊆ domainA := by
  intro v hv
  exact ⟨⟨hv.1.1.le, hv.1.2⟩,
    (parameter_order.2.2.2.1.trans hv.2.1).le, hv.2.2⟩

theorem b_is_high {v : ℝ × ℝ} (hv : v ∈ domainB) : (1 / 4 : ℝ) < v.2 :=
  parameter_order.2.2.2.2.1.trans_le hv.2.1

theorem high_point_not_in_prop43 {x y phi1 phi2 phi3 phi4 : ℝ}
    (hy : (1 / 4 : ℝ) < y) (h4 : phi4 < 1 / 4) :
    (x, y) ∉ Ico phi1 phi2 ×ˢ Ico phi3 phi4 := by
  intro hv
  exact (not_lt_of_ge (h4.trans hy).le) hv.2.2

theorem strict_corner_equalities :
    2 * beta + aCeiling = (1 / 2 : ℝ) ∧
      2 * bCut + sigma = (1 / 2 : ℝ) := by
  constructor <;> dsimp [aCeiling, bCut, sigma] <;> ring

theorem ab_interior_levels {v : ℝ × ℝ} (hv : v ∈ domainA ∪ domainB) :
    v.1 < v.2 ∧ 2 * v.1 + v.2 < 1 / 2 ∧ v.1 + v.2 + alpha < 1 / 2 := by
  rcases hv with ha | hb
  · obtain ⟨⟨hx, hx'⟩, hy, hy'⟩ := ha
    have hab : alpha < beta := parameter_order.2.1.trans parameter_order.2.2.1
    dsimp [aCeiling] at hy'
    exact ⟨hx'.trans_le hy, by linarith, by linarith⟩
  · obtain ⟨⟨hx, hx'⟩, hy, hy'⟩ := hb
    have hba : bCut < aCeiling :=
      parameter_order.2.2.1.trans (parameter_order.2.2.2.1.trans
        parameter_order.2.2.2.2.1)
    have hp := parameter_order.1
    dsimp [bCut] at hx'
    dsimp [sigma] at hy'
    exact ⟨(show v.1 < bCut from hx').trans (hba.trans_le hy),
      by linarith, by linarith⟩

theorem c_classical_parameter {x y : ℝ}
    (hx : x ∈ Icc bCut beta) (hy : y ∈ Icc aCeiling sigma) :
    1 < (1 / 2 - x - y) / alpha ∧ (1 / 2 - x - y) / alpha < 2 := by
  have ha : 0 < alpha := parameter_order.1
  rw [lt_div_iff₀ ha, div_lt_iff₀ ha]
  have hx0 := hx.1
  have hx1 := hx.2
  have hy0 := hy.1
  have hy1 := hy.2
  norm_num [alpha, beta, QuarterTrim.alpha, QuarterTrim.beta, aCeiling, bCut, sigma]
    at hx0 hx1 hy0 hy1 ⊢
  constructor <;> linarith

#check @WuPaper.R2SixthCount.alpha
#check @WuPaper.R2SixthCount.beta
#check @WuPaper.R2SixthCount.aCeiling
#check @WuPaper.R2SixthCount.bCut
#check @WuPaper.R2SixthCount.sigma
#check @WuPaper.R2SixthCount.fullDomain
#check @WuPaper.R2SixthCount.domainA
#check @WuPaper.R2SixthCount.domainB
#check @WuPaper.R2SixthCount.domainC
#check @WuPaper.R2SixthCount.parameter_order
#check @WuPaper.R2SixthCount.full_domain_partition
#check @WuPaper.R2SixthCount.three_blocks_disjoint
#check @WuPaper.R2SixthCount.a_high_open_rectangle
#check @WuPaper.R2SixthCount.b_is_high
#check @WuPaper.R2SixthCount.high_point_not_in_prop43
#check @WuPaper.R2SixthCount.strict_corner_equalities
#check @WuPaper.R2SixthCount.ab_interior_levels
#check @WuPaper.R2SixthCount.c_classical_parameter
#print axioms WuPaper.R2SixthCount.alpha
#print axioms WuPaper.R2SixthCount.beta
#print axioms WuPaper.R2SixthCount.aCeiling
#print axioms WuPaper.R2SixthCount.bCut
#print axioms WuPaper.R2SixthCount.sigma
#print axioms WuPaper.R2SixthCount.fullDomain
#print axioms WuPaper.R2SixthCount.domainA
#print axioms WuPaper.R2SixthCount.domainB
#print axioms WuPaper.R2SixthCount.domainC
#print axioms WuPaper.R2SixthCount.parameter_order
#print axioms WuPaper.R2SixthCount.full_domain_partition
#print axioms WuPaper.R2SixthCount.three_blocks_disjoint
#print axioms WuPaper.R2SixthCount.a_high_open_rectangle
#print axioms WuPaper.R2SixthCount.b_is_high
#print axioms WuPaper.R2SixthCount.high_point_not_in_prop43
#print axioms WuPaper.R2SixthCount.strict_corner_equalities
#print axioms WuPaper.R2SixthCount.ab_interior_levels
#print axioms WuPaper.R2SixthCount.c_classical_parameter
end WuPaper.R2SixthCount
