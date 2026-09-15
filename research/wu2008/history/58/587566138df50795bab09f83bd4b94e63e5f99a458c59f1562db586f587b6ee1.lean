import RMapMMatrixProbe

noncomputable section
namespace WuPaper.RMapMMatrix
open Real Set MeasureTheory Wu2008DoubleSieve NodeExtension ActualNineFeedback
open scoped Interval

def alpha1 (p : SecondFunctionalParameters) : ℝ := p.kappa1 - 2
def alpha2 (p : SecondFunctionalParameters) : ℝ := p.S - 2
def alpha3 (p : SecondFunctionalParameters) : ℝ := p.S - p.S / p.s - 1
def alpha4 (p : SecondFunctionalParameters) : ℝ := p.S - p.S / p.kappa2 - 1
def alpha5 (p : SecondFunctionalParameters) : ℝ := p.S - p.S / p.kappa3 - 1
def alpha6 (p : SecondFunctionalParameters) : ℝ := p.S - 2 * p.S / p.kappa2
def alpha7 (p : SecondFunctionalParameters) : ℝ :=
  p.S - p.S / p.kappa1 - p.S / p.kappa3
def alpha8 (p : SecondFunctionalParameters) : ℝ :=
  p.S - p.S / p.kappa1 - p.S / p.kappa2
def alpha9 (p : SecondFunctionalParameters) : ℝ :=
  p.kappa1 - p.kappa1 / p.kappa2 - 1

def sourceAlphas (p : SecondFunctionalParameters) : Fin 9 → ℝ :=
  ![alpha1 p, alpha2 p, alpha3 p, alpha4 p, alpha5 p,
    alpha6 p, alpha7 p, alpha8 p, alpha9 p]

def PropositionFourGeometry (p : SecondFunctionalParameters) : Prop :=
  2 ≤ p.s ∧ p.s ≤ 3 ∧ 3 ≤ p.S ∧ p.S ≤ 5 ∧
  p.s ≤ p.kappa3 ∧ p.kappa3 < p.kappa2 ∧ p.kappa2 < p.kappa1 ∧
  p.kappa1 ≤ p.S ∧ 2 ≤ p.S - p.S / p.s ∧
  (∀ i, sourceAlphas p i ∈ Icc 1 3) ∧ alpha1 p < alpha4 p ∧ alpha5 p < alpha8 p

theorem original_four_rows_qualified (i : Fin 4) :
    PropositionFourGeometry (coupledRow i) := by
  fin_cases i <;>
    norm_num [PropositionFourGeometry, sourceAlphas, alpha1, alpha2, alpha3,
      alpha4, alpha5, alpha6, alpha7, alpha8, alpha9, coupledRow,
      SecondFunctionalPositive.parameters, SecondFunctionalParameters.row1,
      SecondFunctionalParameters.row2, SecondFunctionalParameters.row3,
      SecondFunctionalParameters.row4, Fin.forall_fin_succ]

theorem original_five_rows_qualified (i : Fin 5) :
    2 ≤ firstNode i ∧ firstNode i ≤ 3 ∧ 3 ≤ firstS i ∧ firstS i ≤ 5 ∧
      2 ≤ firstS i - firstS i / firstNode i :=
  first_geometry i

def wu04Node (i : ℕ) : ℝ := if i = 0 then 1 else 2 + ((i : ℝ) + 1) / 10
def wu08Node (i : ℕ) : ℝ := 2 + (i : ℝ) / 10

theorem source_node_index_eq (i : Fin 9) :
    wu04Node (i.val + 1) = wu08Node (i.val + 2) ∧
      wu04Node (i.val + 1) = upperNode i := by
  simp only [wu04Node, Nat.add_one_ne_zero, if_false, wu08Node, upperNode,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  constructor <;> ring

theorem source_left_endpoint_eq (i : Fin 9) : wu04Node i.val = upperLeft i := by
  simp only [wu04Node, upperLeft]
  split_ifs <;> first | rfl | ring

theorem source_first_cell : upperLeft 0 = 1 ∧ upperNode 0 = 11 / 5 := by
  norm_num [upperLeft, upperNode]

theorem source_last_node : upperNode 8 = 3 := by
  norm_num [upperNode]

theorem alpha6_le_alpha4 {p : SecondFunctionalParameters}
    (hk : 0 < p.kappa2) (hkS : p.kappa2 ≤ p.S) :
    alpha6 p ≤ alpha4 p := by
  have h : 1 ≤ p.S / p.kappa2 := (one_le_div hk).mpr hkS
  dsimp [alpha6, alpha4]
  rw [mul_div_assoc]
  linarith

theorem alpha4_le_alpha2 {p : SecondFunctionalParameters}
    (hk : 0 < p.kappa2) (hkS : p.kappa2 ≤ p.S) :
    alpha4 p ≤ alpha2 p := by
  have h : 1 ≤ p.S / p.kappa2 := (one_le_div hk).mpr hkS
  dsimp [alpha4, alpha2]
  linarith

theorem source66_rectangle_bounds {S k t u : ℝ}
    (hS : 0 < S)
    (ht : t ∈ Icc (1 / S) (1 / k))
    (hu : u ∈ Icc t (1 / k)) :
    S - 2 * S / k ≤ S * (1 - t - u) ∧
      S * (1 - t - u) ≤ S - 2 := by
  have hu0 : 1 / S ≤ u := ht.1.trans hu.1
  have hSt := mul_le_mul_of_nonneg_left ht.1 hS.le
  have hSu := mul_le_mul_of_nonneg_left hu0 hS.le
  have htk := mul_le_mul_of_nonneg_left ht.2 hS.le
  have huk := mul_le_mul_of_nonneg_left hu.2 hS.le
  simp only [mul_one_div, div_self hS.ne'] at hSt hSu htk huk
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem source67_rectangle_bounds {S k1 k2 k3 t u : ℝ}
    (hS : 0 < S)
    (ht : t ∈ Icc (1 / S) (1 / k1))
    (hu : u ∈ Icc (1 / k2) (1 / k3)) :
    S - S / k1 - S / k3 ≤ S * (1 - t - u) ∧
      S * (1 - t - u) ≤ S - S / k2 - 1 := by
  have hSt := mul_le_mul_of_nonneg_left ht.1 hS.le
  have hSu := mul_le_mul_of_nonneg_left hu.1 hS.le
  have htk := mul_le_mul_of_nonneg_left ht.2 hS.le
  have huk := mul_le_mul_of_nonneg_left hu.2 hS.le
  simp only [mul_one_div, div_self hS.ne'] at hSt hSu htk huk
  constructor <;> nlinarith

theorem source68_rectangle_bounds {S k1 k2 t u : ℝ}
    (hS : 0 < S) (hk1 : 0 < k1) (hk2 : 1 ≤ k2)
    (ht : t ∈ Icc (1 / S) (1 / k1))
    (hu : u ∈ Icc t (1 / k2)) :
    k1 - k1 / k2 - 1 ≤ (1 - t - u) / t ∧
      (1 - t - u) / t ≤ S - 2 := by
  have ht0 : 0 < t := (one_div_pos.mpr hS).trans_le ht.1
  have hku : 0 ≤ 1 - 1 / k2 := by
    have h := (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hk2)
    norm_num only [div_one] at h
    linarith
  have htl : k1 * t ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left ht.2 hk1.le
    simpa only [mul_one_div, div_self hk1.ne'] using h
  have htr : 1 ≤ S * t := by
    have h := mul_le_mul_of_nonneg_left ht.1 hS.le
    simpa only [mul_one_div, div_self hS.ne'] using h
  constructor
  · apply (le_div_iff₀ ht0).mpr
    have hprod := mul_le_mul_of_nonneg_right htl hku
    simp only [div_eq_mul_inv] at *
    nlinarith [hu.2]
  · apply (div_le_iff₀ ht0).mpr
    nlinarith [hu.1]

run_cmd do
  for (name, _) in (← Lean.getEnv).constants.toList do
    if name.getPrefix == `WuPaper.RMapMMatrix then
      Lean.Elab.Command.elabCommand (← `(#check @$(Lean.mkIdent name)))
      Lean.Elab.Command.elabCommand (← `(#print axioms $(Lean.mkIdent name)))

end WuPaper.RMapMMatrix
