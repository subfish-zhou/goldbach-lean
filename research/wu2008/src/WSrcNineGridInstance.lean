import WSrcNineRoot
import WSrcGridRoot

noncomputable section
namespace WuTarget.SourceNodeInstance
open Wu2008DoubleSieve NodeExtension

def H (i : ℕ) : ℝ := extendedNode WuSource.SrcNine.z i
def h (j : ℕ) : ℝ := originalTransfer WuSource.SrcNine.z j

theorem upper_nonneg {i : ℕ} (hi : 2 ≤ i) (hi29 : i ≤ 29) : 0 ≤ H i :=
  (WuSource.SrcGrid.full_tables_nonneg (fun k => (WuSource.SrcNine.z_positive k).le)).1
    i hi hi29

theorem lower_nonneg {j : ℕ} (hj : j ≤ 29) : 0 ≤ h j :=
  (WuSource.SrcGrid.full_tables_nonneg (fun k => (WuSource.SrcNine.z_positive k).le)).2 j hj

/-- Concrete nine-vector instantiation, uniform below the proved positive radius. -/
theorem actual_tables {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ WuSource.SrcNine.d) :
    (∀ i : ℕ, 2 ≤ i → i ≤ 29 → H i ≤ wuImprovementLimit true δ (rNode i)) ∧
    (∀ j : ℕ, j ≤ 29 → h j ≤ wuImprovementLimit false δ (rNode j)) :=
  WuSource.SrcGrid.full_tables_lower hδ (hr.trans WuSource.SrcNine.d_cap)
    (WuSource.SrcNine.actual_nine_lower hδ hr)

theorem full_lower_table {δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ WuSource.SrcNine.d)
    (j : Fin 30) : h j.val ≤ wuImprovementLimit false δ (rNode j.val) :=
  (actual_tables hδ hr).2 j.val (by omega)

theorem uniform_certificate :
    0 < WuSource.SrcNine.d ∧ WuSource.SrcNine.d ≤ 1/10 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ WuSource.SrcNine.d →
      (∀ i : ℕ, 2 ≤ i → i ≤ 29 → H i ≤ wuImprovementLimit true δ (rNode i)) ∧
      (∀ j : Fin 30, h j.val ≤ wuImprovementLimit false δ (rNode j.val)) :=
  ⟨WuSource.SrcNine.d_pos, WuSource.SrcNine.d_cap,
    fun _ hδ hr => ⟨(actual_tables hδ hr).1, full_lower_table hδ hr⟩⟩

end WuTarget.SourceNodeInstance

set_option pp.fullNames true
set_option pp.explicit true
#check @WuTarget.SourceNodeInstance.actual_tables
#check @WuTarget.SourceNodeInstance.full_lower_table
#check @WuTarget.SourceNodeInstance.uniform_certificate
#print axioms WuTarget.SourceNodeInstance.actual_tables
#print axioms WuTarget.SourceNodeInstance.full_lower_table
#print axioms WuTarget.SourceNodeInstance.uniform_certificate
