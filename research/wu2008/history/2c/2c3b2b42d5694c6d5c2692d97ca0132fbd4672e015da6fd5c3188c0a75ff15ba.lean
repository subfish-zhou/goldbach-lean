import WSrcNineAdmission

noncomputable section
namespace WuSource.SrcNine

def z : Fin 9 → ℝ :=
  ![18803317/1000000000, 18187144/1000000000, 16806736/1000000000, 15160322/1000000000, 13933425/1000000000, 11221052/1000000000, 8434404/1000000000, 6314864/1000000000, 5909403/1000000000]

theorem z_nonneg (i : Fin 9) : 0 ≤ z i := by
  fin_cases i <;> norm_num [z]

end WuSource.SrcNine
