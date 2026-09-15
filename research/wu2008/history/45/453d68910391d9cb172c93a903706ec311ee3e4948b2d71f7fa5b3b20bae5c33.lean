import WRMapMFirstPartition

noncomputable section
open Real
open Wu08OriginalFirstSteps

namespace WuPaper.RMapMFirst

theorem C1_component_error {l c e dl dc de : ℝ}
    (hl : |log (1127 / 200 : ℝ) - l| ≤ dl)
    (hc : |C (1327 / 200) - c| ≤ dc)
    (he : |E (1327 / 200) - e| ≤ de) :
    |C1 - 8 * (l + c + e)| ≤ 8 * (dl + dc + de) := by
  rw [C1_exact]
  unfold Wu08TerminalAlignment.firstMain
  rcases abs_le.mp hl with ⟨hl0, hl1⟩
  rcases abs_le.mp hc with ⟨hc0, hc1⟩
  rcases abs_le.mp he with ⟨he0, he1⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem C2_component_error {l c dl dc : ℝ}
    (hl : |log (78 / 25 : ℝ) - l| ≤ dl)
    (hc : |C (103 / 25) - c| ≤ dc) :
    |C2 - 8 * (l + c)| ≤ 8 * (dl + dc) := by
  rw [C2_exact, Wu08TerminalAlignment.second_exact]
  rcases abs_le.mp hl with ⟨hl0, hl1⟩
  rcases abs_le.mp hc with ⟨hc0, hc1⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem C1_directed_lower {L l c e dl dc de : ℝ}
    (hl : |log (1127 / 200 : ℝ) - l| ≤ dl)
    (hc : |C (1327 / 200) - c| ≤ dc)
    (he : |E (1327 / 200) - e| ≤ de)
    (hround : L ≤ 8 * (l + c + e - (dl + dc + de))) :
    L ≤ C1 := by
  have h := (abs_le.mp (C1_component_error hl hc he)).1
  linarith

theorem C2_directed_lower {L l c dl dc : ℝ}
    (hl : |log (78 / 25 : ℝ) - l| ≤ dl)
    (hc : |C (103 / 25) - c| ≤ dc)
    (hround : L ≤ 8 * (l + c - (dl + dc))) :
    L ≤ C2 := by
  have h := (abs_le.mp (C2_component_error hl hc)).1
  linarith

theorem C3_component_error {q0 q1 q2 e0 e1 e2 : ℝ}
    (h0 : |lowPiece - q0| ≤ e0)
    (h1 : |middlePiece - q1| ≤ e1)
    (h2 : |highPiece - q2| ≤ e2) :
    |C3 - 8 * (q0 + q1 + q2)| ≤ 8 * (e0 + e1 + e2) := by
  rw [C3_partition]
  rcases abs_le.mp h0 with ⟨h00, h01⟩
  rcases abs_le.mp h1 with ⟨h10, h11⟩
  rcases abs_le.mp h2 with ⟨h20, h21⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem C4_component_error {q1 q2 e1 e2 : ℝ}
    (h1 : |middlePiece - q1| ≤ e1)
    (h2 : |highPiece - q2| ≤ e2) :
    |C4 - 8 * (q1 + q2)| ≤ 8 * (e1 + e2) := by
  rw [C4_partition]
  rcases abs_le.mp h1 with ⟨h10, h11⟩
  rcases abs_le.mp h2 with ⟨h20, h21⟩
  apply abs_le.mpr
  constructor <;> linarith

theorem C3_directed_upper {U q0 q1 q2 e0 e1 e2 : ℝ}
    (h0 : |lowPiece - q0| ≤ e0)
    (h1 : |middlePiece - q1| ≤ e1)
    (h2 : |highPiece - q2| ≤ e2)
    (hround : 8 * (q0 + q1 + q2 + (e0 + e1 + e2)) ≤ U) :
    C3 ≤ U := by
  have h := (abs_le.mp (C3_component_error h0 h1 h2)).2
  linarith

theorem C4_directed_upper {U q1 q2 e1 e2 : ℝ}
    (h1 : |middlePiece - q1| ≤ e1)
    (h2 : |highPiece - q2| ≤ e2)
    (hround : 8 * (q1 + q2 + (e1 + e2)) ≤ U) :
    C4 ≤ U := by
  have h := (abs_le.mp (C4_component_error h1 h2)).2
  linarith

theorem C34_component_error {q0 q1 q2 e0 e1 e2 : ℝ}
    (h0 : |lowPiece - q0| ≤ e0)
    (h1 : |middlePiece - q1| ≤ e1)
    (h2 : |highPiece - q2| ≤ e2) :
    |C3 + C4 - (8 * q0 + 16 * (q1 + q2))| ≤ 8 * e0 + 16 * (e1 + e2) := by
  rw [C34_exact_combination]
  rcases abs_le.mp h0 with ⟨h00, h01⟩
  rcases abs_le.mp h1 with ⟨h10, h11⟩
  rcases abs_le.mp h2 with ⟨h20, h21⟩
  apply abs_le.mpr
  constructor <;> linarith

#check @C1_component_error
#print axioms C1_component_error
#check @C2_component_error
#print axioms C2_component_error
#check @C1_directed_lower
#print axioms C1_directed_lower
#check @C2_directed_lower
#print axioms C2_directed_lower
#check @C3_component_error
#print axioms C3_component_error
#check @C4_component_error
#print axioms C4_component_error
#check @C3_directed_upper
#print axioms C3_directed_upper
#check @C4_directed_upper
#print axioms C4_directed_upper
#check @C34_component_error
#print axioms C34_component_error

end WuPaper.RMapMFirst
