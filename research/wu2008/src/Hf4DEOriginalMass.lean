import Hf4DECellE0
import Hf4DEEndpointE1
import Hf4DEEndpointE2
import Hf4DEEndpointE3
import Hf4DEEndpointE4
import Hf4DEEndpointE5
import Hf4DEEndpointE6
import Hf4DEEndpointE7
import Hf4DEEndpointE8
import Hf4DEDenominator

noncomputable section
namespace Hf4DE
open Real

theorem original_e_mass_bounds : (3239135063483/500000000000000 : ℝ) ≤ TerminalECells.mass NineFeedbackStrength.originalH ∧
    TerminalECells.mass NineFeedbackStrength.originalH ≤ (6478271674201/1000000000000000 : ℝ) := by
  have h0 := e_cell_0_bounds
  have h1 := e_cell_1_bounds
  have h2 := e_cell_2_bounds
  have h3 := e_cell_3_bounds
  have h4 := e_cell_4_bounds
  have h5 := e_cell_5_bounds
  have h6 := e_cell_6_bounds
  have h7 := e_cell_7_bounds
  have h8 := e_cell_8_bounds
  norm_num [TerminalECells.mass, Fin.sum_univ_succ, NineFeedbackStrength.originalH,
    NodeExtension.upperLeft, NodeExtension.upperNode]
  constructor <;> linarith only [h0.1,h0.2,h1.1,h1.2,h2.1,h2.2,h3.1,h3.2,h4.1,h4.2,h5.1,h5.2,h6.1,h6.2,h7.1,h7.2,h8.1,h8.2]

theorem original_e_interval_width : (6478271674201/1000000000000000 : ℝ) - (3239135063483/500000000000000 : ℝ) < (1/1000000 : ℝ) := by norm_num

end Hf4DE
