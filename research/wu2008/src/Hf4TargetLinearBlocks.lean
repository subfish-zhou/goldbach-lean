import Hf4TargetLinear

noncomputable section
namespace Hf4Target
open Real Polynomial SigmaActualBlockSeparable SigmaHermiteActualFTC

theorem linear_block_0_value (t : ℝ) :
    simplePartPrimitive0 t = residueNumerator0.eval 0 * log (t+block0.eval 0) := by
  unfold simplePartPrimitive0
  convert simple_linear_value (residueNumerator0.eval 0) (block0.eval 0) t using 1
  simp [residueNumerator0, block0, add_comm]

theorem linear_block_1_value (t : ℝ) :
    simplePartPrimitive1 t = residueNumerator1.eval 0 * log (t+block1.eval 0) := by
  unfold simplePartPrimitive1
  convert simple_linear_value (residueNumerator1.eval 0) (block1.eval 0) t using 1
  simp [residueNumerator1, block1, add_comm]

theorem linear_block_2_value (t : ℝ) :
    simplePartPrimitive2 t = residueNumerator2.eval 0 * log (t+block2.eval 0) := by
  unfold simplePartPrimitive2
  convert simple_linear_value (residueNumerator2.eval 0) (block2.eval 0) t using 1
  simp [residueNumerator2, block2, add_comm]

theorem linear_block_3_value (t : ℝ) :
    simplePartPrimitive3 t = residueNumerator3.eval 0 * log (t+block3.eval 0) := by
  unfold simplePartPrimitive3
  convert simple_linear_value (residueNumerator3.eval 0) (block3.eval 0) t using 1
  simp [residueNumerator3, block3, add_comm]

theorem linear_block_4_value (t : ℝ) :
    simplePartPrimitive4 t = residueNumerator4.eval 0 * log (t+block4.eval 0) := by
  unfold simplePartPrimitive4
  convert simple_linear_value (residueNumerator4.eval 0) (block4.eval 0) t using 1
  simp [residueNumerator4, block4, add_comm]

theorem linear_block_5_value (t : ℝ) :
    simplePartPrimitive5 t = residueNumerator5.eval 0 * log (t+block5.eval 0) := by
  unfold simplePartPrimitive5
  convert simple_linear_value (residueNumerator5.eval 0) (block5.eval 0) t using 1
  simp [residueNumerator5, block5, add_comm]

theorem linear_block_6_value (t : ℝ) :
    simplePartPrimitive6 t = residueNumerator6.eval 0 * log (t+block6.eval 0) := by
  unfold simplePartPrimitive6
  convert simple_linear_value (residueNumerator6.eval 0) (block6.eval 0) t using 1
  simp [residueNumerator6, block6, add_comm]

theorem linear_block_7_value (t : ℝ) :
    simplePartPrimitive7 t = residueNumerator7.eval 0 * log (t+block7.eval 0) := by
  unfold simplePartPrimitive7
  convert simple_linear_value (residueNumerator7.eval 0) (block7.eval 0) t using 1
  simp [residueNumerator7, block7, add_comm]

theorem linear_block_8_value (t : ℝ) :
    simplePartPrimitive8 t = residueNumerator8.eval 0 * log (t+block8.eval 0) := by
  unfold simplePartPrimitive8
  convert simple_linear_value (residueNumerator8.eval 0) (block8.eval 0) t using 1
  simp [residueNumerator8, block8, add_comm]

theorem linear_block_9_value (t : ℝ) :
    simplePartPrimitive9 t = residueNumerator9.eval 0 * log (t+block9.eval 0) := by
  unfold simplePartPrimitive9
  convert simple_linear_value (residueNumerator9.eval 0) (block9.eval 0) t using 1
  simp [residueNumerator9, block9, add_comm]

end Hf4Target
