import Hf4DirectDagSeedSoundness
import Hf4ConstructiveDagSoundness

/-! UNCOMPILED original-kernel bridge. The interval premises are exactly the
old cell domain: h>=0 and m-h>=1; arithmetic precision/budgets are unchanged. -/
namespace Hf4Quad.ConstructiveDag.Direct
open Hf4Quad.CheckedDag
open Hf4Quad.CheckedDag.DirectSemantics
open Hf4Quad.RationalModel

theorem direct_model (m h : ℚ)
    (ok : checked DirectProgram.seeds m h DirectProgram.plan [] = true) :
    (getCert (run DirectProgram.seeds m h DirectProgram.plan []) 0).Valid
      (fun x => directKernel ((m:ℝ)+(h:ℝ)*x)) := by
  have good := run_sound DirectProgram.seeds (seedFun m h) m h
    (seed_sound m h) DirectProgram.plan [] [] nil_valid ok
  have last := good 0
  rw [original_f370] at last
  simpa only [DirectDag.direct_kernel_dag] using last

theorem original_compact_model (m h : ℚ)
    (hh : 0 ≤ (h:ℝ)) (hm : 1 ≤ (m:ℝ)-(h:ℝ))
    (ok : checked DirectProgram.seeds m h DirectProgram.plan [] = true) :
    (getCert (run DirectProgram.seeds m h DirectProgram.plan []) 0).Valid
      (fun x => compactKernel ((m:ℝ)+(h:ℝ)*x)) := by
  have good := direct_model m h ok
  intro x hx
  have hl := (abs_le.mp hx).1
  have hp : 0 ≤ (h:ℝ)*(x+1) := mul_nonneg hh (by linarith only [hl])
  have ht : 1 ≤ (m:ℝ)+(h:ℝ)*x := by nlinarith only [hm, hp]
  simpa only [compactKernel_eq_directKernel ht] using good x hx

end Hf4Quad.ConstructiveDag.Direct
#print axioms Hf4Quad.ConstructiveDag.Direct.original_compact_model
