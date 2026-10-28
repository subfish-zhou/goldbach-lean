import Hf4DirectDagSemantics
import Hf4QuadRationalModel

/-! UNCOMPILED seed bridge; no original381 SharedCertificates import. -/
namespace Hf4Quad.CheckedDag.DirectSemantics
open RationalModel

private theorem seed_valid_001 (m h : ℚ) :
    (DirectProgram.seeds 1).Valid (seedFun m h 1) := by
  convert radical using 1 <;>
    norm_num [Certificate.Valid, Certificate.cubic, DirectProgram.seeds, seedFun, DirectDag.f1]

private theorem seed_valid_299 (m h : ℚ) :
    (DirectProgram.seeds 299).Valid (seedFun m h 299) := by
  convert radical.scale (189:ℚ) using 1 <;>
    norm_num [Certificate.Valid, Certificate.cubic, RationalModel.scale, DirectProgram.seeds, seedFun, DirectDag.f299, DirectDag.f217, DirectDag.f1]

set_option maxHeartbeats 4000000 in
theorem seed_sound (m h : ℚ) (k : ℕ) :
    (DirectProgram.seeds k).Valid (seedFun m h k) := by
  by_cases hk1 : k = 1
  · subst k
    exact seed_valid_001 m h
  by_cases hk299 : k = 299
  · subst k
    exact seed_valid_299 m h
  unfold DirectProgram.seeds
  split <;> first
  | contradiction
  | simpa only [seedFun, zero, Rat.cast_zero, *] using constant (0 : ℚ)
  | (convert constant _ using 1 <;> norm_num [
        *, DirectProgram.seeds, seedFun, zero, DirectDag.f2,
        DirectDag.f4, DirectDag.f8, DirectDag.f13, DirectDag.f18, DirectDag.f22,
        DirectDag.f26, DirectDag.f30, DirectDag.f33, DirectDag.f35, DirectDag.f38,
        DirectDag.f41, DirectDag.f44, DirectDag.f48, DirectDag.f50, DirectDag.f52,
        DirectDag.f57, DirectDag.f59, DirectDag.f61, DirectDag.f67, DirectDag.f72,
        DirectDag.f114, DirectDag.f116, DirectDag.f125, DirectDag.f127, DirectDag.f132,
        DirectDag.f135, DirectDag.f137, DirectDag.f140, DirectDag.f147, DirectDag.f151,
        DirectDag.f154, DirectDag.f157, DirectDag.f160, DirectDag.f163, DirectDag.f170,
        DirectDag.f206, DirectDag.f208, DirectDag.f211, DirectDag.f213, DirectDag.f217,
        DirectDag.f227, DirectDag.f291, DirectDag.f293, DirectDag.f296, Rat.cast_div,
        Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero, Rat.cast_neg])

end Hf4Quad.CheckedDag.DirectSemantics
#print axioms Hf4Quad.CheckedDag.DirectSemantics.seed_sound
