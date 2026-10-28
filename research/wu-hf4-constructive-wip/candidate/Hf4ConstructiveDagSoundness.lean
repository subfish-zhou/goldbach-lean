import Hf4ConstructiveDagData
import Hf4CheckedDagSoundness

/-! UNCOMPILED full-constructor soundness. The old positive lower bound
is the only checked inverse premise; inv_condition proves the full enclosure. -/
namespace Hf4Quad.ConstructiveDag
open CheckedDag
open RationalModel

theorem next_sound (seeds : ℕ → Certificate)
    (seedFun : ℕ → ℝ → ℝ) (m h : ℚ)
    (seedSound : ∀ k, (seeds k).Valid (seedFun k))
    (op : Step) (cs : List Certificate) (fs : List (ℝ → ℝ))
    (env : EnvValid cs fs) (ok : checkStep op cs = true) :
    (next seeds m h op cs).Valid (nextFun seedFun m h op fs) := by
  cases op with
  | «variable» => exact variableModel m h
  | shared k => exact seedSound k
  | neg a => exact (env a).neg
  | addExact a b => exact (env a).addExact (env b)
  | scale s a => exact (env a).scale s
  | add k a b => exact (env a).add (env b) (Construction.add_condition _ _)
  | mul k a b => exact (env a).mul (env b) (Construction.mul_condition _ _)
  | inv k a => exact (env a).inv (Construction.inv_condition _ (of_decide_eq_true ok))

theorem run_sound (seeds : ℕ → Certificate)
    (seedFun : ℕ → ℝ → ℝ) (m h : ℚ)
    (seedSound : ∀ k, (seeds k).Valid (seedFun k))
    (ops : List Step) (cs : List Certificate) (fs : List (ℝ → ℝ))
    (env : EnvValid cs fs) (ok : checked seeds m h ops cs = true) :
    EnvValid (run seeds m h ops cs) (runFun seedFun m h ops fs) := by
  induction ops generalizing cs fs with
  | nil => exact env
  | cons op tail ih =>
    have ho : checkStep op cs = true ∧
        checked seeds m h tail (next seeds m h op cs::cs) = true :=
      Bool.and_eq_true_iff.mp ok
    exact ih _ _ (cons_valid (next_sound seeds seedFun m h seedSound op cs fs env ho.1) env) ho.2

end Hf4Quad.ConstructiveDag
