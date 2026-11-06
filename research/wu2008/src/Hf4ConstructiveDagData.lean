import Hf4CheckedDagData
import Hf4ConstructionConditions

/-! UNCOMPILED full constructor: add, mul and inv all compute their original
D=10^14 rounded records. Only positive-lower inverse guards are checked.
No literal-certificate function, payload parameter or inverse records. -/
namespace Hf4Quad.ConstructiveDag
open CheckedDag
open RationalModel

def next (seeds : ℕ → Certificate) (m h : ℚ)
    (op : Step) (cs : List Certificate) : Certificate :=
  match op with
  | .variable => ⟨m,h,0,0,0⟩
  | .shared i => seeds i
  | .neg a => RationalModel.neg (getCert cs a)
  | .addExact a b => RationalModel.addExact (getCert cs a) (getCert cs b)
  | .scale s a => RationalModel.scale s (getCert cs a)
  | .add _ a b => Construction.constructAdd (getCert cs a) (getCert cs b)
  | .mul _ a b => Construction.constructMul (getCert cs a) (getCert cs b)
  | .inv _ a => Construction.constructInv (getCert cs a)

def checkStep (op : Step)
    (cs : List Certificate) : Bool :=
  match op with
  | .inv _ a => decide (0 < lower (getCert cs a))
  | _ => true

def run (seeds : ℕ → Certificate) (m h : ℚ) :
    List Step → List Certificate → List Certificate
  | [], cs => cs
  | op::tail, cs => run seeds m h tail (next seeds m h op cs::cs)

def checked (seeds : ℕ → Certificate) (m h : ℚ) :
    List Step → List Certificate → Bool
  | [], _ => true
  | op::tail, cs => checkStep op cs &&
      checked seeds m h tail (next seeds m h op cs::cs)

/-- Optional bounded-range interface retained for resource fallback. -/
def checkRange (plan : List Step) (seeds : ℕ → Certificate)
    (m h : ℚ) (start width : ℕ) : Bool :=
  checked seeds m h ((plan.drop start).take width)
    (run seeds m h (plan.take start) [])

theorem run_append (seeds : ℕ → Certificate) (m h : ℚ)
    (a b : List Step) (cs : List Certificate) :
    run seeds m h (a++b) cs =
      run seeds m h b (run seeds m h a cs) := by
  induction a generalizing cs with
  | nil => rfl
  | cons op tail ih =>
    simpa only [List.cons_append, run] using
      ih (next seeds m h op cs :: cs)

theorem checked_append (seeds : ℕ → Certificate) (m h : ℚ)
    (a b : List Step) (cs : List Certificate) :
    checked seeds m h (a++b) cs =
      (checked seeds m h a cs &&
        checked seeds m h b (run seeds m h a cs)) := by
  induction a generalizing cs with
  | nil => simp [checked, run]
  | cons op tail ih => simp only [List.cons_append, checked, run, ih, Bool.and_assoc]

end Hf4Quad.ConstructiveDag
