import Hf4QuadRatCore

/-! UNCOMPILED scratch interpreter. References are backward offsets into a
reverse topological environment; no Real values enter arithmetic checking. -/
namespace Hf4Quad.CheckedDag
open RationalModel

inductive Step where
  | variable
  | shared (index : ℕ)
  | neg (a : ℕ)
  | addExact (a b : ℕ)
  | scale (s : ℚ) (a : ℕ)
  | add (literal a b : ℕ)
  | mul (literal a b : ℕ)
  | inv (literal a : ℕ)
  deriving DecidableEq

def zero : Certificate := ⟨0,0,0,0,0⟩
def getCert (cs : List Certificate) (i : ℕ) : Certificate := cs[i]?.getD zero

def next (seeds literals : ℕ → Certificate) (m h : ℚ)
    (op : Step) (cs : List Certificate) : Certificate :=
  match op with
  | .variable => ⟨m,h,0,0,0⟩
  | .shared i => seeds i
  | .neg a => RationalModel.neg (getCert cs a)
  | .addExact a b => RationalModel.addExact (getCert cs a) (getCert cs b)
  | .scale s a => RationalModel.scale s (getCert cs a)
  | .add k _ _ | .mul k _ _ | .inv k _ => literals k

def checkStep (literals : ℕ → Certificate) (op : Step)
    (cs : List Certificate) : Bool :=
  match op with
  | .add k a b => decide (addCondition (getCert cs a) (getCert cs b) (literals k))
  | .mul k a b => decide (mulCondition (getCert cs a) (getCert cs b) (literals k))
  | .inv k a => decide (invCondition (getCert cs a) (literals k))
  | _ => true

def run (seeds literals : ℕ → Certificate) (m h : ℚ) :
    List Step → List Certificate → List Certificate
  | [], cs => cs
  | op::tail, cs => run seeds literals m h tail (next seeds literals m h op cs::cs)

def checked (seeds literals : ℕ → Certificate) (m h : ℚ) :
    List Step → List Certificate → Bool
  | [], _ => true
  | op::tail, cs => checkStep literals op cs &&
      checked seeds literals m h tail (next seeds literals m h op cs::cs)

/-- Independent chunk verification reconstructs the prefix but does not recheck
its arithmetic conditions. No single closed decision spans all381 nodes. -/
def checkRange (plan : List Step) (seeds literals : ℕ → Certificate)
    (m h : ℚ) (start width : ℕ) : Bool :=
  checked seeds literals m h ((plan.drop start).take width)
    (run seeds literals m h (plan.take start) [])

theorem run_append (seeds literals : ℕ → Certificate) (m h : ℚ)
    (a b : List Step) (cs : List Certificate) :
    run seeds literals m h (a++b) cs =
      run seeds literals m h b (run seeds literals m h a cs) := by
  induction a generalizing cs with
  | nil => rfl
  | cons op tail ih =>
    simpa only [List.cons_append, run] using
      ih (next seeds literals m h op cs :: cs)

theorem checked_append (seeds literals : ℕ → Certificate) (m h : ℚ)
    (a b : List Step) (cs : List Certificate) :
    checked seeds literals m h (a++b) cs =
      (checked seeds literals m h a cs &&
        checked seeds literals m h b (run seeds literals m h a cs)) := by
  induction a generalizing cs with
  | nil => simp [checked, run]
  | cons op tail ih => simp only [List.cons_append, checked, run, ih, Bool.and_assoc]

end Hf4Quad.CheckedDag
