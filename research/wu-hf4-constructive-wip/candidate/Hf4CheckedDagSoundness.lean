import Hf4CheckedDagData
import Hf4QuadExactOperations

/-! UNCOMPILED proof draft. No new axiom, admission, or external evaluator.
The remaining program-to-original-f380 bridge is a separate required theorem. -/
namespace Hf4Quad.CheckedDag
open RationalModel

def getFun (fs : List (ℝ → ℝ)) (i : ℕ) : ℝ → ℝ := fs[i]?.getD (fun _ => 0)
def EnvValid (cs : List Certificate) (fs : List (ℝ → ℝ)) : Prop :=
  ∀ i, (getCert cs i).Valid (getFun fs i)

noncomputable def nextFun (seeds : ℕ → ℝ → ℝ) (m h : ℚ)
    (op : Step) (fs : List (ℝ → ℝ)) : ℝ → ℝ :=
  match op with
  | .variable => fun x => (m:ℝ)+(h:ℝ)*x
  | .shared i => seeds i
  | .neg a => fun x => -getFun fs a x
  | .addExact a b | .add _ a b => fun x => getFun fs a x+getFun fs b x
  | .scale s a => fun x => (s:ℝ)*getFun fs a x
  | .mul _ a b => fun x => getFun fs a x*getFun fs b x
  | .inv _ a => fun x => (getFun fs a x)⁻¹

noncomputable def runFun (seeds : ℕ → ℝ → ℝ) (m h : ℚ) :
    List Step → List (ℝ → ℝ) → List (ℝ → ℝ)
  | [], fs => fs
  | op::tail, fs => runFun seeds m h tail (nextFun seeds m h op fs::fs)

theorem next_sound (seeds literals : ℕ → Certificate)
    (seedFun : ℕ → ℝ → ℝ) (m h : ℚ)
    (seedSound : ∀ k, (seeds k).Valid (seedFun k))
    (op : Step) (cs : List Certificate) (fs : List (ℝ → ℝ))
    (env : EnvValid cs fs) (ok : checkStep literals op cs = true) :
    (next seeds literals m h op cs).Valid (nextFun seedFun m h op fs) := by
  cases op with
  | «variable» => exact variableModel m h
  | shared k => exact seedSound k
  | neg a => exact (env a).neg
  | addExact a b => exact (env a).addExact (env b)
  | scale s a => exact (env a).scale s
  | add k a b => exact (env a).add (env b) (of_decide_eq_true ok)
  | mul k a b => exact (env a).mul (env b) (of_decide_eq_true ok)
  | inv k a => exact (env a).inv (of_decide_eq_true ok)

theorem cons_valid {cs : List Certificate} {fs : List (ℝ → ℝ)}
    {p : Certificate} {f : ℝ → ℝ} (hp : p.Valid f) (he : EnvValid cs fs) :
    EnvValid (p::cs) (f::fs) := by
  intro i
  cases i with
  | zero => simpa only [getCert, getFun, List.getElem?_cons_zero, Option.getD_some] using hp
  | succ i => simpa only [getCert, getFun, List.getElem?_cons_succ] using he i

theorem nil_valid : EnvValid [] [] := by
  intro i
  simpa [getCert, getFun, zero] using constant (0:ℚ)

theorem run_sound (seeds literals : ℕ → Certificate)
    (seedFun : ℕ → ℝ → ℝ) (m h : ℚ)
    (seedSound : ∀ k, (seeds k).Valid (seedFun k))
    (ops : List Step) (cs : List Certificate) (fs : List (ℝ → ℝ))
    (env : EnvValid cs fs) (ok : checked seeds literals m h ops cs = true) :
    EnvValid (run seeds literals m h ops cs) (runFun seedFun m h ops fs) := by
  induction ops generalizing cs fs with
  | nil => exact env
  | cons op tail ih =>
    have ho : checkStep literals op cs = true ∧
        checked seeds literals m h tail (next seeds literals m h op cs::cs) = true :=
      Bool.and_eq_true_iff.mp ok
    exact ih _ _ (cons_valid (next_sound seeds literals seedFun m h seedSound op cs fs env ho.1) env) ho.2

end Hf4Quad.CheckedDag
