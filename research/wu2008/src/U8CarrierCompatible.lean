import U8Geometry
import MathlibNt.Wu2008DoubleSieve.SeventhEighthFixedGeometry

/-! Canonical provider adapter. All shared data and public helpers are imported.
The unique closed-form witness retains its original statement and proof. -/
noncomputable section
open Finset
open scoped Classical
namespace U8SourceWitness
/-- Closed formula witnesses the original legacy carrier, including all bounds and masks. -/
theorem physicalT8_closed_formula (N : ℕ) :
    Wu2008DoubleSieve.SeventhEighth.physicalT8 N =
    (((
      ((Finset.range ⌈(N : ℝ) + 1⌉₊).filter
        (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N : ℝ)^(100/1327 : ℝ) ≤ (q : ℝ))) ×ˢ
      ((Finset.range ⌈(N : ℝ) + 1⌉₊).filter
        (fun q : ℕ => q.Prime ∧ q.Coprime N ∧ (N : ℝ)^(1/3 : ℝ) ≤ (q : ℝ)))).filter
      (fun t => t.1 < t.2 ∧ t.1*t.2^2 < N)).filter
      (fun t => (t.1 : ℝ) < (N : ℝ)^(1/3 : ℝ))).sigma
      (fun t => (Finset.range (N+1)).filter
        (fun r => r.Prime ∧ t.2 ≤ r ∧ t.1*t.2*r < N ∧ (N-t.1*t.2*r).Prime)) := rfl
end U8SourceWitness
