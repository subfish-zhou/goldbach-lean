import SecondFunctionalUnitKernelOscillation
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalReciprocalGridStep
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelUniform

open scoped BigOperators Classical
namespace SecondFunctionalUnitMasked
open Set MeasureTheory Wu2008DoubleSieve SecondFunctionalUnitKernel

noncomputable def sample {m r : ℕ} (k : ℕ) (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool)
    (a : GridIndex (m+1) k) : ℝ := G phi b C gamma strict (gridCenter a)

noncomputable def primeSum {m r : ℕ} (R phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool) : ℝ :=
  ∑ f : Fin (m+1) → primeSlabPrimes R,
    primeSlabWeight R f * G phi b C gamma strict (gridCoordinates R f)

noncomputable def integral {m r : ℕ} (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool) : ℝ :=
  ∫ t in continuousCube (m+1), G phi b C gamma strict t * continuousDensity t

noncomputable def envelope {m r : ℕ} (h phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) : ℝ :=
  100*(m+1 : ℝ)*h +
  (if |phi - ∑ i, t i - t (Fin.last m)| ≤ (m+2 : ℝ)*h then 10 else 0) +
  (if |phi - ∑ i, t i - b| ≤ (m+1 : ℝ)*h then 10 else 0) +
  ∑ q, (if |dot (C q) t - gamma q| ≤ (∑ i, |C q i|)*h then 10 else 0)

theorem sample_bound {m r : ℕ} (k : ℕ) (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool)
    (a : GridIndex (m+1) k) : |sample k phi b C gamma strict a| ≤ 10 := by
  have hr := G_range phi b C gamma strict
    (gridClosed_subset_cube a (gridCell_subset_closed a (gridCenter_mem a)))
  exact (abs_of_nonneg hr.1).trans_le hr.2

/-- Actual center sampling, including every closed jump band. -/
theorem sampling_pointwise {m r : ℕ} (k : ℕ) (phi b : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (strict : Fin r → Bool)
    {t : Fin (m+1) → ℝ} (ht : t ∈ continuousCube (m+1)) :
    |G phi b C gamma strict t - gridStep (sample k phi b C gamma strict) t| ≤
      envelope (gridWidth k) phi b C gamma t := by
  obtain ⟨a, ha, _⟩ := (gridCell_partition (k := k)).mp ht
  rw [gridStep_on_cell _ a ha]
  exact G_oscillation phi b C gamma strict t (gridCenter a) (gridWidth_pos k).le ht
    (gridClosed_subset_cube a (gridCell_subset_closed a (gridCenter_mem a)))
    (gridCell_oscillation ha (gridCenter_mem a))

end SecondFunctionalUnitMasked
