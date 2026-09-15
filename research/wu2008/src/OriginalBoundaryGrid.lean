import OriginalMassKernel
import MathlibNt.SieveTheory.LiLiuFouvryG9WeightedBoundaryKernel

noncomputable section
open scoped BigOperators Topology Interval
open Filter Finset MeasureTheory Set
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle
namespace OriginalU8.Weighted

/-- The left source endpoint is a parameter; the ambient grid is unchanged. -/
def cells (a : ℝ) (n : ℕ) (h : ℝ) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun q =>
    a ≤ goldbachB9AlphaGridPoint n (q.1+1) ∧
    goldbachB9AlphaGridPoint n q.1 < (1/10 : ℝ) ∧
    (1/3 : ℝ) ≤ goldbachB9BetaGridPoint n (q.2+1) ∧
    goldbachB9AlphaGridPoint n q.1 + 2*goldbachB9BetaGridPoint n q.2 < 1+h

def grid (a : ℝ) (n N : ℕ) (h δ : ℝ) : ℝ :=
  ∑ q ∈ cells a n h, fouvryG9RelaxedIntegralCorner n δ q *
    primeReciprocalLogRectangle N
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))

def upperSum (a : ℝ) (n : ℕ) (h δ : ℝ) : ℝ :=
  ∑ q ∈ cells a n h, fouvryG9RelaxedIntegralCorner n δ q *
    logarithmicRectangleMass
      (goldbachB9AlphaGridPoint n q.1) (goldbachB9AlphaGridPoint n (q.1+1))
      (goldbachB9BetaGridPoint n q.2) (goldbachB9BetaGridPoint n (q.2+1))

theorem fixed_grid_tendsto (a : ℝ) (n : ℕ) (hn : 0 < n) (h δ : ℝ) :
    Tendsto (fun N => grid a n N h δ) atTop (nhds (upperSum a n h δ)) := by
  unfold grid upperSum
  apply tendsto_weighted_sum_primeReciprocalLogRectangle
  · intro q _; exact goldbachB9AlphaGridPoint_pos n q.1
  · intro q _; exact goldbachB9AlphaGridPoint_lt_succ hn
  · intro q _; exact goldbachB9BetaGridPoint_pos n q.2
  · intro q _; exact goldbachB9BetaGridPoint_lt_succ hn

theorem selected_cell_geometry {a : ℝ} {n : ℕ} {h u v : ℝ}
    (q : Fin n × Fin n) (hq : q ∈ cells a n h)
    (hu : u ∈ Ioc (goldbachB9AlphaGridPoint n q.1)
      (goldbachB9AlphaGridPoint n (q.1+1)))
    (hv : v ∈ Ioc (goldbachB9BetaGridPoint n q.2)
      (goldbachB9BetaGridPoint n (q.2+1))) :
    a-goldbachB9AlphaGridStep n < u ∧
    u < 1/10+goldbachB9AlphaGridStep n ∧
    1/3-goldbachB9BetaGridStep n < v ∧
    u+2*v < 1+h+goldbachB9AlphaGridStep n+2*goldbachB9BetaGridStep n := by
  classical
  obtain ⟨_, ha, hb, hc, hd⟩ := Finset.mem_filter.mp hq
  rw [goldbachB9AlphaGridPoint_succ] at ha
  rw [goldbachB9BetaGridPoint_succ] at hc
  have huu := hu.2
  have hvv := hv.2
  rw [goldbachB9AlphaGridPoint_succ] at huu
  rw [goldbachB9BetaGridPoint_succ] at hvv
  exact ⟨by linarith [hu.1], by linarith, by linarith [hv.1], by linarith⟩

/-- This is the literal iterated integral, without a hidden normalization. -/
def low (a : ℝ) : ℝ :=
  ∫ u in a..(1/10 : ℝ),
    ∫ v in (1/3 : ℝ)..((1-u)/2), 1/(u*v*(1-u-v)*(1-u))

end OriginalU8.Weighted
