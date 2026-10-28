import MathlibNt.SieveTheory.LiLiuGoldbachG12LowHighOutput

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve

namespace G12LowHighOutput

/-- A closed real high cut is an open cut at the preceding natural number. -/
def highCut (N : ℕ) : ℝ := ((⌈(N : ℝ)^(1/10 : ℝ)⌉₊ - 1 : ℕ) : ℝ)

def highLo (N : ℕ) (ε : ℝ) (m : ℕ) : ℝ :=
  min (goldbachG11PiLiHi N m) (max (goldbachG11PiLiLo N ε m) (highCut N))

def highWindow (N : ℕ) (ε : ℝ) (m : ℕ) : Finset ℕ :=
  (goldbachG11LinkedPrimeWindow N ε m).filter fun r => (N : ℝ)^(1/10 : ℝ) ≤ r

theorem highCut_lt_iff (N r : ℕ) (hr : 0 < r) :
    highCut N < r ↔ (N : ℝ)^(1/10 : ℝ) ≤ r := by
  unfold highCut
  rw [Nat.cast_lt]
  have h : ⌈(N : ℝ)^(1/10 : ℝ)⌉₊ ≤ r ↔ (N : ℝ)^(1/10 : ℝ) ≤ r := Nat.ceil_le
  rw [← h]
  omega

theorem highLo_bounds {N m : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachG12ActiveProductSupport N) :
    goldbachG11PiLiLo N ε m ≤ highLo N ε m ∧ highLo N ε m ≤ goldbachG11PiLiHi N m := by
  exact ⟨le_min (goldbachG12PiLiEndpoints_bounds hN hm).2.1 (le_max_left _ _),
    min_le_left _ _⟩

/-- Literal closed-high prime window, not an arbitrary filtered SW assertion. -/
theorem mem_highWindow (N m r : ℕ) (ε : ℝ) :
    r ∈ highWindow N ε m ↔ r ∈ range (N+1) ∧ r.Prime ∧
      highLo N ε m < r ∧ (r : ℝ) ≤ goldbachG11PiLiHi N m := by
  simp only [highWindow, goldbachG11LinkedPrimeWindow, mem_filter]
  constructor
  · rintro ⟨⟨hr,hp,hlo,hhi⟩,ha⟩
    exact ⟨hr,hp,(min_le_right _ _).trans_lt
      (max_lt hlo ((highCut_lt_iff N r hp.pos).mpr ha)),hhi⟩
  · rintro ⟨hr,hp,hlo,hhi⟩
    have hmax : max (goldbachG11PiLiLo N ε m) (highCut N) < r := by
      rcases min_lt_iff.mp hlo with hbad | hgood
      · exact False.elim ((not_lt_of_ge hhi) hbad)
      · exact hgood
    exact ⟨⟨hr,hp,(max_lt_iff.mp hmax).1,hhi⟩,
      (highCut_lt_iff N r hp.pos).mp (max_lt_iff.mp hmax).2⟩


end G12LowHighOutput
