import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import MathlibNt.SieveTheory.LiLiuGoldbachG11PiLiEndpoints
import MathlibNt.Wu2004MeanValue.PrimeCenteredDistribution

/-!
# G11 geometric prime-window distribution from a proved common profile

The two complete prime-count-centered prefixes use the same effective
support, coefficient and source constants. No output-prime condition is
inserted into the coefficient.
-/

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.Sieve _root_.AnalyticNumberTheory.LargeSieve
open Wu2004MeanValue

noncomputable section

theorem goldbachG11Linked_balanced_support {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    (N : ℝ) ^ (4 / 53 : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) ≤ (N : ℝ) ^ (1 - (4 / 53 : ℝ)) := by
  obtain ⟨hs, _, hu⟩ := Finset.mem_filter.mp hm
  obtain ⟨hpos, _, _, hfac⟩ := goldbachG11ProductSupport_data hs
  constructor
  · apply hfac.trans
    exact_mod_cast Nat.le_of_dvd hpos (Nat.minFac_dvd m)
  · have he : (1 - (4 / 53 : ℝ)) = 49 / 53 := by norm_num
    rw [he]
    exact hu.le


def goldbachG11LinkedCompletedResidue (N d : ℕ) : ℕ :=
  if N.Coprime d then N else 1

theorem goldbachG11LinkedCompletedResidue_coprime (N d : ℕ) :
    (goldbachG11LinkedCompletedResidue N d).Coprime d := by
  unfold goldbachG11LinkedCompletedResidue
  by_cases h : N.Coprime d
  · simpa only [if_pos h] using h
  · rw [if_neg h]
    exact Nat.coprime_one_left d

theorem goldbachG11LinkedCompletedResidue_eq {N d : ℕ} (h : N.Coprime d) :
    goldbachG11LinkedCompletedResidue N d = N := by
  exact if_pos h

def goldbachG11LinkedModuli (N Q : ℕ) : Finset ℕ :=
  (Icc 1 Q).filter (fun d => Squarefree d ∧ N.Coprime d)

theorem goldbachG11Linked_one_le_weight {d : ℕ} (hd : Squarefree d) :
    1 ≤ wuModulusWeight d := by
  rw [wuModulusWeight, (show (((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2) = 1 by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd), one_mul]
  exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3)


end
end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig