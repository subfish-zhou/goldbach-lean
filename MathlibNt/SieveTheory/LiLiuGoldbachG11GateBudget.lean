import MathlibNt.SieveTheory.FiniteCoprimeGateBudget
import MathlibNt.SieveTheory.FiniteRealWindows
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindow
import MathlibNt.Wu2004MeanValue.RealEndpoints


open scoped BigOperators Topology
open Classical Finset Filter
open AnalyticNumberTheory.LargeSieve

noncomputable section



namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

theorem goldbachG11EffectiveProductSupport_primeFactors {N m : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε) :
    (∀ p ∈ m.primeFactors, (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ)) ∧
      m.primeFactors = largePrimeDivisors m ((N : ℝ) ^ (4 / 53 : ℝ)) ∧
      m.primeFactors.card ≤ 20 := by
  obtain ⟨hm0, hmN, _, hz⟩ := goldbachG11ProductSupport_data (mem_filter.mp hm).1
  have hf : ∀ p ∈ m.primeFactors, (N : ℝ) ^ (4 / 53 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpp, hpm, _⟩ := Nat.mem_primeFactors.mp hp
    exact hz.trans (by exact_mod_cast Nat.minFac_le_of_dvd hpp.two_le hpm)
  have heq : m.primeFactors = largePrimeDivisors m ((N : ℝ) ^ (4 / 53 : ℝ)) := by
    symm
    exact filter_eq_self.mpr hf
  refine ⟨hf, heq, ?_⟩
  rw [heq]
  exact largePrimeDivisors_card_le_twenty hm0 hmN
    (by norm_num : (1 : ℝ) / 21 < 4 / 53)


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig