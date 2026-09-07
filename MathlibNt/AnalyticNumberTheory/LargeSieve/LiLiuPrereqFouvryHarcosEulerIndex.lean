import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosEulerRoots

/-! # The finite Euler index for comparison with minimal-polynomial orbits -/

noncomputable section

open Finset
open scoped Polynomial

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable {p : ℕ} [Fact p.Prime]

/-- Monic irreducibles with nonzero constant coefficient and degree dividing `n`. -/
def harcosEulerNonzeroPrimes (p n : ℕ) [Fact p.Prime] : Finset (ZMod p)[X] := by
  classical
  exact (harcosEulerPrimes p n).filter fun k ↦ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n

theorem mem_harcosEulerNonzeroPrimes (n : ℕ) (hn : n ≠ 0) (k : (ZMod p)[X]) :
    k ∈ harcosEulerNonzeroPrimes p n ↔
      k.Monic ∧ Irreducible k ∧ k.coeff 0 ≠ 0 ∧ k.natDegree ∣ n := by
  classical
  simp only [harcosEulerNonzeroPrimes, mem_filter, mem_harcosEulerPrimes]
  constructor
  · exact fun ⟨⟨hm, hi, _⟩, hc, hd⟩ ↦ ⟨hm, hi, hc, hd⟩
  · rintro ⟨hm, hi, hc, hd⟩
    exact ⟨⟨hm, hi, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hc, hd⟩

theorem harcosEulerLogCoefficient_eq_flat (η : (ZMod p)[X] →* ℂ) (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient η n =
      ∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
        (k.natDegree : ℂ) * η k ^ (n / k.natDegree) := by
  classical
  rw [← harcosEulerLog_coeff η n n le_rfl, harcosEulerLog, map_sum, sum_filter]
  apply sum_congr rfl
  intro k _
  simp only [PowerSeries.coeff_C_mul, map_sub, harcosEulerGeometric,
    PowerSeries.coeff_mk, PowerSeries.coeff_one, if_neg hn, sub_zero]
  split_ifs <;> simp

/-- The exact flat, nonzero-root index used by the finite-field orbit sum. -/
theorem harcosEuler_character_eq_nonzeroPrime_sum (a b : ZMod p)
    (n : ℕ) (hn : n ≠ 0) :
    harcosEulerLogCoefficient (harcosEtaHom a b).toMonoidHom n =
      ∑ k ∈ harcosEulerNonzeroPrimes p n,
        (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree) := by
  classical
  rw [harcosEulerLogCoefficient_eq_flat _ n hn]
  change (∑ k ∈ (harcosEulerPrimes p n).filter (fun k ↦ k.natDegree ∣ n),
    (k.natDegree : ℂ) * harcosEta a b k ^ (n / k.natDegree)) = _
  symm
  apply sum_subset
  · intro k hk
    obtain ⟨hkm, hki, hc, hd⟩ := (mem_harcosEulerNonzeroPrimes n hn k).mp hk
    exact mem_filter.mpr ⟨(mem_harcosEulerPrimes n k).mpr
      ⟨hkm, hki, Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hd⟩, hd⟩
  · intro k hk hkn
    obtain ⟨hkp, hd⟩ := mem_filter.mp hk
    obtain ⟨hkm, hki, hle⟩ := (mem_harcosEulerPrimes n k).mp hkp
    have hc : k.coeff 0 = 0 := by
      by_contra h
      exact hkn ((mem_harcosEulerNonzeroPrimes n hn k).mpr ⟨hkm, hki, h, hd⟩)
    have he : n / k.natDegree ≠ 0 := by
      have := Nat.div_pos hle hki.natDegree_pos
      omega
    simp [harcosEta, hc, he]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
