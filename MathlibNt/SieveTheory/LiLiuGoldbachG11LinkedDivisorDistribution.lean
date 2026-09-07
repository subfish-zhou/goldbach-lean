import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedDistribution
import MathlibNt.SieveTheory.LiLiuGoldbachG11LinkedWindowAP

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Finset
open scoped BigOperators
open AnalyticNumberTheory.LargeSieve

/-- An inadmissible cofactor contributes no actual output divisible by d. -/
theorem goldbachG11Linked_outputDivisors_empty {N m d : ℕ} {ε : ℝ}
    (hm : m ∈ goldbachG11EffectiveProductSupport N ε)
    (hNd : N.Coprime d) (hmd : ¬ m.Coprime d) :
    (goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m) = ∅ := by
  classical
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  obtain ⟨hr, hd⟩ := mem_filter.mp hr
  have hgout : Nat.gcd m d ∣ N-r*m := dvd_trans (Nat.gcd_dvd_right m d) hd
  have hgrm : Nat.gcd m d ∣ r*m := dvd_mul_of_dvd_right (Nat.gcd_dvd_left m d) r
  have hgN := Nat.dvd_add hgout hgrm
  rw [Nat.sub_add_cancel (goldbachG11LinkedPrimeWindow_product_le hm hr)] at hgN
  have hg := Nat.dvd_gcd hgN (Nat.gcd_dvd_right m d)
  rw [hNd.gcd_eq_one] at hg
  exact hmd (Nat.dvd_one.mp hg)

/-- Literal weighted divisor count of the geometric output mother, minus its
coprime-gated prime-window main term. The counting sum runs over the whole E. -/
noncomputable def goldbachG11LinkedDivisorResidual (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG11EffectiveProductSupport N ε,
    goldbachG11EffectiveProductCoefficient N ε m *
      (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
  (∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => m.Coprime d),
    goldbachG11EffectiveProductCoefficient N ε m *
      (PanPrincipal.primeCount ⌊goldbachG11PiLiHi N m⌋₊ -
        PanPrincipal.primeCount ⌊goldbachG11PiLiLo N ε m⌋₊)) / (d.totient : ℝ)

theorem goldbachG11LinkedDivisorResidual_eq {N : ℕ} (hN : 2 ≤ N)
    (ε : ℝ) (d : ℕ) (hNd : N.Coprime d) :
    goldbachG11LinkedDivisorResidual N ε d = goldbachG11LinkedWindowResidual N ε d N := by
  classical
  have hc : (∑ m ∈ goldbachG11EffectiveProductSupport N ε,
      goldbachG11EffectiveProductCoefficient N ε m *
        (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) =
      ∑ m ∈ (goldbachG11EffectiveProductSupport N ε).filter (fun m => m.Coprime d),
      goldbachG11EffectiveProductCoefficient N ε m *
        (((goldbachG11LinkedPrimeWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    by_cases hmd : m.Coprime d
    · simp only [if_pos hmd]
    · rw [if_neg hmd, goldbachG11Linked_outputDivisors_empty hm hNd hmd]
      simp
  unfold goldbachG11LinkedDivisorResidual goldbachG11LinkedWindowResidual
  rw [hc, Finset.sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm, hmd⟩ := mem_filter.mp hm
  have hcount := goldbachG11LinkedAPWindow_card_eq_inverse d N hN hm hmd
  rw [goldbachG11LinkedAPWindow_eq_output_dvd d hm] at hcount
  rw [hcount]
  ring

/-- An unconditional distribution estimate for the actual output-divisor count.
The sole remaining level restriction is the proved source's sqrt(N)/log(N)^B. -/
theorem goldbachG11LinkedDivisorResidual_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q,
        |goldbachG11LinkedDivisorResidual N ε d|) ≤ C*N / Real.log (N : ℝ)^A := by
  obtain ⟨B, C, hB, hC, N₀, hN₀, hbound⟩ := goldbachG11LinkedWindowResidual_squarefree A hA
  refine ⟨B, C, hB, hC, N₀, hN₀, ?_⟩
  intro N hN ε Q hQ
  have hN2 : 2 ≤ N := by omega
  have heq : (∑ d ∈ goldbachG11LinkedModuli N Q,
      |goldbachG11LinkedDivisorResidual N ε d|) =
      ∑ d ∈ goldbachG11LinkedModuli N Q, |goldbachG11LinkedWindowResidual N ε d N| := by
    apply sum_congr rfl
    intro d hd
    rw [goldbachG11LinkedDivisorResidual_eq hN2 ε d (mem_filter.mp hd).2.2]
  rw [heq]
  exact hbound N hN ε Q hQ

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig