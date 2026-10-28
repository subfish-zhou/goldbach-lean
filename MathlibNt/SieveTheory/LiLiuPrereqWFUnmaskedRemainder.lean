import MathlibNt.SieveTheory.LiLiuPrereqWFSignedRemainder
import MathlibNt.SieveTheory.LiLiuPrereqWFUnmaskedSupport

/-!
# Transport to full-modulus sums without masking the WF coefficients

The exact transport holds for arbitrary indexed sequences, including zeros
and multiplicities. Its quantitative version has separate, explicit sequence
hypotheses and uses the canonical arithmetic-progression density `1 / φ(d)`
on reduced residue classes. A prime-only dimension-one condition is never
used to control arbitrary prime-power densities.
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

variable {ι : Type*}

noncomputable def progressionDensity (a : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d.Coprime a then (d.totient : ℝ)⁻¹ else 0, by simp⟩


/-- Only the summation region changes. The arithmetic function in all three
sums is identical, with its non-squarefree extension intact. -/
theorem supported_sum_split_primorial {f : ArithmeticFunction ℝ} {Q : ℝ}
    (hQ : 0 ≤ Q) (hf : SupportedAt f Q) {M : ℕ} (hM : M ≠ 0) (r : ℕ → ℝ) :
    (∑ d ∈ Icc 1 ⌊Q⌋₊, f d * r d) =
      (∑ d ∈ M.divisors, f d * r d) +
        ∑ d ∈ (Icc 1 ⌊Q⌋₊).filter (fun d => ¬ d ∣ M), f d * r d := by
  have heq :
      (∑ d ∈ (Icc 1 ⌊Q⌋₊).filter (fun d => d ∣ M), f d * r d) =
        ∑ d ∈ M.divisors, f d * r d := by
    apply sum_subset
    · intro d hd
      exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hd).2, hM⟩
    · intro d hd hnot
      have hzero : f d = 0 := by
        by_contra hn
        have hd0 : 0 < d := Nat.pos_of_dvd_of_pos (Nat.dvd_of_mem_divisors hd)
          (Nat.pos_of_ne_zero hM)
        exact hnot (mem_filter.mpr ⟨mem_Icc.mpr
          ⟨hd0, (Nat.le_floor_iff hQ).mpr (hf d hn)⟩, Nat.dvd_of_mem_divisors hd⟩)
      simp [hzero]
  rw [← heq, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro d _
  split_ifs <;> simp


end MathlibNt.SieveTheory.LiLiuPrereqWF
