import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighOmega
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryParameters

/-!
# A signed factorization and its high-omega deletion

The original weight is well-factorable at its original level, with closed
factor supports. Only one legitimate split is chosen. Deleting high omega
from the second factor produces a convolution, not a new well-factorable
weight. Its discarded part has an actual divisor majorant and high-omega
modulus support.
-/

noncomputable section
open Classical Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

def factorConvolution (γ ζ : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ p ∈ q.divisorsAntidiagonal, γ p.1 * ζ p.2

def factorSupported (R : ℝ) (γ : ℕ → ℝ) : Prop :=
  ∀ n, γ n ≠ 0 → 0 < n ∧ (n : ℝ) ≤ R

/-- The input weight itself has the stated order. The quantifier over splits
comes after that single weight, and includes a factor level equal to one. -/
def SignedWellFactorable (k : ℕ) (L : ℝ) (c : ℕ → ℝ) : Prop :=
  (∀ q, |c q| ≤ (fouvryTau k q : ℝ)) ∧
    ∀ R S : ℝ, 1 ≤ R → 1 ≤ S → R * S = L →
      ∃ γ ζ : ℕ → ℝ,
        factorSupported R γ ∧ factorSupported S ζ ∧
        (∀ r, |γ r| ≤ (fouvryTau k r : ℝ)) ∧
        (∀ s, |ζ s| ≤ (fouvryTau k s : ℝ)) ∧ c = factorConvolution γ ζ

theorem factorConvolution_abs_le (j k : ℕ) (γ ζ : ℕ → ℝ)
    (hγ : ∀ r, |γ r| ≤ (fouvryTau j r : ℝ))
    (hζ : ∀ s, |ζ s| ≤ (fouvryTau k s : ℝ)) (q : ℕ) :
    |factorConvolution γ ζ q| ≤ (fouvryTau (j + k) q : ℝ) := by
  calc
    _ ≤ ∑ p ∈ q.divisorsAntidiagonal, |γ p.1 * ζ p.2| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ q.divisorsAntidiagonal,
        (fouvryTau j p.1 : ℝ) * fouvryTau k p.2 := by
      apply sum_le_sum
      intro p _
      rw [abs_mul]
      exact mul_le_mul (hγ _) (hζ _) (abs_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by
      simp only [fouvryTau, pow_add, ArithmeticFunction.mul_apply,
        Nat.cast_sum, Nat.cast_mul]

theorem factorConvolution_supported {R S : ℝ} {γ ζ : ℕ → ℝ}
    (hγ : factorSupported R γ) (hζ : factorSupported S ζ) :
    factorSupported (R * S) (factorConvolution γ ζ) := by
  intro q hq
  by_contra h
  apply hq
  apply sum_eq_zero
  intro p hp
  obtain ⟨hpq, hq0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  by_cases hg : γ p.1 = 0
  · simp [hg]
  by_cases hz : ζ p.2 = 0
  · simp [hz]
  obtain ⟨_, hr⟩ := hγ _ hg
  obtain ⟨_, hs⟩ := hζ _ hz
  have hprod : (q : ℝ) ≤ R * S := by
    rw [← hpq, Nat.cast_mul]
    exact mul_le_mul hr hs (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hr)
  exact (h ⟨Nat.pos_of_ne_zero hq0, hprod⟩).elim

theorem factorConvolution_eq_low_add_high (γ ζ : ℕ → ℝ) (ξ : ℝ) :
    factorConvolution γ ζ =
      fun q => factorConvolution γ (betaLowOmega ζ ξ) q +
        factorConvolution γ (betaHighOmega ζ ξ) q := by
  funext q
  unfold factorConvolution
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  rw [← mul_add, ← beta_eq_lowOmega_add_highOmega]

theorem factorConvolution_sub_low (γ ζ : ℕ → ℝ) (ξ : ℝ) :
    (fun q => factorConvolution γ ζ q -
      factorConvolution γ (betaLowOmega ζ ξ) q) =
      factorConvolution γ (betaHighOmega ζ ξ) := by
  funext q
  have h := congrFun (factorConvolution_eq_low_add_high γ ζ ξ) q
  linarith

theorem factorConvolution_high_nonzero {γ ζ : ℕ → ℝ} {ξ : ℝ} {q : ℕ}
    (h : factorConvolution γ (betaHighOmega ζ ξ) q ≠ 0) :
    ξ < (q.primeFactors.card : ℝ) := by
  by_contra hq
  apply h
  apply sum_eq_zero
  intro p hp
  obtain ⟨he, hn⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hd : p.2 ∣ q := ⟨p.1, by simpa [mul_comm] using he.symm⟩
  have hc : (p.2.primeFactors.card : ℝ) ≤ (q.primeFactors.card : ℝ) := by
    exact_mod_cast card_le_card (Nat.primeFactors_mono hd hn)
  have hh : ¬ξ < (p.2.primeFactors.card : ℝ) := by linarith
  simp [betaHighOmega, hh]

theorem factorLowOmega_supported {S : ℝ} {ζ : ℕ → ℝ}
    (hζ : factorSupported S ζ) (ξ : ℝ) :
    factorSupported S (betaLowOmega ζ ξ) := by
  intro n hn
  apply hζ
  intro hz
  exact hn (by simp [betaLowOmega, hz])

theorem factorLowOmega_eq_self_at_one {ζ : ℕ → ℝ}
    (hζ : factorSupported 1 ζ) {ξ : ℝ} (hξ : 0 ≤ ξ) :
    betaLowOmega ζ ξ = ζ := by
  funext n
  by_cases hz : ζ n = 0
  · simp [betaLowOmega, hz]
  obtain ⟨hn, hle⟩ := hζ n hz
  have hn1 : n = 1 := by
    have : n ≤ 1 := by exact_mod_cast hle
    omega
  simp [betaLowOmega, hn1, hξ]

/-- The original level is preserved exactly, including the near-endpoint
branch where the second factor is supported only at one. -/
theorem SignedWellFactorable.c2_split {k : ℕ} {x ν ε : ℝ} {c : ℕ → ℝ}
    (hc : SignedWellFactorable k (x ^ ((5 - 5 * ν) / 9 - ε)) c)
    (hx : 1 ≤ x) (hε : 0 ≤ ε) (hεν : ε ≤ ν) (hν : ν ≤ 1 / 10) :
    let R := x ^ c2RExponent ν ε
    let S := x ^ c2SExponent ν ε
    R * S = x ^ ((5 - 5 * ν) / 9 - ε) ∧
      ∃ γ ζ : ℕ → ℝ,
        factorSupported R γ ∧ factorSupported S ζ ∧
        (∀ r, |γ r| ≤ (fouvryTau k r : ℝ)) ∧
        (∀ s, |ζ s| ≤ (fouvryTau k s : ℝ)) ∧ c = factorConvolution γ ζ := by
  obtain ⟨hR, hS, hRS, _⟩ := c2_factor_levels hx hε hεν hν
  exact ⟨hRS, hc.2 _ _ hR hS hRS⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
