

import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal

/-!
 # Finite Vaughan decomposition and primitive-character prefix reduction

This module is a purely finite algebraic layer between Vaughan's identity and
`weighted_primitive_prefix_maximal`.  It makes no Bombieri--Vinogradov claim and
introduces no analytic hypothesis.

For arbitrary cutoffs `u,v`, the exact all-`n` decomposition is

`Λ n = TypeI(n;u,v) + TypeII(n;u,v) + Small(n;v)`.

Here Type I is `vaughanFirst - vaughanMiddle`, Type II is `vaughanThird`, and
the last term retains the complete exceptional range `n ≤ v`.  The final
theorem consumes this equality inside every primitive-character prefix and
reduces its weighted square maximum to three explicit coefficient energies.
No cutoff is selected or hidden.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The two Type-I pieces of Vaughan's identity, kept together with their
correct relative sign. -/
def vaughanTypeI (n u v : ℕ) : ℝ :=
  Sieve.vaughanFirst n u - Sieve.vaughanMiddle n u v

/-- The genuinely bilinear (large-large) piece of Vaughan's identity. -/
def vaughanTypeII (n u v : ℕ) : ℝ :=
  Sieve.vaughanThird n u v

/-- The complete small-factor exception.  Keeping this term makes the identity
valid without a premise such as `v < n`. -/
def vaughanSmall (n v : ℕ) : ℝ :=
  if n ≤ v then ArithmeticFunction.vonMangoldt n else 0

/-- The finite Vaughan identity, valid for every natural `n` and every pair of
cutoffs.  This internalizes Mathlib's `μ * log = Λ` API through the exact
finite identity in `AnalyticNumberTheory.Sieve.VaughanIdentity`. -/
theorem vaughanIdentity_typeI_typeII_small (n u v : ℕ) :
    ArithmeticFunction.vonMangoldt n =
      vaughanTypeI n u v + vaughanTypeII n u v + vaughanSmall n v := by
  have hsplit :
      (∑ d ∈ n.divisors,
          ∑ e ∈ (n / d).divisors.filter (fun e => e ≤ v),
            ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
              ArithmeticFunction.vonMangoldt e) =
        Sieve.vaughanSecond n u v + Sieve.vaughanMiddle n u v := by
    unfold Sieve.vaughanSecond Sieve.vaughanMiddle
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := n.divisors) (p := fun d => u < d)]
    simp only [not_lt]
  have hsecond : Sieve.vaughanSecond n u v =
      vaughanSmall n v - Sieve.vaughanMiddle n u v := by
    have hfull := Sieve.vaughanFullSecondSum n v
    rw [hsplit] at hfull
    have hsum : Sieve.vaughanSecond n u v + Sieve.vaughanMiddle n u v =
        vaughanSmall n v := by
      simpa [vaughanSmall] using hfull
    linarith
  rw [Sieve.vaughanIdentity, hsecond]
  simp only [vaughanTypeI, vaughanTypeII]
  ring

/-- A scalar coefficient sequence multiplied by the von Mangoldt function. -/
def vaughanLambdaCoeff (b : ℤ → ℂ) (n : ℤ) : ℂ :=
  b n * (ArithmeticFunction.vonMangoldt n.toNat : ℂ)

/-- The Type-I coefficient sequence at the literal cutoffs `u,v`. -/
def vaughanTypeICoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeI n.toNat u v : ℂ)

/-- The Type-II coefficient sequence at the literal cutoffs `u,v`. -/
def vaughanTypeIICoeff (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanTypeII n.toNat u v : ℂ)

/-- The small-factor coefficient sequence at the literal cutoff `v`. -/
def vaughanSmallCoeff (b : ℤ → ℂ) (v : ℕ) (n : ℤ) : ℂ :=
  b n * (vaughanSmall n.toNat v : ℂ)

/-- Pointwise complex-linear form of the exact finite Vaughan identity. -/
theorem vaughanLambdaCoeff_eq (b : ℤ → ℂ) (u v : ℕ) (n : ℤ) :
    vaughanLambdaCoeff b n =
      vaughanTypeICoeff b u v n + vaughanTypeIICoeff b u v n +
        vaughanSmallCoeff b v n := by
  rw [vaughanLambdaCoeff, vaughanTypeICoeff, vaughanTypeIICoeff,
    vaughanSmallCoeff, vaughanIdentity_typeI_typeII_small]
  push_cast
  ring


/-- Three-term square-norm inequality with its explicit finite loss. -/
private theorem norm_add_add_sq_le_three (x y z : ℂ) :
    ‖x + y + z‖ ^ 2 ≤ 3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
  have hnorm : ‖x + y + z‖ ≤ ‖x‖ + ‖y‖ + ‖z‖ := by
    calc
      ‖x + y + z‖ ≤ ‖x + y‖ + ‖z‖ := norm_add_le _ _
      _ ≤ (‖x‖ + ‖y‖) + ‖z‖ := by gcongr; exact norm_add_le _ _
  have hsq : ‖x + y + z‖ ^ 2 ≤ (‖x‖ + ‖y‖ + ‖z‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  have hcauchy : (‖x‖ + ‖y‖ + ‖z‖) ^ 2 ≤
      3 * (‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2) := by
    nlinarith [sq_nonneg (‖x‖ - ‖y‖), sq_nonneg (‖x‖ - ‖z‖),
      sq_nonneg (‖y‖ - ‖z‖)]
  exact hsq.trans hcauchy

/-- A finite pointwise three-piece decomposition on `[1,N]` is consumed by the
primitive-character prefix maximum, uniformly in the character and modulus. -/
theorem primitiveCharacterPrefixMaxSquare_le_three
    (b bI bII bSmall : ℤ → ℂ) (N q : ℕ) (χ : PrimitiveCharacter q)
    (hdecomp : ∀ n ∈ Finset.Icc (1 : ℤ) N,
      b n = bI n + bII n + bSmall n) :
    primitiveCharacterPrefixMaxSquare b 0 N q χ ≤
      3 * (primitiveCharacterPrefixMaxSquare bI 0 N q χ +
        primitiveCharacterPrefixMaxSquare bII 0 N q χ +
        primitiveCharacterPrefixMaxSquare bSmall 0 N q χ) := by
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro s hs
  rcases Finset.mem_image.mp hs with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  let xI := ∑ n ∈ Finset.Icc (1 : ℤ) y, bI n * χ.1 (n : ZMod q)
  let xII := ∑ n ∈ Finset.Icc (1 : ℤ) y, bII n * χ.1 (n : ZMod q)
  let xSmall := ∑ n ∈ Finset.Icc (1 : ℤ) y, bSmall n * χ.1 (n : ZMod q)
  have hsum :
      (∑ n ∈ Finset.Icc (1 : ℤ) y, b n * χ.1 (n : ZMod q)) =
        xI + xII + xSmall := by
    simp only [xI, xII, xSmall, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [hdecomp n]
    · ring
    · rw [Finset.mem_Icc] at hn ⊢
      exact ⟨hn.1, hn.2.trans (by exact_mod_cast hyN)⟩
  simp only [primitiveCharacterPrefixSquare, zero_add]
  change ‖∑ n ∈ Finset.Icc (1 : ℤ) (y : ℤ),
      b n * χ.1 (n : ZMod q)‖ ^ 2 ≤ _
  rw [hsum]
  have hI := primitiveCharacterPrefixSquare_le_max bI 0 hyN χ
  have hII := primitiveCharacterPrefixSquare_le_max bII 0 hyN χ
  have hSmall := primitiveCharacterPrefixSquare_le_max bSmall 0 hyN χ
  dsimp [primitiveCharacterPrefixSquare] at hI hII hSmall
  simp only [zero_add] at hI hII hSmall
  refine (norm_add_add_sq_le_three xI xII xSmall).trans ?_
  gcongr
  · simpa [xI, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hI
  · simpa [xII, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hII
  · simpa [xSmall, primitiveCharacterPrefixMaxSquare,
      primitiveCharacterPrefixSquare] using hSmall


end

end AnalyticNumberTheory.LargeSieve
