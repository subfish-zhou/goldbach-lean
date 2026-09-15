

import MathlibNt.AnalyticNumberTheory.LargeSieve.ConductorChangeLevelLedger
import MathlibNt.AnalyticNumberTheory.LargeSieve.DyadicPrefixMaximal

/-!
 # Explicit control of imprimitive conductor multiplicity

The exact conductor ledger counts a primitive character of conductor `d` once
for every multiple `q = d r`.  This module rewrites that fibre literally and
then bounds it using the supermultiplicativity of Euler's totient.  The
quadratic coarse bound in `Q / d` is deliberately elementary; the final dyadic
theorem records how this multiplicity is paid against the `d²` term in the
primitive large sieve.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators

noncomputable section

/-- Rewrite the levels divisible by `d` as `q = d r`, without discarding the
exact `q / φ(q)` weight. -/
theorem imprimitiveConductorWeight_eq_sum_multiples
    (Q d : ℕ) (hd : 0 < d) :
    imprimitiveConductorWeight Q d =
      ∑ r ∈ Finset.Icc 1 (Q / d),
        ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ) := by
  rw [imprimitiveConductorWeight]
  symm
  refine Finset.sum_bij (fun r _ => d * r) ?_ ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hr' := Finset.mem_Icc.mp hr
    exact ⟨⟨Nat.mul_pos hd hr'.1,
      (Nat.mul_le_mul_left d hr'.2).trans (Nat.mul_div_le Q d)⟩,
      dvd_mul_right d r⟩
  · intro r₁ hr₁ r₂ hr₂ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    refine ⟨q / d, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      constructor
      · exact Nat.div_pos (Nat.le_of_dvd (Finset.mem_Icc.mp hq'.1).1 hq'.2) hd
      · exact Nat.div_le_div_right (Finset.mem_Icc.mp hq'.1).2
    · exact Nat.mul_div_cancel' hq'.2
  · intro r hr
    rfl

/-- A factor in the multiple fibre is bounded by the conductor weight times
its multiplicity parameter. -/
theorem multiple_totient_ratio_le
    (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ) ≤
      ((d : ℝ) / (d.totient : ℝ)) * (r : ℝ) := by
  have hφnat : d.totient * r.totient ≤ (d * r).totient :=
    Nat.totient_super_multiplicative d r
  have hφ : (d.totient : ℝ) * (r.totient : ℝ) ≤ ((d * r).totient : ℝ) := by
    exact_mod_cast hφnat
  have hdφ : 0 < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd
  have hrφ : 0 < (r.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hr
  calc
    ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ)
        ≤ ((d * r : ℕ) : ℝ) / ((d.totient : ℝ) * (r.totient : ℝ)) := by
          exact div_le_div_of_nonneg_left (by positivity) (by positivity) hφ
    _ = ((d : ℝ) / (d.totient : ℝ)) *
          ((r : ℝ) / (r.totient : ℝ)) := by
          push_cast
          field_simp
    _ ≤ ((d : ℝ) / (d.totient : ℝ)) * (r : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          · apply div_le_self (by positivity)
            exact_mod_cast Nat.succ_le_iff.mpr (Nat.totient_pos.mpr hr)
          · positivity

/-- Elementary explicit conductor-fibre bound.  It is weaker than the optimal
logarithmic estimate but has the precise shape needed by a dyadic BV argument:
the extra multiplicity is at most `(Q/d)²`. -/
theorem imprimitiveConductorWeight_le_sq
    (Q d : ℕ) (hd : 0 < d) :
    imprimitiveConductorWeight Q d ≤
      (((Q / d : ℕ) : ℝ) ^ 2) * ((d : ℝ) / (d.totient : ℝ)) := by
  rw [imprimitiveConductorWeight_eq_sum_multiples Q d hd]
  let R := Q / d
  calc
    (∑ r ∈ Finset.Icc 1 R,
        ((d * r : ℕ) : ℝ) / ((d * r).totient : ℝ))
      ≤ ∑ _r ∈ Finset.Icc 1 R,
          ((d : ℝ) / (d.totient : ℝ)) * (R : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact (multiple_totient_ratio_le d r hd (Finset.mem_Icc.mp hr).1).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast (Finset.mem_Icc.mp hr).2)
            (by positivity))
    _ = ((Finset.Icc 1 R).card : ℝ) *
          (((d : ℝ) / (d.totient : ℝ)) * (R : ℝ)) := by simp
    _ = (R : ℝ) * (((d : ℝ) / (d.totient : ℝ)) * (R : ℝ)) := by
        simp
    _ = ((R : ℝ) ^ 2) * ((d : ℝ) / (d.totient : ℝ)) := by ring

/-- Dyadic conductor-window transport.  On `D ≤ d ≤ 2D`, the coarse fibre
multiplicity costs `(Q/D)²`; what remains is exactly the weight `d/φ(d)` used by
the primitive prefix large sieve. -/
theorem imprimitive_conductor_window_le_weighted_primitive
    (F : (d : ℕ) → PrimitiveCharacter d → ℝ)
    (hF : ∀ d ψ, 0 ≤ F d ψ) (Q D : ℕ) (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D (2 * D),
      imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ) ≤
      (((Q / D : ℕ) : ℝ) ^ 2) *
        ∑ d ∈ Finset.Icc D (2 * D),
          ((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d, F d ψ := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d hdmem
  have hd : 0 < d := hD.trans_le (Finset.mem_Icc.mp hdmem).1
  have hdiv : Q / d ≤ Q / D := Nat.div_le_div_left (Finset.mem_Icc.mp hdmem).1 hD
  have hsum : 0 ≤ ∑ ψ : PrimitiveCharacter d, F d ψ :=
    Finset.sum_nonneg fun ψ _ => hF d ψ
  calc
    imprimitiveConductorWeight Q d * ∑ ψ : PrimitiveCharacter d, F d ψ
      ≤ ((((Q / d : ℕ) : ℝ) ^ 2) * ((d : ℝ) / (d.totient : ℝ))) *
          ∑ ψ : PrimitiveCharacter d, F d ψ :=
        mul_le_mul_of_nonneg_right (imprimitiveConductorWeight_le_sq Q d hd) hsum
    _ ≤ ((((Q / D : ℕ) : ℝ) ^ 2) * ((d : ℝ) / (d.totient : ℝ))) *
          ∑ ψ : PrimitiveCharacter d, F d ψ := by
        gcongr
    _ = ((Q / D : ℕ) : ℝ) ^ 2 *
          (((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d, F d ψ) := by ring

/-- Direct specialization to primitive prefix maxima.  Combined with
`weighted_primitive_prefix_maximal` at modulus cutoff `2D`, this is the exact
bridge from the imprimitive conductor ledger to the existing primitive LS.
The conductor window sum on the right is a nonnegative subsum of the range
`1 ≤ d ≤ 2D`. -/
theorem imprimitive_conductor_window_prefix_le
    (b : ℤ → ℂ) (M : ℤ) (N Q D : ℕ) (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D (2 * D),
      imprimitiveConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare b M N d ψ) ≤
      (((Q / D : ℕ) : ℝ) ^ 2) *
        ∑ d ∈ Finset.Icc 1 (2 * D),
          ((d : ℝ) / (d.totient : ℝ)) *
            ∑ ψ : PrimitiveCharacter d,
              primitiveCharacterPrefixMaxSquare b M N d ψ := by
  refine (imprimitive_conductor_window_le_weighted_primitive
    (fun d ψ => primitiveCharacterPrefixMaxSquare b M N d ψ)
    (fun d ψ => ?_) Q D hD).trans ?_
  · exact primitiveCharacterPrefixMaxSquare_nonneg b M N d ψ
  · apply mul_le_mul_of_nonneg_left
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        have hm := Finset.mem_Icc.mp hd
        exact Finset.mem_Icc.mpr ⟨hD.trans_le hm.1, hm.2⟩
      · intro d hd hnot
        exact mul_nonneg (div_nonneg (by positivity) (by positivity))
          (Finset.sum_nonneg fun ψ _ =>
            primitiveCharacterPrefixMaxSquare_nonneg b M N d ψ)
    · positivity

/-- Fully discharged dyadic-window estimate.  The factor `(Q/D)²` multiplies
the primitive LS constant at cutoff `2D`; in particular its quadratic modulus
term is `(Q/D)² (2D)² ≤ 4Q²`, uniformly in the dyadic conductor range. -/
theorem imprimitive_conductor_window_prefix_large_sieve
    (b : ℤ → ℂ) (M : ℤ) (N Q D : ℕ) (hD : 0 < D) :
    (∑ d ∈ Finset.Icc D (2 * D),
      imprimitiveConductorWeight Q d *
        ∑ ψ : PrimitiveCharacter d,
          primitiveCharacterPrefixMaxSquare b M N d ψ) ≤
      (((Q / D : ℕ) : ℝ) ^ 2) *
        ((((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
          primitiveLargeSieveConstant N (2 * D) *
            ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) := by
  refine (imprimitive_conductor_window_prefix_le b M N Q D hD).trans ?_
  apply mul_le_mul_of_nonneg_left
  · exact weighted_primitive_prefix_maximal b M N (2 * D) (Nat.mul_pos (by decide) hD)
  · positivity

/-- The key dyadic payment identity behind the preceding theorem.  Although
the elementary conductor-fibre estimate loses `(Q/D)²`, this loss cancels the
quadratic modulus scale `(2D)²` of the primitive large sieve, leaving at most
`4Q²`.  Thus the coarse bound is a genuine BV bound on the high-conductor
ranges where the `N` term is no larger than the modulus-square term. -/
theorem dyadic_multiplicity_mul_modulus_sq_le (Q D : ℕ) :
    (((Q / D : ℕ) : ℝ) ^ 2) * (((2 * D : ℕ) : ℝ) ^ 2) ≤
      4 * ((Q : ℝ) ^ 2) := by
  have hnat : (Q / D) * D ≤ Q := by
    simpa [mul_comm] using Nat.mul_div_le Q D
  have hreal : ((Q / D : ℕ) : ℝ) * (D : ℝ) ≤ Q := by
    exact_mod_cast hnat
  calc
    (((Q / D : ℕ) : ℝ) ^ 2) * (((2 * D : ℕ) : ℝ) ^ 2) =
        4 * (((Q / D : ℕ) : ℝ) * (D : ℝ)) ^ 2 := by push_cast; ring
    _ ≤ 4 * ((Q : ℝ) ^ 2) := by
      gcongr

end

end AnalyticNumberTheory.LargeSieve
