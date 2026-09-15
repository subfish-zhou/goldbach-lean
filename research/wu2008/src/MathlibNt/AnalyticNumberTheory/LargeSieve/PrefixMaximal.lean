

import MathlibNt.AnalyticNumberTheory.LargeSieve.BombieriDavenport

/-!
 # Prefix-maximal weighted primitive-character large sieve

This module isolates the finite Rademacher--Menshov transfer needed by Vaughan
Type I/II arguments.  A prefix is allowed to be written as a sum of at most `L`
interval blocks, and the total block energy is allowed to cover each coefficient
at most `D` times.  The resulting loss is exactly `L * D`, uniformly in the
coefficient sequence, the interval origin, the modulus bound, and the character.

For the usual aligned dyadic decomposition one takes
`L = D = Nat.log2 N + 1`; the final corollary records the resulting square-log
loss explicitly.  Keeping the finite decomposition hypotheses visible makes the
lemma directly reusable by Vaughan decompositions without introducing any
analytic or asymptotic assumption.
-/

namespace AnalyticNumberTheory.LargeSieve

open scoped BigOperators
open Classical

noncomputable section

/-- The fully expanded constant in the non-maximal weighted primitive-character
large sieve. -/
def primitiveLargeSieveConstant (N Q : ℕ) : ℝ :=
  (N : ℝ) +
    (2 * (Nat.ceil (Real.log ((Q : ℝ) ^ 2) / Real.log 2) : ℝ) + 12) *
      (Q : ℝ) ^ 2

/-- The existing Bombieri--Davenport estimate, packaged with its explicit
constant for use by the maximal transfer. -/
theorem weighted_primitive_bombieri_davenport_explicit' (b : ℤ → ℂ) (M : ℤ)
    (N Q : ℕ) (hQ : 0 < Q) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
            b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
      primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  simpa [primitiveLargeSieveConstant] using
    weighted_primitive_bombieri_davenport_explicit b M N Q hQ

/-- The explicit large-sieve constant is monotone in the interval length. -/
theorem primitiveLargeSieveConstant_mono_left {N₁ N₂ Q : ℕ} (hN : N₁ ≤ N₂) :
    primitiveLargeSieveConstant N₁ Q ≤ primitiveLargeSieveConstant N₂ Q := by
  unfold primitiveLargeSieveConstant
  gcongr

/-- Squared norm of a finite sum, with the exact cardinality loss used in the
Rademacher--Menshov step. -/
theorem norm_finset_sum_sq_le_card_mul_sum_norm_sq
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℂ) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤
      (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have hnorm : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le s z
  have hsq : ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := hsq
    _ = (∑ i ∈ s, ‖z i‖ * 1) ^ 2 := by simp
    _ ≤ (∑ i ∈ s, ‖z i‖ ^ 2) * ∑ _i ∈ s, (1 : ℝ) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖z i‖) (fun _ => 1)
    _ = (s.card : ℝ) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
      simp [mul_comm]

/-- Prefix square for one primitive character. -/
def primitiveCharacterPrefixSquare (b : ℤ → ℂ) (M : ℤ) (y q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ‖∑ n ∈ Finset.Icc (M + 1) (M + y), b n * χ.1 (n : ZMod q)‖ ^ 2

/-- Maximum of the character-sum square over all integer prefixes `0 ≤ y ≤ N`.
The defining finite set is nonempty because it contains `y = 0`. -/
def primitiveCharacterPrefixMaxSquare (b : ℤ → ℂ) (M : ℤ) (N q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image
      (fun y => primitiveCharacterPrefixSquare b M y q χ)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Every prefix square is bounded by the corresponding finite prefix maximum. -/
theorem primitiveCharacterPrefixSquare_le_max (b : ℤ → ℂ) (M : ℤ)
    {N y q : ℕ} (hy : y ≤ N) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare b M y q χ ≤
      primitiveCharacterPrefixMaxSquare b M N q χ := by
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨y, by simpa [Finset.mem_range] using hy, rfl⟩

/-- **Finite Rademacher--Menshov transfer for primitive characters.**

The interval indexed by `i` is `(blockStart i, blockStart i + blockLength i]`.
The first hypothesis says that every prefix is the sum of at most `L` selected
blocks.  The second bounds all block lengths by the ambient length `N`.  The
last is the overlap-energy estimate; for aligned dyadic blocks its sharp finite
value is `D = Nat.log2 N + 1`.

The conclusion has the maximum *inside* the primitive-character sum.  Its
constant is uniform and completely explicit: `L * D` times the already proved
`N + (2⌈log₂(Q²)⌉+12)Q²` constant. -/
theorem weighted_primitive_prefix_maximal_of_interval_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q L D : ℕ) (hQ : 0 < Q)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ)
    (prefixBlocks : ℕ → Finset ι)
    (hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
        ∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), f n)
    (hcard : ∀ y ∈ Finset.range (N + 1), (prefixBlocks y).card ≤ L)
    (hlength : ∀ i, blockLength i ≤ N)
    (hoverlap :
      (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
          (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        (D : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (L : ℝ) * (D : ℝ) * primitiveLargeSieveConstant N Q *
        ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have hmax : ∀ q : ℕ, ∀ χ : PrimitiveCharacter q,
      primitiveCharacterPrefixMaxSquare b M N q χ ≤
        (L : ℝ) * ∑ i : ι,
          ‖∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i),
              b n * χ.1 (n : ZMod q)‖ ^ 2 := by
    intro q χ
    unfold primitiveCharacterPrefixMaxSquare
    apply Finset.max'_le
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
    unfold primitiveCharacterPrefixSquare
    rw [hdecomp y hy (fun n => b n * χ.1 (n : ZMod q))]
    let z : ι → ℂ := fun i =>
      ∑ n ∈ Finset.Icc (blockStart i + 1)
        (blockStart i + blockLength i), b n * χ.1 (n : ZMod q)
    calc
      ‖∑ i ∈ prefixBlocks y, z i‖ ^ 2 ≤
          ((prefixBlocks y).card : ℝ) *
            ∑ i ∈ prefixBlocks y, ‖z i‖ ^ 2 :=
        norm_finset_sum_sq_le_card_mul_sum_norm_sq (prefixBlocks y) z
      _ ≤ (L : ℝ) * ∑ i ∈ prefixBlocks y, ‖z i‖ ^ 2 := by
        gcongr
        exact_mod_cast hcard y hy
      _ ≤ (L : ℝ) * ∑ i : ι, ‖z i‖ ^ 2 := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_univ_sum_of_nonneg (fun i => sq_nonneg ‖z i‖)
        · positivity
  have hblocks :
      (∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
        ((q : ℝ) / (q.totient : ℝ)) *
          ∑ χ : PrimitiveCharacter q,
            ‖∑ n ∈ Finset.Icc (blockStart i + 1)
              (blockStart i + blockLength i),
                b n * χ.1 (n : ZMod q)‖ ^ 2) ≤
        primitiveLargeSieveConstant N Q *
          ∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
    calc
      _ ≤ ∑ i : ι, primitiveLargeSieveConstant (blockLength i) Q *
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
        exact Finset.sum_le_sum fun i _ =>
          weighted_primitive_bombieri_davenport_explicit'
            b (blockStart i) (blockLength i) Q hQ
      _ ≤ ∑ i : ι, primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right
          (primitiveLargeSieveConstant_mono_left (hlength i))
          (Finset.sum_nonneg fun n hn => sq_nonneg ‖b n‖)
      _ = _ := by rw [Finset.mul_sum]
  calc
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ)
      ≤ ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ((L : ℝ) * ∑ i : ι,
                ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                  (blockStart i + blockLength i),
                    b n * χ.1 (n : ZMod q)‖ ^ 2) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum fun χ _ => hmax q χ
        · positivity
    _ = (L : ℝ) * ∑ i : ι, ∑ q ∈ Finset.Icc 1 Q,
          ((q : ℝ) / (q.totient : ℝ)) *
            ∑ χ : PrimitiveCharacter q,
              ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                (blockStart i + blockLength i),
                  b n * χ.1 (n : ZMod q)‖ ^ 2 := by
        calc
          _ = ∑ q ∈ Finset.Icc 1 Q, (L : ℝ) * ∑ i : ι,
                ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ : PrimitiveCharacter q,
                    ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                      (blockStart i + blockLength i),
                        b n * χ.1 (n : ZMod q)‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro q hq
              simp_rw [Finset.mul_sum]
              rw [Finset.sum_comm]
              ring_nf
          _ = (L : ℝ) * ∑ q ∈ Finset.Icc 1 Q, ∑ i : ι,
                ((q : ℝ) / (q.totient : ℝ)) *
                  ∑ χ : PrimitiveCharacter q,
                    ‖∑ n ∈ Finset.Icc (blockStart i + 1)
                      (blockStart i + blockLength i),
                        b n * χ.1 (n : ZMod q)‖ ^ 2 := by
              rw [Finset.mul_sum]
          _ = _ := by
              congr 1
              rw [Finset.sum_comm]
    _ ≤ (L : ℝ) * (primitiveLargeSieveConstant N Q *
          ∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), ‖b n‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hblocks (by positivity)
    _ ≤ (L : ℝ) * (primitiveLargeSieveConstant N Q *
          ((D : ℝ) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2)) := by
        gcongr
        · unfold primitiveLargeSieveConstant
          positivity
    _ = (L : ℝ) * (D : ℝ) * primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by ring

/-- Dyadic/Rademacher--Menshov specialization.  Supplying the standard aligned
finite dyadic decomposition with depth `Nat.log2 N + 1` gives the exact new loss
`(Nat.log2 N + 1)²`, on top of the pre-existing additive large-sieve logarithm.
All constants remain uniform in `b`, `M`, `Q`, and every primitive character. -/
theorem weighted_primitive_prefix_maximal_of_dyadic_decomposition
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : ℤ → ℂ) (M : ℤ) (N Q : ℕ) (hQ : 0 < Q)
    (blockStart : ι → ℤ) (blockLength : ι → ℕ)
    (prefixBlocks : ℕ → Finset ι)
    (hdecomp : ∀ y ∈ Finset.range (N + 1), ∀ f : ℤ → ℂ,
      (∑ n ∈ Finset.Icc (M + 1) (M + y), f n) =
        ∑ i ∈ prefixBlocks y,
          ∑ n ∈ Finset.Icc (blockStart i + 1)
            (blockStart i + blockLength i), f n)
    (hcard : ∀ y ∈ Finset.range (N + 1),
      (prefixBlocks y).card ≤ Nat.log2 N + 1)
    (hlength : ∀ i, blockLength i ≤ N)
    (hoverlap :
      (∑ i : ι, ∑ n ∈ Finset.Icc (blockStart i + 1)
          (blockStart i + blockLength i), ‖b n‖ ^ 2) ≤
        ((Nat.log2 N + 1 : ℕ) : ℝ) *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2) :
    (∑ q ∈ Finset.Icc 1 Q,
      ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ : PrimitiveCharacter q,
          primitiveCharacterPrefixMaxSquare b M N q χ) ≤
      (((Nat.log2 N + 1 : ℕ) : ℝ) ^ 2) *
        primitiveLargeSieveConstant N Q *
          ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖b n‖ ^ 2 := by
  have h := weighted_primitive_prefix_maximal_of_interval_decomposition
    b M N Q (Nat.log2 N + 1) (Nat.log2 N + 1) hQ
    blockStart blockLength prefixBlocks hdecomp hcard hlength hoverlap
  simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h

end

end AnalyticNumberTheory.LargeSieve
