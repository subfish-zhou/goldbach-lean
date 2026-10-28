

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanDirectL1Physical
import MathlibNt.AnalyticNumberTheory.LargeSieve.BilinearTensorFourthMomentExplicit

/-!
 # Actual hyperbolic decomposition of the direct Vaughan Type-II mean

The prefix cutoff in Vaughan Type II is the genuine hyperbola `d * e * m ≤ y`.
This file does not replace it by a rowwise square estimate.  Instead it first
partitions the two divisor variables into the canonical dyadic rectangles, then
takes the finite maximum of each resulting collected `(d,t=e*m)` prefix over the
original prefix endpoint `y`.  Rectangles whose lower dyadic corner lies above
`N` are proved identically zero and removed before the direct mean is summed.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- Canonical rectangles which can meet the hyperbola `d*e*m ≤ N` (`m ≥ 1`). -/
def vaughanTypeIIActiveCanonicalRectangles (N u v : ℕ) : Finset (ℕ × ℕ) :=
  (vaughanCanonicalDyadicRectangles N u v).filter
    (fun kl => 2 ^ kl.1 * 2 ^ kl.2 ≤ N)

@[simp] theorem mem_vaughanTypeIIActiveCanonicalRectangles {N u v : ℕ}
    {kl : ℕ × ℕ} :
    kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v ↔
      kl ∈ vaughanCanonicalDyadicRectangles N u v ∧
        2 ^ kl.1 * 2 ^ kl.2 ≤ N := by
  simp [vaughanTypeIIActiveCanonicalRectangles]

/-- The actual maximal collected-prefix square on one canonical rectangle.
The tensor collection is the exact substitution `t=e*m`; the maximum is still
over the original hyperbolic endpoint, so no rectangular majorization has been
inserted. -/
def vaughanCanonicalCollectedPrefixMaxSquare
    (N u v k l q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ((Finset.range (N + 1)).image (fun y =>
      ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
        y N u v k l q χ‖ ^ 2)).max'
    (Finset.image_nonempty.mpr ⟨0, by simp⟩)


private lemma primitiveCharacterPrefixSquare_typeII_eq_full
    (y u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitiveCharacterPrefixSquare
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 y q χ =
      ‖vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ‖ ^ 2 := by
  unfold primitiveCharacterPrefixSquare vaughanTypeIIFullPrefix
  simp only [zero_add]
  have hsum := sum_Ioc_nat_eq_sum_Icc_int 0 0 y
    (fun z => vaughanTypeIICoeff vaughanUnitIntegerCoeff u v z *
      χ.1 (z : ZMod q))
  have hset : Finset.Ioc 0 y = Finset.Icc 1 y := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  rw [hset] at hsum
  have hsum' :
      (∑ x ∈ Finset.Icc (1 : ℤ) y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v x * χ.1 (x : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q) := by
    simpa using hsum.symm
  rw [hsum']
  have hterms :
      (∑ n ∈ Finset.Icc 1 y,
        vaughanTypeIICoeff vaughanUnitIntegerCoeff u v (n : ℤ) *
          χ.1 ((n : ℤ) : ZMod q)) =
      ∑ n ∈ Finset.Icc 1 y,
        1 * χ.1 (n : ZMod q) * vaughanTypeIIFullAt n u v := by
    apply Finset.sum_congr rfl
    intro n hn
    simp only [vaughanTypeIICoeff, vaughanUnitIntegerCoeff, one_mul,
      Int.toNat_natCast, vaughanTypeII, vaughanTypeIIFullAt_eq_vaughanThird,
      Int.cast_natCast]
    ring
  rw [hterms]


/-- A canonical rectangle above the lower-corner hyperbola contributes zero to
every prefix `y ≤ N`. -/
lemma vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive
    {y N u v k l q : ℕ} (χ : PrimitiveCharacter q) (hyN : y ≤ N)
    (hinactive : N < 2 ^ k * 2 ^ l) :
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
      y N u v k l q χ = 0 := by
  unfold vaughanTypeIICanonicalBilinearBlock
  apply Finset.sum_eq_zero
  intro d hd
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro e he
  apply mul_eq_zero_of_right
  have hde : N < d * e := by
    have hdk : 2 ^ k ≤ d := (vaughanCanonicalDyadicBlock_pow_bounds hd).1
    have hel : 2 ^ l ≤ e := (vaughanCanonicalDyadicBlock_pow_bounds he).1
    exact hinactive.trans_le (Nat.mul_le_mul hdk hel)
  have hdiv : y / (d * e) = 0 := Nat.div_eq_of_lt (hyN.trans_lt hde)
  simp [hdiv]

/-- Exact finite reindexing: at every prefix endpoint the full Type-II form is
the sum of precisely the active canonical hyperbolic shells. -/
theorem vaughanTypeIIFullPrefix_eq_sum_active_canonical
    (y N u v q : ℕ) (χ : PrimitiveCharacter q) (hyN : y ≤ N) :
    vaughanTypeIIFullPrefix (fun _ => 1) y u v q χ =
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ := by
  rw [vaughanTypeIIFullPrefix_eq_sum_canonical_bilinear
    (fun _ => 1) y N u v q χ hyN]
  rw [← Finset.sum_product (f := fun kl : ℕ × ℕ =>
    vaughanTypeIICanonicalBilinearBlock (fun _ => 1) y N u v kl.1 kl.2 q χ)]
  rw [vaughanTypeIIActiveCanonicalRectangles, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro kl hkl
  by_cases hactive : 2 ^ kl.1 * 2 ^ kl.2 ≤ N
  · simp [hactive]
  · rw [if_neg hactive]
    exact vaughanTypeIICanonicalBilinearBlock_eq_zero_of_inactive χ hyN
      (Nat.lt_of_not_ge hactive)

/-- The maximal full Type-II prefix of one primitive character is dominated by
the sum of the actual canonical collected-prefix shell maxima. -/
theorem primitivePrefixAmplitude_vaughanTypeII_le_active_collected_shells
    (N u v q : ℕ) (χ : PrimitiveCharacter q) :
    primitivePrefixAmplitude
        (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) N q χ ≤
      ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
          N u v kl.1 kl.2 q χ) := by
  let R : ℝ := ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
    Real.sqrt (vaughanCanonicalCollectedPrefixMaxSquare
      N u v kl.1 kl.2 q χ)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  change Real.sqrt (primitiveCharacterPrefixMaxSquare
    (vaughanTypeIICoeff vaughanUnitIntegerCoeff u v) 0 N q χ) ≤ R
  rw [← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  unfold primitiveCharacterPrefixMaxSquare
  apply Finset.max'_le
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := by simpa [Finset.mem_range] using hy
  rw [primitiveCharacterPrefixSquare_typeII_eq_full]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [vaughanTypeIIFullPrefix_eq_sum_active_canonical y N u v q χ hyN]
  calc
    ‖∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
        vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
          y N u v kl.1 kl.2 q χ‖
      ≤ ∑ kl ∈ vaughanTypeIIActiveCanonicalRectangles N u v,
          ‖vaughanTypeIICanonicalBilinearBlock (fun _ => 1)
            y N u v kl.1 kl.2 q χ‖ := norm_sum_le _ _
    _ ≤ R := by
      dsimp [R]
      apply Finset.sum_le_sum
      intro kl hkl
      rw [← Real.sqrt_sq (norm_nonneg _)]
      apply Real.sqrt_le_sqrt
      unfold vaughanCanonicalCollectedPrefixMaxSquare
      apply Finset.le_max'
      exact Finset.mem_image.mpr ⟨y, by simp [hyN], rfl⟩


/-- The active family is finite with the same canonical `log² N` budget. -/
theorem card_vaughanTypeIIActiveCanonicalRectangles_le (N u v : ℕ) :
    (vaughanTypeIIActiveCanonicalRectangles N u v).card ≤
      (Nat.log 2 N + 1) ^ 2 := by
  exact (Finset.card_filter_le _ _).trans
    (card_vaughanCanonicalDyadicRectangles_le N u v)


end

end AnalyticNumberTheory.LargeSieve
