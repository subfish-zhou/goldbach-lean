

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIEnergy

/-!
 # Genuine bilinear blocks for Vaughan Type II

This module performs the finite rearrangement before any pointwise square is
taken.  A dyadic rectangle in the large variables `d,e` is rewritten from a
prefix in `n` into the exact variables `n = d*e*m`; multiplicativity then puts
one character on each variable.  The final estimates apply Cauchy only in the
outer `d` variable and leave the complete `e,m` sum visible.
-/

namespace AnalyticNumberTheory.LargeSieve

open Classical Finset
open scoped BigOperators ArithmeticFunction

noncomputable section

/-- The half-open dyadic interval `(D,2D]`. -/
def vaughanDyadicBlock (D : ℕ) : Finset ℕ := Finset.Ioc D (2 * D)

@[simp] theorem mem_vaughanDyadicBlock {D d : ℕ} :
    d ∈ vaughanDyadicBlock D ↔ D < d ∧ d ≤ 2 * D := by
  simp [vaughanDyadicBlock]

/-- A dyadic block contains exactly `D` natural numbers. -/
theorem card_vaughanDyadicBlock (D : ℕ) : (vaughanDyadicBlock D).card = D := by
  simp [vaughanDyadicBlock, Nat.card_Ioc]
  omega

/-- Exact finite enumeration of the positive multiples of `k` in `[1,y]`.
This is the atomic `n = k*m` reindexing used with `k=d*e`. -/
theorem sum_multiples_Icc_reindex {R : Type*} [AddCommMonoid R]
    (F : ℕ → R) {k y : ℕ} (hk : 0 < k) :
    (∑ n ∈ (Finset.Icc 1 y).filter (fun n => k ∣ n), F n) =
      ∑ m ∈ Finset.Icc 1 (y / k), F (k * m) := by
  refine Finset.sum_bij (fun n _ => n / k) ?_ ?_ ?_ ?_
  · intro n hn
    rw [Finset.mem_filter] at hn
    have hnI := Finset.mem_Icc.mp hn.1
    rw [Finset.mem_Icc]
    constructor
    · exact Nat.div_pos (Nat.le_of_dvd hnI.1 hn.2) hk
    · exact Nat.div_le_div_right hnI.2
  · intro n₁ hn₁ n₂ hn₂ h
    rw [Finset.mem_filter] at hn₁ hn₂
    calc
      n₁ = k * (n₁ / k) := (Nat.mul_div_cancel' hn₁.2).symm
      _ = k * (n₂ / k) := by rw [h]
      _ = n₂ := Nat.mul_div_cancel' hn₂.2
  · intro m hm
    rw [Finset.mem_Icc] at hm
    refine ⟨k * m, ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · constructor
        · exact Nat.mul_pos hk hm.1
        · simpa [mul_comm] using (Nat.le_div_iff_mul_le hk).mp hm.2
      · exact dvd_mul_right k m
    · exact Nat.mul_div_cancel_left m hk
  · intro n hn
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]

/-- Prefix form of one rectangular block.  The divisibility indicator is the
literal statement that the prefix index has a factorization `n=d*e*m`. -/
def vaughanBilinearBlockPrefix
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E : ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    c n * χ.1 (n : ZMod q) *
      ∑ d ∈ vaughanDyadicBlock D,
        ∑ e ∈ vaughanDyadicBlock E,
          if d * e ∣ n then α d * β e else 0

/-- The same block after the exact finite substitution `n=d*e*m`, but before
splitting the character. -/
def vaughanBilinearBlockRaw
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E : ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanDyadicBlock D,
    ∑ e ∈ vaughanDyadicBlock E,
      α d * β e *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          c (d * e * m) * χ.1 ((d * e * m : ℕ) : ZMod q)

/-- Exact finite rectangular reindexing of a prefix.  No convergence or
analytic estimate is involved. -/
theorem vaughanBilinearBlockPrefix_eq_raw
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) (hD : 0 < D) (hE : 0 < E) :
    vaughanBilinearBlockPrefix α β c y D E q χ =
      vaughanBilinearBlockRaw α β c y D E q χ := by
  unfold vaughanBilinearBlockPrefix vaughanBilinearBlockRaw
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  have hdpos : 0 < d := hD.trans_le (mem_vaughanDyadicBlock.mp hd).1.le
  have hepos : 0 < e := hE.trans_le (mem_vaughanDyadicBlock.mp he).1.le
  have hk : 0 < d * e := Nat.mul_pos hdpos hepos
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter]
  rw [sum_multiples_Icc_reindex
    (fun n => c n * χ.1 (n : ZMod q) * (α d * β e)) hk]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- Character-separated `d,e,m` form of a dyadic rectangular block. -/
def vaughanBilinearBlock
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E : ℕ)
    (q : ℕ) (χ : PrimitiveCharacter q) : ℂ :=
  ∑ d ∈ vaughanDyadicBlock D,
    (α d * χ.1 (d : ZMod q)) *
      ∑ e ∈ vaughanDyadicBlock E,
        (β e * χ.1 (e : ZMod q)) *
          ∑ m ∈ Finset.Icc 1 (y / (d * e)),
            c (d * e * m) * χ.1 (m : ZMod q)

/-- Exact multiplicative separation of the character across `n=d*e*m`. -/
theorem vaughanBilinearBlockRaw_eq_separated
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) :
    vaughanBilinearBlockRaw α β c y D E q χ =
      vaughanBilinearBlock α β c y D E q χ := by
  unfold vaughanBilinearBlockRaw vaughanBilinearBlock
  apply Finset.sum_congr rfl
  intro d hd
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  apply Finset.sum_congr rfl
  intro m hm
  have hcast : ((d * e * m : ℕ) : ZMod q) =
      (d : ZMod q) * (e : ZMod q) * (m : ZMod q) := by
    simp only [Nat.cast_mul]
  rw [hcast, map_mul, map_mul]
  ring

/-- Combined exact prefix-to-bilinear theorem for one dyadic rectangle. -/
theorem vaughanBilinearBlockPrefix_eq_separated
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) (hD : 0 < D) (hE : 0 < E) :
    vaughanBilinearBlockPrefix α β c y D E q χ =
      vaughanBilinearBlock α β c y D E q χ :=
  (vaughanBilinearBlockPrefix_eq_raw α β c y D E q χ hD hE).trans
    (vaughanBilinearBlockRaw_eq_separated α β c y D E q χ)

/-- The still-bilinear inner `e,m` packet after selecting the outer variable
`d`.  This is deliberately not squared pointwise in the product `n`. -/
def vaughanBilinearInner
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y E q d : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ e ∈ vaughanDyadicBlock E,
    (β e * χ.1 (e : ZMod q)) *
      ∑ m ∈ Finset.Icc 1 (y / (d * e)),
        c (d * e * m) * χ.1 (m : ZMod q)

/-- The exact norm interface left after Cauchy in `d` only. -/
def vaughanBilinearOuterEnergy
    (β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) : ℝ :=
  ∑ d ∈ vaughanDyadicBlock D, ‖vaughanBilinearInner β c y E q d χ‖ ^ 2

/-- The `d`-coefficient energy, with the character twist kept literal. -/
def vaughanBilinearLeftEnergy
    (α : ℕ → ℂ) (D q : ℕ) (χ : PrimitiveCharacter q) : ℝ :=
  ∑ d ∈ vaughanDyadicBlock D, ‖α d * χ.1 (d : ZMod q)‖ ^ 2

/-- One-variable Cauchy--Schwarz.  The physical ledger has one outer `d`
energy and one sum of squared `e,m` packets; there is no `D²E²` pointwise
coefficient loss. -/
theorem vaughanBilinearBlock_norm_sq_le
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) :
    ‖vaughanBilinearBlock α β c y D E q χ‖ ^ 2 ≤
      vaughanBilinearLeftEnergy α D q χ *
        vaughanBilinearOuterEnergy β c y D E q χ := by
  unfold vaughanBilinearBlock vaughanBilinearLeftEnergy
    vaughanBilinearOuterEnergy vaughanBilinearInner
  have hnorm := norm_sum_le (vaughanDyadicBlock D)
    (fun d => (α d * χ.1 (d : ZMod q)) *
      ∑ e ∈ vaughanDyadicBlock E,
        (β e * χ.1 (e : ZMod q)) *
          ∑ m ∈ Finset.Icc 1 (y / (d * e)),
            c (d * e * m) * χ.1 (m : ZMod q))
  have hsq : ‖∑ d ∈ vaughanDyadicBlock D,
      (α d * χ.1 (d : ZMod q)) *
        ∑ e ∈ vaughanDyadicBlock E,
          (β e * χ.1 (e : ZMod q)) *
            ∑ m ∈ Finset.Icc 1 (y / (d * e)),
              c (d * e * m) * χ.1 (m : ZMod q)‖ ^ 2 ≤
      (∑ d ∈ vaughanDyadicBlock D,
        ‖α d * χ.1 (d : ZMod q)‖ *
          ‖∑ e ∈ vaughanDyadicBlock E,
            (β e * χ.1 (e : ZMod q)) *
              ∑ m ∈ Finset.Icc 1 (y / (d * e)),
                c (d * e * m) * χ.1 (m : ZMod q)‖) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    simpa [norm_mul] using hnorm
  exact hsq.trans (Finset.sum_mul_sq_le_sq_mul_sq (vaughanDyadicBlock D)
    (fun d => ‖α d * χ.1 (d : ZMod q)‖)
    (fun d => ‖∑ e ∈ vaughanDyadicBlock E,
      (β e * χ.1 (e : ZMod q)) *
        ∑ m ∈ Finset.Icc 1 (y / (d * e)),
          c (d * e * m) * χ.1 (m : ZMod q)‖))

/-- Primitive-character block-norm interface.  A future bilinear primitive
large sieve can consume the remaining sum of outer energies directly. -/
theorem sum_primitive_vaughanBilinearBlock_norm_sq_le
    (α β : ℕ → ℂ) (c : ℕ → ℂ) (y D E q : ℕ) :
    (∑ χ : PrimitiveCharacter q,
      ‖vaughanBilinearBlock α β c y D E q χ‖ ^ 2) ≤
      ∑ χ : PrimitiveCharacter q,
        vaughanBilinearLeftEnergy α D q χ *
          vaughanBilinearOuterEnergy β c y D E q χ := by
  exact Finset.sum_le_sum fun χ _ =>
    vaughanBilinearBlock_norm_sq_le α β c y D E q χ

/-- Literal physical scale after Cauchy in `d`: a pointwise bound on the
twisted left coefficient costs exactly the block length `D`, not `D²`. -/
theorem vaughanBilinearLeftEnergy_le_blockLength
    (α : ℕ → ℂ) (D q : ℕ) (χ : PrimitiveCharacter q) (A : ℝ)
    (hA : ∀ d ∈ vaughanDyadicBlock D,
      ‖α d * χ.1 (d : ZMod q)‖ ^ 2 ≤ A) :
    vaughanBilinearLeftEnergy α D q χ ≤ (D : ℝ) * A := by
  unfold vaughanBilinearLeftEnergy
  calc
    (∑ d ∈ vaughanDyadicBlock D,
        ‖α d * χ.1 (d : ZMod q)‖ ^ 2) ≤
        ∑ _d ∈ vaughanDyadicBlock D, A :=
      Finset.sum_le_sum fun d hd => hA d hd
    _ = ((vaughanDyadicBlock D).card : ℝ) * A := by simp
    _ = (D : ℝ) * A := by rw [card_vaughanDyadicBlock]

/-- Vaughan's actual factor weights for the Type-II rectangle. -/
def vaughanMoebiusCoeff (d : ℕ) : ℂ := ((ArithmeticFunction.moebius d : ℤ) : ℂ)

def vaughanMangoldtCoeff (e : ℕ) : ℂ := (ArithmeticFunction.vonMangoldt e : ℂ)

/-- The contribution at `n` from one dyadic rectangle in the two large
divisor variables of `Sieve.vaughanThird`. -/
def vaughanTypeIIBlockAt (n D E : ℕ) : ℂ :=
  ∑ d ∈ n.divisors.filter (fun d => d ∈ vaughanDyadicBlock D),
    ∑ e ∈ (n / d).divisors.filter (fun e => e ∈ vaughanDyadicBlock E),
      vaughanMoebiusCoeff d * vaughanMangoldtCoeff e

/-- The nested divisor definition of a Type-II rectangle is exactly the
fixed rectangular pair sum with the condition `d*e ∣ n`. -/
theorem vaughanTypeIIBlockAt_eq_rectangular {n D E : ℕ}
    (hn : 0 < n) (hD : 0 < D) :
    vaughanTypeIIBlockAt n D E =
      ∑ d ∈ vaughanDyadicBlock D,
        ∑ e ∈ vaughanDyadicBlock E,
          if d * e ∣ n then
            vaughanMoebiusCoeff d * vaughanMangoldtCoeff e else 0 := by
  unfold vaughanTypeIIBlockAt
  have hdset : n.divisors.filter (fun d => d ∈ vaughanDyadicBlock D) =
      (vaughanDyadicBlock D).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors]
    simp [hn.ne', and_comm]
  rw [hdset]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases hdn : d ∣ n
  · simp only [if_pos hdn]
    have hdblock : d ∈ vaughanDyadicBlock D := hd
    have hdpos : 0 < d := hD.trans_le (mem_vaughanDyadicBlock.mp hdblock).1.le
    have hndpos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd hn hdn) hdpos
    have heset : (n / d).divisors.filter (fun e => e ∈ vaughanDyadicBlock E) =
        (vaughanDyadicBlock E).filter (fun e => d * e ∣ n) := by
      ext e
      simp only [Finset.mem_filter, Nat.mem_divisors]
      rw [Nat.dvd_div_iff_mul_dvd hdn]
      simp [hndpos.ne', and_comm]
    rw [heset, Finset.sum_filter]
  · have hde : ∀ e : ℕ, ¬ d * e ∣ n := by
      intro e h
      exact hdn ((dvd_mul_right d e).trans h)
    simp [hdn, hde]

/-- The literal prefix contribution of one Type-II divisor rectangle. -/
def vaughanTypeIIBlockPrefix (b : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  ∑ n ∈ Finset.Icc 1 y,
    b n * χ.1 (n : ZMod q) * vaughanTypeIIBlockAt n D E

/-- The rectangular indicator prefix used by the generic reindexing is the
actual nested Vaughan Type-II divisor block. -/
theorem vaughanTypeIIBlockPrefix_eq_generic
    (b : ℕ → ℂ) (y D E q : ℕ) (χ : PrimitiveCharacter q)
    (hD : 0 < D) :
    vaughanTypeIIBlockPrefix b y D E q χ =
      vaughanBilinearBlockPrefix vaughanMoebiusCoeff
        vaughanMangoldtCoeff b y D E q χ := by
  unfold vaughanTypeIIBlockPrefix vaughanBilinearBlockPrefix
  apply Finset.sum_congr rfl
  intro n hn
  rw [vaughanTypeIIBlockAt_eq_rectangular (Finset.mem_Icc.mp hn).1 hD]

/-- The concrete Type-II block uses Möbius in `d`, von Mangoldt in `e`, and
keeps the external coefficient at the physical product `d*e*m`. -/
def vaughanTypeIIBilinearBlock (b : ℕ → ℂ) (y D E q : ℕ)
    (χ : PrimitiveCharacter q) : ℂ :=
  vaughanBilinearBlock vaughanMoebiusCoeff vaughanMangoldtCoeff b y D E q χ

/-- Headline algebraic rearrangement for an actual Vaughan Type-II dyadic
rectangle: prefix in `n`, exact substitution `n=d*e*m`, and character
separation, all as a finite equality. -/
theorem vaughanTypeIIBlockPrefix_eq_bilinear
    (b : ℕ → ℂ) (y D E q : ℕ) (χ : PrimitiveCharacter q)
    (hD : 0 < D) (hE : 0 < E) :
    vaughanTypeIIBlockPrefix b y D E q χ =
      vaughanTypeIIBilinearBlock b y D E q χ := by
  rw [vaughanTypeIIBlockPrefix_eq_generic b y D E q χ hD]
  exact vaughanBilinearBlockPrefix_eq_separated
    vaughanMoebiusCoeff vaughanMangoldtCoeff b y D E q χ hD hE

/-- Finite family version: once positive dyadic block bases have been selected,
the whole block sum is reindexed rectangle by rectangle.  Disjoint-cover
bookkeeping is intentionally separate from this algebraic theorem. -/
theorem sum_vaughanTypeIIBlockPrefix_eq_bilinear
    (b : ℕ → ℂ) (y q : ℕ) (χ : PrimitiveCharacter q)
    (DS ES : Finset ℕ)
    (hDS : ∀ D ∈ DS, 0 < D) (hES : ∀ E ∈ ES, 0 < E) :
    (∑ D ∈ DS, ∑ E ∈ ES, vaughanTypeIIBlockPrefix b y D E q χ) =
      ∑ D ∈ DS, ∑ E ∈ ES, vaughanTypeIIBilinearBlock b y D E q χ := by
  apply Finset.sum_congr rfl
  intro D hD
  apply Finset.sum_congr rfl
  intro E hE
  exact vaughanTypeIIBlockPrefix_eq_bilinear b y D E q χ
    (hDS D hD) (hES E hE)

end

end AnalyticNumberTheory.LargeSieve
