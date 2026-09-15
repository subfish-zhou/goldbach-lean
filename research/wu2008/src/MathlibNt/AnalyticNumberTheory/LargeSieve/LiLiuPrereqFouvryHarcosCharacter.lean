import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHarcosTrace
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryKloostermanDescent

/-!
# Harcos's extension-field character sums

The coefficients belong to the fixed prime field, not to a varying extension.
The trace is `Algebra.trace`; its Frobenius formula and additive-character
orthogonality identify the sum over frequencies with the actual affine count.
-/

noncomputable section

open Finset

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

variable (p : ℕ) [Fact p.Prime]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod p) F]

def harcosTraceKloosterman (a b m : ZMod p) : ℂ :=
  ∑ t : Fˣ, ZMod.stdAddChar (m * Algebra.trace (ZMod p) F
    (algebraMap (ZMod p) F a * (t : F) +
      algebraMap (ZMod p) F b * (t : F)⁻¹))

omit [DecidableEq F] in
theorem harcos_trace_eq_frobenius_sum (x : F) :
    algebraMap (ZMod p) F (Algebra.trace (ZMod p) F x) =
      ∑ i ∈ range (Module.finrank (ZMod p) F), x ^ (p ^ i) := by
  simpa only [Nat.card_eq_fintype_card, ZMod.card] using
    FiniteField.algebraMap_trace_eq_sum_pow (ZMod p) F x

omit [DecidableEq F] in
theorem harcos_trace_eq_frobenius_sum_of_card (n : ℕ)
    (hcard : Fintype.card F = p ^ n) (x : F) :
    algebraMap (ZMod p) F (Algebra.trace (ZMod p) F x) =
      ∑ i ∈ range n, x ^ (p ^ i) := by
  have hd : Module.finrank (ZMod p) F = n := by
    apply Nat.pow_right_injective (Fact.out : p.Prime).one_lt
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    simpa only [ZMod.card, hcard] using h.symm
  rw [harcos_trace_eq_frobenius_sum, hd]

theorem harcosTraceKloosterman_zero (a b : ZMod p) :
    harcosTraceKloosterman p F a b 0 = Fintype.card Fˣ := by
  simp [harcosTraceKloosterman]

theorem harcosTraceKloosterman_frequency_sum (a b : ZMod p) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (p : ℂ) * ((univ.filter fun t : Fˣ =>
        Algebra.trace (ZMod p) F
          (algebraMap (ZMod p) F a * (t : F) +
            algebraMap (ZMod p) F b * (t : F)⁻¹) = 0).card : ℂ) := by
  unfold harcosTraceKloosterman
  rw [sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  rw [card_filter, Nat.cast_sum, mul_sum]
  apply sum_congr rfl
  intro t _
  split_ifs <;> simp

theorem harcosTraceKloosterman_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m : ZMod p, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) := by
  rw [harcosTraceKloosterman_frequency_sum,
    harcosCurvePointCount_eq_prime_mul_traceZero p hp2 _ _
      (fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm)))
      (fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))),
    Nat.cast_mul]

theorem harcosTraceKloosterman_nonzero_sum_eq_curve [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∑ m ∈ (univ : Finset (ZMod p)).erase 0, harcosTraceKloosterman p F a b m =
      (harcosCurvePointCount p (algebraMap (ZMod p) F a)
        (algebraMap (ZMod p) F b) : ℂ) - (Fintype.card F : ℂ) + 1 := by
  have h := sum_erase_add (univ : Finset (ZMod p))
    (fun m => harcosTraceKloosterman p F a b m) (mem_univ 0)
  rw [harcosTraceKloosterman_sum_eq_curve p F hp2 a b ha hb,
    harcosTraceKloosterman_zero, Fintype.card_units,
    Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (NeZero.ne (Fintype.card F))),
    Nat.cast_one] at h
  linear_combination h

theorem harcosTraceKloosterman_algEquiv
    (G : Type*) [Field G] [Fintype G] [DecidableEq G] [Algebra (ZMod p) G]
    (e : F ≃ₐ[ZMod p] G) (a b m : ZMod p) :
    harcosTraceKloosterman p F a b m = harcosTraceKloosterman p G a b m := by
  unfold harcosTraceKloosterman
  apply Fintype.sum_equiv (Units.mapEquiv e.toRingEquiv.toMulEquiv).toEquiv
  intro t
  change ZMod.stdAddChar (m * Algebra.trace (ZMod p) F
    (algebraMap (ZMod p) F a * (t : F) + algebraMap (ZMod p) F b * (t : F)⁻¹)) =
      ZMod.stdAddChar (m * Algebra.trace (ZMod p) G
        (algebraMap (ZMod p) G a * e (t : F) +
          algebraMap (ZMod p) G b * (e (t : F))⁻¹))
  congr 2
  simpa only [map_add, map_mul, map_inv₀, e.commutes] using
    (Algebra.trace_eq_of_algEquiv e
      (algebraMap (ZMod p) F a * (t : F) +
        algebraMap (ZMod p) F b * (t : F)⁻¹)).symm

theorem harcosTraceKloosterman_primeField (a b m : ZMod p) :
    harcosTraceKloosterman p (ZMod p) a b m =
      completeKloosterman p (m * a) ((m * b).val : ℤ) := by
  rw [completeKloosterman_eq_sum_units]
  unfold harcosTraceKloosterman
  apply sum_congr rfl
  intro t _
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Algebra.trace_self,
    LinearMap.id_apply, Int.cast_natCast, ZMod.natCast_zmod_val, Units.val_inv_eq_inv_val]
  congr 1
  ring

theorem harcosTraceKloosterman_nonzero_sum_bound [CharP F p]
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hcard : Fintype.card F = p ^ n) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosTraceKloosterman p F a b m‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  have ha' : algebraMap (ZMod p) F a ≠ 0 :=
    fun h => ha ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have hb' : algebraMap (ZMod p) F b ≠ 0 :=
    fun h => hb ((algebraMap (ZMod p) F).injective (h.trans (map_zero _).symm))
  have h := harcos_curve_pointCount_bound_of_card_eq_pow p n
    (Fact.out : p.Prime) hp2 _ _ ha' hb' hcard hn
  rw [harcosTraceKloosterman_nonzero_sum_eq_curve p F hp2 a b ha hb, hcard,
    Nat.cast_pow]
  calc
    _ ≤ ‖(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℂ) - (p : ℂ) ^ n‖ + ‖(1 : ℂ)‖ :=
        norm_add_le _ _
    _ = |(harcosCurvePointCount p (algebraMap (ZMod p) F a)
      (algebraMap (ZMod p) F b) : ℝ) - (p : ℝ) ^ n| + 1 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_natCast p,
          ← Complex.ofReal_pow, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs, norm_one]
    _ ≤ _ := by linarith

def harcosExtensionKloosterman (a b m : ZMod p) (n : ℕ) : ℂ := by
  letI := Fintype.ofFinite (GaloisField p n)
  letI := Classical.decEq (GaloisField p n)
  exact harcosTraceKloosterman p (GaloisField p n) a b m

theorem harcosExtensionKloosterman_one (a b m : ZMod p) :
    harcosExtensionKloosterman p a b m 1 =
      completeKloosterman p (m * a) ((m * b).val : ℤ) := by
  let := Fintype.ofFinite (GaloisField p 1)
  let := Classical.decEq (GaloisField p 1)
  exact (harcosTraceKloosterman_algEquiv p (GaloisField p 1)
    (ZMod p) (GaloisField.equivZmodP p) a b m).trans
      (harcosTraceKloosterman_primeField p a b m)

theorem harcosExtensionKloosterman_nonzero_sum_bound
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        8 * (p : ℝ) * ⌈Real.sqrt ((p : ℝ) ^ n)⌉₊ + 1 := by
  let := Fintype.ofFinite (GaloisField p n)
  let := Classical.decEq (GaloisField p n)
  apply harcosTraceKloosterman_nonzero_sum_bound p (GaloisField p n) hp2 a b ha hb n
  · simpa only [Nat.card_eq_fintype_card] using GaloisField.card p n (by omega)
  · exact hn

/-- A single constant for all extension degrees. This bounds the sum over
nonzero frequencies, not any individual Kloosterman sum. -/
theorem harcosExtensionKloosterman_total_growth
    (hp2 : p ≠ 2) (a b : ZMod p) (ha : a ≠ 0) (hb : b ≠ 0)
    (n : ℕ) (hn : 4 ≤ n) :
    ‖∑ m ∈ (univ : Finset (ZMod p)).erase 0,
      harcosExtensionKloosterman p a b m n‖ ≤
        (16 * (p : ℝ) + 1) * Real.sqrt (p : ℝ) ^ n := by
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hroot : 1 ≤ Real.sqrt (p : ℝ) ^ n :=
    one_le_pow₀ (Real.one_le_sqrt.mpr hp)
  have hsqrt : Real.sqrt ((p : ℝ) ^ n) = Real.sqrt (p : ℝ) ^ n := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [Real.sq_sqrt (by positivity), ← pow_mul, mul_comm n 2, pow_mul,
      Real.sq_sqrt (by positivity)]
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg ((p : ℝ) ^ n))
  rw [hsqrt] at hceil
  have h := harcosExtensionKloosterman_nonzero_sum_bound p hp2 a b ha hb n hn
  rw [hsqrt] at h
  have hpay : (⌈Real.sqrt (p : ℝ) ^ n⌉₊ : ℝ) ≤ 2 * Real.sqrt (p : ℝ) ^ n := by
    linarith
  nlinarith [mul_le_mul_of_nonneg_left hpay (show 0 ≤ 8 * (p : ℝ) by positivity)]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
