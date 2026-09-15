

import MathlibNt.AnalyticNumberTheory.Vaughan.VaughanTypeIIActualTensorEnergy

/-!
 # Divisor-square moments for the actual Vaughan Type-II tensor energy

The fibre Cauchy bound is summed in `(d,t)` before any pointwise estimate in
`n = d*t`.  Each actual `e*m=t` fibre injects into the divisors of `t`, and its
Mangoldt energy is bounded by the same divisor count times `log (y+1)^2`.
Thus a whole fixed-`d` row is controlled by a divisor-square prefix at length
`y/d`.

The only frozen analytic input below is the classical divisor-square moment
bound.  It is stated for that scalar prefix, not for the tensor energy or for
the final Type-II conclusion.
-/

namespace AnalyticNumberTheory.LargeSieve

open Finset
open scoped BigOperators ArithmeticFunction

/-- The scalar divisor-square prefix, written on the integer interval used by
the primitive large-sieve modules.  On this interval `t.toNat` is positive. -/
noncomputable def divisorSquarePrefix (X : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc (1 : ℤ) X, ((t.toNat.divisors.card : ℝ) ^ 2)

/-- The minimal classical analytic input: an explicit `X log^3(X+1)` upper
bound for the second moment of the divisor function. -/
def DivisorSquareMomentBound (C : ℝ) : Prop :=
  ∀ X : ℕ, divisorSquarePrefix X ≤
    C * (X : ℝ) * Real.log (X + 1 : ℕ) ^ 3

/-- The quotient mass left after applying the divisor moment row by row. -/
noncomputable def vaughanQuotientMass (y : ℕ) (DS : Finset ℕ) : ℝ :=
  ∑ d ∈ DS, ((y / d : ℕ) : ℝ)

private lemma mem_vaughanTensorFiber_iff (y d e : ℕ) (ES : Finset ℕ) (t : ℤ) :
    e ∈ vaughanTensorFiber y d ES t ↔
      e ∈ ES ∧ ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t := by
  simp only [vaughanTensorFiber, Finset.mem_filter]

lemma vaughanTensorFiber_subset_divisors
    (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (ht : t ∈ Finset.Icc (1 : ℤ) y) :
    vaughanTensorFiber y d ES t ⊆ t.toNat.divisors := by
  intro e he
  rw [Nat.mem_divisors]
  have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
  have htnatpos : 0 < t.toNat := by omega
  have hex : ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t :=
    (mem_vaughanTensorFiber_iff y d e ES t).mp he |>.2
  obtain ⟨m, hm, hem⟩ := hex
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
  have hemnat : e * m = t.toNat := by
    exact_mod_cast hem.trans htcast.symm
  exact ⟨⟨m, hemnat.symm⟩, htnatpos.ne'⟩

lemma vaughanTensorFiberMultiplicity_le_divisors
    (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (ht : t ∈ Finset.Icc (1 : ℤ) y) :
    vaughanTensorFiberMultiplicity y d ES t ≤ t.toNat.divisors.card := by
  unfold vaughanTensorFiberMultiplicity
  exact Finset.card_le_card (vaughanTensorFiber_subset_divisors y d ES t ht)

lemma vaughanTensorFiber_support
    (y d : ℕ) (ES : Finset ℕ) (t : ℤ) (hd : 0 < d)
    (ht : t ∈ Finset.Icc (1 : ℤ) y)
    (hne : (vaughanTensorFiber y d ES t).Nonempty) :
    d * t.toNat ≤ y := by
  obtain ⟨e, he⟩ := hne
  have hex : ∃ m ∈ Finset.Icc 1 (y / (d * e)), ((e * m : ℕ) : ℤ) = t :=
    (mem_vaughanTensorFiber_iff y d e ES t).mp he |>.2
  obtain ⟨m, hm, hem⟩ := hex
  have hepos : 0 < e := by
    by_contra h
    simp only [Nat.not_lt, Nat.le_zero] at h
    subst e
    norm_num at hem
    have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
    omega
  have hde : 0 < d * e := Nat.mul_pos hd hepos
  have hdem : d * e * m ≤ y := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      (Nat.le_div_iff_mul_le hde).mp (Finset.mem_Icc.mp hm).2
  have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one (Finset.mem_Icc.mp ht).1
  have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
  have hemnat : e * m = t.toNat := by
    exact_mod_cast hem.trans htcast.symm
  simpa [hemnat, mul_assoc] using hdem

lemma vaughanTensorFiberMangoldtEnergy_le
    (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (hES : ∀ e ∈ ES, 0 < e)
    (ht : t ∈ Finset.Icc (1 : ℤ) y) :
    vaughanTensorFiberMangoldtEnergy y d ES t ≤
      (t.toNat.divisors.card : ℝ) * Real.log (y + 1 : ℕ) ^ 2 := by
  let L : ℝ := Real.log (y + 1 : ℕ)
  have htI := Finset.mem_Icc.mp ht
  have htY : t.toNat ≤ y := by
    have ht0 : 0 ≤ t := le_trans (by norm_num) htI.1
    have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg ht0
    have hcast : (t.toNat : ℤ) ≤ (y : ℕ) := htcast.trans_le htI.2
    exact_mod_cast hcast
  have hterm : ∀ e ∈ vaughanTensorFiber y d ES t,
      ‖vaughanMangoldtCoeff e‖ ^ 2 ≤ L ^ 2 := by
    intro e he
    have heES : e ∈ ES := (mem_vaughanTensorFiber_iff y d e ES t).mp he |>.1
    have hepos : 0 < e := hES e heES
    have hediv : e ∣ t.toNat := (Nat.mem_divisors.mp
      (vaughanTensorFiber_subset_divisors y d ES t ht he)).1
    have htnatpos : 0 < t.toNat := by
      have htpos : 0 < t := lt_of_lt_of_le Int.zero_lt_one htI.1
      have htcast : (t.toNat : ℤ) = t := Int.toNat_of_nonneg htpos.le
      have : (0 : ℤ) < (t.toNat : ℕ) := by simpa [htcast] using htpos
      exact_mod_cast this
    have het : e ≤ t.toNat := Nat.le_of_dvd htnatpos hediv
    have hey : (e : ℝ) ≤ (y + 1 : ℕ) := by
      exact_mod_cast (het.trans htY).trans (Nat.le_succ y)
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    have hyR : (0 : ℝ) < (y + 1 : ℕ) := by positivity
    have hlog : Real.log (e : ℝ) ≤ L :=
      Real.strictMonoOn_log.monotoneOn heR hyR hey
    have hcoeff : ‖vaughanMangoldtCoeff e‖ ≤ L := by
      calc
        ‖vaughanMangoldtCoeff e‖ = ArithmeticFunction.vonMangoldt e := by
          simp [vaughanMangoldtCoeff, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
        _ ≤ Real.log (e : ℝ) := ArithmeticFunction.vonMangoldt_le_log
        _ ≤ L := hlog
    exact pow_le_pow_left₀ (norm_nonneg _) hcoeff 2
  unfold vaughanTensorFiberMangoldtEnergy
  calc
    (∑ e ∈ vaughanTensorFiber y d ES t, ‖vaughanMangoldtCoeff e‖ ^ 2) ≤
        ∑ _e ∈ vaughanTensorFiber y d ES t, L ^ 2 :=
      Finset.sum_le_sum hterm
    _ = ((vaughanTensorFiber y d ES t).card : ℝ) * L ^ 2 := by simp
    _ ≤ (t.toNat.divisors.card : ℝ) * L ^ 2 := by
      have hc : (vaughanTensorFiber y d ES t).card ≤ t.toNat.divisors.card :=
        Finset.card_le_card (vaughanTensorFiber_subset_divisors y d ES t ht)
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
      exact_mod_cast hc

/-- Pointwise only at the divisor weight (never at ambient length `y`): the
multiplicity times Mangoldt energy is at most `tau(t)^2 log(y+1)^2`. -/
lemma vaughanTensorFiber_weight_le_divisor_sq
    (y d : ℕ) (ES : Finset ℕ) (t : ℤ)
    (hES : ∀ e ∈ ES, 0 < e)
    (ht : t ∈ Finset.Icc (1 : ℤ) y) :
    (vaughanTensorFiberMultiplicity y d ES t : ℝ) *
        vaughanTensorFiberMangoldtEnergy y d ES t ≤
      (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (y + 1 : ℕ) ^ 2 := by
  have hm : (vaughanTensorFiberMultiplicity y d ES t : ℝ) ≤
      (t.toNat.divisors.card : ℝ) := by
    exact_mod_cast vaughanTensorFiberMultiplicity_le_divisors y d ES t ht
  have hE := vaughanTensorFiberMangoldtEnergy_le y d ES t hES ht
  have hM0 : 0 ≤ (vaughanTensorFiberMultiplicity y d ES t : ℝ) := by positivity
  have hτ0 : 0 ≤ (t.toNat.divisors.card : ℝ) := by positivity
  calc
    (vaughanTensorFiberMultiplicity y d ES t : ℝ) *
        vaughanTensorFiberMangoldtEnergy y d ES t ≤
      (t.toNat.divisors.card : ℝ) *
        ((t.toNat.divisors.card : ℝ) * Real.log (y + 1 : ℕ) ^ 2) :=
      mul_le_mul hm hE (vaughanTensorFiberMangoldtEnergy_nonneg y d ES t) hτ0
    _ = (t.toNat.divisors.card : ℝ) ^ 2 * Real.log (y + 1 : ℕ) ^ 2 := by ring

private lemma row_indicator_sum
    (y d : ℕ) (hd : 0 < d) :
    (∑ t ∈ Finset.Icc (1 : ℤ) y,
      if d * t.toNat ≤ y then ((t.toNat.divisors.card : ℝ) ^ 2) else 0) =
      divisorSquarePrefix (y / d) := by
  unfold divisorSquarePrefix
  have hsub : Finset.Icc (1 : ℤ) (y / d : ℕ) ⊆ Finset.Icc (1 : ℤ) y := by
    intro t ht
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp ht).1,
      (Finset.mem_Icc.mp ht).2.trans (by exact_mod_cast Nat.div_le_self y d)⟩
  -- On the positive integer interval, the physical row support is exactly `t ≤ y/d`.
  have hsupport (t : ℤ) (ht : t ∈ Finset.Icc (1 : ℤ) y) :
      d * t.toNat ≤ y ↔ t ∈ Finset.Icc (1 : ℤ) (y / d : ℕ) := by
    rw [mul_comm, ← Nat.le_div_iff_mul_le hd, Finset.mem_Icc]
    have htLower := (Finset.mem_Icc.mp ht).1
    omega
  rw [← Finset.sum_subset hsub]
  · apply Finset.sum_congr rfl
    intro t ht
    rw [if_pos ((hsupport t (hsub ht)).mpr ht)]
  · intro t htY htSmall
    rw [if_neg (fun hdt => htSmall ((hsupport t htY).mp hdt))]

/-- Finite combinatorial rearrangement: after summing over all `(d,t)`, the
actual tensor coefficient energy is bounded by a sum of divisor-square moments
at the physical row lengths `y/d`. -/
theorem vaughanActualTensorCoeffEnergy_le_divisorSquarePrefixes
    (b : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ) (B : ℝ)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B) :
    vaughanActualTensorCoeffEnergy b y DS ES ≤
      B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
        ∑ d ∈ DS, divisorSquarePrefix (y / d) := by
  unfold vaughanActualTensorCoeffEnergy
  calc
    (∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) y,
      (vaughanTensorFiberMultiplicity y d ES t : ℝ) *
        vaughanTensorFiberMangoldtEnergy y d ES t * ‖b (d * t.toNat)‖ ^ 2) ≤
      ∑ d ∈ DS, ∑ t ∈ Finset.Icc (1 : ℤ) y,
        B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
          (if d * t.toNat ≤ y then (t.toNat.divisors.card : ℝ) ^ 2 else 0) := by
      apply Finset.sum_le_sum
      intro d hd
      apply Finset.sum_le_sum
      intro t ht
      by_cases hf : (vaughanTensorFiber y d ES t).Nonempty
      · have hsupport := vaughanTensorFiber_support y d ES t (hDS d hd) ht hf
        rw [if_pos hsupport]
        have hb := hB (d * t.toNat) hsupport
        have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
        have hw := vaughanTensorFiber_weight_le_divisor_sq y d ES t hES ht
        calc
          _ ≤ ((t.toNat.divisors.card : ℝ) ^ 2 * Real.log (y + 1 : ℕ) ^ 2) * B ^ 2 :=
            (mul_le_mul_of_nonneg_right hw (sq_nonneg _)).trans
              (mul_le_mul_of_nonneg_left hb2 (by positivity))
          _ = B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
              (t.toNat.divisors.card : ℝ) ^ 2 := by ring
      · have hcard : vaughanTensorFiberMultiplicity y d ES t = 0 := by
          unfold vaughanTensorFiberMultiplicity
          exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hf)
        simp only [hcard, Nat.cast_zero, zero_mul]
        split <;> positivity
    _ = B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
        ∑ d ∈ DS, divisorSquarePrefix (y / d) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.mul_sum, row_indicator_sum y d (hDS d hd)]

/-- Consequence of the frozen scalar divisor-square moment.  No tensor-energy
or Type-II conclusion occurs in the premise. -/
theorem vaughanActualTensorCoeffEnergy_le_of_divisorSquareMoment
    (b : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ) (B C : ℝ)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C) :
    vaughanActualTensorCoeffEnergy b y DS ES ≤
      C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 * vaughanQuotientMass y DS := by
  refine (vaughanActualTensorCoeffEnergy_le_divisorSquarePrefixes
    b y DS ES B hDS hES hB).trans ?_
  unfold DivisorSquareMomentBound at hMoment
  unfold vaughanQuotientMass
  have hL0 : 0 ≤ Real.log (y + 1 : ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le y))
  calc
    B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
        ∑ d ∈ DS, divisorSquarePrefix (y / d) ≤
      B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
        ∑ d ∈ DS, C * (y / d : ℕ) * Real.log (y / d + 1 : ℕ) ^ 3 := by
      gcongr with d hd
      exact hMoment (y / d)
    _ ≤ B ^ 2 * Real.log (y + 1 : ℕ) ^ 2 *
        ∑ d ∈ DS, C * (y / d : ℕ) * Real.log (y + 1 : ℕ) ^ 3 := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro d hd
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (by exact_mod_cast Nat.zero_le (y / d)))
      have hleft : (0 : ℝ) < (y / d + 1 : ℕ) := by positivity
      have hright : (0 : ℝ) < (y + 1 : ℕ) := by positivity
      have hlog : Real.log (y / d + 1 : ℕ) ≤ Real.log (y + 1 : ℕ) :=
        Real.strictMonoOn_log.monotoneOn hleft hright
          (by exact_mod_cast Nat.succ_le_succ (Nat.div_le_self y d))
      have hlog0 : 0 ≤ Real.log (y / d + 1 : ℕ) :=
        Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le (y / d)))
      exact pow_le_pow_left₀ hlog0 hlog 3
    _ = C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 *
        ∑ d ∈ DS, ((y / d : ℕ) : ℝ) := by
      simp_rw [Finset.mul_sum]
      ring

/-- A canonical binary shell has at most its lower endpoint `2^k`
integers.  This is the finite cardinality input that cancels the row length. -/
lemma card_vaughanCanonicalDyadicBlock_le_pow (N u k : ℕ) :
    (vaughanCanonicalDyadicBlock N u k).card ≤ 2 ^ k := by
  have hsub : vaughanCanonicalDyadicBlock N u k ⊆ Finset.Ico (2 ^ k) (2 ^ (k + 1)) := by
    intro d hd
    exact Finset.mem_Ico.mpr (vaughanCanonicalDyadicBlock_pow_bounds hd)
  have hc := Finset.card_le_card hsub
  calc
    (vaughanCanonicalDyadicBlock N u k).card ≤ 2 * 2 ^ k - 2 ^ k := by
      simpa [Nat.pow_succ, Nat.mul_comm] using hc
    _ = 2 ^ k := by omega

/-- On one canonical `d`-shell, the sum of physical row lengths `y/d` is at
most `y`; no pointwise ambient-`y` loss is paid for every `d`. -/
lemma vaughanQuotientMass_canonical_le (y N u k : ℕ) :
    vaughanQuotientMass y (vaughanCanonicalDyadicBlock N u k) ≤ (y : ℝ) := by
  let D := 2 ^ k
  have hD : 0 < D := by positivity
  unfold vaughanQuotientMass
  calc
    (∑ d ∈ vaughanCanonicalDyadicBlock N u k, ((y / d : ℕ) : ℝ)) ≤
        ∑ _d ∈ vaughanCanonicalDyadicBlock N u k, ((y / D : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast Nat.div_le_div_left
        (vaughanCanonicalDyadicBlock_pow_bounds hd).1 hD
    _ = ((vaughanCanonicalDyadicBlock N u k).card : ℝ) * (y / D : ℕ) := by simp
    _ ≤ (D : ℝ) * (y / D : ℕ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_vaughanCanonicalDyadicBlock_le_pow N u k
    _ ≤ (y : ℝ) := by
      exact_mod_cast Nat.mul_div_le y D

/-- Premise-minimal canonical-row closure.  The classical divisor-square
moment alone gives actual tensor energy `O(y log^5 y)` on every dyadic shell;
the shell cardinality cancels against the physical row length. -/
theorem vaughanActualTensorCoeffEnergy_canonical_le_BVScale
    (b : ℕ → ℂ) (y N u v k l : ℕ) (B C : ℝ)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C) :
    vaughanActualTensorCoeffEnergy b y
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalDyadicBlock N v l) ≤
      C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 5 := by
  refine (vaughanActualTensorCoeffEnergy_le_of_divisorSquareMoment b y
    (vaughanCanonicalDyadicBlock N u k)
    (vaughanCanonicalDyadicBlock N v l) B C
    (fun d hd => (mem_vaughanCanonicalDyadicBlock.mp hd).1)
    (fun e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)
    hB hMoment hC).trans ?_
  have hfac : 0 ≤ C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 := by positivity
  calc
    C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 *
        vaughanQuotientMass y (vaughanCanonicalDyadicBlock N u k) ≤
      C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 * (y : ℝ) :=
        mul_le_mul_of_nonneg_left (vaughanQuotientMass_canonical_le y N u k) hfac
    _ = C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 5 := by ring

/-- The same canonical closure in the tensor-energy slot consumed by the
weighted primitive full Type-II rectangle ledger. -/
theorem vaughanBilinearTensorEnergy_canonical_le_BVScale
    (b : ℕ → ℂ) (y N u v k l : ℕ) (B C : ℝ)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C) :
    vaughanBilinearTensorEnergy vaughanMangoldtCoeff b y
        (vaughanCanonicalDyadicBlock N u k)
        (vaughanCanonicalDyadicBlock N v l) ≤
      C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 5 :=
  (vaughanBilinearTensorEnergy_le_actual b y _ _
      (fun _e he => (mem_vaughanCanonicalDyadicBlock.mp he).1)).trans
    (vaughanActualTensorCoeffEnergy_canonical_le_BVScale
      b y N u v k l B C hB hMoment hC)

/-- BV-compatible scalar scale: a harmonic quotient-mass estimate of size
`y log(y+1)` turns the second divisor moment into `y log^6(y+1)`. -/
theorem vaughanActualTensorCoeffEnergy_le_BVScale
    (b : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ) (B C : ℝ)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C)
    (hQuotient : vaughanQuotientMass y DS ≤
      (y : ℝ) * Real.log (y + 1 : ℕ)) :
    vaughanActualTensorCoeffEnergy b y DS ES ≤
      C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 6 := by
  refine (vaughanActualTensorCoeffEnergy_le_of_divisorSquareMoment
    b y DS ES B C hDS hES hB hMoment hC).trans ?_
  have hfac : 0 ≤ C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 := by positivity
  calc
    C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 * vaughanQuotientMass y DS ≤
      C * B ^ 2 * Real.log (y + 1 : ℕ) ^ 5 *
        ((y : ℝ) * Real.log (y + 1 : ℕ)) :=
      mul_le_mul_of_nonneg_left hQuotient hfac
    _ = C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 6 := by ring

/-- The actual-energy estimate closes the tensor-energy slot used by the full
Type-II rectangle ledger.  Its premises are only the scalar divisor moment,
a coefficient supremum, and the explicit quotient-mass estimate. -/
theorem vaughanBilinearTensorEnergy_le_BVScale
    (b : ℕ → ℂ) (y : ℕ) (DS ES : Finset ℕ) (B C : ℝ)
    (hDS : ∀ d ∈ DS, 0 < d) (hES : ∀ e ∈ ES, 0 < e)
    (hB : ∀ n ≤ y, ‖b n‖ ≤ B)
    (hMoment : DivisorSquareMomentBound C) (hC : 0 ≤ C)
    (hQuotient : vaughanQuotientMass y DS ≤
      (y : ℝ) * Real.log (y + 1 : ℕ)) :
    vaughanBilinearTensorEnergy vaughanMangoldtCoeff b y DS ES ≤
      C * B ^ 2 * (y : ℝ) * Real.log (y + 1 : ℕ) ^ 6 :=
  (vaughanBilinearTensorEnergy_le_actual b y DS ES hES).trans
    (vaughanActualTensorCoeffEnergy_le_BVScale
      b y DS ES B C hDS hES hB hMoment hC hQuotient)

end AnalyticNumberTheory.LargeSieve
