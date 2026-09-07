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

theorem progressionDensity_abs_le (a d : ℕ) :
    |progressionDensity a d| ≤ (d.totient : ℝ)⁻¹ := by
  change |if d.Coprime a then (d.totient : ℝ)⁻¹ else 0| ≤ _
  split_ifs <;> simp [abs_of_nonneg (by positivity : 0 ≤ (d.totient : ℝ)⁻¹)]

noncomputable def fullSignedFamilyRemainder (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (I : Finset ι) (a : ι → ℕ) (X : ℝ)
    (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ signedTags upper P D ε label, ∑ d ∈ Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊,
    signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d

noncomputable def exceptionalFamilyRemainder (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (I : Finset ι) (a : ι → ℕ) (X : ℝ)
    (g : ArithmeticFunction ℝ) : ℝ :=
  ∑ t ∈ signedTags upper P D ε label,
    ∑ d ∈ (Icc 1 ⌊D ^ (1 + ε + ε ^ 9)⌋₊).filter (fun d => ¬ d ∣ P.prod id),
      signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d

noncomputable def fullModulusTransportCost (upper : Bool) (P : Finset ℕ) (D ε : ℝ)
    (label : ℕ → ℕ) (N : ℕ) (X : ℝ) : ℝ :=
  ((signedTags upper P D ε label).card : ℝ) *
    (((N : ℝ) + |X|) * ((4 / D ^ (ε ^ 2)) *
      (1 + Real.log (⌊D ^ (1 + ε + ε ^ 9)⌋₊ : ℕ)) ^ 2))

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

/-- Exact restricted-to-full transport for the actual family and actual
remainders, with no assumptions on the sequence or density. -/
theorem signedFamilyRemainder_full_identity (upper : Bool) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (label : ℕ → ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (I : Finset ι) (a : ι → ℕ) (X : ℝ) (g : ArithmeticFunction ℝ) :
    fullSignedFamilyRemainder upper P D ε label I a X g =
      signedFamilyRemainder upper P D ε label I a X g +
        exceptionalFamilyRemainder upper P D ε label I a X g := by
  unfold fullSignedFamilyRemainder signedFamilyRemainder exceptionalFamilyRemainder
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro t ht
  have hf := signedTags_common_wellFactorable upper P label hD hε hεsmall t ht
  exact supported_sum_split_primorial (by linarith [hf.1]) hf.2.2.1
    (prod_ne_zero_iff.mpr fun p hp => (hP p hp).ne_zero) _

/-- Divisibility counts for a genuinely injective positive bounded sequence.
The exact transport above does not require these quantitative hypotheses. -/
theorem sequenceDivisibility_le_div (I : Finset ι) (a : ι → ℕ) (N : ℕ)
    (ha : ∀ i ∈ I, 0 < a i ∧ a i ≤ N) (hinj : Set.InjOn a (↑I : Set ι))
    (d : ℕ) :
    sequenceDivisibility I a d ≤ (N : ℝ) / d := by
  have hid : sequenceDivisibility I a d =
      ((I.filter fun i => d ∣ a i).card : ℝ) := by
    simp [sequenceDivisibility]
  have hc : (I.filter fun i => d ∣ a i).card ≤
      ((Ioc 0 N).filter fun n => d ∣ n).card := by
    apply card_le_card_of_injOn a
    · intro i hi
      have hi' := mem_filter.mp hi
      exact mem_filter.mpr ⟨mem_Ioc.mpr (ha i hi'.1), hi'.2⟩
    · exact hinj.mono (filter_subset _ _)
  rw [Nat.Ioc_filter_dvd_card_eq_div] at hc
  rw [hid]
  exact (by exact_mod_cast hc : ((I.filter fun i => d ∣ a i).card : ℝ) ≤ (N / d : ℕ)).trans
    Nat.cast_div_le

theorem sequenceRemainder_abs_le_inv_totient (I : Finset ι) (a : ι → ℕ) (N : ℕ)
    (ha : ∀ i ∈ I, 0 < a i ∧ a i ≤ N) (hinj : Set.InjOn a (↑I : Set ι))
    (X : ℝ) {g : ArithmeticFunction ℝ}
    (hg : ∀ d, |g d| ≤ (d.totient : ℝ)⁻¹) {d : ℕ} (hd : 0 < d) :
    |sequenceRemainder I a X g d| ≤ ((N : ℝ) + |X|) * (d.totient : ℝ)⁻¹ := by
  have hc0 : 0 ≤ sequenceDivisibility I a d :=
    sum_nonneg fun i _ => by split_ifs <;> positivity
  have hφ : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφd : (d.totient : ℝ) ≤ d := by exact_mod_cast Nat.totient_le d
  calc
    _ ≤ |sequenceDivisibility I a d| + |X * g d| := by
      simpa only [sequenceRemainder, sub_eq_add_neg, abs_neg] using
        abs_add_le (sequenceDivisibility I a d) (-(X * g d))
    _ = sequenceDivisibility I a d + |X| * |g d| := by rw [abs_of_nonneg hc0, abs_mul]
    _ ≤ (N : ℝ) / d + |X| * (d.totient : ℝ)⁻¹ :=
      add_le_add (sequenceDivisibility_le_div I a N ha hinj d)
        (mul_le_mul_of_nonneg_left (hg d) (abs_nonneg X))
    _ ≤ (N : ℝ) / d.totient + |X| * (d.totient : ℝ)⁻¹ :=
      add_le_add (div_le_div_of_nonneg_left (by positivity : (0 : ℝ) ≤ N) hφ hφd) le_rfl
    _ = _ := by ring

/-- Quantitative transport for a canonical-density majorant. It costs
`4 J (N+|X|) (1+log(floor Q))^2 / D^(epsilon^2)`, with the ACTUAL tag count J.
No family-cardinality estimate is assumed. The all-modulus density majorant
is explicit, and is proved above for `progressionDensity`. -/
theorem exceptionalFamilyRemainder_abs_le (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε)
    (hεsmall : ε < 1 / 8) (I : Finset ι) (a : ι → ℕ) (N : ℕ)
    (ha : ∀ i ∈ I, 0 < a i ∧ a i ≤ N) (hinj : Set.InjOn a (↑I : Set ι))
    (X : ℝ) {g : ArithmeticFunction ℝ}
    (hg : ∀ d, |g d| ≤ (d.totient : ℝ)⁻¹) :
    |exceptionalFamilyRemainder upper P D ε label I a X g| ≤
      ((signedTags upper P D ε label).card : ℝ) *
        (((N : ℝ) + |X|) * ((4 / D ^ (ε ^ 2)) *
          (1 + Real.log (⌊D ^ (1 + ε + ε ^ 9)⌋₊ : ℕ)) ^ 2)) := by
  let T := ⌊D ^ (1 + ε + ε ^ 9)⌋₊
  let E := (4 / D ^ (ε ^ 2)) * (1 + Real.log (T : ℕ)) ^ 2
  have hper : ∀ t ∈ signedTags upper P D ε label,
      |∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
        signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d| ≤
          ((N : ℝ) + |X|) * E := by
    intro t ht
    calc
      _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
          |signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
          ((N : ℝ) + |X|) * (|signedFamilyTerm upper P D ε t d| * (d.totient : ℝ)⁻¹) := by
        apply sum_le_sum
        intro d hd
        rw [abs_mul]
        have hb := mul_le_mul_of_nonneg_left
          (sequenceRemainder_abs_le_inv_totient I a N ha hinj X hg
            (mem_Icc.mp (mem_filter.mp hd).1).1)
          (abs_nonneg (signedFamilyTerm upper P D ε t d))
        convert hb using 1
        ring
      _ = ((N : ℝ) + |X|) *
          ∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
            |signedFamilyTerm upper P D ε t d| * (d.totient : ℝ)⁻¹ :=
        (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (signedFamilyTerm_exceptional_mass_le upper P label t hD hε hεsmall ht T)
        (by positivity)
  calc
    _ ≤ ∑ t ∈ signedTags upper P D ε label,
        |∑ d ∈ (Icc 1 T).filter (fun d => ¬ d ∣ P.prod id),
          signedFamilyTerm upper P D ε t d * sequenceRemainder I a X g d| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ signedTags upper P D ε label, ((N : ℝ) + |X|) * E :=
      sum_le_sum hper
    _ = _ := by simp only [sum_const, nsmul_eq_mul]; rfl

/-- The finite sieve now has genuinely full-modulus signed remainders, against
the original WF members. The density remains that of the accepted family;
the explicit correction pays both the extra main terms and actual counts. -/
theorem signedFamily_full_sequence_sieve (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    (I : Finset ι) (a : ι → ℕ) (N : ℕ)
    (ha : ∀ i ∈ I, 0 < a i ∧ a i ≤ N) (hinj : Set.InjOn a (↑I : Set ι))
    (X : ℝ) {g : ArithmeticFunction ℝ}
    (hg : ∀ d, |g d| ≤ (d.totient : ℝ)⁻¹) :
    let label := geometricSieveLabel D ε
    X * signedFamilyDensity false P D ε label g +
        fullSignedFamilyRemainder false P D ε label I a X g -
        fullModulusTransportCost false P D ε label N X ≤ sequenceSifted I a P ∧
      sequenceSifted I a P ≤ X * signedFamilyDensity true P D ε label g +
        fullSignedFamilyRemainder true P D ε label I a X g +
        fullModulusTransportCost true P D ε label N X := by
  dsimp only
  let label := geometricSieveLabel D ε
  have hs := signedFamily_sequence_sieve P hP hD hε hεsmall hcut I a X g
  have hl := signedFamilyRemainder_full_identity false P hP label hD hε hεsmall I a X g
  have hu := signedFamilyRemainder_full_identity true P hP label hD hε hεsmall I a X g
  have hcl := abs_le.mp
    (exceptionalFamilyRemainder_abs_le false P label hD hε hεsmall I a N ha hinj X hg)
  have hcu := abs_le.mp
    (exceptionalFamilyRemainder_abs_le true P label hD hε hεsmall I a N ha hinj X hg)
  change _ ≤ sequenceSifted I a P ∧ sequenceSifted I a P ≤ _ at hs
  change X * signedFamilyDensity false P D ε label g + _ - _ ≤ _ ∧
    _ ≤ X * signedFamilyDensity true P D ε label g + _ + _
  unfold fullModulusTransportCost
  constructor <;> linarith [hs.1, hs.2]

/-- Concrete Goldbach-shift specialization. Distinct `p < N` give distinct
positive entries `N-p`; primality may be imposed by the caller's index set.
The density is constructed, not supplied as a prime-power bound. -/
theorem signedFamily_full_shifted_sieve (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D)
    (I : Finset ℕ) (N : ℕ) (hI : ∀ p ∈ I, p < N) (X : ℝ) :
    let label := geometricSieveLabel D ε
    let a := fun p => N - p
    let g := progressionDensity N
    X * signedFamilyDensity false P D ε label g +
        fullSignedFamilyRemainder false P D ε label I a X g -
        fullModulusTransportCost false P D ε label N X ≤ sequenceSifted I a P ∧
      sequenceSifted I a P ≤ X * signedFamilyDensity true P D ε label g +
        fullSignedFamilyRemainder true P D ε label I a X g +
        fullModulusTransportCost true P D ε label N X := by
  apply signedFamily_full_sequence_sieve P hP hD hε hεsmall hcut I (fun p => N - p) N
  · intro p hp
    exact ⟨Nat.sub_pos_of_lt (hI p hp), Nat.sub_le N p⟩
  · intro p hp q hq heq
    have hpN := hI p hp
    have hqN := hI q hq
    dsimp only at heq
    omega
  · exact progressionDensity_abs_le N

#check signedFamilyRemainder_full_identity
#print axioms signedFamilyRemainder_full_identity
#check sequenceDivisibility_le_div
#print axioms sequenceDivisibility_le_div
#check exceptionalFamilyRemainder_abs_le
#print axioms exceptionalFamilyRemainder_abs_le
#check signedFamily_full_sequence_sieve
#print axioms signedFamily_full_sequence_sieve
#check signedFamily_full_shifted_sieve
#print axioms signedFamily_full_shifted_sieve

end MathlibNt.SieveTheory.LiLiuPrereqWF
