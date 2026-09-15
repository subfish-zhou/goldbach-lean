import MathlibNt.SieveTheory.LiLiuPrereqWFSignedFamily

/-!
# Finite sieve inequalities for the fixed normalized signed family

The full-integer family is not squarefree-masked. Consequently its sieve
inequalities are stated over divisors of the sieve primorial (or its gcd with
an arbitrary integer), not over unrestricted divisors.

We first sum the actual small Rosser weights on the positive and negative
rough branches separately. Only then do we use the normalized rough sieve
inequalities. The tight lower-even convention remains that of (18).
-/

namespace MathlibNt.SieveTheory.LiLiuPrereqWF

open Finset ArithmeticFunction
open scoped Classical

private theorem primeProduct_eq_one_iff (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) : S.prod id = 1 ↔ S = ∅ := by
  constructor
  · intro h
    have hf : (S.prod id).primeFactors = S := by
      simpa only [id_eq] using Nat.primeFactors_prod hS
    simpa only [h, Nat.primeFactors_one] using hf.symm
  · rintro rfl
    exact Finset.prod_empty

/-- The actual powerset bijection used in the small/rough join. -/
theorem sum_powerset_partition (N B : Finset ℕ)
    (f : Finset ℕ → Finset ℕ → ℝ) :
    (∑ s ∈ N.powerset, f (s \ B) (s ∩ B)) =
      ∑ r ∈ (N \ B).powerset, ∑ a ∈ (N ∩ B).powerset, f r a := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun s _ => (s \ B, s ∩ B)) ?_ ?_ ?_ ?_
  · intro s hs
    have hsub := Finset.mem_powerset.mp hs
    exact Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr (by
      intro p hp
      exact mem_sdiff.mpr ⟨hsub (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩),
      Finset.mem_powerset.mpr (by
        intro p hp
        exact mem_inter.mpr ⟨hsub (mem_inter.mp hp).1, (mem_inter.mp hp).2⟩)⟩
  · intro s _ t _ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    have hu := congrArg₂ (fun (s t : Finset ℕ) => s ∪ t) h₁ h₂
    simpa only [sdiff_union_inter] using hu
  · rintro ⟨r, a⟩ h
    obtain ⟨hr, ha⟩ := Finset.mem_product.mp h
    have hr' := Finset.mem_powerset.mp hr
    have ha' := Finset.mem_powerset.mp ha
    refine ⟨r ∪ a, Finset.mem_powerset.mpr ?_, ?_⟩
    · intro p hp
      rcases mem_union.mp hp with hp | hp
      · exact (mem_sdiff.mp (hr' hp)).1
      · exact (mem_inter.mp (ha' hp)).1
    · apply Prod.ext <;> ext p <;> simp only [mem_sdiff, mem_union, mem_inter]
      · have hx : p ∈ r → p ∉ B := fun hp => (mem_sdiff.mp (hr' hp)).2
        have hy : p ∈ a → p ∈ B := fun hp => (mem_inter.mp (ha' hp)).2
        tauto
      · have hx : p ∈ r → p ∉ B := fun hp => (mem_sdiff.mp (hr' hp)).2
        have hy : p ∈ a → p ∈ B := fun hp => (mem_inter.mp (ha' hp)).2
        tauto
  · intro s _
    rfl

private theorem normalizedSet_powerset_bounds (R : Finset ℕ) (D : ℝ)
    (b c : ℕ → ℝ) (hR : ∀ p ∈ R, p.Prime) (hD : 1 < D)
    (hcut : ∀ p ∈ R, (p : ℝ) < D)
    (hb : ∀ p ∈ R, 0 ≤ b p)
    (hbp : ∀ p ∈ R, b p ≤ (p : ℝ))
    (hpc : ∀ p ∈ R, (p : ℝ) ≤ c p) :
    (∑ r ∈ R.powerset, normalizedLowerSet b c D r) ≤
        (if R = ∅ then 1 else 0) ∧
      (if R = ∅ then 1 else 0) ≤
        ∑ r ∈ R.powerset, normalizedUpperSet b c D r := by
  have hsf := SmallRosser.primeProduct_squarefree R hR
  have hpf : (R.prod id).primeFactors = R := by
    simpa only [id_eq] using Nat.primeFactors_prod hR
  have hlo := SmallRosser.lowerWeight_divisor_sum hsf
    (fun p hp => hcut p (hpf ▸ hp)) (dvd_refl (R.prod id))
  have hhi : (if R.prod id = 1 then (1 : ℝ) else 0) ≤
      ∑ d ∈ (R.prod id).divisors, SmallRosser.upperWeight (R.prod id) D d := by
    simp_rw [SmallRosser.upperWeight_eq_producer]
    exact LinearSieve.upperRosserWeight_divisor_sum
      (LinearSieve.upperRosserWeight_certificate hsf hsf.ne_zero
        (Nat.lt_ceil.mpr (by simpa using hD))
        (fun p hp => Nat.lt_ceil.mpr (hcut p (hpf ▸ hp)))) (dvd_refl _)
  simp only [SmallRosser.sum_divisors_eq_sum_powerset hsf, hpf,
    primeProduct_eq_one_iff R hR] at hlo hhi
  constructor
  · refine (Finset.sum_le_sum (fun r hr => ?_)).trans hlo
    rw [SmallRosser.lowerWeight_prod_eq_setWeight hsf
      (by simpa only [hpf] using mem_powerset.mp hr)]
    exact normalizedLowerSet_le_setWeight
      (fun p hp => hb p (mem_powerset.mp hr hp))
      (fun p hp => hbp p (mem_powerset.mp hr hp))
      (fun p hp => hpc p (mem_powerset.mp hr hp))
  · refine hhi.trans (Finset.sum_le_sum (fun r hr => ?_))
    rw [SmallRosser.upperWeight_prod_eq_setWeight hsf
      (by simpa only [hpf] using mem_powerset.mp hr)]
    exact upperSetWeight_le_normalizedUpperSet
      (fun p hp => hb p (mem_powerset.mp hr hp))
      (fun p hp => hbp p (mem_powerset.mp hr hp))
      (fun p hp => hpc p (mem_powerset.mp hr hp))

private theorem smallWeight_powerset_bounds (P A : Finset ℕ) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : A ⊆ geometricSmallPrimes P D ε) :
    (∑ a ∈ A.powerset, SmallRosser.lowerSmallWeight P D ε (a.prod id)) ≤
        (if A = ∅ then 1 else 0) ∧
      (if A = ∅ then 1 else 0) ≤
        ∑ a ∈ A.powerset, SmallRosser.upperSmallWeight P D ε (a.prod id) := by
  have hprime : ∀ p ∈ A, p.Prime := fun p hp =>
    SmallRosser.smallPrimes_prime P D ε p (hA hp)
  have hsf := SmallRosser.primeProduct_squarefree A hprime
  have hpf : (A.prod id).primeFactors = A := by
    simpa only [id_eq] using Nat.primeFactors_prod hprime
  have hdvd : A.prod id ∣ (geometricSmallPrimes P D ε).prod id :=
    Finset.prod_dvd_prod_of_subset A _ id hA
  have hlo := SmallRosser.lowerSmallWeight_divisor_sum P
    (by linarith : 1 ≤ D) hε.le hε1 hdvd
  have hhi := SmallRosser.upperSmallWeight_divisor_sum_of_le_one P hD hε hε1 hdvd
  simp only [SmallRosser.sum_divisors_eq_sum_powerset hsf, hpf,
    primeProduct_eq_one_iff A hprime] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Each rough branch is multiplied only after the small divisor sum is
bounded with its correct sign. In particular no small coefficient is assumed
nonnegative. -/
theorem normalizedSignedSet_small_sum_bounds (P A r : Finset ℕ)
    {D ε : ℝ} (b c : ℕ → ℝ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hA : A ⊆ geometricSmallPrimes P D ε) :
    normalizedLowerSet b c D r *
        (∑ a ∈ A.powerset, signedSmallWeight false P D ε r.card (a.prod id)) ≤
      normalizedLowerSet b c D r * (if A = ∅ then 1 else 0) ∧
    normalizedUpperSet b c D r * (if A = ∅ then 1 else 0) ≤
      normalizedUpperSet b c D r *
        (∑ a ∈ A.powerset, signedSmallWeight true P D ε r.card (a.prod id)) := by
  obtain ⟨hlo, hhi⟩ := smallWeight_powerset_bounds P A hD hε hε1 hA
  by_cases heven : Even r.card
  · simp only [signedSmallWeight, LooseSign, Bool.false_eq_true, if_false,
      if_true, heven, not_true_eq_false,
      normalizedLowerSet, normalizedUpperSet]
    constructor <;> split_ifs <;> simp_all
  · simp only [signedSmallWeight, LooseSign, Bool.false_eq_true, if_false,
      if_true, heven, not_false_eq_true,
      normalizedLowerSet, normalizedUpperSet]
    constructor <;> split_ifs <;> simp_all

/-- Exact sum reindexing for the same full-integer aggregate. The outer
variable is the rough prime subset, so its sign and small-weight choice stay
fixed throughout the inner sum. -/
theorem signedFamilyAggregate_divisor_sum_partition (upper : Bool) (P : Finset ℕ)
    {D ε : ℝ} (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {n : ℕ} (hn : Squarefree n) (hsub : n.primeFactors ⊆ P) :
    (∑ d ∈ n.divisors, signedFamilyAggregate upper P D ε label d) =
      ∑ r ∈ (n.primeFactors \ geometricSmallPrimes P D ε).powerset,
        normalizedSignedSet upper
          (fun p => geometricLower D ε (ε ^ 9) (label p))
          (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D r *
        ∑ a ∈ (n.primeFactors ∩ geometricSmallPrimes P D ε).powerset,
          signedSmallWeight upper P D ε r.card (a.prod id) := by
  rw [SmallRosser.sum_divisors_eq_sum_powerset hn]
  calc
    _ = ∑ s ∈ n.primeFactors.powerset,
        normalizedSignedSet upper
          (fun p => geometricLower D ε (ε ^ 9) (label p))
          (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D
          (s \ geometricSmallPrimes P D ε) *
        signedSmallWeight upper P D ε (s \ geometricSmallPrimes P D ε).card
          ((s ∩ geometricSmallPrimes P D ε).prod id) := by
      apply Finset.sum_congr rfl
      intro s hs
      have hs' := mem_powerset.mp hs
      have hprime : ∀ p ∈ s, p.Prime :=
        fun p hp => Nat.prime_of_mem_primeFactors (hs' hp)
      have hpf : (s.prod id).primeFactors = s := by
        simpa only [id_eq] using Nat.primeFactors_prod hprime
      simpa only [hpf] using signedFamilyAggregate_squarefree_normalized
        upper P label hD hε hlabel hhead
        (SmallRosser.primeProduct_squarefree s hprime)
        (by simpa only [hpf] using hs'.trans hsub)
    _ = _ := by
      simpa only [Finset.mul_sum] using
        sum_powerset_partition n.primeFactors (geometricSmallPrimes P D ε)
          (fun r a =>
            normalizedSignedSet upper
              (fun p => geometricLower D ε (ε ^ 9) (label p))
              (fun p => geometricLower D ε (ε ^ 9) (label p) ^ (1 + ε ^ 9)) D r *
            signedSmallWeight upper P D ε r.card (a.prod id))

private theorem partition_empty_indicator (N B : Finset ℕ) :
    (if N \ B = ∅ then (1 : ℝ) else 0) * (if N ∩ B = ∅ then 1 else 0) =
      if N = ∅ then 1 else 0 := by
  have h : N = ∅ ↔ N \ B = ∅ ∧ N ∩ B = ∅ := by
    constructor
    · rintro rfl
      simp
    · rintro ⟨hr, ha⟩
      rw [← sdiff_union_inter N B, hr, ha, union_empty]
  by_cases hr : N \ B = ∅ <;> by_cases ha : N ∩ B = ∅ <;> simp [h, hr, ha]

private theorem geometric_rough_cutoff (P : Finset ℕ) {D ε : ℝ}
    (label : ℕ → ℕ) (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D) :
    ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < D := by
  intro p hp
  have hD1 : 1 ≤ D := by linarith
  have hθ : 0 ≤ ε ^ 9 := pow_nonneg hε.le _
  have hθ1 : ε ^ 9 ≤ 1 := pow_le_one₀ hε.le (by linarith)
  have htop := ((mem_geometricPrimeBox _ _ _ _ _ _).mp (hlabel p hp)).2.2.2
  rw [geometricLower_succ (by linarith : 0 ≤ D)] at htop
  have hpow := Real.rpow_le_rpow_of_exponent_le
    (geometricLower_one_le (ε := ε) hD1 hθ (label p))
    (show 1 + ε ^ 9 ≤ (2 : ℝ) by linarith)
  rw [Real.rpow_two] at hpow
  exact htop.trans_le hpow |>.trans (hhead p hp)

/-- Both finite sieve directions for the actual normalized family, on a
divisor of the fixed prime product. Geometric membership and the source head
restriction are the only box-label inputs. -/
theorem signedFamilyAggregate_divisor_sum_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (label : ℕ → ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D)
    {n : ℕ} (hn : n ∣ P.prod id) :
    (∑ d ∈ n.divisors, signedFamilyAggregate false P D ε label d) ≤
        (if n = 1 then 1 else 0) ∧
      (if n = 1 then 1 else 0) ≤
        ∑ d ∈ n.divisors, signedFamilyAggregate true P D ε label d := by
  have hM := SmallRosser.primeProduct_squarefree P hP
  have hsf := Squarefree.squarefree_of_dvd hn hM
  have hpf : (P.prod id).primeFactors = P := by
    simpa only [id_eq] using Nat.primeFactors_prod hP
  have hsub : n.primeFactors ⊆ P := hpf ▸ Nat.primeFactors_mono hn hM.ne_zero
  let B := geometricSmallPrimes P D ε
  let R := n.primeFactors \ B
  let A := n.primeFactors ∩ B
  let b := fun p => geometricLower D ε (ε ^ 9) (label p)
  let c := fun p => b p ^ (1 + ε ^ 9)
  have hR : R ⊆ P \ B := by
    intro p hp
    exact mem_sdiff.mpr ⟨hsub (mem_sdiff.mp hp).1, (mem_sdiff.mp hp).2⟩
  have hA : A ⊆ B := inter_subset_right
  have hD1 : 1 ≤ D := by linarith
  have hθ : 0 ≤ ε ^ 9 := pow_nonneg hε.le _
  have hbox : ∀ p ∈ R, b p ≤ (p : ℝ) ∧ (p : ℝ) ≤ c p := by
    intro p hp
    have h := ((mem_geometricPrimeBox _ _ _ _ _ _).mp (hlabel p (hR hp))).2.2
    rw [geometricLower_succ (by linarith : 0 ≤ D)] at h
    exact ⟨h.1, h.2.le⟩
  obtain ⟨hlo, hhi⟩ := normalizedSet_powerset_bounds R D b c
    (fun p hp => hP p (mem_sdiff.mp (hR hp)).1) (by linarith)
    (fun p hp => geometric_rough_cutoff P label hD hε hεsmall hlabel hhead p (hR hp))
    (fun p _ => (by norm_num : (0 : ℝ) ≤ 1).trans
      (geometricLower_one_le hD1 hθ (label p)))
    (fun p hp => (hbox p hp).1) (fun p hp => (hbox p hp).2)
  have hbranch := fun r => normalizedSignedSet_small_sum_bounds P A r b c
    hD hε (by linarith) hA
  have hn1 : n.primeFactors = ∅ ↔ n = 1 := by
    rw [Nat.primeFactors_eq_empty]
    simp only [hsf.ne_zero, false_or]
  have hind :
      (if R = ∅ then (1 : ℝ) else 0) * (if A = ∅ then 1 else 0) =
        if n = 1 then 1 else 0 := by
    simpa only [R, A, hn1] using partition_empty_indicator n.primeFactors B
  have hnonneg : (0 : ℝ) ≤ if A = ∅ then 1 else 0 := by split <;> norm_num
  rw [signedFamilyAggregate_divisor_sum_partition false P label hD hε hlabel hhead
      hsf hsub,
    signedFamilyAggregate_divisor_sum_partition true P label hD hε hlabel hhead
      hsf hsub]
  change (∑ r ∈ R.powerset, normalizedLowerSet b c D r *
      ∑ a ∈ A.powerset, signedSmallWeight false P D ε r.card (a.prod id)) ≤ _ ∧
    _ ≤ ∑ r ∈ R.powerset, normalizedUpperSet b c D r *
      ∑ a ∈ A.powerset, signedSmallWeight true P D ε r.card (a.prod id)
  constructor
  · calc
      _ ≤ ∑ r ∈ R.powerset, normalizedLowerSet b c D r *
          (if A = ∅ then 1 else 0) := Finset.sum_le_sum (fun r _ => (hbranch r).1)
      _ = (∑ r ∈ R.powerset, normalizedLowerSet b c D r) *
          (if A = ∅ then 1 else 0) := (Finset.sum_mul ..).symm
      _ ≤ (if R = ∅ then 1 else 0) * (if A = ∅ then 1 else 0) :=
        mul_le_mul_of_nonneg_right hlo hnonneg
      _ = _ := hind
  · calc
      _ = (if R = ∅ then 1 else 0) * (if A = ∅ then 1 else 0) := hind.symm
      _ ≤ (∑ r ∈ R.powerset, normalizedUpperSet b c D r) *
          (if A = ∅ then 1 else 0) := mul_le_mul_of_nonneg_right hhi hnonneg
      _ = ∑ r ∈ R.powerset, normalizedUpperSet b c D r *
          (if A = ∅ then 1 else 0) := Finset.sum_mul ..
      _ ≤ _ := Finset.sum_le_sum (fun r _ => (hbranch r).2)

/-- Restricting to primorial divisors also handles zero, including the empty
primorial. No assertion is made about unrestricted prime-power divisors. -/
theorem signedFamilyAggregate_gcd_divisor_sum_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ} (label : ℕ → ℕ)
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hlabel : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (label p))
    (hhead : ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (label p) ^ 2 < D) (n : ℕ) :
    (∑ d ∈ (n.gcd (P.prod id)).divisors,
      signedFamilyAggregate false P D ε label d) ≤
        (if n.Coprime (P.prod id) then 1 else 0) ∧
      (if n.Coprime (P.prod id) then 1 else 0) ≤
        ∑ d ∈ (n.gcd (P.prod id)).divisors,
          signedFamilyAggregate true P D ε label d :=
  signedFamilyAggregate_divisor_sum_bounds P hP label hD hε hεsmall hlabel hhead
    (Nat.gcd_dvd_right n (P.prod id))

/-- The first geometric box whose upper endpoint exceeds `p`. This choice is
fixed independently of every level split and every sieve integer. -/
noncomputable def geometricSieveLabel (D ε : ℝ) (p : ℕ) : ℕ :=
  if h : ∃ j : ℕ, (p : ℝ) < geometricLower D ε (ε ^ 9) (j + 1)
  then Nat.find h else 0

private theorem exists_geometric_upper {D ε : ℝ} (hD : 1 < D) (hε : 0 < ε)
    (p : ℕ) : ∃ j : ℕ, (p : ℝ) < geometricLower D ε (ε ^ 9) (j + 1) := by
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (p : ℝ) hD
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt ((m : ℝ) / ε ^ 2)
    (show (1 : ℝ) < 1 + ε ^ 9 by linarith [pow_pos hε 9])
  have hexp : (m : ℝ) < ε ^ 2 * (1 + ε ^ 9) ^ j := by
    have h := (div_lt_iff₀ hε2).mp hj
    nlinarith
  have hpow := Real.rpow_lt_rpow_of_exponent_lt hD hexp
  rw [Real.rpow_natCast] at hpow
  exact ⟨j, (hm.trans hpow).trans_le
    (geometricLower_monotone (ε := ε) hD.le (pow_nonneg hε.le _) (Nat.le_succ j))⟩

theorem geometricSieveLabel_mem (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 1 < D) (hε : 0 < ε) :
    ∀ p ∈ P \ geometricSmallPrimes P D ε,
      p ∈ geometricPrimeBox P D ε (ε ^ 9) (geometricSieveLabel D ε p) := by
  intro p hp
  obtain ⟨hpP, hpB⟩ := mem_sdiff.mp hp
  have hprime := hP p hpP
  have hbase : geometricLower D ε (ε ^ 9) 0 ≤ (p : ℝ) := by
    have hnot : ¬ (p : ℝ) < D ^ (ε ^ 2) := by
      intro h
      exact hpB (mem_filter.mpr ⟨hpP, hprime, h⟩)
    simpa only [geometricLower, pow_zero, mul_one] using le_of_not_gt hnot
  have hex := exists_geometric_upper hD hε p
  rw [geometricSieveLabel, dif_pos hex, mem_geometricPrimeBox]
  refine ⟨hpP, hprime, ?_, Nat.find_spec hex⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
  · simpa only [hzero] using hbase
  · have hmin := Nat.find_min hex (Nat.sub_one_lt_of_lt hpos)
    rw [Nat.sub_add_cancel hpos] at hmin
    exact le_of_not_gt hmin

theorem geometricSieveLabel_head_lt (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    {D ε : ℝ} (hD : 1 < D) (hε : 0 < ε)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) :
    ∀ p ∈ P \ geometricSmallPrimes P D ε,
      geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p) ^ 2 < D := by
  intro p hp
  have hlo := ((mem_geometricPrimeBox _ _ _ _ _ _).mp
    (geometricSieveLabel_mem P hP hD hε p hp)).2.2.1
  have hnonneg : 0 ≤ geometricLower D ε (ε ^ 9) (geometricSieveLabel D ε p) :=
    (by norm_num : (0 : ℝ) ≤ 1).trans
      (geometricLower_one_le hD.le (pow_nonneg hε.le _) _)
  have hsq := pow_le_pow_left₀ hnonneg hlo 2
  have hpnonneg : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hsqrt := Real.sq_sqrt (show 0 ≤ D by linarith)
  have hlt := hcut p hp
  nlinarith [Real.sqrt_nonneg D]

/-- The canonical label discharges all box hypotheses under the usual
rough-prime cutoff `p < sqrt D`. The coefficients remain unchanged. -/
theorem signedFamilyAggregate_canonical_gcd_divisor_sum_bounds (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {D ε : ℝ}
    (hD : 2 ≤ D) (hε : 0 < ε) (hεsmall : ε < 1 / 8)
    (hcut : ∀ p ∈ P \ geometricSmallPrimes P D ε, (p : ℝ) < Real.sqrt D) (n : ℕ) :
    (∑ d ∈ (n.gcd (P.prod id)).divisors,
      signedFamilyAggregate false P D ε (geometricSieveLabel D ε) d) ≤
        (if n.Coprime (P.prod id) then 1 else 0) ∧
      (if n.Coprime (P.prod id) then 1 else 0) ≤
        ∑ d ∈ (n.gcd (P.prod id)).divisors,
          signedFamilyAggregate true P D ε (geometricSieveLabel D ε) d :=
  signedFamilyAggregate_gcd_divisor_sum_bounds P hP (geometricSieveLabel D ε)
    hD hε hεsmall (geometricSieveLabel_mem P hP (by linarith) hε)
    (geometricSieveLabel_head_lt P hP (by linarith) hε hcut) n

#check sum_powerset_partition
#check normalizedSignedSet_small_sum_bounds
#check signedFamilyAggregate_divisor_sum_partition
#check signedFamilyAggregate_divisor_sum_bounds
#check signedFamilyAggregate_gcd_divisor_sum_bounds
#check geometricSieveLabel_mem
#check geometricSieveLabel_head_lt
#check signedFamilyAggregate_canonical_gcd_divisor_sum_bounds
#print axioms sum_powerset_partition
#print axioms normalizedSignedSet_small_sum_bounds
#print axioms signedFamilyAggregate_divisor_sum_partition
#print axioms signedFamilyAggregate_divisor_sum_bounds
#print axioms signedFamilyAggregate_gcd_divisor_sum_bounds
#print axioms geometricSieveLabel_mem
#print axioms geometricSieveLabel_head_lt
#print axioms signedFamilyAggregate_canonical_gcd_divisor_sum_bounds

end MathlibNt.SieveTheory.LiLiuPrereqWF
