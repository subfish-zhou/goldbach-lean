/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nous Research
-/
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969CombinedModulusEStar
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969SquarefulA4
import MathlibNt.SieveTheory.LinearSieve.Richert.Richert1969Theorem1FiniteChain
import MathlibNt.SieveTheory.Arithmetic.MertensTheorem

/-!
# Richert 1969: specialization of ordinary (4.18) to Chen's weighted remainder

Frozen source:

* `references/richert-1969/richert-1969.pdf`, PDF pages 17--20,
  equation (4.18) and the Cauchy--Schwarz argument after (4.22);
* `references/richert-1969/VISION_TRANSCRIPTION.md`, sections 7 and 9.

This module specializes the quantified ordinary prefix-maximal
Bombieri--Vinogradov estimate to Chen's combined moduli.  The cutoff,
pointwise envelope, Lemma 3 payment, and logarithmic-integral normalization
shift are all discharged here.  No weighted Bombieri theorem is assumed.
-/

noncomputable section

open Finset Filter
open scoped BigOperators Topology

namespace MathlibNt.SieveTheory.Richert1969

open SwitchingPrinciple
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

private theorem primeProduct_le_totient_ratio
    {x d : ℕ} (hd : 1 ≤ d) (hdx : d ≤ x) :
    MertensTheorem.primeProduct x ≤ (d.totient : ℝ) / d := by
  let S := d.primeFactors
  let T := (Finset.range (x + 1)).filter Nat.Prime
  let f : ℕ → ℝ := fun p => 1 - 1 / (p : ℝ)
  have hST : S ⊆ T := by
    intro p hp
    have hpprime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ≤ d := Nat.le_of_dvd (by omega)
      (Nat.dvd_of_mem_primeFactors hp)
    simp only [T, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hpprime⟩
  have hf0 : ∀ p ∈ T, 0 ≤ f p := by
    intro p hp
    have hpprime : p.Prime := (Finset.mem_filter.mp hp).2
    dsimp [f]
    have hpcast : (1 : ℝ) ≤ p := by exact_mod_cast hpprime.one_le
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
    have hinv : 1 / (p : ℝ) ≤ 1 := (div_le_one hpR).2 hpcast
    linarith
  have hf1 : ∀ p ∈ T, f p ≤ 1 := by
    intro p hp
    dsimp [f]
    have : 0 ≤ 1 / (p : ℝ) := by positivity
    linarith
  have hprodS0 : 0 ≤ ∏ p ∈ S, f p :=
    Finset.prod_nonneg fun p hp => hf0 p (hST hp)
  have hdiff : ∏ p ∈ T \ S, f p ≤ 1 :=
    Finset.prod_le_one
      (fun p hp => hf0 p (Finset.sdiff_subset hp))
      (fun p hp => hf1 p (Finset.sdiff_subset hp))
  have hprod : (∏ p ∈ T, f p) ≤ ∏ p ∈ S, f p := by
    rw [← Finset.prod_sdiff hST]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hdiff hprodS0
  have hEulerQ := Nat.totient_eq_mul_prod_factors d
  have hEulerR : (d.totient : ℝ) =
      (d : ℝ) * ∏ p ∈ d.primeFactors, (1 - (p : ℝ)⁻¹) := by
    have hmap := congrArg (algebraMap ℚ ℝ) hEulerQ
    simpa using hmap
  calc
    MertensTheorem.primeProduct x = ∏ p ∈ T, f p := rfl
    _ ≤ ∏ p ∈ S, f p := hprod
    _ = (d.totient : ℝ) / d := by
      rw [hEulerR]
      field_simp [show (d : ℝ) ≠ 0 by exact_mod_cast (by omega : d ≠ 0)]
      rfl

/-- Mertens' product theorem pays the reciprocal totient in the pointwise
`m E*(N,m)` estimate, uniformly for `1 ≤ m ≤ N`. -/
theorem exists_reciprocal_totient_le_richert_log_div :
    ∃ C : ℝ, 0 < C ∧ ∀ N m : ℕ, 2 ≤ N → 1 ≤ m → m ≤ N →
      (1 : ℝ) / m.totient ≤ C * Real.log N / m := by
  obtain ⟨c₁, _c₂, hc₁, hM⟩ :=
    MertensTheorem.primeProduct_asymptotic_order
  refine ⟨c₁⁻¹, inv_pos.mpr hc₁, ?_⟩
  intro N m hN hm hmN
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hphi : 0 < (m.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < m)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hlow : c₁ / Real.log N ≤ (m.totient : ℝ) / m :=
    (hM N hN).1.trans (primeProduct_le_totient_ratio hm hmN)
  have hcross : c₁ * (m : ℝ) ≤ (m.totient : ℝ) * Real.log N :=
    (div_le_div_iff₀ hlog hmR).mp hlow
  rw [div_le_div_iff₀ hphi hmR]
  calc
    1 * (m : ℝ) = c₁⁻¹ * (c₁ * (m : ℝ)) := by
      field_simp [ne_of_gt hc₁]
    _ ≤ c₁⁻¹ * ((m.totient : ℝ) * Real.log N) :=
      mul_le_mul_of_nonneg_left hcross (le_of_lt (inv_pos.mpr hc₁))
    _ = (c₁⁻¹ * Real.log N) * (m.totient : ℝ) := by ring

/-- A residue class modulo `m` contains at most `N / m + 1` integers through
the endpoint `N`; primality can only decrease that count. -/
theorem primesInAP_le_div_add_one
    (N m l : ℕ) (_hm : 0 < m) :
    BombieriVinogradov.primesInAP N m l ≤ N / m + 1 := by
  let S := (Finset.range (N + 1)).filter (fun n => n ≡ l [MOD m])
  have hprimeSub :
      (Finset.range (N + 1)).filter
          (fun p => p.Prime ∧ p ≡ l [MOD m]) ⊆ S := by
    intro p hp
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hp).1, (Finset.mem_filter.mp hp).2.2⟩
  have hinj : Set.InjOn (fun n : ℕ => n / m) S := by
    intro a ha b hb hab
    have hmod : a % m = b % m := by
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      exact ha'.trans hb'.symm
    change a / m = b / m at hab
    calc
      a = a % m + m * (a / m) := (Nat.mod_add_div a m).symm
      _ = b % m + m * (b / m) := by rw [hmod, hab]
      _ = b := Nat.mod_add_div b m
  have himage :
      S.image (fun n => n / m) ⊆ Finset.range (N / m + 1) := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨n, hn, rfl⟩
    have hnN : n ≤ N :=
      Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.div_le_div_right hnN))
  calc
    BombieriVinogradov.primesInAP N m l =
        ((Finset.range (N + 1)).filter
          (fun p => p.Prime ∧ p ≡ l [MOD m])).card := rfl
    _ ≤ S.card := Finset.card_le_card hprimeSub
    _ = (S.image (fun n => n / m)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.range (N / m + 1)).card :=
      Finset.card_le_card himage
    _ = N / m + 1 := Finset.card_range _

/-- Multiplying the preceding residue-class count by its modulus costs at
most one additional modulus. -/
theorem modulus_mul_primesInAP_le
    (N m l : ℕ) (hm : 0 < m) :
    m * BombieriVinogradov.primesInAP N m l ≤ N + m := by
  have hcount := Nat.mul_le_mul_left m (primesInAP_le_div_add_one N m l hm)
  have hdiv : m * (N / m) ≤ N := Nat.mul_div_le N m
  calc
    m * BombieriVinogradov.primesInAP N m l ≤ m * (N / m + 1) :=
      hcount
    _ = m * (N / m) + m := by simp [mul_add]
    _ ≤ N + m := Nat.add_le_add_right hdiv m

/-- One fixed positive constant in the Mertens reciprocal-totient bound. -/
noncomputable def richertReciprocalTotientConstant : ℝ :=
  Classical.choose exists_reciprocal_totient_le_richert_log_div

theorem richertReciprocalTotientConstant_pos :
    0 < richertReciprocalTotientConstant :=
  (Classical.choose_spec exists_reciprocal_totient_le_richert_log_div).1

theorem reciprocal_totient_le_richertConstant_log_div
    {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (1 : ℝ) / m.totient ≤
      richertReciprocalTotientConstant * Real.log N / m :=
  (Classical.choose_spec exists_reciprocal_totient_le_richert_log_div).2
    N m hN hm hmN

/-- The fixed coefficient in the elementary pointwise
`m E*(N,m) ≪ N(1 + log N)` envelope. -/
noncomputable def richert418PointwiseEnvelopeConstant : ℝ :=
  2 + LiuWeight.liuLogarithmicIntegralUpperConstant 0 *
    richertReciprocalTotientConstant / Real.log 2

theorem richert418PointwiseEnvelopeConstant_pos :
    0 < richert418PointwiseEnvelopeConstant := by
  unfold richert418PointwiseEnvelopeConstant
  have hupper :
      0 ≤ LiuWeight.liuLogarithmicIntegralUpperConstant 0 :=
    LiuWeight.liuLogarithmicIntegralUpperConstant_nonneg 0
  have hrecip : 0 ≤ richertReciprocalTotientConstant :=
    richertReciprocalTotientConstant_pos.le
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  positivity

private theorem modulus_mul_abs_primeAPError_le
    {N x m l : ℕ} (hN : 2 ≤ N) (hx : 2 ≤ x) (hxN : x ≤ N)
    (hm : 1 ≤ m) (hmN : m ≤ N) :
    (m : ℝ) * |primeAPError x m l| ≤
      richert418PointwiseEnvelopeConstant * (N : ℝ) *
        (1 + Real.log N) := by
  let L := LiuWeight.liuLogarithmicIntegralUpperConstant 0
  let C := richertReciprocalTotientConstant
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL : 0 ≤ L := LiuWeight.liuLogarithmicIntegralUpperConstant_nonneg 0
  have hC : 0 ≤ C := richertReciprocalTotientConstant_pos.le
  have hli0 :
      |logarithmicIntegral x| ≤ L * (x : ℝ) / Real.log x := by
    simpa [logarithmicIntegral, L] using
      LiuWeight.liuLogarithmicIntegral_abs_le 0
        (show (2 : ℝ) ≤ x by exact_mod_cast hx)
  have hxR : (x : ℝ) ≤ N := by exact_mod_cast hxN
  have hlog2x : Real.log (2 : ℝ) ≤ Real.log (x : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
      (show (x : ℝ) ∈ Set.Ioi 0 by
        exact (show (0 : ℝ) < x by exact_mod_cast (show 0 < x by omega)))
      (by exact_mod_cast hx)
  have hratio :
      (x : ℝ) / Real.log x ≤ (N : ℝ) / Real.log 2 := by
    calc
      (x : ℝ) / Real.log x ≤ (N : ℝ) / Real.log x := by gcongr
      _ ≤ (N : ℝ) / Real.log 2 := by
        exact div_le_div_of_nonneg_left (by positivity) hlog2 hlog2x
  have hli :
      |logarithmicIntegral x| ≤ L * (N : ℝ) / Real.log 2 := by
    calc
      |logarithmicIntegral x| ≤ L * (x : ℝ) / Real.log x := hli0
      _ ≤ L * ((N : ℝ) / Real.log 2) := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_left hratio hL
      _ = L * (N : ℝ) / Real.log 2 := by ring
  have hphi := reciprocal_totient_le_richertConstant_log_div hN hm hmN
  have hmphi :
      (m : ℝ) * ((1 : ℝ) / m.totient) ≤ C * Real.log N := by
    have hmR : 0 ≤ (m : ℝ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hphi hmR
    calc
      (m : ℝ) * ((1 : ℝ) / m.totient) ≤
          (m : ℝ) *
            (richertReciprocalTotientConstant * Real.log N / m) :=
        hscaled
      _ = C * Real.log N := by
        dsimp [C]
        field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmPos.ne']
  have hcountNat := modulus_mul_primesInAP_le x m l hmPos
  have hcount :
      (m : ℝ) * (BombieriVinogradov.primesInAP x m l : ℝ) ≤
        2 * (N : ℝ) := by
    have hcountR :
        (m : ℝ) * (BombieriVinogradov.primesInAP x m l : ℝ) ≤
          (x : ℝ) + m := by exact_mod_cast hcountNat
    have hmNR : (m : ℝ) ≤ N := by exact_mod_cast hmN
    linarith
  have hliTerm :
      (m : ℝ) * (|logarithmicIntegral x| / m.totient) ≤
        (L * C / Real.log 2) * (N : ℝ) * Real.log N := by
    calc
      (m : ℝ) * (|logarithmicIntegral x| / m.totient) =
          |logarithmicIntegral x| *
            ((m : ℝ) * ((1 : ℝ) / m.totient)) := by ring
      _ ≤ (L * (N : ℝ) / Real.log 2) * (C * Real.log N) :=
        mul_le_mul hli hmphi (by positivity) (by positivity)
      _ = (L * C / Real.log 2) * (N : ℝ) * Real.log N := by ring
  have hbasic :
      (m : ℝ) * |primeAPError x m l| ≤
        2 * (N : ℝ) +
          (L * C / Real.log 2) * (N : ℝ) * Real.log N := by
    unfold primeAPError
    calc
      (m : ℝ) *
          |(BombieriVinogradov.primesInAP x m l : ℝ) -
            logarithmicIntegral x / m.totient| ≤
          (m : ℝ) *
            ((BombieriVinogradov.primesInAP x m l : ℝ) +
              |logarithmicIntegral x / m.totient|) := by
        gcongr
        calc
          |(BombieriVinogradov.primesInAP x m l : ℝ) -
              logarithmicIntegral x / m.totient| ≤
              |(BombieriVinogradov.primesInAP x m l : ℝ)| +
                |logarithmicIntegral x / m.totient| := abs_sub _ _
          _ = (BombieriVinogradov.primesInAP x m l : ℝ) +
                |logarithmicIntegral x / m.totient| := by
            rw [abs_of_nonneg (by positivity)]
      _ = (m : ℝ) *
            (BombieriVinogradov.primesInAP x m l : ℝ) +
          (m : ℝ) * (|logarithmicIntegral x| / m.totient) := by
        rw [abs_div]
        have hphi : 0 ≤ (m.totient : ℝ) := by positivity
        rw [abs_of_nonneg hphi]
        ring
      _ ≤ 2 * (N : ℝ) +
          (L * C / Real.log 2) * (N : ℝ) * Real.log N :=
        add_le_add hcount hliTerm
  dsimp [richert418PointwiseEnvelopeConstant, L, C]
  have hcoef :
      0 ≤ LiuWeight.liuLogarithmicIntegralUpperConstant 0 *
        richertReciprocalTotientConstant / Real.log 2 := by positivity
  have hNR : 0 ≤ (N : ℝ) := by positivity
  nlinarith [mul_nonneg hNR hlogN.le]

/-- Uniform pointwise envelope for Richert's exact nested maximum.  It is the
elementary second-factor input in the Cauchy step following (4.22). -/
theorem modulus_mul_primeAPPrefixMaxError_le
    {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) (hmN : m ≤ N) :
    (m : ℝ) * primeAPPrefixMaxError N m ≤
      richert418PointwiseEnvelopeConstant * (N : ℝ) *
        (1 + Real.log N) := by
  let X :=
    richert418PointwiseEnvelopeConstant * (N : ℝ) * (1 + Real.log N)
  have hmR : (0 : ℝ) < m := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hX : 0 ≤ X := by
    dsimp [X]
    have hlogN : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    exact mul_nonneg
      (mul_nonneg richert418PointwiseEnvelopeConstant_pos.le (by positivity))
      (by linarith)
  have hprefix : primeAPPrefixMaxError N m ≤ X / m := by
    unfold primeAPPrefixMaxError
    apply Finset.max'_le
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_image] at hy
    rcases hy with rfl | ⟨x, hx, rfl⟩
    · exact div_nonneg hX hmR.le
    · unfold primeAPResidueMaxError
      apply Finset.max'_le
      intro y hy
      simp only [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨l, hl, rfl⟩
      · exact div_nonneg hX hmR.le
      · apply (le_div_iff₀ hmR).2
        simpa [mul_comm, X] using
          modulus_mul_abs_primeAPError_le hN
            (Finset.mem_Icc.mp hx).1 (Finset.mem_Icc.mp hx).2 hm hmN
  have hscaled := mul_le_mul_of_nonneg_left hprefix hmR.le
  calc
    (m : ℝ) * primeAPPrefixMaxError N m ≤ (m : ℝ) * (X / m) :=
      hscaled
    _ = X := by field_simp [hmR.ne']
    _ = richert418PointwiseEnvelopeConstant * (N : ℝ) *
          (1 + Real.log N) := rfl

/-- The real combined-modulus bound lands in the floor-safe source cutoff.
This is the exact integer form needed before invoking (4.18). -/
theorem chenReducedCombinedModuli_le_liuSourceDEpsilon
    {N m : ℕ} {ε : ℝ} (hm : m ∈ chenReducedCombinedModuli N ε) :
    m ≤ LiuWeight.liuSourceDEpsilon N ε := by
  unfold LiuWeight.liuSourceDEpsilon
  apply Nat.le_floor
  exact chenReducedCombinedModuli_cast_le hm

/-- For every positive level loss and nonnegative logarithmic cutoff exponent,
Chen's exact combined moduli eventually lie in the modulus range of (4.18). -/
theorem eventually_chenReducedCombinedModuli_subset_panModulusCutoff
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∀ᶠ N : ℕ in Filter.atTop,
      chenReducedCombinedModuli N ε ⊆
        Finset.Icc 1 (LiuWeight.panModulusCutoff N B) := by
  filter_upwards
      [LiuWeight.eventually_liuSourceDEpsilon_le_panModulusCutoff ε B hε hB]
      with N hcut
  intro m hm
  have hmPos : 0 < m := by
    rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hmImage⟩
    rcases Finset.mem_image.mp hmImage with ⟨d, hd, rfl⟩
    have hqPos :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1.pos
    have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    exact Nat.mul_pos hqPos (Nat.pos_of_dvd_of_pos hdDiv
      (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N)))
  exact Finset.mem_Icc.mpr
    ⟨hmPos, (chenReducedCombinedModuli_le_liuSourceDEpsilon hm).trans hcut⟩

/-- Quantified ordinary (4.18), specialized by finite subset monotonicity to
Chen's exact combined-modulus carrier. -/
theorem eventually_sum_richertEStar_combined_le_of_ordinary418
    (h418 : Richert418BombieriVinogradov)
    (ε U : ℝ) (hε : 0 < ε) (hU : 0 < U) :
    ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
      ∀ᶠ N : ℕ in Filter.atTop,
        (∑ m ∈ chenReducedCombinedModuli N ε,
          primeAPPrefixMaxError N m) ≤
            K * (N : ℝ) / Real.log N ^ U := by
  obtain ⟨B, hB, K, hK, hordinary⟩ := h418 U hU
  refine ⟨B, hB, K, hK, ?_⟩
  have hsubset :=
    eventually_chenReducedCombinedModuli_subset_panModulusCutoff
      ε B hε hB.le
  filter_upwards [hsubset, hordinary, Filter.eventually_ge_atTop 2]
      with N hSN hordinaryN hN
  have hsum :
      (∑ m ∈ chenReducedCombinedModuli N ε,
          primeAPPrefixMaxError N m) ≤
        ∑ m ∈ Finset.Icc 1 (LiuWeight.panModulusCutoff N B),
          primeAPPrefixMaxError N m := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hSN
    intro m hm hmNot
    exact primeAPPrefixMaxError_nonneg N m
  exact hsum.trans (hordinaryN hN)

/-- Every combined modulus is a medium prime times a coprime squarefree
sifting divisor; both finite Lemma 3 payments use this same fact. -/
private theorem chenReducedCombinedModuli_squarefree
    {N m : ℕ} {ε : ℝ} (hm : m ∈ chenReducedCombinedModuli N ε) :
    Squarefree m := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨d, hd, rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqPrime := (Finset.mem_filter.mp hqSource).2.1
  have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hdSquarefree :=
    (jurkatRichertSourceSiftingProduct_squarefree N).squarefree_of_dvd hdDiv
  have hcop :=
    jurkatRichertSourceMediumPrime_coprime_siftingDivisor hqSource hdDiv
  exact (Nat.squarefree_mul hcop).mpr ⟨hqPrime.squarefree, hdSquarefree⟩

/-- Floor-safe form of Richert's Cauchy/Lemma 3 payment on Chen's exact
combined moduli.  Its only distribution premise is the ordinary unweighted
initial-range mass from (4.18). -/
theorem chenReducedPairWeightedEStar_sq_le_of_ordinary418_floorSafe
    (N Q : ℕ) (ε B : ℝ) (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hsubset : chenReducedCombinedModuli N ε ⊆ Finset.Icc 1 Q)
    (hOrdinary418 :
      (∑ m ∈ Finset.Icc 1 Q, primeAPPrefixMaxError N m) ≤ B) :
    ∃ C : ℝ, 0 < C ∧
      chenReducedPairWeightedEStar N ε ^ 2 ≤
        (C * (Real.log (Q + 2)) ^ (9 : ℝ)) *
          ((richert418PointwiseEnvelopeConstant * (N : ℝ) *
            (1 + Real.log N)) * B) := by
  let S := chenReducedCombinedModuli N ε
  let E := primeAPPrefixMaxError N
  have hS : S ⊆ Finset.range (Q + 1) := by
    intro m hm
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp (hsubset hm)).2)
  have hSquarefree : ∀ m ∈ S, Squarefree m :=
    fun _ hm => chenReducedCombinedModuli_squarefree hm
  have hE : ∀ m ∈ S, 0 ≤ E m := by
    intro m hm
    exact primeAPPrefixMaxError_nonneg N m
  have henvelope : ∀ m ∈ S,
      (m : ℝ) * E m ≤
        richert418PointwiseEnvelopeConstant * (N : ℝ) *
          (1 + Real.log N) := by
    intro m hm
    have hmIcc := Finset.mem_Icc.mp (hsubset hm)
    have hmN : m ≤ N := by
      have hmReal := chenReducedCombinedModuli_cast_le hm
      have hpow :
          (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) := by
        exact Real.rpow_le_self_of_one_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
      exact_mod_cast hmReal.trans hpow
    exact modulus_mul_primeAPPrefixMaxError_le hN hmIcc.1 hmN
  have hordinaryS : (∑ m ∈ S, E m) ≤ B := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun m hm hmNot => primeAPPrefixMaxError_nonneg N m)).trans
        hOrdinary418
  obtain ⟨C, hC, hmass⟩ :=
    threeOmegaError_sq_le_of_ordinaryBombieri_squarefree
      S Q E
        (richert418PointwiseEnvelopeConstant * (N : ℝ) *
          (1 + Real.log N))
        B hS hSquarefree hE
        (by
          have hlog : 0 ≤ Real.log (N : ℝ) :=
            Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
          exact mul_nonneg
            (mul_nonneg richert418PointwiseEnvelopeConstant_pos.le
              (by positivity))
            (by linarith))
        henvelope hordinaryS
  refine ⟨C, hC, ?_⟩
  have hpairNonneg : 0 ≤ chenReducedPairWeightedEStar N ε := by
    unfold chenReducedPairWeightedEStar
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (primeAPPrefixMaxError_nonneg N (q * d))
  have hcombinedNonneg : 0 ≤ threeOmegaErrorMass S E := by
    unfold threeOmegaErrorMass
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (primeAPPrefixMaxError_nonneg N m)
  calc
    chenReducedPairWeightedEStar N ε ^ 2 ≤
        threeOmegaErrorMass S E ^ 2 :=
      (sq_le_sq₀ hpairNonneg hcombinedNonneg).2
        (chenReducedPairWeightedEStar_le_combinedMass N ε)
    _ ≤ (C * (Real.log (Q + 2)) ^ (9 : ℝ)) *
          ((richert418PointwiseEnvelopeConstant * (N : ℝ) *
            (1 + Real.log N)) * B) := hmass

/-- The fixed pointwise-envelope coefficient after translating back from
Richert's literal integral to the project's standard normalization. -/
noncomputable def richertStandardPointwiseEnvelopeConstant : ℝ :=
  richert418PointwiseEnvelopeConstant +
    (2 / Real.log 2) * richertReciprocalTotientConstant

theorem richertStandardPointwiseEnvelopeConstant_pos :
    0 < richertStandardPointwiseEnvelopeConstant := by
  unfold richertStandardPointwiseEnvelopeConstant
  exact add_pos_of_pos_of_nonneg richert418PointwiseEnvelopeConstant_pos
    (mul_nonneg (by positivity) richertReciprocalTotientConstant_pos.le)

/-- The explicit fixed normalization shift preserves the same
`N(1 + log N)` pointwise envelope on every Chen combined modulus. -/
theorem modulus_mul_standardPrimeAPMaxError_le_on_combined
    {N m : ℕ} {ε : ℝ} (hN : 2 ≤ N)
    (hm : m ∈ chenReducedCombinedModuli N ε) (hε : 0 ≤ ε) :
    (m : ℝ) * BombieriVinogradov.standardPrimeAPMaxError N m ≤
      richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
        (1 + Real.log N) := by
  rcases Finset.mem_biUnion.mp hm with ⟨q, hq, hmImage⟩
  rcases Finset.mem_image.mp hmImage with ⟨d, hd, rfl⟩
  have hqSource := (Finset.mem_filter.mp hq).1
  have hqN := (Finset.mem_filter.mp hq).2
  have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
    Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
  have hqPos := (Finset.mem_filter.mp hqSource).2.1.pos
  have hdPos := Nat.pos_of_dvd_of_pos hdDiv
    (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
  have hmPos : 0 < q * d := Nat.mul_pos hqPos hdPos
  have hres :
      (AnalyticNumberTheory.Sieve.unitResidues (q * d)).Nonempty :=
    ⟨N % (q * d),
      jurkatRichertSource_mul_mod_mem_unitResidues hqSource hdDiv hqN⟩
  have hmN : q * d ≤ N := by
    have hmReal := chenReducedCombinedModuli_cast_le
      (show q * d ∈ chenReducedCombinedModuli N ε from hm)
    have hpow :
        (N : ℝ) ^ (1 / 2 - ε) ≤ (N : ℝ) :=
      Real.rpow_le_self_of_one_le
        (by exact_mod_cast (show 1 ≤ N by omega)) (by linarith)
    exact_mod_cast hmReal.trans hpow
  have hcompare :=
    standardPrimeAPMaxError_le_richertEStar_add
      N (q * d) hN hmPos hres
  have hscaled := mul_le_mul_of_nonneg_left hcompare
    (show 0 ≤ ((q * d : ℕ) : ℝ) by positivity)
  have hestar :=
    modulus_mul_primeAPPrefixMaxError_le hN hmPos hmN
  have hphi :=
    reciprocal_totient_le_richertConstant_log_div hN hmPos hmN
  have hshift :
      ((q * d : ℕ) : ℝ) * richert418NormalizationShift (q * d) ≤
        (2 / Real.log 2) * richertReciprocalTotientConstant *
          Real.log N := by
    unfold richert418NormalizationShift
    have hmul := mul_le_mul_of_nonneg_left hphi
      (show 0 ≤ ((q * d : ℕ) : ℝ) * (2 / Real.log 2) by positivity)
    calc
      ((q * d : ℕ) : ℝ) *
          ((2 / Real.log 2) / Nat.totient (q * d)) =
        (((q * d : ℕ) : ℝ) * (2 / Real.log 2)) *
          ((1 : ℝ) / Nat.totient (q * d)) := by ring
      _ ≤ (((q * d : ℕ) : ℝ) * (2 / Real.log 2)) *
          (richertReciprocalTotientConstant * Real.log N /
            ((q * d : ℕ) : ℝ)) :=
        hmul
      _ = (2 / Real.log 2) * richertReciprocalTotientConstant *
          Real.log N := by
        field_simp [show (((q * d : ℕ) : ℝ)) ≠ 0 by
          exact_mod_cast hmPos.ne']
  have hlogN : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hNR : 1 ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogScale :
      Real.log (N : ℝ) ≤ (N : ℝ) * (1 + Real.log N) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hNR) hlogN]
  have hkappaC :
      0 ≤ (2 / Real.log 2) * richertReciprocalTotientConstant := by
    exact mul_nonneg (by positivity)
      richertReciprocalTotientConstant_pos.le
  have hshiftLarge :
      ((q * d : ℕ) : ℝ) * richert418NormalizationShift (q * d) ≤
        ((2 / Real.log 2) * richertReciprocalTotientConstant) *
          ((N : ℝ) * (1 + Real.log N)) :=
    hshift.trans (mul_le_mul_of_nonneg_left hlogScale hkappaC)
  calc
    ((q * d : ℕ) : ℝ) *
        BombieriVinogradov.standardPrimeAPMaxError N (q * d) ≤
      ((q * d : ℕ) : ℝ) *
        (primeAPPrefixMaxError N (q * d) +
          richert418NormalizationShift (q * d)) := hscaled
    _ = ((q * d : ℕ) : ℝ) * primeAPPrefixMaxError N (q * d) +
        ((q * d : ℕ) : ℝ) * richert418NormalizationShift (q * d) := by ring
    _ ≤ richert418PointwiseEnvelopeConstant * (N : ℝ) *
          (1 + Real.log N) +
        ((2 / Real.log 2) * richertReciprocalTotientConstant) *
          ((N : ℝ) * (1 + Real.log N)) :=
      add_le_add hestar hshiftLarge
    _ = richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
          (1 + Real.log N) := by
      unfold richertStandardPointwiseEnvelopeConstant
      ring

private theorem chenReducedCombinedModulusFibres_pairwise_standard
    (N : ℕ) (ε : ℝ) :
    ∀ q₁ ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
      ∀ q₂ ∈ (jurkatRichertSourceMediumPrimes N).filter (fun q => ¬q ∣ N),
        q₁ ≠ q₂ →
          Disjoint
            (((jurkatRichertSourceSiftingProduct N).divisors.filter
              fun d => d < jurkatRichertSourceUpperLevel N q₁ ε).image
                fun d => q₁ * d)
            (((jurkatRichertSourceSiftingProduct N).divisors.filter
              fun d => d < jurkatRichertSourceUpperLevel N q₂ ε).image
                fun d => q₂ * d) := by
  exact MathlibNt.SieveTheory.Richert1969.chenReducedCombinedModulusFibres_pairwise N ε

/-- The exact injective `(q,d) ↦ qd` reindexing pays the `3^ω(d)` weight for
the project's standard endpoint errors as well. -/
theorem chenReducedWeightedBVSum_le_combinedMass
    (N : ℕ) (ε : ℝ) :
    jurkatRichertSourceReducedWeightedBVSum N ε ≤
      threeOmegaErrorMass (chenReducedCombinedModuli N ε)
        (BombieriVinogradov.standardPrimeAPMaxError N) := by
  unfold jurkatRichertSourceReducedWeightedBVSum threeOmegaErrorMass
  unfold chenReducedCombinedModuli
  rw [Finset.sum_biUnion
    (chenReducedCombinedModulusFibres_pairwise_standard N ε)]
  apply Finset.sum_le_sum
  intro q hq
  rw [Finset.sum_image]
  · apply Finset.sum_le_sum
    intro d hd
    have hqPrime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    have hdDiv : d ∣ jurkatRichertSourceSiftingProduct N :=
      Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdPos := Nat.pos_of_dvd_of_pos hdDiv
      (Nat.pos_of_ne_zero (jurkatRichertSourceSiftingProduct_ne_zero N))
    have hsubset : d.primeFactors ⊆ (q * d).primeFactors := by
      rw [Nat.primeFactors_mul hqPrime.ne_zero hdPos.ne']
      exact Finset.subset_union_right
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3)
        (Finset.card_le_card hsubset))
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N (q * d))
  · intro d₁ hd₁ d₂ hd₂ hmul
    have hqPrime :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2.1
    exact Nat.mul_left_cancel hqPrime.pos hmul

/-- One fixed positive constant in Richert's Lemma 3 payment at `h = 9`. -/
noncomputable def richertLemma3NineConstant : ℝ :=
  Classical.choose lemma3NineOmegaMass_le_polylog

theorem richertLemma3NineConstant_pos :
    0 < richertLemma3NineConstant :=
  (Classical.choose_spec lemma3NineOmegaMass_le_polylog).1

theorem lemma3NineOmegaMass_le_richertConstant
    (Q : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.range (Q + 1))
    (hSquarefree : ∀ d ∈ S, Squarefree d) :
    lemma3NineOmegaMass S ≤
      richertLemma3NineConstant * (Real.log (Q + 2)) ^ (9 : ℝ) :=
  (Classical.choose_spec lemma3NineOmegaMass_le_polylog).2
    Q S hS hSquarefree

/-- Standard endpoint-error version of the floor-safe finite payment.  The
ordinary input remains the unweighted prefix-maximal Bombieri mass. -/
theorem chenReducedWeightedBVSum_sq_le_of_ordinary
    (N Q : ℕ) (ε B : ℝ) (hN : 2 ≤ N) (hε : 0 ≤ ε)
    (hsubset : chenReducedCombinedModuli N ε ⊆ Finset.Icc 1 Q)
    (hOrdinary :
      (∑ m ∈ Finset.Icc 1 Q,
        BombieriVinogradov.standardPrimeAPPrefixMaxError N m) ≤ B) :
    jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
      (richertLemma3NineConstant *
        (Real.log (Q + 2)) ^ (9 : ℝ)) *
      ((richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
        (1 + Real.log N)) * B) := by
  let S := chenReducedCombinedModuli N ε
  let E := BombieriVinogradov.standardPrimeAPMaxError N
  let X :=
    richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
      (1 + Real.log N)
  have hS : S ⊆ Finset.range (Q + 1) := by
    intro m hm
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Finset.mem_Icc.mp (hsubset hm)).2)
  have hSquarefree : ∀ m ∈ S, Squarefree m :=
    fun _ hm => chenReducedCombinedModuli_squarefree hm
  have hE : ∀ m ∈ S, 0 ≤ E m := by
    intro m hm
    exact BombieriVinogradov.standardPrimeAPMaxError_nonneg N m
  have hX : 0 ≤ X := by
    dsimp [X]
    have hlog : 0 ≤ Real.log (N : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
    exact mul_nonneg
      (mul_nonneg richertStandardPointwiseEnvelopeConstant_pos.le
        (by positivity))
      (by linarith)
  have henvelope : ∀ m ∈ S, (m : ℝ) * E m ≤ X := by
    intro m hm
    exact modulus_mul_standardPrimeAPMaxError_le_on_combined hN hm hε
  have hordinaryS : (∑ m ∈ S, E m) ≤ B := by
    calc
      (∑ m ∈ S, E m) ≤
          ∑ m ∈ Finset.Icc 1 Q, E m :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset
          (fun m hm hmNot =>
            BombieriVinogradov.standardPrimeAPMaxError_nonneg N m)
      _ ≤ ∑ m ∈ Finset.Icc 1 Q,
          BombieriVinogradov.standardPrimeAPPrefixMaxError N m :=
        BombieriVinogradov.sum_standardPrimeAPMaxError_le_prefixMaxError
          N (Finset.Icc 1 Q)
      _ ≤ B := hOrdinary
  have hcauchy :=
    weightedError_sq_le_lemma3Mass_mul_ordinary S
      (fun m => (3 : ℝ) ^ m.primeFactors.card) E X
      (fun m hm => (Finset.mem_Icc.mp (hsubset hm)).1)
      hE henvelope
  have hmass :
      (∑ m ∈ S,
          ((3 : ℝ) ^ m.primeFactors.card) ^ 2 / (m : ℝ)) =
        lemma3NineOmegaMass S := by
    unfold lemma3NineOmegaMass
    apply Finset.sum_congr rfl
    intro m hm
    rw [pow_two, ← mul_pow]
    norm_num
  rw [hmass] at hcauchy
  have hlemma :=
    lemma3NineOmegaMass_le_richertConstant Q S hS hSquarefree
  have hcombined :
      threeOmegaErrorMass S E ^ 2 ≤
        (richertLemma3NineConstant *
          (Real.log (Q + 2)) ^ (9 : ℝ)) * (X * B) := by
    calc
      threeOmegaErrorMass S E ^ 2 ≤
          lemma3NineOmegaMass S * (X * ∑ m ∈ S, E m) := by
        simpa [threeOmegaErrorMass] using hcauchy
      _ ≤ (richertLemma3NineConstant *
          (Real.log (Q + 2)) ^ (9 : ℝ)) *
            (X * ∑ m ∈ S, E m) := by
        exact mul_le_mul_of_nonneg_right hlemma
          (mul_nonneg hX (Finset.sum_nonneg fun m hm => hE m hm))
      _ ≤ (richertLemma3NineConstant *
          (Real.log (Q + 2)) ^ (9 : ℝ)) * (X * B) := by
        gcongr
        exact mul_nonneg richertLemma3NineConstant_pos.le
          (Real.rpow_nonneg
            (Real.log_nonneg (by exact_mod_cast
              (show 1 ≤ Q + 2 by omega))) 9)
  have hleft : 0 ≤ jurkatRichertSourceReducedWeightedBVSum N ε := by
    unfold jurkatRichertSourceReducedWeightedBVSum
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N (q * d))
  have hright : 0 ≤ threeOmegaErrorMass S E := by
    unfold threeOmegaErrorMass
    apply Finset.sum_nonneg
    intro m hm
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N m)
  have hsquare :
      jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
        threeOmegaErrorMass S E ^ 2 :=
    (sq_le_sq₀ hleft hright).2
      (chenReducedWeightedBVSum_le_combinedMass N ε)
  simpa [X] using hsquare.trans hcombined

/-- Pan's floor cutoff is at most the endpoint once `N ≥ 3` and the
logarithmic exponent is nonnegative. -/
theorem panModulusCutoff_le_endpoint
    (N : ℕ) (B : ℝ) (hN : 3 ≤ N) (hB : 0 ≤ B) :
    LiuWeight.panModulusCutoff N B ≤ N := by
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have he1 : Real.exp 1 < (3 : ℝ) :=
      Real.exp_one_lt_d9.trans (by norm_num)
    exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
      (he1.trans_le (by exact_mod_cast hN)) |>.le
  have hden : 1 ≤ Real.log (N : ℝ) ^ B :=
    Real.one_le_rpow hlog hB
  unfold LiuWeight.panModulusCutoff
  have hreal :
      (↑⌊(N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B⌋₊ : ℝ) ≤ N := by
    calc
      (↑⌊(N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B⌋₊ : ℝ) ≤
          (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B :=
        Nat.floor_le (by positivity)
      _ ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        div_le_self (Real.rpow_nonneg (by positivity) _) hden
      _ ≤ (N : ℝ) :=
        Real.rpow_le_self_of_one_le
          (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  exact_mod_cast hreal

private theorem log_cutoff_add_two_le_two_log
    {N Q : ℕ} (hN : 2 ≤ N) (hQ : Q ≤ N) :
    Real.log (Q + 2 : ℕ) ≤ 2 * Real.log N := by
  have hQN : Q + 2 ≤ N ^ 2 := by nlinarith
  have hposQ : (0 : ℝ) < Q + 2 := by positivity
  have hposN2 : (0 : ℝ) < N ^ 2 := by positivity
  calc
    Real.log (Q + 2 : ℕ) = Real.log ((Q : ℝ) + 2) := by norm_num
    _ ≤ Real.log ((N : ℝ) ^ 2) :=
      Real.strictMonoOn_log.monotoneOn hposQ hposN2
        (by exact_mod_cast hQN)
    _ = 2 * Real.log N := by
      rw [Real.log_pow]
      norm_num

/-- Ordinary Bombieri--Vinogradov pays Chen's exact `3^ω`-weighted
varying-level remainder.  The proof uses the quantified exponent
`U = 2A + 10`: nine logarithms are Richert Lemma 3 and one is the pointwise
`m E` envelope. -/
theorem chenWeightedBombieriVinogradov_of_standard
    (hBV : BombieriVinogradov.StandardBombieriVinogradov) :
    ChenJurkatRichertVaryingQWeightedBombieriVinogradov := by
  intro ε hε hεSixth A hA
  let U := 2 * A + 10
  have hU : 0 < U := by dsimp [U]; linarith
  obtain ⟨B, hB, K, hK, hordinary⟩ := hBV U hU
  let D :=
    richertLemma3NineConstant * (2 ^ (10 : ℕ) : ℝ) *
      richertStandardPointwiseEnvelopeConstant * K
  let C := Real.sqrt D + 1
  have hD : 0 ≤ D := by
    dsimp [D]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg richertLemma3NineConstant_pos.le (by positivity))
        richertStandardPointwiseEnvelopeConstant_pos.le)
      hK.le
  have hC : 0 < C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  have hsubset :=
    eventually_chenReducedCombinedModuli_subset_panModulusCutoff
      ε B hε hB
  filter_upwards [hsubset, hordinary, Filter.eventually_ge_atTop 3]
      with N hSN hordinaryN hN
  have hN2 : 2 ≤ N := by omega
  let Q := LiuWeight.panModulusCutoff N B
  have hQN : Q ≤ N := panModulusCutoff_le_endpoint N B hN hB
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hlogQ :
      Real.log (Q + 2 : ℕ) ≤ 2 * Real.log N :=
    log_cutoff_add_two_le_two_log hN2 hQN
  have hlogQReal :
      Real.log ((Q : ℝ) + 2) ≤ 2 * Real.log N := by
    simpa [Nat.cast_add] using hlogQ
  have honeLog : 1 + Real.log (N : ℝ) ≤ 2 * Real.log N := by
    have hlogOne : 1 ≤ Real.log (N : ℝ) := by
      have he1 : Real.exp 1 < (3 : ℝ) :=
        Real.exp_one_lt_d9.trans (by norm_num)
      exact (Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < N)).2
        (he1.trans_le (by exact_mod_cast hN)) |>.le
    linarith
  have hsquare :=
    chenReducedWeightedBVSum_sq_le_of_ordinary
      N Q ε (K * (N : ℝ) / Real.log N ^ U) hN2 hε.le hSN
        (hordinaryN hN2)
  have hlogQNonneg : 0 ≤ Real.log ((Q : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  have hmajor :
      jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
        D * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
    calc
      jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
          (richertLemma3NineConstant *
            (Real.log (Q + 2)) ^ (9 : ℝ)) *
          ((richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
            (1 + Real.log N)) *
              (K * (N : ℝ) / Real.log N ^ U)) := hsquare
      _ ≤ (richertLemma3NineConstant *
            (2 * Real.log N) ^ (9 : ℝ)) *
          ((richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
            (2 * Real.log N)) *
              (K * (N : ℝ) / Real.log N ^ U)) := by
        have hrpow :
            Real.log ((Q : ℝ) + 2) ^ (9 : ℝ) ≤
              (2 * Real.log N) ^ (9 : ℝ) :=
          Real.rpow_le_rpow hlogQNonneg hlogQReal (by norm_num)
        have hfirst :
            richertLemma3NineConstant *
                Real.log ((Q : ℝ) + 2) ^ (9 : ℝ) ≤
              richertLemma3NineConstant *
                (2 * Real.log N) ^ (9 : ℝ) :=
          mul_le_mul_of_nonneg_left hrpow richertLemma3NineConstant_pos.le
        have hsecond :
            richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
                (1 + Real.log N) ≤
              richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
                (2 * Real.log N) :=
          mul_le_mul_of_nonneg_left honeLog
            (mul_nonneg richertStandardPointwiseEnvelopeConstant_pos.le
              (by positivity))
        have hfactor : 0 ≤ K * (N : ℝ) / Real.log N ^ U := by
          exact div_nonneg (mul_nonneg hK.le (by positivity))
            (Real.rpow_nonneg hlog.le _)
        have hlowerSecond :
            0 ≤
            (richertStandardPointwiseEnvelopeConstant * (N : ℝ) *
              (1 + Real.log N)) *
              (K * (N : ℝ) / Real.log N ^ U) :=
          mul_nonneg
            (mul_nonneg
            (mul_nonneg richertStandardPointwiseEnvelopeConstant_pos.le
              (by positivity))
            (by linarith))
            hfactor
        have hupperFirst :
            0 ≤ richertLemma3NineConstant *
            (2 * Real.log N) ^ (9 : ℝ) :=
          mul_nonneg richertLemma3NineConstant_pos.le
            (Real.rpow_nonneg (by positivity) _)
        exact mul_le_mul hfirst
          (mul_le_mul_of_nonneg_right hsecond hfactor)
          hlowerSecond hupperFirst
      _ = D * ((N : ℝ) / Real.log N ^ A) ^ 2 := by
        have hpowU :
            Real.log N ^ U =
              (Real.log N ^ A) ^ (2 : ℝ) *
                Real.log N ^ (10 : ℝ) := by
          dsimp [U]
          rw [show 2 * A + 10 = A * 2 + 10 by ring,
            Real.rpow_add hlog, Real.rpow_mul hlog.le]
        rw [hpowU]
        rw [show (Real.log N ^ A) ^ (2 : ℝ) =
            (Real.log N ^ A) ^ (2 : ℕ) by
          exact Real.rpow_natCast _ 2]
        rw [show Real.log N ^ (10 : ℝ) =
            Real.log N ^ (10 : ℕ) by
          exact Real.rpow_natCast _ 10]
        rw [show (2 * Real.log N) ^ (9 : ℝ) =
            (2 * Real.log N) ^ (9 : ℕ) by
          exact Real.rpow_natCast _ 9]
        dsimp [D]
        field_simp [hlog.ne']
  have hleft : 0 ≤ jurkatRichertSourceReducedWeightedBVSum N ε := by
    unfold jurkatRichertSourceReducedWeightedBVSum
    apply Finset.sum_nonneg
    intro q hq
    apply Finset.sum_nonneg
    intro d hd
    exact mul_nonneg (pow_nonneg (by norm_num) _)
      (BombieriVinogradov.standardPrimeAPMaxError_nonneg N (q * d))
  have htargetNonneg : 0 ≤ C * (N : ℝ) / Real.log N ^ A := by
    positivity
  have hDsquare : D ≤ C ^ 2 := by
    dsimp [C]
    nlinarith [Real.sq_sqrt hD, Real.sqrt_nonneg D]
  have hmajor' :
      jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
        (C * (N : ℝ) / Real.log N ^ A) ^ 2 := by
    calc
      jurkatRichertSourceReducedWeightedBVSum N ε ^ 2 ≤
          D * ((N : ℝ) / Real.log N ^ A) ^ 2 := hmajor
      _ ≤ C ^ 2 * ((N : ℝ) / Real.log N ^ A) ^ 2 := by gcongr
      _ = (C * (N : ℝ) / Real.log N ^ A) ^ 2 := by ring
  exact (sq_le_sq₀ hleft htargetNonneg).1 hmajor'

/-- Chen-facing Richert source chain with Theorem A honestly imported and the
weighted varying-level error derived from ordinary Bombieri--Vinogradov
`(4.18)`.  The lower object, conditioned upper sieves, squareful correction,
and Stieltjes prime integral are assembled by the source-faithful Theorem 1
endpoint. -/
theorem chenWeightedLowerBound_of_importedTheoremA_and_standardBombieri
    (hLowerTheoremA : DimensionOneLowerRosserDensityFundamentalLemma)
    (hOrdinaryBombieri : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperTheoremA : DimensionOneUpperRosserDensityFundamentalLemma) :
    ChenJurkatRichertWeightedLowerBound :=
  Chen.weightedLowerBound_of_importedTheoremA
    hLowerTheoremA hOrdinaryBombieri hUpperTheoremA
      (chenWeightedBombieriVinogradov_of_standard hOrdinaryBombieri)

/-- A single certificate carrying every literal Richert source stage used for
the Chen-facing specialization.  The finite Theorem 1 and `(A4)` fields record
their exact conditional statements; the analytic endpoint retains Theorem A
as an imported dependency. -/
structure ChenFacingSourceChainCertificate : Prop where
  theoremOneFinite :
    ∀ (A : Finset ℕ) (X : ℝ) (K : ℕ) (v u lambda : ℝ),
      0 ≤ lambda →
      (∀ p ∈ theoremOneWeightedPrimes X K u v,
        0 ≤ theoremOnePrimeWeight X u p) →
      ((lowerCarrier A (theoremOneSiftingProduct X K v)).card : ℝ) -
          squarefulCorrection A (theoremOneWeightedPrimes X K u v)
            (theoremOneSiftingProduct X K v) -
          lambda * primeConditionedUpperAggregate A
            (theoremOneWeightedPrimes X K u v)
            (theoremOneSiftingProduct X K v)
            (theoremOnePrimeWeight X u) ≤
        theoremOneWeightedLowerObject A X K v u lambda
  lowerS :
    ∀ N : ℕ,
      (jurkatRichertSourceBoundingSieve N).siftedSum =
        (jurkatRichertSourceCandidates N).card
  conditionedUpperS :
    ∀ (N p : ℕ),
      (jurkatRichertSourceConditionedBoundingSieve N p).siftedSum =
        ((jurkatRichertSourceCandidates N).filter
          fun q => p ∣ N - q).card
  weightedObject :
    ∀ N : ℕ,
      jurkatRichertSourceWeightedCount N =
        ((jurkatRichertSourceCandidates N).card : ℝ) -
          jurkatRichertSourceMediumPrimeAggregate N / 2
  squarefulA4 :
    ∀ (A : Finset ℕ) (X : ℝ) (K : ℕ) (v u A4 : ℝ),
      SquarefulA4On A (theoremOneWeightedPrimes X K u v) X A4 →
      squarefulCorrection A (theoremOneWeightedPrimes X K u v)
          (theoremOneSiftingProduct X K v) ≤
        ∑ p ∈ theoremOneWeightedPrimes X K u v,
          A4 * (X * Real.log X / (p : ℝ) ^ 2 + 1)
  stieltjesPrimeIntegral :
    ChenJurkatRichertVaryingQPrimeSumAsymptotic
  weightedBombieri :
    ChenJurkatRichertVaryingQWeightedBombieriVinogradov
  weightedLowerBound :
    ChenJurkatRichertWeightedLowerBound

/-- Complete source-chain certificate from lower/upper Theorem A and ordinary
Bombieri--Vinogradov.  In particular, the `3^ω` statement is a conclusion,
not an additional premise. -/
theorem chenFacingSourceChainCertificate_of_importedTheoremA_and_standardBombieri
    (hLowerTheoremA : DimensionOneLowerRosserDensityFundamentalLemma)
    (hOrdinaryBombieri : BombieriVinogradov.StandardBombieriVinogradov)
    (hUpperTheoremA : DimensionOneUpperRosserDensityFundamentalLemma) :
    ChenFacingSourceChainCertificate where
  theoremOneFinite := theoremOneFiniteLowerBound
  lowerS := Chen.lowerS_eq_candidateCard
  conditionedUpperS := Chen.primeConditionedUpperS_eq_candidateCard
  weightedObject := Chen.weightedLowerObject_eq_lower_sub_half_conditioned
  squarefulA4 := theoremOneSquarefulCorrection_le_sum_A4
  stieltjesPrimeIntegral := Chen.stieltjesPrimeIntegral
  weightedBombieri :=
    chenWeightedBombieriVinogradov_of_standard hOrdinaryBombieri
  weightedLowerBound :=
    chenWeightedLowerBound_of_importedTheoremA_and_standardBombieri
      hLowerTheoremA hOrdinaryBombieri hUpperTheoremA

end MathlibNt.SieveTheory.Richert1969
