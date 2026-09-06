import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanPrimePowerCorrection
import AnalyticNumberTheory.LargeSieve.CharacterIndicators

/-!
# Character form of Liu's prime-power correction

The coefficient below records every admissible ordered Liu pair and every
prime-power correction factor separately.  Thus no multiplicity is lost before
the progression condition is converted to characters.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset
open AnalyticNumberTheory.Sieve
open AnalyticNumberTheory.LargeSieve
open ArithmeticFunction

/-- The nonnegative non-prime part of the logarithmically normalized
von Mangoldt function. -/
noncomputable def liuPanPrimePowerKappa (m : ℕ) : ℝ :=
  if m.Prime then 0 else Λ m / Real.log (m : ℝ)

/-- The finite multiplicity-preserving coefficient obtained from Liu's ordered
prime-pair source and the non-prime von Mangoldt correction. -/
noncomputable def liuPanPrimePowerCoefficient (N n : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    ∑ m ∈ range (N + 1),
      if p.1 * p.2 * m = n then liuPanPrimePowerKappa m else 0

/-- The progression partial sum of the multiplicity-preserving coefficient. -/
noncomputable def liuPanPrimePowerAPSum (N y q l : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1),
    liuPanPrimePowerCoefficient N n * if n ≡ l [MOD q] then 1 else 0

/-- The same AP sum before the finite product coefficient is collected. -/
noncomputable def liuPanPrimePowerSourceAPSum (N y q l : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    ∑ m ∈ range (N + 1),
      liuPanPrimePowerKappa m *
        if p.1 * p.2 * m ≤ y ∧ p.1 * p.2 * m ≡ l [MOD q] then 1 else 0

/-- The source AP sum with the coprimality gate appearing in Liu's signed
correction bound still displayed. -/
noncomputable def liuPanPrimePowerCoprimeSourceAPSum (N y q l : ℕ) : ℝ :=
  ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
    if (p.1 * p.2).Coprime q then
      ∑ m ∈ range (N + 1), liuPanPrimePowerKappa m *
        if p.1 * p.2 * m ≤ y ∧ p.1 * p.2 * m ≡ l [MOD q] then 1 else 0
    else 0

/-- The full character mean attached to the coefficient AP sum. -/
noncomputable def liuPanPrimePowerCharacterMean (N y q l : ℕ) : ℂ :=
  (Nat.totient q : ℂ)⁻¹ *
    ∑ χ : DirichletCharacter ℂ q,
      star (χ (l : ZMod q)) *
        ∑ n ∈ range (y + 1),
          (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)

/-- The unprogressed coefficient mass through `y`. -/
noncomputable def liuPanPrimePowerTotal (N y : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), liuPanPrimePowerCoefficient N n

/-- The coefficient mass through `y` on integers coprime to `q`.  This is the
mass selected by the principal Dirichlet character modulo `q`. -/
noncomputable def liuPanPrimePowerCoprimeTotal (N y q : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1),
    liuPanPrimePowerCoefficient N n * if n.Coprime q then 1 else 0

/-- The complementary coefficient mass through `y` on nonunits modulo `q`. -/
noncomputable def liuPanPrimePowerNoncoprimeTotal (N y q : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1),
    liuPanPrimePowerCoefficient N n * if n.Coprime q then 0 else 1

/-- The real character discrepancy: the real part of the full character mean
minus its principal density contribution. -/
noncomputable def liuPanPrimePowerDiscrepancy (N y q l : ℕ) : ℝ :=
  (liuPanPrimePowerCharacterMean N y q l).re -
    liuPanPrimePowerTotal N y / Nat.totient q

/-- The genuine nonprincipal discrepancy: the AP sum minus the mass selected
by the principal character, divided by `φ(q)`. -/
noncomputable def liuPanPrimePowerNonprincipalDiscrepancy
    (N y q l : ℕ) : ℝ :=
  liuPanPrimePowerAPSum N y q l -
    liuPanPrimePowerCoprimeTotal N y q / Nat.totient q

theorem liuPanPrimePowerKappa_nonneg (m : ℕ) :
    0 ≤ liuPanPrimePowerKappa m := by
  unfold liuPanPrimePowerKappa
  by_cases hm : m.Prime
  · simp [hm]
  · simp only [hm, if_false]
    exact div_nonneg vonMangoldt_nonneg (by
      rcases m with _ | m
      · simp
      exact Real.log_nonneg (by norm_num))

/-- The normalized non-prime von Mangoldt contribution is at most one. -/
theorem liuPanPrimePowerKappa_le_one (m : ℕ) :
    liuPanPrimePowerKappa m ≤ 1 := by
  unfold liuPanPrimePowerKappa
  by_cases hm : m.Prime
  · simp [hm]
  · simp only [hm, if_false]
    rcases m with _ | _ | m
    · simp
    · simp
    have hm2 : (1 : ℝ) < (m + 2 : ℕ) := by exact_mod_cast (by omega : 1 < m + 2)
    exact (div_le_one (Real.log_pos hm2)).2
      ArithmeticFunction.vonMangoldt_le_log

/-- Every coefficient is nonnegative. -/
theorem liuPanPrimePowerCoefficient_nonneg (N n : ℕ) :
    0 ≤ liuPanPrimePowerCoefficient N n := by
  unfold liuPanPrimePowerCoefficient
  apply sum_nonneg
  intro p hp
  apply sum_nonneg
  intro m hm
  split_ifs
  exact liuPanPrimePowerKappa_nonneg m
  exact le_rfl

/-- The number of ordered nonzero source representations of `n` is at most the
square of the number of distinct prime divisors of `n`. -/
theorem liuPanPrimePowerCoefficient_le_primeFactors_sq (N n : ℕ) :
   liuPanPrimePowerCoefficient N n ≤ (n.primeFactors.card : ℝ) ^ 2 := by
  classical
  let P := liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)
  let S := (P ×ˢ range (N + 1)).filter
   (fun x => x.1.1 * x.1.2 * x.2 = n ∧ x.2 ≠ 0)
  have hrewrite :
     liuPanPrimePowerCoefficient N n =
       ∑ x ∈ S, liuPanPrimePowerKappa x.2 := by
   unfold liuPanPrimePowerCoefficient
   dsimp [P, S]
   rw [sum_filter, sum_product]
   apply sum_congr rfl
   intro p hp
   apply sum_congr rfl
   intro m hm
   by_cases heq : p.1 * p.2 * m = n
   · by_cases hm0 : m = 0
     · subst m
       simp [liuPanPrimePowerKappa]
     · simp [heq, hm0]
   · simp [heq]
  have hcard : S.card ≤ (n.primeFactors ×ˢ n.primeFactors).card := by
   apply card_le_card_of_injOn (fun x => x.1)
   · intro x hx
     rw [mem_coe, mem_filter, mem_product] at hx
     rw [mem_coe, mem_product]
     have hp := mem_liuWeightPairs.mp hx.1.1
     have hn0 : n ≠ 0 := by
       rw [← hx.2.1]
       exact Nat.mul_ne_zero
         (Nat.mul_ne_zero hp.1.ne_zero hp.2.1.ne_zero) hx.2.2
     refine ⟨hp.1.mem_primeFactors ?_ hn0, hp.2.1.mem_primeFactors ?_ hn0⟩
     · exact ⟨x.1.2 * x.2, by simpa [mul_assoc] using hx.2.1.symm⟩
     · exact ⟨x.1.1 * x.2, by
         simpa [mul_assoc, mul_left_comm, mul_comm] using hx.2.1.symm⟩
   · intro x hx y hy hxy
     rw [mem_coe, mem_filter, mem_product] at hx hy
     dsimp only at hxy
     apply Prod.ext hxy
     apply Nat.mul_left_cancel (liuWeightPairs_product_pos hx.1.1)
     calc
       x.1.1 * x.1.2 * x.2 = n := hx.2.1
       _ = y.1.1 * y.1.2 * y.2 := hy.2.1.symm
       _ = x.1.1 * x.1.2 * y.2 := by rw [hxy]
  rw [hrewrite]
  calc
   (∑ x ∈ S, liuPanPrimePowerKappa x.2) ≤ ∑ _x ∈ S, (1 : ℝ) :=
     sum_le_sum fun x _ => liuPanPrimePowerKappa_le_one x.2
   _ = S.card := by simp
   _ ≤ (n.primeFactors ×ˢ n.primeFactors).card := by exact_mod_cast hcard
   _ = (n.primeFactors.card : ℝ) ^ 2 := by simp [pow_two]

/-- The standard elementary bound `ω(n) ≤ log n / log 2`. -/
theorem primeFactors_card_cast_le_log {n : ℕ} (hn : 2 ≤ n) :
   (n.primeFactors.card : ℝ) ≤
     Real.log (n : ℝ) / Real.log 2 := by
  have hpow : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p := by
   calc
     2 ^ n.primeFactors.card = ∏ _p ∈ n.primeFactors, (2 : ℕ) := by
       rw [prod_const]
     _ ≤ ∏ p ∈ n.primeFactors, p := by
       exact prod_le_prod (fun _ _ => by omega)
         (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hpow_le : 2 ^ n.primeFactors.card ≤ n :=
   hpow.trans (Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n))
  have hcast : ((2 ^ n.primeFactors.card : ℕ) : ℝ) ≤ (n : ℝ) := by
   exact_mod_cast hpow_le
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  calc
   (n.primeFactors.card : ℝ) * Real.log 2 =
       Real.log (((2 ^ n.primeFactors.card : ℕ) : ℝ)) := by
     rw [show ((2 ^ n.primeFactors.card : ℕ) : ℝ) =
       (2 : ℝ) ^ n.primeFactors.card by norm_num, Real.log_pow]
   _ ≤ Real.log (n : ℝ) :=
     Real.log_le_log (by positivity) hcast

/-- Pointwise polylogarithmic multiplicity bound for the collected source
coefficient. -/
theorem liuPanPrimePowerCoefficient_le_log_sq (N n : ℕ) :
   liuPanPrimePowerCoefficient N n ≤
     1 + (Real.log (n + 1 : ℕ) / Real.log 2) ^ 2 := by
  by_cases hn : n < 2
  case pos =>
   have hcard := liuPanPrimePowerCoefficient_le_primeFactors_sq N n
   have hpf : n.primeFactors.card = 0 := by
     interval_cases n <;> simp
   rw [hpf] at hcard
   norm_num at hcard
   have hright : 0 ≤ 1 + (Real.log (n + 1 : ℕ) / Real.log 2) ^ 2 :=
     by positivity
   exact hcard.trans hright
  case neg =>
   have hn' : 2 ≤ n := by omega
   have homega := primeFactors_card_cast_le_log hn'
   have hlog : Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) :=
     Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ n)
   have hdiv : Real.log (n : ℝ) / Real.log 2 ≤
       Real.log (n + 1 : ℕ) / Real.log 2 :=
     div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num))
   have hsquare : (n.primeFactors.card : ℝ) ^ 2 ≤
       (Real.log (n + 1 : ℕ) / Real.log 2) ^ 2 :=
     pow_le_pow_left₀ (Nat.cast_nonneg _) (homega.trans hdiv) 2
   exact (liuPanPrimePowerCoefficient_le_primeFactors_sq N n).trans
     (hsquare.trans (le_add_of_nonneg_left zero_le_one))

/-- The exact `L² ≤ L∞ · L¹` reduction for Liu's collected coefficients, with
the pointwise multiplicity supplied by the logarithmic bound above. -/
theorem liuPanPrimePowerCoefficient_sq_sum_le (N : ℕ) :
   (∑ n ∈ range (N + 1), liuPanPrimePowerCoefficient N n ^ 2) ≤
     (1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
       liuPanPrimePowerTotal N N := by
  rw [liuPanPrimePowerTotal]
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hnN : n ≤ N := Nat.le_of_lt_succ (mem_range.mp hn)
  have hlog : Real.log (n + 1 : ℕ) ≤ Real.log (N + 1 : ℕ) :=
   Real.log_le_log (by positivity) (by exact_mod_cast Nat.succ_le_succ hnN)
  have hdiv : Real.log (n + 1 : ℕ) / Real.log 2 ≤
     Real.log (N + 1 : ℕ) / Real.log 2 :=
   div_le_div_of_nonneg_right hlog (Real.log_nonneg (by norm_num))
  have hc := liuPanPrimePowerCoefficient_le_log_sq N n
  have hn1 : (1 : ℝ) ≤ (n + 1 : ℕ) := by
   exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hnlog : 0 ≤ Real.log (n + 1 : ℕ) / Real.log 2 :=
   div_nonneg (Real.log_nonneg hn1) (Real.log_nonneg (by norm_num))
  have hsquare :
     1 + (Real.log (n + 1 : ℕ) / Real.log 2) ^ 2 ≤
       1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2 :=
   add_le_add le_rfl (pow_le_pow_left₀ hnlog hdiv 2)
  calc
   liuPanPrimePowerCoefficient N n ^ 2 ≤
       (1 + (Real.log (n + 1 : ℕ) / Real.log 2) ^ 2) *
         liuPanPrimePowerCoefficient N n := by
     simpa only [pow_two] using
       mul_le_mul_of_nonneg_right hc (liuPanPrimePowerCoefficient_nonneg N n)
   _ ≤ (1 + (Real.log (N + 1 : ℕ) / Real.log 2) ^ 2) *
         liuPanPrimePowerCoefficient N n := by
     exact mul_le_mul_of_nonneg_right hsquare
       (liuPanPrimePowerCoefficient_nonneg N n)

/-- The coefficient has the explicit finite support supplied by its two finite
index sets. -/
theorem liuPanPrimePowerCoefficient_eq_zero_of_sq_lt
    {N n : ℕ} (hn : N * N < n) :
    liuPanPrimePowerCoefficient N n = 0 := by
  classical
  unfold liuPanPrimePowerCoefficient
  apply sum_eq_zero
  intro p hp
  apply sum_eq_zero
  intro m hm
  have ha : p.1 * p.2 ≤ N :=
    liuWeightSupport_le ⟨p, hp, rfl⟩
  have hmle : m ≤ N := Nat.le_of_lt_succ (mem_range.mp hm)
  have ham : p.1 * p.2 * m ≤ N * N :=
    Nat.mul_le_mul ha hmle
  have hne : p.1 * p.2 * m ≠ n := by
    intro h
    rw [← h] at hn
    exact (not_lt_of_ge ham) hn
  simp [hne]

/-- The coefficient sequence is finitely supported, with the transparent
support cutoff `N²`. -/
theorem liuPanPrimePowerCoefficient_eq_zero_of_lt
    {N n : ℕ} (hn : N * N < n) :
    liuPanPrimePowerCoefficient N n = 0 :=
  liuPanPrimePowerCoefficient_eq_zero_of_sq_lt hn

/-- The exact floor-division audit needed when a source factor is absorbed into
the prime-power variable. -/
theorem liuPanPrimePower_mem_range_mul_iff
    {N y a m : ℕ} (hy : y ≤ N) (ha : 0 < a) :
    m ∈ range (y / a + 1) ↔
      m ∈ (range (N + 1)).filter (fun m => a * m ≤ y) := by
  rw [mem_filter]
  constructor
  · intro hm
    have hmle : m ≤ y / a := Nat.le_of_lt_succ (mem_range.mp hm)
    refine ⟨mem_range.mpr (by
      have : m ≤ y := hmle.trans (Nat.div_le_self _ _)
      omega), ?_⟩
    simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le ha).mp hmle
  · rintro ⟨hm, hmy⟩
    apply mem_range.mpr
    rw [Nat.lt_succ_iff]
    exact (Nat.le_div_iff_mul_le ha).mpr (by simpa [Nat.mul_comm] using hmy)

/-- The inverse-residue convention in the correction kernel is exactly the
congruence obtained after restoring the source factor. -/
theorem liuPanPrimePower_mul_mod_iff
    {a m q l : ℕ} (hcop : a.Coprime q) :
    a * m ≡ l [MOD q] ↔
      m ≡ natInvMod q a * l % q [MOD q] := by
  constructor
  · intro h
    have h' : m ≡ natInvMod q a * l [MOD q] :=
      (modEq_mul_left_inv_iff (natInvMod_congr hcop)).mp h
    exact h'.trans (Nat.mod_modEq _ _).symm
  · intro h
    have h' : m ≡ natInvMod q a * l [MOD q] :=
      h.trans (Nat.mod_modEq _ _)
    exact (modEq_mul_left_inv_iff (natInvMod_congr hcop)).mpr h'

/-- A unit product residue forces the Liu source factor to be coprime to the
modulus.  This is the step which makes the unrestricted collected coefficient
compatible with the coprime source sum. -/
theorem liuPanPrimePower_coprime_of_mul_modEq
    {a m q l : ℕ} (hl : IsUnit (l : ZMod q))
    (hmod : a * m ≡ l [MOD q]) : a.Coprime q := by
  apply (ZMod.isUnit_iff_coprime a q).mp
  have heq : ((a * m : ℕ) : ZMod q) = (l : ZMod q) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod
  have hunit : IsUnit ((a : ZMod q) * (m : ZMod q)) := by
    rw [← Nat.cast_mul, heq]
    exact hl
  exact (IsUnit.mul_iff.mp hunit).1

/-- Exact one-source-factor regrouping of the correction kernel.  The proof
uses both the floor-division and inverse-residue audits above. -/
theorem liuPanPrimePowerCorrectionKernel_eq_productSum
    {N y a q l : ℕ} (hy : y ≤ N) (ha : 0 < a) (hcop : a.Coprime q) :
    liuPanSignedCorrectionKernel y a q l =
      ∑ m ∈ range (N + 1), liuPanPrimePowerKappa m *
        if a * m ≤ y ∧ a * m ≡ l [MOD q] then 1 else 0 := by
  unfold liuPanSignedCorrectionKernel apPrimePowerCorrection
    liuPanPrimePowerKappa
  have hr : range (y / a + 1) =
      (range (N + 1)).filter (fun m => a * m ≤ y) := by
    ext m
    exact liuPanPrimePower_mem_range_mul_iff hy ha
  rw [hr, sum_filter]
  apply sum_congr rfl
  intro m hm
  by_cases hle : a * m ≤ y <;>
    by_cases hmod : a * m ≡ l [MOD q] <;>
    simp [hle, hmod, (liuPanPrimePower_mul_mod_iff hcop).symm]

/-- Reindexing the characteristic Liu weight by its unique source pair turns
the correction bound into the coprime source AP sum. -/
theorem liuPanSignedCorrectionBound_eq_coprimeSourceAPSum
    {N y q l : ℕ} (hy : y ≤ N) :
    liuPanSignedCorrectionBound y N q l
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuPanPrimePowerCoprimeSourceAPSum N y q l := by
  classical
  unfold liuPanSignedCorrectionBound liuPanPrimePowerCoprimeSourceAPSum
  calc
    (∑ a ∈ Icc 1 N,
        if a.Coprime q then
          |liuWeight N (liuSourceZ10 N) (liuSourceY3 N) a| *
            liuPanSignedCorrectionKernel y a q l
        else 0) =
        ∑ a ∈ (Icc 1 N).filter
          (LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N)),
          if a.Coprime q then liuPanSignedCorrectionKernel y a q l else 0 := by
      rw [sum_filter]
      apply sum_congr rfl
      intro a ha
      by_cases hs : LiuWeightSupport N (liuSourceZ10 N) (liuSourceY3 N) a <;>
        simp [liuWeight, hs]
    _ = ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          if (p.1 * p.2).Coprime q then
            liuPanSignedCorrectionKernel y (p.1 * p.2) q l
          else 0 := by
      symm
      apply sum_bij (fun p _ => p.1 * p.2)
      · intro p hp
        rw [mem_filter, mem_Icc]
        exact ⟨⟨liuWeightPairs_product_pos hp,
          liuWeightSupport_le ⟨p, hp, rfl⟩⟩, ⟨p, hp, rfl⟩⟩
      · intro p hp p' hp' hpp'
        have hu := liuPairConditions_unique
          (mem_liuWeightPairs.mp hp) (mem_liuWeightPairs.mp hp') hpp'
        exact Prod.ext hu.1 hu.2
      · intro a ha
        rcases (mem_filter.mp ha).2 with ⟨p, hp, hpa⟩
        exact ⟨p, hp, hpa⟩
      · intro p hp
        rfl
    _ = ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          if (p.1 * p.2).Coprime q then
            ∑ m ∈ range (N + 1), liuPanPrimePowerKappa m *
              if p.1 * p.2 * m ≤ y ∧ p.1 * p.2 * m ≡ l [MOD q] then 1 else 0
          else 0 := by
      apply sum_congr rfl
      intro p hp
      by_cases hcop : (p.1 * p.2).Coprime q
      · simp [liuPanPrimePowerCorrectionKernel_eq_productSum hy
          (liuWeightPairs_product_pos hp) hcop]
      · simp [hcop]

/-- A unit target residue makes the coprimality gate in the source AP sum
redundant, since a non-unit source factor cannot produce that residue. -/
theorem liuPanPrimePowerCoprimeSourceAPSum_eq_sourceAPSum
    {N y q l : ℕ} (hl : IsUnit (l : ZMod q)) :
    liuPanPrimePowerCoprimeSourceAPSum N y q l =
      liuPanPrimePowerSourceAPSum N y q l := by
  classical
  unfold liuPanPrimePowerCoprimeSourceAPSum liuPanPrimePowerSourceAPSum
  apply sum_congr rfl
  intro p hp
  by_cases hcop : (p.1 * p.2).Coprime q
  · simp [hcop]
  · simp only [if_neg hcop]
    apply (sum_eq_zero fun m hm => ?_).symm
    by_cases hcond : p.1 * p.2 * m ≤ y ∧ p.1 * p.2 * m ≡ l [MOD q]
    · exact False.elim (hcop
        (liuPanPrimePower_coprime_of_mul_modEq hl hcond.2))
    · simp [hcond]

private theorem liuPanPrimePower_sum_eq_ite_of_le
    (t y : ℕ) (x : ℝ) :
    (∑ n ∈ range (y + 1), if t = n then x else 0) =
      if t ≤ y then x else 0 := by
  simp

/-- Collecting the finite coefficient back into its source pairs is exact; in
particular every product collision retains its multiplicity. -/
theorem liuPanPrimePowerAPSum_eq_sourceAPSum (N y q l : ℕ) :
    liuPanPrimePowerAPSum N y q l =
      liuPanPrimePowerSourceAPSum N y q l := by
  classical
  unfold liuPanPrimePowerAPSum liuPanPrimePowerCoefficient
    liuPanPrimePowerSourceAPSum
  calc
    (∑ n ∈ range (y + 1),
        (∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          ∑ m ∈ range (N + 1),
            if p.1 * p.2 * m = n then liuPanPrimePowerKappa m else 0) *
          if n ≡ l [MOD q] then 1 else 0) =
        ∑ n ∈ range (y + 1),
          ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
            ∑ m ∈ range (N + 1),
              (if p.1 * p.2 * m = n then liuPanPrimePowerKappa m else 0) *
                if n ≡ l [MOD q] then 1 else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [sum_mul]
      apply sum_congr rfl
      intro p hp
      rw [sum_mul]
    _ = ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          ∑ m ∈ range (N + 1),
            ∑ n ∈ range (y + 1),
              (if p.1 * p.2 * m = n then liuPanPrimePowerKappa m else 0) *
                if n ≡ l [MOD q] then 1 else 0 := by
      rw [sum_comm]
      apply sum_congr rfl
      intro p hp
      rw [sum_comm]
    _ = ∑ p ∈ liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N),
          ∑ m ∈ range (N + 1),
            liuPanPrimePowerKappa m *
              if p.1 * p.2 * m ≤ y ∧ p.1 * p.2 * m ≡ l [MOD q] then 1 else 0 := by
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro m hm
      let t := p.1 * p.2 * m
      calc
        (∑ n ∈ range (y + 1),
          (if t = n then liuPanPrimePowerKappa m else 0) *
            if n ≡ l [MOD q] then 1 else 0) =
        ∑ n ∈ range (y + 1),
          if t = n then
            liuPanPrimePowerKappa m *
              if t ≡ l [MOD q] then 1 else 0
          else 0 := by
          apply sum_congr rfl
          intro n hn
          by_cases htn : t = n <;> simp [htn]
        _ = if t ≤ y then
              liuPanPrimePowerKappa m *
                if t ≡ l [MOD q] then 1 else 0
            else 0 :=
          liuPanPrimePower_sum_eq_ite_of_le t y _
        _ = liuPanPrimePowerKappa m *
            if t ≤ y ∧ t ≡ l [MOD q] then 1 else 0 := by
          by_cases hty : t ≤ y <;> by_cases htl : t ≡ l [MOD q] <;>
            simp [hty, htl]

/-- For `y ≤ N` and a unit residue, Liu's exact prime-power correction is the
AP partial sum of the finite multiplicity-preserving coefficient. -/
theorem liuPanSignedCorrectionBound_eq_apSum
    {N y q l : ℕ} (hy : y ≤ N) (hl : IsUnit (l : ZMod q)) :
    liuPanSignedCorrectionBound y N q l
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuPanPrimePowerAPSum N y q l := by
  rw [liuPanSignedCorrectionBound_eq_coprimeSourceAPSum hy,
    liuPanPrimePowerCoprimeSourceAPSum_eq_sourceAPSum hl,
    ← liuPanPrimePowerAPSum_eq_sourceAPSum]

/-- The complex character mean is exactly the complexification of the AP
partial sum. -/
theorem liuPanPrimePowerCharacterMean_eq_apSum
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    liuPanPrimePowerCharacterMean N y q l =
      (liuPanPrimePowerAPSum N y q l : ℂ) := by
  classical
  unfold liuPanPrimePowerCharacterMean liuPanPrimePowerAPSum
  rw [← charSum_ap hq hl (fun n => (liuPanPrimePowerCoefficient N n : ℂ)) y]
  rw [Complex.ofReal_sum]
  apply sum_congr rfl
  intro n hn
  by_cases h : n ≡ l [MOD q] <;> simp [h]

/-- The real part of the character mean is the real AP partial sum. -/
theorem liuPanPrimePowerCharacterMean_re_eq_apSum
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    (liuPanPrimePowerCharacterMean N y q l).re =
      liuPanPrimePowerAPSum N y q l := by
  rw [liuPanPrimePowerCharacterMean_eq_apSum hq hl]
  simp

/-- The character sum with the principal character removed. -/
noncomputable def liuPanPrimePowerNonprincipalCharacterMean
    (N y q l : ℕ) : ℂ :=
  by
    classical
    exact
      (Nat.totient q : ℂ)⁻¹ *
        ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
          star (χ (l : ZMod q)) *
            ∑ n ∈ range (y + 1),
              (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)

/-- The principal character selects exactly the coefficient mass on units. -/
theorem liuPanPrimePowerPrincipalCharacterTerm_eq_coprimeTotal
    (N y q : ℕ) :
    ∑ n ∈ range (y + 1),
        (liuPanPrimePowerCoefficient N n : ℂ) *
          (1 : DirichletCharacter ℂ q) (n : ZMod q) =
      (liuPanPrimePowerCoprimeTotal N y q : ℂ) := by
  classical
  unfold liuPanPrimePowerCoprimeTotal
  rw [Complex.ofReal_sum (range (y + 1))
    (fun n => liuPanPrimePowerCoefficient N n *
      if n.Coprime q then 1 else 0)]
  apply sum_congr rfl
  intro n hn
  by_cases hcop : n.Coprime q
  · have hunit : IsUnit (n : ZMod q) :=
      (ZMod.isUnit_iff_coprime n q).mpr hcop
    rw [MulChar.one_apply hunit]
    simp [hcop]
  · have hnonunit : ¬ IsUnit (n : ZMod q) := by
      intro hunit
      exact hcop ((ZMod.isUnit_iff_coprime n q).mp hunit)
    rw [MulChar.map_nonunit (1 : DirichletCharacter ℂ q) hnonunit]
    simp [hcop]

/-- The genuine discrepancy is the real part of the normalized sum over
nonprincipal characters, with the principal mass removed exactly. -/
theorem liuPanPrimePowerNonprincipalDiscrepancy_eq_re_nonprincipalCharacterMean
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    liuPanPrimePowerNonprincipalDiscrepancy N y q l =
      (liuPanPrimePowerNonprincipalCharacterMean N y q l).re := by
  classical
  unfold liuPanPrimePowerNonprincipalDiscrepancy
    liuPanPrimePowerNonprincipalCharacterMean
  rw [← liuPanPrimePowerCharacterMean_re_eq_apSum hq hl]
  let f : DirichletCharacter ℂ q → ℂ := fun χ =>
    star (χ (l : ZMod q)) *
      ∑ n ∈ range (y + 1),
        (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)
  have hsum :
      (∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), f χ) +
          f (1 : DirichletCharacter ℂ q) =
        ∑ χ : DirichletCharacter ℂ q, f χ :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  change
    ((
        (Nat.totient q : ℂ)⁻¹ *
          ∑ χ : DirichletCharacter ℂ q, f χ).re -
      liuPanPrimePowerCoprimeTotal N y q / Nat.totient q) =
      ((Nat.totient q : ℂ)⁻¹ *
        ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)), f χ).re
  rw [← hsum]
  have hprincipal :
      f (1 : DirichletCharacter ℂ q) =
        (liuPanPrimePowerCoprimeTotal N y q : ℂ) := by
    dsimp [f]
    have hone : (1 : DirichletCharacter ℂ q) (l : ZMod q) = 1 :=
      MulChar.one_apply hl
    rw [hone]
    simp
    rw [liuPanPrimePowerPrincipalCharacterTerm_eq_coprimeTotal]
  rw [hprincipal]
  norm_num [Complex.div_re]
  ring

/-- The exact square sum over the nonprincipal characters at a fixed cutoff. -/
noncomputable def liuPanPrimePowerNonprincipalCharacterSquareSum
    (N y q l : ℕ) : ℝ :=
  by
    classical
    exact
      ∑ χ ∈ (Finset.univ.erase (1 : DirichletCharacter ℂ q)),
        ‖star (χ (l : ZMod q)) *
          ∑ n ∈ range (y + 1),
            (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)‖ ^ 2

/-- The finite number of nonprincipal characters used in the square-sum bound. -/
noncomputable def liuPanPrimePowerNonprincipalCharacterCount (q : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ.erase (1 : DirichletCharacter ℂ q)).card

/-- A pointwise absolute Cauchy--Schwarz bound for the bridge, with the
all-nonprincipal square sum left explicit and no large-sieve estimate. -/
theorem liuPanPrimePowerNonprincipalDiscrepancy_abs_le_cauchySchwarz
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    |liuPanPrimePowerNonprincipalDiscrepancy N y q l| ≤
      (Nat.totient q : ℝ)⁻¹ *
          Real.sqrt
            ((liuPanPrimePowerNonprincipalCharacterCount q : ℕ) : ℝ) *
        Real.sqrt
          (liuPanPrimePowerNonprincipalCharacterSquareSum N y q l) := by
  classical
  let S := Finset.univ.erase (1 : DirichletCharacter ℂ q)
  let f : DirichletCharacter ℂ q → ℂ := fun χ =>
    star (χ (l : ZMod q)) *
      ∑ n ∈ range (y + 1),
        (liuPanPrimePowerCoefficient N n : ℂ) * χ (n : ZMod q)
  let g : DirichletCharacter ℂ q → ℝ := fun χ => ‖f χ‖
  have hphi : 0 < (Nat.totient q : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr hq
  have hphinorm : ‖(Nat.totient q : ℂ)⁻¹‖ = (Nat.totient q : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  have htriangle :
      ‖∑ χ ∈ S, f χ‖ ≤ ∑ χ ∈ S, g χ := by
    exact norm_sum_le S f
  have hcs :
      (∑ χ ∈ S, (1 : ℝ) * g χ) ≤
        Real.sqrt (∑ χ ∈ S, (1 : ℝ) ^ 2) *
          Real.sqrt (∑ χ ∈ S, g χ ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt S (fun _ => (1 : ℝ)) g
  have hcs' :
      (∑ χ ∈ S, g χ) ≤
        Real.sqrt (S.card : ℝ) * Real.sqrt (∑ χ ∈ S, g χ ^ 2) := by
    simpa using hcs
  calc
    |liuPanPrimePowerNonprincipalDiscrepancy N y q l| =
        |(liuPanPrimePowerNonprincipalCharacterMean N y q l).re| := by
          rw [liuPanPrimePowerNonprincipalDiscrepancy_eq_re_nonprincipalCharacterMean
            hq hl]
    _ ≤ ‖liuPanPrimePowerNonprincipalCharacterMean N y q l‖ :=
      Complex.abs_re_le_norm _
    _ = ‖(Nat.totient q : ℂ)⁻¹ * ∑ χ ∈ S, f χ‖ := by
      rfl
    _ ≤ ‖(Nat.totient q : ℂ)⁻¹‖ * ‖∑ χ ∈ S, f χ‖ := by
      rw [norm_mul]
    _ ≤ (Nat.totient q : ℝ)⁻¹ * ∑ χ ∈ S, g χ := by
      rw [hphinorm]
      exact mul_le_mul_of_nonneg_left htriangle (inv_nonneg.mpr hphi.le)
    _ ≤ (Nat.totient q : ℝ)⁻¹ *
          (Real.sqrt (S.card : ℝ) *
            Real.sqrt (∑ χ ∈ S, g χ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hcs' (inv_nonneg.mpr hphi.le)
    _ = (Nat.totient q : ℝ)⁻¹ *
          Real.sqrt (liuPanPrimePowerNonprincipalCharacterCount q : ℝ) *
            Real.sqrt (liuPanPrimePowerNonprincipalCharacterSquareSum N y q l) := by
      exact (mul_assoc _ _ _).symm

/-- The unrestricted mass is the disjoint sum of its unit and nonunit parts. -/
theorem liuPanPrimePowerTotal_eq_coprime_add_noncoprime
    (N y q : ℕ) :
    liuPanPrimePowerTotal N y =
      liuPanPrimePowerCoprimeTotal N y q +
        liuPanPrimePowerNoncoprimeTotal N y q := by
  unfold liuPanPrimePowerTotal liuPanPrimePowerCoprimeTotal
    liuPanPrimePowerNoncoprimeTotal
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [← mul_add]
  by_cases h : n.Coprime q
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- The principal-character mass is nonnegative. -/
theorem liuPanPrimePowerCoprimeTotal_nonneg (N y q : ℕ) :
    0 ≤ liuPanPrimePowerCoprimeTotal N y q := by
  unfold liuPanPrimePowerCoprimeTotal
  apply sum_nonneg
  intro n hn
  exact mul_nonneg (liuPanPrimePowerCoefficient_nonneg N n) (by
    split <;> norm_num)

/-- The unrestricted coefficient mass is nonnegative. -/
theorem liuPanPrimePowerTotal_nonneg (N y : ℕ) :
    0 ≤ liuPanPrimePowerTotal N y := by
  unfold liuPanPrimePowerTotal
  exact sum_nonneg (fun n _ => liuPanPrimePowerCoefficient_nonneg N n)

/-- The full coefficient mass is exactly the modulus-one correction. -/
theorem liuPanPrimePowerTotal_eq_correctionBound_mod_one (N : ℕ) :
    liuPanPrimePowerTotal N N =
      liuPanSignedCorrectionBound N N 1 0
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) := by
  have hunit : IsUnit ((0 : ℕ) : ZMod 1) := by
    rw [show ((0 : ℕ) : ZMod 1) = 1 by exact Subsingleton.elim _ _]
    exact isUnit_one
  rw [liuPanSignedCorrectionBound_eq_apSum le_rfl hunit]
  unfold liuPanPrimePowerAPSum liuPanPrimePowerTotal
  simp [Nat.modEq_one]

/-- Chebyshev's global correction bound controls the full coefficient mass by
the exact square-root mass of Liu's source pairs. -/
theorem liuPanPrimePowerTotal_le_pairSqrtMass
    {C : ℝ}
    (hglobal : ∀ t : ℕ,
      globalPrimePowerCorrection t ≤ C * Real.sqrt t)
    (N : ℕ) :
    liuPanPrimePowerTotal N N ≤
      C * liuPanPrimePowerPairSqrtMass N := by
  rw [liuPanPrimePowerTotal_eq_correctionBound_mod_one N]
  exact (liuPanSignedCorrectionBound_le_sqrtSupport hglobal N N 1 0
    (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))).trans_eq
      (congrArg (C * ·)
        (liuPanPrimePowerSqrtSupport_source_eq_pairSqrtMass N))

/-- The source-pair square-root mass is nonnegative. -/
theorem liuPanPrimePowerPairSqrtMass_nonneg (N : ℕ) :
    0 ≤ liuPanPrimePowerPairSqrtMass N := by
  unfold liuPanPrimePowerPairSqrtMass
  exact sum_nonneg fun p hp => Real.sqrt_nonneg _

/-- The exact source pair set injects into the rectangle supplied by Liu's
`p₁ ≤ N^(1/3)` and corrected `p₂ ≤ N^(9/20)` cutoffs. -/
theorem liuWeightPairs_source_card_le (N : ℕ) :
    (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card ≤
      (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1) *
        (Nat.floor ((N : ℝ) ^ (9 / 20 : ℝ)) + 1) := by
  classical
  calc
    (liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card ≤
        (range (Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1) ×ˢ
          range (Nat.floor ((N : ℝ) ^ (9 / 20 : ℝ)) + 1)).card := by
      apply card_le_card
      rintro ⟨p₁, p₂⟩ hp
      rw [mem_product, mem_range, mem_range]
      have hrange := liuWeightPairs_source_range hp
      exact ⟨Nat.lt_succ_iff.mpr ((Nat.le_floor_iff
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr hrange.2.1),
        Nat.lt_succ_iff.mpr ((Nat.le_floor_iff
          (Real.rpow_nonneg (Nat.cast_nonneg N) _)).mpr hrange.2.2.2)⟩
    _ = _ := by simp

/-- A real-power form of the finite source-pair cardinality bound. -/
theorem liuWeightPairs_source_card_cast_le (N : ℕ) (hN : 1 ≤ N) :
    ((liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card : ℝ) ≤
      4 * (N : ℝ) ^ (47 / 60 : ℝ) := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hy1 : 1 ≤ (N : ℝ) ^ (9 / 20 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hcard := liuWeightPairs_source_card_le N
  have hcardR :
      ((liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card : ℝ) ≤
        ((Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) + 1 : ℕ) : ℝ) *
          ((Nat.floor ((N : ℝ) ^ (9 / 20 : ℝ)) + 1 : ℕ) : ℝ) := by
    exact_mod_cast hcard
  calc
    ((liuWeightPairs N (liuSourceZ10 N) (liuSourceY3 N)).card : ℝ) ≤
        ((Nat.floor ((N : ℝ) ^ (1 / 3 : ℝ)) : ℝ) + 1) *
          ((Nat.floor ((N : ℝ) ^ (9 / 20 : ℝ)) : ℝ) + 1) := by
      simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hcardR
    _ ≤ (2 * (N : ℝ) ^ (1 / 3 : ℝ)) *
          (2 * (N : ℝ) ^ (9 / 20 : ℝ)) := by
      apply mul_le_mul
      · linarith [Nat.floor_le
          (Real.rpow_nonneg (Nat.cast_nonneg N) (1 / 3 : ℝ))]
      · linarith [Nat.floor_le
          (Real.rpow_nonneg (Nat.cast_nonneg N) (9 / 20 : ℝ))]
      · positivity
      · positivity
    _ = 4 * (N : ℝ) ^ (47 / 60 : ℝ) := by
      rw [show (47 / 60 : ℝ) = 1 / 3 + 9 / 20 by norm_num,
        Real.rpow_add (by positivity : (0 : ℝ) < N)]
      ring

/-- Cauchy--Schwarz, the exact source rectangle, and the two uniform reciprocal
prime sums put the source-pair square-root mass on the `N^(107/120)` scale. -/
theorem liuPanPrimePowerPairSqrtMass_le_rpow
    (N : ℕ) (hN : 8 ≤ N) :
    liuPanPrimePowerPairSqrtMass N ≤
      2 * Real.sqrt
          (liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound) *
        (N : ℝ) ^ (107 / 120 : ℝ) := by
  let R := liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound
  change liuPanPrimePowerPairSqrtMass N ≤
    2 * Real.sqrt R * (N : ℝ) ^ (107 / 120 : ℝ)
  have hR : 0 ≤ R := mul_nonneg liuWeightP₁ReciprocalBound_nonneg
    liuSourceR1P₂ReciprocalBound_nonneg
  have hcard := liuWeightPairs_source_card_cast_le N (by omega)
  have hrecip := liuWeightPairReciprocalSum_le N hN
  have hsq : liuPanPrimePowerPairSqrtMass N ^ 2 ≤
      (4 * (N : ℝ) ^ (47 / 60 : ℝ)) * ((N : ℝ) * R) :=
    (liuPanPrimePowerPairSqrtMass_sq_le N).trans
      (mul_le_mul hcard
        (mul_le_mul_of_nonneg_left hrecip (Nat.cast_nonneg N))
        (mul_nonneg (Nat.cast_nonneg N) (by
          unfold liuWeightPairReciprocalSum
          exact sum_nonneg fun p hp => by positivity))
        (by positivity))
  apply (sq_le_sq₀ (liuPanPrimePowerPairSqrtMass_nonneg N)
    (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (Real.rpow_nonneg (Nat.cast_nonneg N) _))).mp
  calc
    liuPanPrimePowerPairSqrtMass N ^ 2 ≤
        (4 * (N : ℝ) ^ (47 / 60 : ℝ)) * ((N : ℝ) * R) := hsq
    _ = 4 * R * (N : ℝ) ^ (107 / 60 : ℝ) := by
      rw [show (107 / 60 : ℝ) = 47 / 60 + 1 by norm_num,
        Real.rpow_add (by positivity : (0 : ℝ) < N), Real.rpow_one]
      ring
    _ = (2 * Real.sqrt R * (N : ℝ) ^ (107 / 120 : ℝ)) ^ 2 := by
      have hpow : ((N : ℝ) ^ (107 / 120 : ℝ)) ^ 2 =
          (N : ℝ) ^ (107 / 60 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
        norm_num
      rw [mul_pow, mul_pow, Real.sq_sqrt hR, hpow]
      ring

/-- Restricting to units can only decrease the nonnegative coefficient mass. -/
theorem liuPanPrimePowerCoprimeTotal_le_total (N y q : ℕ) :
    liuPanPrimePowerCoprimeTotal N y q ≤ liuPanPrimePowerTotal N y := by
  rw [liuPanPrimePowerTotal_eq_coprime_add_noncoprime N y q]
  exact le_add_of_nonneg_right (by
    unfold liuPanPrimePowerNoncoprimeTotal
    apply sum_nonneg
    intro n hn
    exact mul_nonneg (liuPanPrimePowerCoefficient_nonneg N n) (by
      split <;> norm_num))

/-- The coprime principal mass is monotone in the partial-sum cutoff. -/
theorem liuPanPrimePowerCoprimeTotal_mono
    {N y x q : ℕ} (hyx : y ≤ x) :
    liuPanPrimePowerCoprimeTotal N y q ≤
      liuPanPrimePowerCoprimeTotal N x q := by
  unfold liuPanPrimePowerCoprimeTotal
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hyx))
    (fun n _ _ => mul_nonneg (liuPanPrimePowerCoefficient_nonneg N n) (by
      split <;> norm_num))

/-- Exact principal-density plus discrepancy decomposition of the coefficient
AP partial sum. -/
theorem liuPanPrimePowerAPSum_eq_density_add_discrepancy
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    liuPanPrimePowerAPSum N y q l =
      liuPanPrimePowerTotal N y / Nat.totient q +
        liuPanPrimePowerDiscrepancy N y q l := by
  unfold liuPanPrimePowerDiscrepancy
  rw [liuPanPrimePowerCharacterMean_re_eq_apSum hq hl]
  ring

/-- Exact principal-character density plus genuine nonprincipal discrepancy. -/
theorem liuPanPrimePowerAPSum_eq_coprimeDensity_add_nonprincipal
    (N y q l : ℕ) :
    liuPanPrimePowerAPSum N y q l =
      liuPanPrimePowerCoprimeTotal N y q / Nat.totient q +
        liuPanPrimePowerNonprincipalDiscrepancy N y q l := by
  unfold liuPanPrimePowerNonprincipalDiscrepancy
  ring

/-- The previous all-total discrepancy differs from the genuine nonprincipal
discrepancy by exactly the omitted noncoprime principal-character mass. -/
theorem liuPanPrimePowerNonprincipalDiscrepancy_eq_discrepancy_add_noncoprime
    {N y q l : ℕ} (hq : 0 < q) (hl : IsUnit (l : ZMod q)) :
    liuPanPrimePowerNonprincipalDiscrepancy N y q l =
      liuPanPrimePowerDiscrepancy N y q l +
        liuPanPrimePowerNoncoprimeTotal N y q / Nat.totient q := by
  unfold liuPanPrimePowerNonprincipalDiscrepancy
    liuPanPrimePowerDiscrepancy
  rw [liuPanPrimePowerCharacterMean_re_eq_apSum hq hl,
    liuPanPrimePowerTotal_eq_coprime_add_noncoprime N y q]
  ring

/-- Character reduction of Liu's correction bound at each nonzero unit
progression.  This combines the exact source regrouping with `charSum_ap`. -/
theorem liuPanSignedCorrectionBound_eq_density_add_discrepancy
    {N y q l : ℕ} (hy : y ≤ N) (hq : 0 < q)
    (hl : IsUnit (l : ZMod q)) :
    liuPanSignedCorrectionBound y N q l
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuPanPrimePowerTotal N y / Nat.totient q +
        liuPanPrimePowerDiscrepancy N y q l := by
  rw [liuPanSignedCorrectionBound_eq_apSum hy hl,
    liuPanPrimePowerAPSum_eq_density_add_discrepancy hq hl]

/-- Character reduction with the actual principal-character mass. -/
theorem liuPanSignedCorrectionBound_eq_coprimeDensity_add_nonprincipal
    {N y q l : ℕ} (hy : y ≤ N) (hl : IsUnit (l : ZMod q)) :
    liuPanSignedCorrectionBound y N q l
      (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) =
      liuPanPrimePowerCoprimeTotal N y q / Nat.totient q +
        liuPanPrimePowerNonprincipalDiscrepancy N y q l := by
  rw [liuPanSignedCorrectionBound_eq_apSum hy hl,
    liuPanPrimePowerAPSum_eq_coprimeDensity_add_nonprincipal]

/-- At modulus one the character discrepancy vanishes exactly. -/
theorem liuPanPrimePowerDiscrepancy_mod_one (N y l : ℕ) :
    liuPanPrimePowerDiscrepancy N y 1 l = 0 := by
  have hl : IsUnit (l : ZMod 1) := by
    rw [show (l : ZMod 1) = 1 by exact Subsingleton.elim _ _]
    exact isUnit_one
  unfold liuPanPrimePowerDiscrepancy
  rw [liuPanPrimePowerCharacterMean_re_eq_apSum (N := N) (y := y)
    (q := 1) (l := l) (by norm_num) hl]
  unfold liuPanPrimePowerAPSum liuPanPrimePowerTotal
  simp [Nat.modEq_one]

/-- At modulus one the genuine nonprincipal discrepancy also vanishes exactly. -/
theorem liuPanPrimePowerNonprincipalDiscrepancy_mod_one (N y l : ℕ) :
    liuPanPrimePowerNonprincipalDiscrepancy N y 1 l = 0 := by
  unfold liuPanPrimePowerNonprincipalDiscrepancy
    liuPanPrimePowerAPSum liuPanPrimePowerCoprimeTotal
  simp [Nat.modEq_one]

/-- Liu's nonnegative squarefree modulus weight. -/
noncomputable def liuPanPrimePowerModulusWeight (q : ℕ) : ℝ :=
  (((moebius q : ℤ) : ℝ) ^ 2) * (3 : ℝ) ^ q.primeFactors.card

/-- The zero modulus is killed before any character argument is invoked. -/
theorem liuPanPrimePowerModulusWeight_zero :
    liuPanPrimePowerModulusWeight 0 = 0 := by
  exact liuPanPrimePower_modulusWeight_zero

/-- Nonnegativity of the modulus weight used in the density and residual
averages. -/
theorem liuPanPrimePowerModulusWeight_nonneg (q : ℕ) :
    0 ≤ liuPanPrimePowerModulusWeight q := by
  unfold liuPanPrimePowerModulusWeight
  exact mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _)

/-- Nonsquarefree moduli have zero weight. -/
theorem liuPanPrimePowerModulusWeight_eq_zero_of_not_squarefree
    {q : ℕ} (hq : ¬Squarefree q) :
    liuPanPrimePowerModulusWeight q = 0 := by
  unfold liuPanPrimePowerModulusWeight
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq]
  norm_num

/-- The squarefree modulus weight divided by Euler's totient is multiplicative
on positive coprime arguments. -/
theorem liuPanPrimePowerModulusWeight_div_totient_mul_of_coprime
    {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : m.Coprime n) :
    liuPanPrimePowerModulusWeight (m * n) / Nat.totient (m * n) =
      (liuPanPrimePowerModulusWeight m / Nat.totient m) *
        (liuPanPrimePowerModulusWeight n / Nat.totient n) := by
  unfold liuPanPrimePowerModulusWeight
  have hpf (d : ℕ) : d.primeFactors.card =
      ArithmeticFunction.cardDistinctFactors d := by
    rw [ArithmeticFunction.cardDistinctFactors_apply, ← List.card_toFinset,
      Nat.toFinset_factors]
  have hcard : (m * n).primeFactors.card =
      m.primeFactors.card + n.primeFactors.card := by
    rw [hpf, hpf, hpf]
    exact ArithmeticFunction.cardDistinctFactors_mul hmn
  have hmu :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn
  have htot := Nat.totient_mul hmn
  have htotm : Nat.totient m ≠ 0 :=
    ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm))
  have htotn : Nat.totient n ≠ 0 :=
    ne_of_gt (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
  rw [hmu, htot, hcard, Int.cast_mul, pow_add, Nat.cast_mul]
  field_simp [htotm, htotn]

/-- If `d * r` is squarefree and `e ∣ r`, its normalized modulus weight
factors into the conductor, selected divisor, and complementary cofactor. -/
theorem liuPanPrimePowerModulusWeight_div_totient_eq_three_factors
    {d r e : ℕ} (hsq : Squarefree (d * r)) (he : e ∣ r) :
    liuPanPrimePowerModulusWeight (d * r) / Nat.totient (d * r) =
      (liuPanPrimePowerModulusWeight d / Nat.totient d) *
        (liuPanPrimePowerModulusWeight e / Nat.totient e) *
          (liuPanPrimePowerModulusWeight (r / e) /
            Nat.totient (r / e)) := by
  have hdr0 : d * r ≠ 0 := by
    intro hzero
    rw [hzero] at hsq
    exact not_squarefree_zero hsq
  have hd0 : d ≠ 0 := left_ne_zero_of_mul hdr0
  have hr0 : r ≠ 0 := right_ne_zero_of_mul hdr0
  obtain ⟨hdr, hd, hr⟩ := Nat.squarefree_mul_iff.mp hsq
  have hre : r = e * (r / e) := (Nat.mul_div_cancel' he).symm
  have hersq : Squarefree (e * (r / e)) := hre ▸ hr
  obtain ⟨her, heSq, hreSq⟩ := Nat.squarefree_mul_iff.mp hersq
  have he0 : e ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hre
    exact hr0 hre
  have hre0 : r / e ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hre
    exact hr0 hre
  rw [liuPanPrimePowerModulusWeight_div_totient_mul_of_coprime hd0 hr0 hdr]
  have hfactor :=
    liuPanPrimePowerModulusWeight_div_totient_mul_of_coprime he0 hre0 her
  rw [← hre] at hfactor
  rw [hfactor]
  ring

/-- The finite `H₃` mass used when the squarefree modulus sum is regrouped
conductor first. -/
noncomputable def liuPanPrimePowerH3Mass (Q : ℕ) : ℝ :=
  ∑ q ∈ range (Q + 1),
    liuPanPrimePowerModulusWeight q / Nat.totient q

/-- The finite `J₉` mass generated by Cauchy--Schwarz in the squarefree
cofactor variable. -/
noncomputable def liuPanPrimePowerJ9Mass (Q : ℕ) : ℝ :=
  ∑ d ∈ range (Q + 1),
    (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d

/-- The dilated-coefficient cofactor mass with the square-root saving supplied
by the large sieve. -/
noncomputable def liuPanPrimePowerCofactorSqrtMass (Q : ℕ) : ℝ :=
  ∑ e ∈ range (Q + 1),
    (liuPanPrimePowerModulusWeight e / Nat.totient e) / Real.sqrt e

/-- The stronger cofactor mass occurring in the `Q²` part of the large-sieve
bound. -/
noncomputable def liuPanPrimePowerCofactorLinearMass (Q : ℕ) : ℝ :=
  ∑ e ∈ range (Q + 1),
    (liuPanPrimePowerModulusWeight e / Nat.totient e) / e

theorem liuPanPrimePowerH3Mass_nonneg (Q : ℕ) :
    0 ≤ liuPanPrimePowerH3Mass Q := by
  unfold liuPanPrimePowerH3Mass
  exact sum_nonneg fun q _ =>
    div_nonneg (liuPanPrimePowerModulusWeight_nonneg q) (Nat.cast_nonneg _)

theorem liuPanPrimePowerJ9Mass_nonneg (Q : ℕ) :
    0 ≤ liuPanPrimePowerJ9Mass Q := by
  unfold liuPanPrimePowerJ9Mass
  exact sum_nonneg fun d _ =>
    div_nonneg
      (mul_nonneg (sq_nonneg _) (pow_nonneg (by norm_num) _))
      (Nat.cast_nonneg _)

/-- On squarefree integers the `J₉` summand is its expected Euler product. -/
theorem liuPanPrimePowerJ9_term_squarefree (d : ℕ) (hd : Squarefree d) :
    (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d =
      ∏ p ∈ d.primeFactors, (9 : ℝ) / p := by
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hd
  have hdprod : d = ∏ p ∈ d.primeFactors, p := by
    have hprod : d = ∏ p ∈ d.primeFactors, p ^ d.factorization p :=
      Nat.prod_primeFactors_pow_factorization hd0
    calc
      d = ∏ p ∈ d.primeFactors, p ^ d.factorization p := hprod
      _ = ∏ p ∈ d.primeFactors, p := by
        apply prod_congr rfl
        intro p hp
        rw [Nat.factorization_eq_one_of_squarefree hd
          (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp),
          pow_one]
  have hmu : (((moebius d : ℤ) : ℝ) ^ 2) = 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq_eq_one_of_squarefree hd]
    norm_num
  calc
    (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d =
        (∏ p ∈ d.primeFactors, (9 : ℝ)) /
          (∏ p ∈ d.primeFactors, (p : ℝ)) := by
      rw [hmu, ← prod_const, ← Nat.cast_prod, ← hdprod]
      norm_num
    _ = ∏ p ∈ d.primeFactors, (9 : ℝ) / p := by
      rw [← prod_div_distrib]

theorem liuPanPrimePowerJ9_term_non_squarefree (d : ℕ)
    (hd : ¬Squarefree d) :
    (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d = 0 := by
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hd]
  norm_num

/-- Subset expansion bounds the finite `J₉` mass by its positive Euler
product. -/
theorem liuPanPrimePowerJ9Mass_le_prod_one_add (Q : ℕ) :
    liuPanPrimePowerJ9Mass Q ≤
      ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
        (1 + (9 : ℝ) / p) := by
  unfold liuPanPrimePowerJ9Mass
  calc
    (∑ d ∈ range (Q + 1),
        (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d) =
        ∑ d ∈ range (Q + 1),
          if Squarefree d then
            (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d
          else 0 := by
      apply sum_congr rfl
      intro d hd
      by_cases hds : Squarefree d
      · rw [if_pos hds]
      · rw [if_neg hds, liuPanPrimePowerJ9_term_non_squarefree d hds]
    _ = ∑ d ∈ (range (Q + 1)).filter Squarefree,
        (((moebius d : ℤ) : ℝ) ^ 2) * (9 : ℝ) ^ d.primeFactors.card / d := by
      rw [sum_filter]
    _ = ∑ d ∈ (range (Q + 1)).filter Squarefree,
        ∏ p ∈ d.primeFactors, (9 : ℝ) / p := by
      apply sum_congr rfl
      intro d hd
      exact liuPanPrimePowerJ9_term_squarefree d (mem_filter.mp hd).2
    _ ≤ ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
        (1 + (9 : ℝ) / p) := by
      exact sum_squarefree_prod_primeFactors_le_prod_one_add Q
        (fun p => (9 : ℝ) / p) fun p hp =>
          div_nonneg (by norm_num) (Nat.cast_nonneg p)

theorem liuPanPrimePowerCofactorSqrtMass_nonneg (Q : ℕ) :
    0 ≤ liuPanPrimePowerCofactorSqrtMass Q := by
  unfold liuPanPrimePowerCofactorSqrtMass
  exact sum_nonneg fun e _ =>
    div_nonneg
      (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _))
      (Real.sqrt_nonneg _)

theorem liuPanPrimePowerCofactorLinearMass_nonneg (Q : ℕ) :
    0 ≤ liuPanPrimePowerCofactorLinearMass Q := by
  unfold liuPanPrimePowerCofactorLinearMass
  exact sum_nonneg fun e _ =>
    div_nonneg
      (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _))
      (Nat.cast_nonneg _)

theorem liuPanPrimePowerH3Mass_eq_panMainTotientWeightedSum (Q : ℕ) :
    liuPanPrimePowerH3Mass Q = panMainTotientWeightedSum Q := by
  rfl

/-- The square-root cofactor mass is already dominated by `H₃`; no extra
power of the conductor cutoff is lost. -/
theorem liuPanPrimePowerCofactorSqrtMass_le_H3Mass (Q : ℕ) :
    liuPanPrimePowerCofactorSqrtMass Q ≤ liuPanPrimePowerH3Mass Q := by
  unfold liuPanPrimePowerCofactorSqrtMass liuPanPrimePowerH3Mass
  apply sum_le_sum
  intro e he
  by_cases he0 : e = 0
  · subst e
    simp [liuPanPrimePowerModulusWeight_zero]
  · have he1 : (1 : ℝ) ≤ Real.sqrt e := by
      rw [Real.one_le_sqrt]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr he0)
    exact div_le_self
      (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _))
      he1

/-- The linearly damped cofactor mass is also dominated by `H₃`. -/
theorem liuPanPrimePowerCofactorLinearMass_le_H3Mass (Q : ℕ) :
    liuPanPrimePowerCofactorLinearMass Q ≤ liuPanPrimePowerH3Mass Q := by
  unfold liuPanPrimePowerCofactorLinearMass liuPanPrimePowerH3Mass
  apply sum_le_sum
  intro e he
  by_cases he0 : e = 0
  · subst e
    simp [liuPanPrimePowerModulusWeight_zero]
  · exact div_le_self
      (div_nonneg (liuPanPrimePowerModulusWeight_nonneg e) (Nat.cast_nonneg _))
      (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr he0))

/-- The existing Pan main-term estimate is exactly the needed finite `H₃`
polylogarithmic bound. -/
theorem liuPanPrimePowerH3Mass_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      liuPanPrimePowerH3Mass Q ≤
        C * (Real.log (Q + 2)) ^ (6 : ℝ) := by
  simpa [liuPanPrimePowerH3Mass_eq_panMainTotientWeightedSum] using
    panMainTotientWeightedSum_le_polylog

/-- The second squarefree cofactor moment has the `log⁹` growth predicted by
its Euler product. -/
theorem liuPanPrimePowerJ9Mass_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ,
      liuPanPrimePowerJ9Mass Q ≤
        C * (Real.log (Q + 2)) ^ (9 : ℝ) := by
  classical
  obtain ⟨C₁, hC₁, hM⟩ :=
    AnalyticNumberTheory.Mertens.mertensSecond_nat
  let K : ℝ :=
    |AnalyticNumberTheory.Mertens.mertensSecondConstant| +
      C₁ / Real.log 2
  let C : ℝ :=
    max (1 / (Real.log 2) ^ (9 : ℝ)) (Real.exp (9 * K))
  have hlog2 : (0 : ℝ) < Real.log 2 :=
    Real.log_pos (by norm_num)
  have hC : 0 < C := by
    dsimp [C]
    exact lt_max_of_lt_left
      (div_pos zero_lt_one (Real.rpow_pos_of_pos hlog2 9))
  refine ⟨C, hC, ?_⟩
  intro Q
  by_cases hQ : Q ≤ 1
  · have hmass : liuPanPrimePowerJ9Mass Q ≤ 1 := by
      calc
        liuPanPrimePowerJ9Mass Q ≤
            ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
              (1 + (9 : ℝ) / p) :=
          liuPanPrimePowerJ9Mass_le_prod_one_add Q
        _ = 1 := by
          rw [AnalyticNumberTheory.Mertens.primesUpTo_eq_empty_of_le_one hQ]
          simp
    have hQ2 : (2 : ℕ) ≤ Q + 2 := by omega
    have hlogpow :
        (Real.log 2) ^ (9 : ℝ) ≤
          (Real.log (Q + 2)) ^ (9 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlog2)
        (Real.log_le_log (by norm_num) (by exact_mod_cast hQ2))
        (by norm_num)
    calc
      liuPanPrimePowerJ9Mass Q ≤ 1 := hmass
      _ = 1 / (Real.log 2) ^ (9 : ℝ) *
          (Real.log 2) ^ (9 : ℝ) := by
        field_simp [(Real.rpow_pos_of_pos hlog2 9).ne']
      _ ≤ 1 / (Real.log 2) ^ (9 : ℝ) *
          (Real.log (Q + 2)) ^ (9 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlogpow
          (div_nonneg zero_le_one
            (Real.rpow_nonneg (le_of_lt hlog2) 9))
      _ ≤ C * (Real.log (Q + 2)) ^ (9 : ℝ) := by
        exact mul_le_mul_of_nonneg_right
          (le_max_left (1 / (Real.log 2) ^ (9 : ℝ))
            (Real.exp (9 * K)))
          (Real.rpow_nonneg (Real.log_nonneg
            (by exact_mod_cast (show 1 ≤ Q + 2 by omega))) 9)
  · have hQ2 : 2 ≤ Q := by omega
    have hQ1 : (1 : ℝ) < Q := by exact_mod_cast (show 1 < Q by omega)
    have hlogQ : 0 < Real.log (Q : ℝ) := Real.log_pos hQ1
    have hM' :
        |AnalyticNumberTheory.Mertens.primeReciprocalSum Q -
          (Real.log (Real.log (Q : ℝ)) +
            AnalyticNumberTheory.Mertens.mertensSecondConstant)| ≤
          C₁ / Real.log (Q : ℝ) :=
      hM Q hQ2
    have hpRS :
        AnalyticNumberTheory.Mertens.primeReciprocalSum Q ≤
          Real.log (Real.log (Q : ℝ)) + K := by
      have hupper :
          AnalyticNumberTheory.Mertens.primeReciprocalSum Q ≤
            Real.log (Real.log (Q : ℝ)) +
              AnalyticNumberTheory.Mertens.mertensSecondConstant +
                C₁ / Real.log (Q : ℝ) := by
        linarith [(abs_le.mp hM').2]
      have hconst :
          AnalyticNumberTheory.Mertens.mertensSecondConstant ≤
            |AnalyticNumberTheory.Mertens.mertensSecondConstant| :=
        le_abs_self _
      have hquot : C₁ / Real.log (Q : ℝ) ≤ C₁ / Real.log 2 := by
        exact div_le_div_of_nonneg_left (le_of_lt hC₁) hlog2
          (Real.log_le_log (by norm_num) (by exact_mod_cast hQ2))
      dsimp [K]
      linarith
    have hsum :
        (∑ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
          (9 : ℝ) / p) =
          9 * AnalyticNumberTheory.Mertens.primeReciprocalSum Q := by
      unfold AnalyticNumberTheory.Mertens.primeReciprocalSum
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    have hlogle :
        (Real.log (Q : ℝ)) ^ (9 : ℝ) ≤
          (Real.log (Q + 2)) ^ (9 : ℝ) := by
      exact Real.rpow_le_rpow (le_of_lt hlogQ)
        (Real.log_le_log (by positivity)
          (by exact_mod_cast (show Q ≤ Q + 2 by omega)))
        (by norm_num)
    have hu :
        ∀ p : ℕ, 0 ≤ (9 : ℝ) / p := fun p =>
      div_nonneg (by norm_num) (Nat.cast_nonneg p)
    calc
      liuPanPrimePowerJ9Mass Q ≤
          ∏ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
            (1 + (9 : ℝ) / p) :=
        liuPanPrimePowerJ9Mass_le_prod_one_add Q
      _ ≤ Real.exp
          (∑ p ∈ AnalyticNumberTheory.Mertens.primesUpTo Q,
            (9 : ℝ) / p) :=
        Real.prod_one_add_le_exp_sum
          (AnalyticNumberTheory.Mertens.primesUpTo Q) hu
      _ = Real.exp
          (9 * AnalyticNumberTheory.Mertens.primeReciprocalSum Q) := by
        rw [hsum]
      _ ≤ Real.exp (9 * (Real.log (Real.log (Q : ℝ)) + K)) := by
        exact Real.exp_le_exp.mpr
          (mul_le_mul_of_nonneg_left hpRS (by norm_num))
      _ = Real.exp (9 * K) * (Real.log (Q : ℝ)) ^ (9 : ℝ) := by
        calc
          Real.exp (9 * (Real.log (Real.log (Q : ℝ)) + K)) =
              Real.exp (9 * Real.log (Real.log (Q : ℝ)) + 9 * K) := by
            congr 1
            ring
          _ = Real.exp (9 * Real.log (Real.log (Q : ℝ))) *
                Real.exp (9 * K) := by
            rw [Real.exp_add]
          _ = (Real.log (Q : ℝ)) ^ (9 : ℝ) * Real.exp (9 * K) := by
            rw [show 9 * Real.log (Real.log (Q : ℝ)) =
              Real.log (Real.log (Q : ℝ)) * 9 by ring,
              Real.exp_mul, Real.exp_log hlogQ]
          _ = Real.exp (9 * K) * (Real.log (Q : ℝ)) ^ (9 : ℝ) := by
            ring
      _ ≤ C * (Real.log (Q + 2)) ^ (9 : ℝ) := by
        exact mul_le_mul
          (le_max_right (1 / (Real.log 2) ^ (9 : ℝ))
            (Real.exp (9 * K)))
          hlogle
          (Real.rpow_nonneg (le_of_lt hlogQ) 9)
          (le_of_lt hC)

/-- The density modulus mass occurring after averaging over Liu's moduli. -/
noncomputable def liuPanPrimePowerDensityModulusMass
    (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q / Nat.totient q

/-- The density modulus mass is nonnegative. -/
theorem liuPanPrimePowerDensityModulusMass_nonneg (N : ℕ) (B : ℝ) :
    0 ≤ liuPanPrimePowerDensityModulusMass N B := by
  unfold liuPanPrimePowerDensityModulusMass
  apply sum_nonneg
  intro q hq
  exact div_nonneg (liuPanPrimePowerModulusWeight_nonneg q) (Nat.cast_nonneg _)

/-- The density modulus mass is exactly the existing Pan main-term
totient-weighted sum at Liu's modulus cutoff. -/
theorem liuPanPrimePowerDensityModulusMass_eq_panMainTotientWeightedSum
    (N : ℕ) (B : ℝ) :
    liuPanPrimePowerDensityModulusMass N B =
      panMainTotientWeightedSum (panModulusCutoff N B) := by
  rfl

/-- The known Pan modulus estimate supplies the required polylogarithmic density
bound without discarding the arithmetic-progression structure. -/
theorem liuPanPrimePowerDensityModulusMass_le_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ),
      liuPanPrimePowerDensityModulusMass N B ≤
        C * (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := panMainTotientWeightedSum_le_polylog
  refine ⟨C, hC, fun N B => ?_⟩
  rw [liuPanPrimePowerDensityModulusMass_eq_panMainTotientWeightedSum]
  exact hbound _

/-- The unrestricted coefficient mass has a uniform power saving.  The exponent
comes only from the exact source rectangle and global Chebyshev control. -/
theorem liuPanPrimePowerTotal_le_rpow :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 8 ≤ N →
      liuPanPrimePowerTotal N N ≤
        C * (N : ℝ) ^ (107 / 120 : ℝ) := by
  obtain ⟨Cg, hCg, hglobal⟩ := exists_globalPrimePowerCorrection_le_sqrt
  let D := 2 * Real.sqrt
    (liuWeightP₁ReciprocalBound * liuSourceR1P₂ReciprocalBound)
  let C := max (Cg * D) 1
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro N hN
  have hD : 0 ≤ D := by
    dsimp [D]
    positivity
  calc
    liuPanPrimePowerTotal N N ≤
        Cg * liuPanPrimePowerPairSqrtMass N :=
      liuPanPrimePowerTotal_le_pairSqrtMass hglobal N
    _ ≤ Cg * (D * (N : ℝ) ^ (107 / 120 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by simpa [D, mul_assoc] using
          liuPanPrimePowerPairSqrtMass_le_rpow N hN) hCg
    _ = (Cg * D) * (N : ℝ) ^ (107 / 120 : ℝ) := by ring
    _ ≤ C * (N : ℝ) ^ (107 / 120 : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- The density product has the explicit power-saving coefficient scale,
uniformly in the modulus cutoff. -/
theorem liuPanPrimePowerDensityProduct_le_rpow_polylog :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 8 ≤ N →
      liuPanPrimePowerTotal N N *
          liuPanPrimePowerDensityModulusMass N B ≤
        C * (N : ℝ) ^ (107 / 120 : ℝ) *
          (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ) := by
  obtain ⟨Ct, hCt, htotal⟩ := liuPanPrimePowerTotal_le_rpow
  obtain ⟨Cd, hCd, hdensity⟩ :=
    liuPanPrimePowerDensityModulusMass_le_polylog
  refine ⟨Ct * Cd, mul_pos hCt hCd, ?_⟩
  intro N B hN
  calc
    liuPanPrimePowerTotal N N *
        liuPanPrimePowerDensityModulusMass N B ≤
      (Ct * (N : ℝ) ^ (107 / 120 : ℝ)) *
        (Cd * (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ)) := by
      exact mul_le_mul (htotal N hN) (hdensity N B)
        (liuPanPrimePowerDensityModulusMass_nonneg N B)
        (mul_nonneg hCt.le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
    _ = (Ct * Cd) * (N : ℝ) ^ (107 / 120 : ℝ) *
        (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ) := by ring

/-- The maximal character discrepancy over unit residue classes. -/
noncomputable def liuPanPrimePowerDiscrepancyMaxL
    (N y q : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuPanPrimePowerDiscrepancy N y q l|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- The maximal character discrepancy over `y ≤ N` and unit residues. -/
noncomputable def liuPanPrimePowerDiscrepancyMaxY
    (N q : ℕ) : ℝ :=
  ((range (N + 1)).image (fun y =>
    liuPanPrimePowerDiscrepancyMaxL N y q)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- A transparent weighted maximal character residual, with no large-sieve
estimate asserted. -/
noncomputable def liuMainPanPrimePowerCharacterResidual
    (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanPrimePowerDiscrepancyMaxY N q

/-- The maximal genuine nonprincipal discrepancy over unit residue classes. -/
noncomputable def liuPanPrimePowerNonprincipalDiscrepancyMaxL
    (N y q : ℕ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l =>
      |liuPanPrimePowerNonprincipalDiscrepancy N y q l|)).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- The maximal genuine nonprincipal discrepancy over `y ≤ N` and unit
residue classes. -/
noncomputable def liuPanPrimePowerNonprincipalDiscrepancyMaxY
    (N q : ℕ) : ℝ :=
  ((range (N + 1)).image (fun y =>
    liuPanPrimePowerNonprincipalDiscrepancyMaxL N y q)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- The transparent residual after the true principal mass is removed.  Via
`liuPanPrimePowerNonprincipalDiscrepancy_eq_discrepancy_add_noncoprime`, it is
exactly the old character discrepancy together with its noncoprime correction. -/
noncomputable def liuMainPanPrimePowerCharacterNoncoprimeResidual
    (N : ℕ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    liuPanPrimePowerModulusWeight q *
      liuPanPrimePowerNonprincipalDiscrepancyMaxY N q

theorem liuPanPrimePowerTotal_mono {N y x : ℕ} (hyx : y ≤ x) :
    liuPanPrimePowerTotal N y ≤ liuPanPrimePowerTotal N x := by
  unfold liuPanPrimePowerTotal
  exact sum_le_sum_of_subset_of_nonneg (range_mono (Nat.succ_le_succ hyx))
    (fun _ _ _ => liuPanPrimePowerCoefficient_nonneg _ _)

theorem liuPanPrimePowerDiscrepancy_le_maxY
    {N y q l : ℕ} (hy : y ≤ N) (hl : l ∈ unitResidues q) :
    liuPanPrimePowerDiscrepancy N y q l ≤
      liuPanPrimePowerDiscrepancyMaxY N q := by
  have hS : (unitResidues q).Nonempty := ⟨l, hl⟩
  have hL : |liuPanPrimePowerDiscrepancy N y q l| ≤
      liuPanPrimePowerDiscrepancyMaxL N y q := by
    unfold liuPanPrimePowerDiscrepancyMaxL
    rw [dif_pos hS]
    have hlmem : |liuPanPrimePowerDiscrepancy N y q l| ∈
        (unitResidues q).image (fun z =>
          |liuPanPrimePowerDiscrepancy N y q z|) :=
      mem_image.mpr ⟨l, hl, rfl⟩
    exact le_max' _ _ hlmem
  unfold liuPanPrimePowerDiscrepancyMaxY
  have hmem : liuPanPrimePowerDiscrepancyMaxL N y q ∈
      (range (N + 1)).image (fun z =>
        liuPanPrimePowerDiscrepancyMaxL N z q) :=
    mem_image.mpr
      ⟨y, mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩
  exact (le_abs_self _).trans (hL.trans (le_max' _ _ hmem))

theorem liuPanPrimePowerNonprincipalDiscrepancy_le_maxY
    {N y q l : ℕ} (hy : y ≤ N) (hl : l ∈ unitResidues q) :
    liuPanPrimePowerNonprincipalDiscrepancy N y q l ≤
      liuPanPrimePowerNonprincipalDiscrepancyMaxY N q := by
  have hS : (unitResidues q).Nonempty := ⟨l, hl⟩
  have hL : |liuPanPrimePowerNonprincipalDiscrepancy N y q l| ≤
      liuPanPrimePowerNonprincipalDiscrepancyMaxL N y q := by
    unfold liuPanPrimePowerNonprincipalDiscrepancyMaxL
    rw [dif_pos hS]
    have hlmem : |liuPanPrimePowerNonprincipalDiscrepancy N y q l| ∈
        (unitResidues q).image (fun z =>
          |liuPanPrimePowerNonprincipalDiscrepancy N y q z|) :=
      mem_image.mpr ⟨l, hl, rfl⟩
    exact le_max' _ _ hlmem
  unfold liuPanPrimePowerNonprincipalDiscrepancyMaxY
  have hmem : liuPanPrimePowerNonprincipalDiscrepancyMaxL N y q ∈
      (range (N + 1)).image (fun z =>
        liuPanPrimePowerNonprincipalDiscrepancyMaxL N z q) :=
    mem_image.mpr
      ⟨y, mem_range.mpr (Nat.lt_succ_iff.mpr hy), rfl⟩
  exact (le_abs_self _).trans (hL.trans (le_max' _ _ hmem))

theorem liuPanAPPrimePowerCorrectionMaxY_le_coprimeDensity_add_nonprincipal
    (N q : ℕ) (hq : 0 < q) :
    liuPanAPPrimePowerCorrectionMaxY N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      liuPanPrimePowerCoprimeTotal N N q / Nat.totient q +
        liuPanPrimePowerNonprincipalDiscrepancyMaxY N q := by
  unfold liuPanAPPrimePowerCorrectionMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (mem_range.mp hy)
  unfold liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  have hS : (unitResidues q).Nonempty := by
    by_cases hq1 : q = 1
    · subst q
      simp
    · have hq2 : 1 < q := by omega
      exact ⟨1, by simp [unitResidues, hq2]⟩
  rw [dif_pos hS]
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨l, hl, rfl⟩
  have hlunit : IsUnit (l : ZMod q) :=
    (ZMod.isUnit_iff_coprime l q).mpr (by
      rw [unitResidues, mem_filter] at hl
      exact hl.2)
  rw [liuPanSignedCorrectionBound_eq_coprimeDensity_add_nonprincipal
    hyN hlunit]
  exact add_le_add
    (div_le_div_of_nonneg_right
      (liuPanPrimePowerCoprimeTotal_mono (q := q) hyN)
      (Nat.cast_nonneg _))
    (liuPanPrimePowerNonprincipalDiscrepancy_le_maxY hyN hl)

theorem liuPanAPPrimePowerCorrectionMaxY_le_density_add_character
    (N q : ℕ) (hq : 0 < q) :
    liuPanAPPrimePowerCorrectionMaxY N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) ≤
      liuPanPrimePowerTotal N N / Nat.totient q +
        liuPanPrimePowerDiscrepancyMaxY N q := by
  unfold liuPanAPPrimePowerCorrectionMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  have hyN : y ≤ N := Nat.le_of_lt_succ (mem_range.mp hy)
  unfold liuPanAPPrimePowerCorrectionMaxL
  dsimp only
  have hS : (unitResidues q).Nonempty := by
    by_cases hq1 : q = 1
    · subst q
      simp
    · have hq2 : 1 < q := by omega
      exact ⟨1, by simp [unitResidues, hq2]⟩
  rw [dif_pos hS]
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨l, hl, rfl⟩
  have hlunit : IsUnit (l : ZMod q) :=
    (ZMod.isUnit_iff_coprime l q).mpr (by
      rw [unitResidues, mem_filter] at hl
      exact hl.2)
  rw [liuPanSignedCorrectionBound_eq_density_add_discrepancy hyN hq hlunit]
  exact add_le_add
    (div_le_div_of_nonneg_right (liuPanPrimePowerTotal_mono hyN)
      (Nat.cast_nonneg _))
    (liuPanPrimePowerDiscrepancy_le_maxY hyN hl)

/-- Exact structural reduction of the prime-power average: a coefficient mass
times the totient-weighted modulus density, plus one maximal character residual.
No estimate for the residual is asserted here. -/
theorem liuMainPanAPPrimePowerCorrectionAverage_le_density_add_character
    (N : ℕ) (B : ℝ) :
    (∑ q ∈ range (panModulusCutoff N B + 1),
      liuPanPrimePowerModulusWeight q *
        liuPanAPPrimePowerCorrectionMaxY N q N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
      liuPanPrimePowerTotal N N *
          liuPanPrimePowerDensityModulusMass N B +
        liuMainPanPrimePowerCharacterResidual N B := by
  unfold liuPanPrimePowerDensityModulusMass
    liuMainPanPrimePowerCharacterResidual
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          liuPanAPPrimePowerCorrectionMaxY N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
      ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          (liuPanPrimePowerTotal N N / Nat.totient q +
            liuPanPrimePowerDiscrepancyMaxY N q) := by
      apply sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        simp [liuPanPrimePowerModulusWeight_zero]
      · exact mul_le_mul_of_nonneg_left
          (liuPanAPPrimePowerCorrectionMaxY_le_density_add_character
            N q (Nat.pos_of_ne_zero hq0))
          (liuPanPrimePowerModulusWeight_nonneg q)
    _ = liuPanPrimePowerTotal N N *
          (∑ q ∈ range (panModulusCutoff N B + 1),
            liuPanPrimePowerModulusWeight q / Nat.totient q) +
        ∑ q ∈ range (panModulusCutoff N B + 1),
          liuPanPrimePowerModulusWeight q *
            liuPanPrimePowerDiscrepancyMaxY N q := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      ring

/-- Source-faithful reduction of the averaged correction: the true coprime
principal mass is bounded by the full coefficient mass, while all remaining
character and noncoprime effects stay in one explicit maximal residual. -/
theorem
    liuMainPanAPPrimePowerCorrectionAverage_le_density_add_characterNoncoprime
    (N : ℕ) (B : ℝ) :
    (∑ q ∈ range (panModulusCutoff N B + 1),
      liuPanPrimePowerModulusWeight q *
        liuPanAPPrimePowerCorrectionMaxY N q N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
      liuPanPrimePowerTotal N N *
          liuPanPrimePowerDensityModulusMass N B +
        liuMainPanPrimePowerCharacterNoncoprimeResidual N B := by
  unfold liuPanPrimePowerDensityModulusMass
    liuMainPanPrimePowerCharacterNoncoprimeResidual
  calc
    (∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          liuPanAPPrimePowerCorrectionMaxY N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
      ∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          (liuPanPrimePowerTotal N N / Nat.totient q +
            liuPanPrimePowerNonprincipalDiscrepancyMaxY N q) := by
      apply sum_le_sum
      intro q hq
      by_cases hq0 : q = 0
      · subst q
        simp [liuPanPrimePowerModulusWeight_zero]
      · apply mul_le_mul_of_nonneg_left _ (liuPanPrimePowerModulusWeight_nonneg q)
        refine (liuPanAPPrimePowerCorrectionMaxY_le_coprimeDensity_add_nonprincipal
          N q (Nat.pos_of_ne_zero hq0)).trans ?_
        exact add_le_add
          (div_le_div_of_nonneg_right
            (liuPanPrimePowerCoprimeTotal_le_total N N q)
            (Nat.cast_nonneg _))
          le_rfl
    _ = liuPanPrimePowerTotal N N *
          (∑ q ∈ range (panModulusCutoff N B + 1),
            liuPanPrimePowerModulusWeight q / Nat.totient q) +
        ∑ q ∈ range (panModulusCutoff N B + 1),
          liuPanPrimePowerModulusWeight q *
            liuPanPrimePowerNonprincipalDiscrepancyMaxY N q := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro q hq
      ring

/-- The density term in the averaged correction is bounded by the known
polylogarithmic modulus sum; no estimate for the explicit residual is asserted. -/
theorem
    liuMainPanAPPrimePowerCorrectionAverage_le_polylog_add_characterNoncoprime :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ),
      (∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          liuPanAPPrimePowerCorrectionMaxY N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
        liuPanPrimePowerTotal N N *
            (C * (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ)) +
          liuMainPanPrimePowerCharacterNoncoprimeResidual N B := by
  obtain ⟨C, hC, hbound⟩ :=
    liuPanPrimePowerDensityModulusMass_le_polylog
  refine ⟨C, hC, fun N B => ?_⟩
  refine
    (liuMainPanAPPrimePowerCorrectionAverage_le_density_add_characterNoncoprime
      N B).trans ?_
  exact add_le_add
    (mul_le_mul_of_nonneg_left (hbound N B)
      (liuPanPrimePowerTotal_nonneg N N))
    le_rfl

/-- Quantitative density reduction of Liu's exact AP correction average.  The
only unestimated term is the displayed maximal character/noncoprime residual. -/
theorem
    liuMainPanAPPrimePowerCorrectionAverage_le_rpow_polylog_add_characterNoncoprime :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (B : ℝ), 8 ≤ N →
      (∑ q ∈ range (panModulusCutoff N B + 1),
        liuPanPrimePowerModulusWeight q *
          liuPanAPPrimePowerCorrectionMaxY N q N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N))) ≤
        C * (N : ℝ) ^ (107 / 120 : ℝ) *
            (Real.log (panModulusCutoff N B + 2)) ^ (6 : ℝ) +
          liuMainPanPrimePowerCharacterNoncoprimeResidual N B := by
  obtain ⟨C, hC, hdensity⟩ :=
    liuPanPrimePowerDensityProduct_le_rpow_polylog
  refine ⟨C, hC, fun N B hN => ?_⟩
  exact
    (liuMainPanAPPrimePowerCorrectionAverage_le_density_add_characterNoncoprime
      N B).trans (add_le_add (hdensity N B hN) le_rfl)

end MathlibNt.SieveTheory.LiuWeight
