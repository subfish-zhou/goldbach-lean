import MathlibNt.SieveTheory.Selberg.Liu.LiuSelbergCoefficient
import MathlibNt.SieveTheory.Arithmetic.LiuSingularSeries

/-!
# Exact finite Selberg optimization for Liu's source modulus

Liu's lemma `lm-selberg` states the existence of coefficients with main term
`[8 + O(ε)] 𝔖(N) / log N`; it does not prove the finite minimization in the
form needed by this development.  This file performs that minimization exactly.
After it, the genuinely analytic missing statement is precisely the eventual,
uniform weighted Mertens--Selberg lower bound for
`∑_{l ∣ Q, l ≤ R} ∏_{p ∣ l} 1 / (p - 2)`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset

/-- The positive local Selberg factor attached to a source divisor. -/
noncomputable def liuSelbergTerm (l : ℕ) : ℝ :=
  ∏ p ∈ l.primeFactors, ((p : ℝ) - 2)⁻¹

/-- Liu's truncated Selberg denominator.  It has no proof argument. -/
noncomputable def liuSelbergDenominator (N : ℕ) (epsilon : ℝ) : ℝ :=
  ∑ l ∈ liuSelbergLambdaSourceCarrier N epsilon, liuSelbergTerm l

/-- On the even source modulus, the explicit local factor is Mathlib's
`BoundingSieve.selbergTerms`. -/
theorem liuSelbergTerm_eq_selbergTerms
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∣ liuPaperQModulus N epsilon) :
    liuSelbergTerm l =
      (liuSelbergBoundingSieve N epsilon hNeven).selbergTerms l := by
  let S := liuSelbergBoundingSieve N epsilon hNeven
  rw [BoundingSieve.selbergTerms_apply, ← S.prod_primeFactors_nu hl,
    ← Finset.prod_mul_distrib]
  unfold liuSelbergTerm
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpl : p ∣ l := Nat.dvd_of_mem_primeFactors hp
  have hpQ : p ∣ liuPaperQModulus N epsilon := hpl.trans hl
  have hpN : ¬p ∣ N :=
    (prime_dvd_liuPaperQModulus (N := N) (epsilon := epsilon) hpprime).mp hpQ |>.2
  have hp2 : p ≠ 2 := fun h => hpN (h.symm ▸ hNeven.two_dvd)
  have hpgt : 2 < p :=
    lt_of_le_of_ne hpprime.two_le (by simpa using hp2.symm)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (lt_trans Nat.one_lt_two hpgt)
  have hp2r : (2 : ℝ) < p := by exact_mod_cast hpgt
  have hnu : S.nu p = ((p : ℝ) - 1)⁻¹ := by
    dsimp [S, liuSelbergBoundingSieve, liuSelbergReciprocalTotient]
    rw [if_neg hpprime.ne_zero, Nat.totient_prime hpprime]
    rw [Nat.cast_sub hpprime.one_le]
    simp [one_div]
  rw [hnu]
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpm2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have hpm2' : -2 + (p : ℝ) ≠ 0 := by linarith
  field_simp [hpm1, hpm2, hpm2']
  rw [show (p : ℝ) - 1 - 1 = (p : ℝ) - 2 by ring, div_self hpm2]

/-- Every explicit Selberg term on the source carrier is positive. -/
theorem liuSelbergTerm_pos
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    0 < liuSelbergTerm l := by
  rw [liuSelbergTerm_eq_selbergTerms hNeven
    ((Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1)]
  exact BoundingSieve.selbergTerms_pos
    (s := liuSelbergBoundingSieve N epsilon hNeven)
    ((Nat.mem_divisors.mp (Finset.mem_filter.mp hl).1).1)

/-- The denominator is positive once the truncation contains `1`. -/
theorem liuSelbergDenominator_pos
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    0 < liuSelbergDenominator N epsilon := by
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  have h1 : 1 ∈ liuSelbergLambdaSourceCarrier N epsilon := by
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hQ0⟩, hR⟩
  exact Finset.sum_pos
    (fun l hl => liuSelbergTerm_pos hNeven hl) ⟨1, h1⟩

/-- The prescribed diagonal coordinate, extended by zero off the truncation. -/
noncomputable def liuSelbergOptimalX
    (N : ℕ) (epsilon : ℝ) (l : ℕ) : ℝ :=
  if l ∈ liuSelbergLambdaSourceCarrier N epsilon then
    (μ l : ℝ) * liuSelbergTerm l / liuSelbergDenominator N epsilon
  else 0

/-- Reverse-divisor Möbius inversion of the optimal diagonal coordinates. -/
noncomputable def liuSelbergOptimalLambda
    (N : ℕ) (epsilon : ℝ) (d : ℕ) : ℝ :=
  if d ∈ liuSelbergLambdaSourceCarrier N epsilon then
    (∑ e ∈ liuSelbergLambdaSourceCarrier N epsilon,
      if d ∣ e then (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0) /
      liuSelbergReciprocalTotient d
  else 0

theorem liuSelbergOptimalLambda_eq_zero_of_not_mem
    {N d : ℕ} {epsilon : ℝ}
    (hd : d ∉ liuSelbergLambdaSourceCarrier N epsilon) :
    liuSelbergOptimalLambda N epsilon d = 0 := by
  simp [liuSelbergOptimalLambda, hd]

/-- The explicit optimizer is supported on divisors of the source modulus below
the source cutoff. -/
theorem liuSelbergOptimalLambda_support
    {N d : ℕ} {epsilon : ℝ}
    (hd : liuSelbergOptimalLambda N epsilon d ≠ 0) :
    d ∣ liuPaperQModulus N epsilon ∧ d ≤ paperQSourceCutoff N epsilon := by
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  by_contra h
  apply hd
  apply liuSelbergOptimalLambda_eq_zero_of_not_mem
  intro hdmem
  apply h
  exact ⟨(Nat.mem_divisors.mp (Finset.mem_filter.mp hdmem).1).1,
    (Finset.mem_filter.mp hdmem).2⟩

private lemma sum_moebius_eq_one {n : ℕ} :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then (1 : ℝ) else 0 := by
  have h := ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℝ)
  have hkey : (ζ * (μ : ArithmeticFunction ℝ)) n =
      (1 : ArithmeticFunction ℝ) n := by rw [h]
  rw [ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.one_apply] at hkey
  simpa [ArithmeticFunction.intCoe_apply, mul_comm] using hkey

private lemma dvd_iff_div_dvd {e l d : ℕ}
    (he : e ≠ 0) (hd : d ∣ e) (hl : l ∣ e) :
    l ∣ d ↔ e / d ∣ e / l := by
  constructor
  · rintro ⟨k, rfl⟩
    have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hl (Nat.pos_of_ne_zero he)
    have hkl : k ∣ e / l := by
      have heq : e = l * (e / l) := by
        rw [mul_comm, Nat.div_mul_cancel hl]
      rw [heq] at hd
      exact (Nat.mul_dvd_mul_iff_left hl0).mp hd
    rw [(Nat.div_div_eq_div_mul e l k).symm]
    exact Nat.div_dvd_of_dvd hkl
  · rintro ⟨j, hj⟩
    have heq1 : e = l * (e / l) := by
      rw [mul_comm, Nat.div_mul_cancel hl]
    have heq2 : d * (e / d) = e := by
      rw [mul_comm, Nat.div_mul_cancel hd]
    have hdq : 0 < e / d :=
      Nat.pos_of_dvd_of_pos (Nat.div_dvd_of_dvd hd) (Nat.pos_of_ne_zero he)
    refine ⟨j, Nat.mul_right_cancel hdq ?_⟩
    calc
      d * (e / d) = e := heq2
      _ = l * (e / l) := heq1
      _ = l * j * (e / d) := by rw [hj]; ring

private lemma sum_moebius_quotient_of_dvd {e l : ℕ}
    (he : e ≠ 0) (hle : l ∣ e) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  have hbij :
      (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
        ∑ d ∈ e.divisors, if d ∣ e / l then (μ d : ℝ) else 0 := by
    refine Finset.sum_bij (fun d _ => e / d) ?_ ?_ ?_ ?_
    · intro d hd
      exact Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, he⟩
    · intro a ha b hb hab
      exact (Nat.div_div_self (Nat.mem_divisors.mp ha).1 he).symm.trans
        ((congrArg (e / ·) hab).trans
          (Nat.div_div_self (Nat.mem_divisors.mp hb).1 he))
    · intro d hd
      exact ⟨e / d, Nat.mem_divisors.mpr
        ⟨Nat.div_dvd_of_dvd (Nat.mem_divisors.mp hd).1, he⟩,
        Nat.div_div_self (Nat.mem_divisors.mp hd).1 he⟩
    · intro d hd
      have hdvd := (Nat.mem_divisors.mp hd).1
      by_cases hld : l ∣ d
      · simp [hld, (dvd_iff_div_dvd he hdvd hle).mp hld]
      · simp [hld, not_congr (dvd_iff_div_dvd he hdvd hle) |>.mp hld]
  rw [hbij, ← Finset.sum_filter,
    Nat.divisors_filter_dvd_of_dvd he (Nat.div_dvd_of_dvd hle),
    sum_moebius_eq_one]
  by_cases hel : e = l
  · subst e
    have hl0 : 0 < l := Nat.pos_of_ne_zero he
    simp [Nat.div_self hl0]
  · have hdiv : e / l ≠ 1 := by
      intro h
      apply hel
      calc
        e = l * (e / l) := by rw [mul_comm, Nat.div_mul_cancel hle]
        _ = l := by rw [h, mul_one]
    simp [hel, hdiv]

set_option maxHeartbeats 800000 in
/-- Reverse-divisor inversion recovers every diagonal coordinate on the
truncated carrier. -/
theorem liuSelbergOptimalX_eq_sum_nu_mul_lambda
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hl : l ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    liuSelbergOptimalX N epsilon l =
      ∑ d ∈ (liuPaperQModulus N epsilon).divisors,
        if l ∣ d then
          (liuSelbergBoundingSieve N epsilon hNeven).nu d *
            liuSelbergOptimalLambda N epsilon d
        else 0 := by
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let S := liuSelbergBoundingSieve N epsilon hNeven
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  have hcancel : ∀ d ∈ C,
      S.nu d * liuSelbergOptimalLambda N epsilon d =
        ∑ e ∈ C, if d ∣ e then
          (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0 := by
    intro d hd
    have hdQ : d ∣ S.prodPrimes := by
      exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hnu : S.nu d ≠ 0 := S.nu_ne_zero hdQ
    have hnu_eq : S.nu d = liuSelbergReciprocalTotient d := rfl
    rw [liuSelbergOptimalLambda, if_pos hd]
    rw [← hnu_eq]
    field_simp [hnu]
    rfl
  have hrestrict :
      (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
        if l ∣ d then S.nu d * liuSelbergOptimalLambda N epsilon d else 0) =
      ∑ d ∈ C, if l ∣ d then S.nu d *
        liuSelbergOptimalLambda N epsilon d else 0 := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hdQ hdC
      rw [liuSelbergOptimalLambda_eq_zero_of_not_mem hdC]
      simp
  rw [hrestrict]
  have hexpand :
      (∑ d ∈ C, if l ∣ d then S.nu d *
        liuSelbergOptimalLambda N epsilon d else 0) =
      ∑ d ∈ C, if l ∣ d then
        (∑ e ∈ C, if d ∣ e then (μ (e / d) : ℝ) *
          liuSelbergOptimalX N epsilon e else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · rw [if_pos hld, if_pos hld, hcancel d hd]
    · simp [hld]
  rw [hexpand]
  have hdouble :
      (∑ d ∈ C, if l ∣ d then
        (∑ e ∈ C, if d ∣ e then (μ (e / d) : ℝ) *
          liuSelbergOptimalX N epsilon e else 0) else 0) =
      ∑ d ∈ C, ∑ e ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) *
          liuSelbergOptimalX N epsilon e else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · simp only [hld, if_true]
    · simp only [hld, if_false, Finset.sum_const_zero]
  rw [hdouble]
  rw [Finset.sum_comm]
  have hinner : ∀ e ∈ C,
      (∑ d ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
        if e = l then (1 : ℝ) else 0 := by
    intro e he
    have heQ : e ∣ liuPaperQModulus N epsilon :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
    have he0 : e ≠ 0 :=
      Nat.ne_of_gt (Nat.pos_of_dvd_of_pos heQ (Nat.pos_of_ne_zero hQ0))
    have hfilt :
        C.filter (fun d => l ∣ d ∧ d ∣ e) =
          e.divisors.filter (fun d => l ∣ d) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdC, hld, hde⟩
        exact ⟨⟨hde, he0⟩, hld⟩
      · rintro ⟨⟨hde, _⟩, hld⟩
        have hdQ : d ∣ liuPaperQModulus N epsilon := hde.trans heQ
        have hdle : d ≤ paperQSourceCutoff N epsilon :=
          (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hde).trans
            (Finset.mem_filter.mp he).2
        exact ⟨Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨hdQ, hQ0⟩, hdle⟩, hld, hde⟩
    calc
      (∑ d ∈ C, if l ∣ d then
          (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
          ∑ d ∈ C.filter (fun d => l ∣ d ∧ d ∣ e),
            (μ (e / d) : ℝ) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;>
                simp [hld, hde]
      _ = ∑ d ∈ e.divisors, if l ∣ d then
            (μ (e / d) : ℝ) else 0 := by
              rw [hfilt, Finset.sum_filter]
      _ = if e = l then (1 : ℝ) else 0 := by
        by_cases hle : l ∣ e
        · exact sum_moebius_quotient_of_dvd he0 hle
        · have hel : e ≠ l := fun h => hle (h ▸ dvd_refl l)
          have hz : (∑ d ∈ e.divisors,
              if l ∣ d then (μ (e / d) : ℝ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro d hd
            rw [if_neg]
            intro hld
            exact hle (hld.trans (Nat.mem_divisors.mp hd).1)
          rw [hz]
          simp [hel]
  symm
  calc
    (∑ e ∈ C, ∑ d ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) *
          liuSelbergOptimalX N epsilon e else 0) else 0) =
        ∑ e ∈ C, liuSelbergOptimalX N epsilon e *
          (∑ d ∈ C, if l ∣ d then
            (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;>
        simp [hld, hde, mul_comm]
    _ = ∑ e ∈ C, liuSelbergOptimalX N epsilon e *
          (if e = l then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hinner e he]
    _ = liuSelbergOptimalX N epsilon l := by
      simp_rw [mul_ite, mul_one, mul_zero]
      have hlC : l ∈ C := by
        simpa [C] using hl
      rw [Finset.sum_ite_eq' C l, if_pos hlC]
    _ = liuSelbergOptimalX N epsilon l := rfl

/-- The reverse-divisor construction is normalized at `1`. -/
theorem liuSelbergOptimalLambda_one
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergOptimalLambda N epsilon 1 = 1 := by
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let G := liuSelbergDenominator N epsilon
  have hG : 0 < G := liuSelbergDenominator_pos hNeven hR
  have hQ0 : liuPaperQModulus N epsilon ≠ 0 :=
    (liuPaperQModulus_squarefree N epsilon).ne_zero
  have h1 : 1 ∈ C := by
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, hQ0⟩, hR⟩
  rw [liuSelbergOptimalLambda, if_pos h1]
  have hsum :
      (∑ e ∈ C, if 1 ∣ e then
        (μ (e / 1) : ℝ) * liuSelbergOptimalX N epsilon e else 0) = 1 := by
    calc
      (∑ e ∈ C, if 1 ∣ e then
          (μ (e / 1) : ℝ) * liuSelbergOptimalX N epsilon e else 0) =
          ∑ e ∈ C, liuSelbergTerm e / G := by
        apply Finset.sum_congr rfl
        intro e he
        have heQ : e ∣ liuPaperQModulus N epsilon :=
          (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
        have hesq : Squarefree e :=
          (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd heQ
        have hmu : ((μ e : ℤ) : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hesq
        rw [if_pos (one_dvd e), Nat.div_one, liuSelbergOptimalX, if_pos he]
        calc
          (μ e : ℝ) * ((μ e : ℝ) * liuSelbergTerm e / G) =
              ((μ e : ℝ) ^ 2) * liuSelbergTerm e / G := by ring
          _ = liuSelbergTerm e / G := by rw [hmu, one_mul]
      _ = 1 := by
        rw [← Finset.sum_div, show (∑ e ∈ C, liuSelbergTerm e) = G by rfl]
        exact div_self hG.ne'
  rw [hsum]
  simp [liuSelbergReciprocalTotient]

/-- The diagonal coordinate identity also holds off the truncation: both sides
vanish there. -/
theorem sum_nu_mul_liuSelbergOptimalLambda_eq_optimalX
    {N l : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hlQ : l ∣ liuPaperQModulus N epsilon) :
    (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
      if l ∣ d then
        (liuSelbergBoundingSieve N epsilon hNeven).nu d *
          liuSelbergOptimalLambda N epsilon d
      else 0) =
      liuSelbergOptimalX N epsilon l := by
  by_cases hlC : l ∈ liuSelbergLambdaSourceCarrier N epsilon
  · exact (liuSelbergOptimalX_eq_sum_nu_mul_lambda hNeven hlC).symm
  · rw [liuSelbergOptimalX]
    simp only [hlC, if_false]
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hld : l ∣ d
    · have hd0 : d ≠ 0 := Nat.ne_of_gt <|
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1
          (Nat.pos_of_ne_zero (liuPaperQModulus_squarefree N epsilon).ne_zero)
      have hlambda : liuSelbergOptimalLambda N epsilon d = 0 := by
        apply liuSelbergOptimalLambda_eq_zero_of_not_mem
        intro hdC
        apply hlC
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr
              ⟨hlQ, (liuPaperQModulus_squarefree N epsilon).ne_zero⟩,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld).trans
              (Finset.mem_filter.mp hdC).2⟩
      simp [hld, hlambda]
    · simp [hld]

/-- Exact finite Selberg minimization: the source quadratic coefficient of the
explicit optimizer is the reciprocal truncated denominator. -/
theorem liuSelbergCoefficientFactor_optimalLambda
    {N : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    liuSelbergCoefficientFactor N epsilon
        (liuSelbergOptimalLambda N epsilon) =
      1 / liuSelbergDenominator N epsilon := by
  let S := liuSelbergBoundingSieve N epsilon hNeven
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let G := liuSelbergDenominator N epsilon
  have hG : 0 < G := liuSelbergDenominator_pos hNeven hR
  rw [← liuSelbergCoefficientFactor_eq_mainSum_lambdaSquared_of_support
    hNeven (fun d hd => liuSelbergOptimalLambda_support hd)]
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hdiag :
      (∑ l ∈ (liuPaperQModulus N epsilon).divisors,
        (S.selbergTerms l)⁻¹ *
          (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
            if l ∣ d then S.nu d * liuSelbergOptimalLambda N epsilon d
            else 0) ^ 2) =
        ∑ l ∈ C, liuSelbergTerm l / G ^ 2 := by
    unfold C liuSelbergLambdaSourceCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlR : l ≤ paperQSourceCutoff N epsilon
    · rw [if_pos hlR]
      have hlQ : l ∣ liuPaperQModulus N epsilon :=
        (Nat.mem_divisors.mp hl).1
      have hlC : l ∈ liuSelbergLambdaSourceCarrier N epsilon :=
        Finset.mem_filter.mpr ⟨hl, hlR⟩
      rw [show
        (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
          if l ∣ d then S.nu d * liuSelbergOptimalLambda N epsilon d else 0) =
            liuSelbergOptimalX N epsilon l by
              exact sum_nu_mul_liuSelbergOptimalLambda_eq_optimalX hNeven hlQ]
      rw [liuSelbergOptimalX, if_pos hlC,
        ← liuSelbergTerm_eq_selbergTerms hNeven hlQ]
      have hterm : liuSelbergTerm l ≠ 0 :=
        (liuSelbergTerm_pos hNeven hlC).ne'
      have hmu : ((μ l : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          ((liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd hlQ)
      change
        (liuSelbergTerm l)⁻¹ *
            ((μ l : ℝ) * liuSelbergTerm l / G) ^ 2 =
          liuSelbergTerm l / G ^ 2
      field_simp [hterm, hG.ne']
      rw [hmu]
    · rw [if_neg hlR]
      have hlQ : l ∣ liuPaperQModulus N epsilon :=
        (Nat.mem_divisors.mp hl).1
      rw [show
        (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
          if l ∣ d then S.nu d * liuSelbergOptimalLambda N epsilon d else 0) =
            liuSelbergOptimalX N epsilon l by
              exact sum_nu_mul_liuSelbergOptimalLambda_eq_optimalX hNeven hlQ]
      rw [liuSelbergOptimalX, if_neg]
      · simp
      · simp [liuSelbergLambdaSourceCarrier, hlR]
  change
    (∑ l ∈ (liuPaperQModulus N epsilon).divisors,
      (S.selbergTerms l)⁻¹ *
        (∑ d ∈ (liuPaperQModulus N epsilon).divisors,
          if l ∣ d then S.nu d * liuSelbergOptimalLambda N epsilon d else 0) ^ 2) =
      1 / G
  rw [hdiag, ← Finset.sum_div]
  change (∑ l ∈ C, liuSelbergTerm l) / G ^ 2 = 1 / G
  rw [show (∑ l ∈ C, liuSelbergTerm l) = G by rfl]
  field_simp [hG.ne']

private theorem optimalLambda_packet_le_denominator
    {N d : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hd : d ∈ liuSelbergLambdaSourceCarrier N epsilon) :
    (∑ e ∈ liuSelbergLambdaSourceCarrier N epsilon,
        if d ∣ e then liuSelbergTerm e else 0) *
        ((liuSelbergBoundingSieve N epsilon hNeven).nu d)⁻¹ ≤
      liuSelbergDenominator N epsilon := by
  let Q := liuPaperQModulus N epsilon
  let C := liuSelbergLambdaSourceCarrier N epsilon
  let D := C.filter (d ∣ ·)
  let S := liuSelbergBoundingSieve N epsilon hNeven
  let P := D ×ˢ d.divisors
  let f : ℕ × ℕ → ℕ := fun x => (x.1 / d) * x.2
  have hQ0 : Q ≠ 0 := (liuPaperQModulus_squarefree N epsilon).ne_zero
  have hdQ : d ∣ Q := (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hd0 : d ≠ 0 := Nat.ne_of_gt <|
    Nat.pos_of_dvd_of_pos hdQ (Nat.pos_of_ne_zero hQ0)
  have hdivsum : (∑ k ∈ d.divisors, S.selbergTerms k) =
      S.selbergTerms d * (S.nu d)⁻¹ := by
    calc
      (∑ k ∈ d.divisors, S.selbergTerms k) =
          ∑ k ∈ Q.divisors, if k ∣ d then S.selbergTerms k else 0 := by
        rw [← Finset.sum_filter, Nat.divisors_filter_dvd_of_dvd hQ0 hdQ]
      _ = S.selbergTerms d * (S.nu d)⁻¹ :=
        S.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdQ
  have hpacket : ∀ e ∈ D,
      (∑ k ∈ d.divisors, S.selbergTerms ((e / d) * k)) =
        S.selbergTerms e * (S.nu d)⁻¹ := by
    intro e he
    have heC : e ∈ C := (Finset.mem_filter.mp he).1
    have hde : d ∣ e := (Finset.mem_filter.mp he).2
    have heQ : e ∣ Q := (Nat.mem_divisors.mp (Finset.mem_filter.mp heC).1).1
    have hesq : Squarefree e :=
      (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd heQ
    have hemul : d * (e / d) = e := Nat.mul_div_cancel' hde
    have hcop : d.Coprime (e / d) := by
      apply Nat.coprime_of_squarefree_mul
      rw [hemul]
      exact S.squarefree_of_mem_divisors_prodPrimes (Finset.mem_filter.mp heC).1
    calc
      (∑ k ∈ d.divisors, S.selbergTerms ((e / d) * k)) =
          S.selbergTerms (e / d) * ∑ k ∈ d.divisors, S.selbergTerms k := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        exact S.selbergTerms_isMultiplicative.map_mul_of_coprime
          (hcop.symm.of_dvd_right (Nat.mem_divisors.mp hk).1)
      _ = S.selbergTerms (e / d) *
          (S.selbergTerms d * (S.nu d)⁻¹) := by rw [hdivsum]
      _ = S.selbergTerms e * (S.nu d)⁻¹ := by
        rw [← mul_assoc,
          ← S.selbergTerms_isMultiplicative.map_mul_of_coprime hcop.symm]
        rw [mul_comm (e / d) d, hemul]
  have hinj : Set.InjOn f P := by
    intro x hx y hy hxy
    change (x.1 / d) * x.2 = (y.1 / d) * y.2 at hxy
    have hxmem := Finset.mem_product.mp hx
    have hymem := Finset.mem_product.mp hy
    have hxD := hxmem.1
    have hyD := hymem.1
    have hxde : d ∣ x.1 := (Finset.mem_filter.mp hxD).2
    have hyde : d ∣ y.1 := (Finset.mem_filter.mp hyD).2
    have hxC : x.1 ∈ C := (Finset.mem_filter.mp hxD).1
    have hyC : y.1 ∈ C := (Finset.mem_filter.mp hyD).1
    have hxeQ : x.1 ∣ Q :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hxC).1).1
    have hyeQ : y.1 ∣ Q :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hyC).1).1
    have hxcop : (x.1 / d).Coprime d :=
      (Nat.coprime_of_squarefree_mul (by
        rw [Nat.mul_div_cancel' hxde]
        exact (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd hxeQ)).symm
    have hycop : (y.1 / d).Coprime d :=
      (Nat.coprime_of_squarefree_mul (by
        rw [Nat.mul_div_cancel' hyde]
        exact (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd hyeQ)).symm
    have hk : x.2 = y.2 := by
      have hg := congrArg (fun n => Nat.gcd n d) hxy
      rw [Nat.gcd_mul_of_coprime_of_dvd hxcop
            (Nat.mem_divisors.mp hxmem.2).1,
          Nat.gcd_mul_of_coprime_of_dvd hycop
            (Nat.mem_divisors.mp hymem.2).1] at hg
      exact hg
    have hkpos : 0 < x.2 := Nat.pos_of_dvd_of_pos
      (Nat.mem_divisors.mp hxmem.2).1 (Nat.pos_of_ne_zero hd0)
    have hquot : x.1 / d = y.1 / d := by
      rw [hk] at hxy
      exact Nat.mul_right_cancel (hk ▸ hkpos) hxy
    apply Prod.ext
    · calc
        x.1 = d * (x.1 / d) := (Nat.mul_div_cancel' hxde).symm
        _ = d * (y.1 / d) := by rw [hquot]
        _ = y.1 := Nat.mul_div_cancel' hyde
    · exact hk
  have himage : P.image f ⊆ C := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have hxmem := Finset.mem_product.mp hx
    have hxC : x.1 ∈ C := (Finset.mem_filter.mp hxmem.1).1
    have hxde : d ∣ x.1 := (Finset.mem_filter.mp hxmem.1).2
    have hxeQ : x.1 ∣ Q :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hxC).1).1
    have hfxe : f x ∣ x.1 := by
      rw [show x.1 = (x.1 / d) * d by exact (Nat.div_mul_cancel hxde).symm]
      exact Nat.mul_dvd_mul_left (x.1 / d) (Nat.mem_divisors.mp hxmem.2).1
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hfxe.trans hxeQ, hQ0⟩, ?_⟩
    exact (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hxeQ
      (Nat.pos_of_ne_zero hQ0)) hfxe).trans (Finset.mem_filter.mp hxC).2
  have hnonneg : ∀ n ∈ C, 0 ≤ S.selbergTerms n := by
    intro n hn
    exact (S.selbergTerms_pos
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1).le
  change (∑ e ∈ C, if d ∣ e then liuSelbergTerm e else 0) *
    (S.nu d)⁻¹ ≤ _
  rw [← Finset.sum_filter]
  change (∑ e ∈ D, liuSelbergTerm e) * (S.nu d)⁻¹ ≤ _
  calc
    (∑ e ∈ D, liuSelbergTerm e) * (S.nu d)⁻¹ =
        (∑ e ∈ D, S.selbergTerms e) * (S.nu d)⁻¹ := by
      congr 1
      apply Finset.sum_congr rfl
      intro e he
      apply liuSelbergTerm_eq_selbergTerms hNeven
      exact (Nat.mem_divisors.mp
        (Finset.mem_filter.mp (Finset.mem_filter.mp he).1).1).1
    _ = ∑ e ∈ D, ∑ k ∈ d.divisors,
          S.selbergTerms ((e / d) * k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      exact (hpacket e he).symm
    _ = ∑ x ∈ P, S.selbergTerms (f x) := by
      exact (Finset.sum_product D d.divisors
        (fun x => S.selbergTerms (f x))).symm
    _ = ∑ n ∈ P.image f, S.selbergTerms n := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ C, S.selbergTerms n :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun n hn _ => hnonneg n hn)
    _ = liuSelbergDenominator N epsilon := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      apply liuSelbergTerm_eq_selbergTerms hNeven
      exact (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1

/-- Every finite optimal coefficient has the classical Selberg bound. -/
theorem abs_liuSelbergOptimalLambda_le_one
    {N d : ℕ} {epsilon : ℝ} (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    |liuSelbergOptimalLambda N epsilon d| ≤ 1 := by
  by_cases hd : d ∈ liuSelbergLambdaSourceCarrier N epsilon
  · let C := liuSelbergLambdaSourceCarrier N epsilon
    let S := liuSelbergBoundingSieve N epsilon hNeven
    let G := liuSelbergDenominator N epsilon
    have hG : 0 < G := liuSelbergDenominator_pos hNeven hR
    have hdQ : d ∣ liuPaperQModulus N epsilon :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hnu : 0 < S.nu d := S.nu_pos_of_dvd_prodPrimes hdQ
    have hsumabs :
        (∑ e ∈ C, |if d ∣ e then
          (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0|) =
          (∑ e ∈ C, if d ∣ e then liuSelbergTerm e else 0) / G := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hde : d ∣ e
      · have heQ : e ∣ liuPaperQModulus N epsilon :=
          (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
        have hesq : Squarefree e :=
          (liuPaperQModulus_squarefree N epsilon).squarefree_of_dvd heQ
        have hqsq : Squarefree (e / d) :=
          hesq.squarefree_of_dvd (Nat.div_dvd_of_dvd hde)
        have hmue : |(μ e : ℝ)| = 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hesq
        have hmuq : |(μ (e / d) : ℝ)| = 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hqsq
        have hterm : 0 < liuSelbergTerm e := liuSelbergTerm_pos hNeven he
        rw [if_pos hde, liuSelbergOptimalX, if_pos he, abs_mul, abs_div,
          abs_mul, hmuq, hmue, abs_of_pos hterm, abs_of_pos hG]
        rw [if_pos hde]
        ring
      · simp [hde]
    rw [liuSelbergOptimalLambda, if_pos hd, abs_div]
    change |∑ e ∈ C, if d ∣ e then
      (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0| /
        |S.nu d| ≤ 1
    rw [abs_of_pos hnu]
    calc
      |∑ e ∈ C, if d ∣ e then
          (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0| / S.nu d ≤
          (∑ e ∈ C, |if d ∣ e then
            (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0|) /
              S.nu d :=
        div_le_div_of_nonneg_right
          (Finset.abs_sum_le_sum_abs
            (fun e => if d ∣ e then
              (μ (e / d) : ℝ) * liuSelbergOptimalX N epsilon e else 0) C)
          hnu.le
      _ = ((∑ e ∈ C, if d ∣ e then liuSelbergTerm e else 0) *
          (S.nu d)⁻¹) / G := by
        rw [hsumabs]
        field_simp [hG.ne', hnu.ne']
      _ ≤ G / G := div_le_div_of_nonneg_right
        (optimalLambda_packet_le_denominator hNeven hd) hG.le
      _ = 1 := div_self hG.ne'
  · rw [liuSelbergOptimalLambda_eq_zero_of_not_mem hd]
    simp

/-- Divisors of the sieve product retained by a finite Selberg cutoff. -/
def truncatedSelbergCarrier (S : BoundingSieve) (R : ℕ) : Finset ℕ :=
  S.prodPrimes.divisors.filter (fun d => d ≤ R)

/-- The finite Selberg denominator for an arbitrary bounding sieve and cutoff. -/
noncomputable def truncatedSelbergDenominator (S : BoundingSieve) (R : ℕ) : ℝ :=
  ∑ d ∈ truncatedSelbergCarrier S R, S.selbergTerms d

/-- The diagonal coordinates of the finite truncated Selberg optimizer. -/
noncomputable def truncatedSelbergOptimalX
    (S : BoundingSieve) (R l : ℕ) : ℝ :=
  if l ∈ truncatedSelbergCarrier S R then
    (μ l : ℝ) * S.selbergTerms l / truncatedSelbergDenominator S R
  else 0

/-- Reverse-divisor Möbius inversion of the truncated optimal diagonal coordinates. -/
noncomputable def truncatedSelbergOptimalLambda
    (S : BoundingSieve) (R d : ℕ) : ℝ :=
  if d ∈ truncatedSelbergCarrier S R then
    (∑ e ∈ truncatedSelbergCarrier S R,
      if d ∣ e then (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0) /
      S.nu d
  else 0

theorem truncatedSelbergDenominator_pos (S : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    0 < truncatedSelbergDenominator S R := by
  have h1 : 1 ∈ truncatedSelbergCarrier S R := by
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, S.prodPrimes_ne_zero⟩, hR⟩
  exact Finset.sum_pos
    (fun d hd => S.selbergTerms_pos
      ((Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1)) ⟨1, h1⟩

theorem truncatedSelbergOptimalLambda_eq_zero_of_not_mem
    {S : BoundingSieve} {R d : ℕ} (hd : d ∉ truncatedSelbergCarrier S R) :
    truncatedSelbergOptimalLambda S R d = 0 := by
  simp [truncatedSelbergOptimalLambda, hd]

/-- The finite optimizer is supported on divisors of the sieve product below its
cutoff. -/
theorem truncatedSelbergOptimalLambda_support
    {S : BoundingSieve} {R d : ℕ}
    (hd : truncatedSelbergOptimalLambda S R d ≠ 0) :
    d ∣ S.prodPrimes ∧ d ≤ R := by
  by_contra h
  apply hd
  apply truncatedSelbergOptimalLambda_eq_zero_of_not_mem
  intro hmem
  apply h
  exact ⟨(Nat.mem_divisors.mp (Finset.mem_filter.mp hmem).1).1,
    (Finset.mem_filter.mp hmem).2⟩

private theorem truncatedSelbergOptimalX_eq_sum_nu_mul_lambda
    (S : BoundingSieve) (R l : ℕ) (hl : l ∈ truncatedSelbergCarrier S R) :
    truncatedSelbergOptimalX S R l =
      ∑ d ∈ S.prodPrimes.divisors,
        if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0 := by
  let C := truncatedSelbergCarrier S R
  have hrestrict :
      (∑ d ∈ S.prodPrimes.divisors,
        if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0) =
      ∑ d ∈ C, if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0 := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact (Finset.mem_filter.mp hd).1
    · intro d hdP hdC
      rw [truncatedSelbergOptimalLambda_eq_zero_of_not_mem hdC]
      simp
  rw [hrestrict]
  have hcancel : ∀ d ∈ C,
      S.nu d * truncatedSelbergOptimalLambda S R d =
        ∑ e ∈ C, if d ∣ e then
          (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0 := by
    intro d hd
    have hdP : d ∣ S.prodPrimes :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hnu : S.nu d ≠ 0 := S.nu_ne_zero hdP
    rw [truncatedSelbergOptimalLambda, if_pos hd]
    field_simp [hnu]
    rfl
  have hexpand :
      (∑ d ∈ C, if l ∣ d then S.nu d *
        truncatedSelbergOptimalLambda S R d else 0) =
      ∑ d ∈ C, if l ∣ d then
        (∑ e ∈ C, if d ∣ e then (μ (e / d) : ℝ) *
          truncatedSelbergOptimalX S R e else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · rw [if_pos hld, if_pos hld, hcancel d hd]
    · simp [hld]
  rw [hexpand]
  have hdouble :
      (∑ d ∈ C, if l ∣ d then
        (∑ e ∈ C, if d ∣ e then (μ (e / d) : ℝ) *
          truncatedSelbergOptimalX S R e else 0) else 0) =
      ∑ d ∈ C, ∑ e ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) *
          truncatedSelbergOptimalX S R e else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    by_cases hld : l ∣ d
    · simp only [hld, if_true]
    · simp only [hld, if_false, Finset.sum_const_zero]
  rw [hdouble]
  rw [Finset.sum_comm]
  have hinner : ∀ e ∈ C,
      (∑ d ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
        if e = l then (1 : ℝ) else 0 := by
    intro e he
    have heP : e ∣ S.prodPrimes :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
    have he0 : e ≠ 0 := Nat.ne_of_gt <|
      Nat.pos_of_dvd_of_pos heP (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)
    have hfilt :
        C.filter (fun d => l ∣ d ∧ d ∣ e) =
          e.divisors.filter (fun d => l ∣ d) := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors]
      constructor
      · rintro ⟨hdC, hld, hde⟩
        exact ⟨⟨hde, he0⟩, hld⟩
      · rintro ⟨⟨hde, _⟩, hld⟩
        have hdP : d ∣ S.prodPrimes := hde.trans heP
        have hdR : d ≤ R :=
          (Nat.le_of_dvd (Nat.pos_of_ne_zero he0) hde).trans
            (Finset.mem_filter.mp he).2
        exact ⟨Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨hdP, S.prodPrimes_ne_zero⟩, hdR⟩, hld, hde⟩
    calc
      (∑ d ∈ C, if l ∣ d then
          (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) =
          ∑ d ∈ C.filter (fun d => l ∣ d ∧ d ∣ e),
            (μ (e / d) : ℝ) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro d hd
              by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;>
                simp [hld, hde]
      _ = ∑ d ∈ e.divisors, if l ∣ d then
            (μ (e / d) : ℝ) else 0 := by
              rw [hfilt, Finset.sum_filter]
      _ = if e = l then (1 : ℝ) else 0 := by
        by_cases hle : l ∣ e
        · exact sum_moebius_quotient_of_dvd he0 hle
        · have hel : e ≠ l := fun h => hle (h ▸ dvd_refl l)
          have hz : (∑ d ∈ e.divisors,
              if l ∣ d then (μ (e / d) : ℝ) else 0) = 0 := by
            apply Finset.sum_eq_zero
            intro d hd
            rw [if_neg]
            intro hld
            exact hle (hld.trans (Nat.mem_divisors.mp hd).1)
          rw [hz]
          simp [hel]
  symm
  calc
    (∑ e ∈ C, ∑ d ∈ C, if l ∣ d then
        (if d ∣ e then (μ (e / d) : ℝ) *
          truncatedSelbergOptimalX S R e else 0) else 0) =
        ∑ e ∈ C, truncatedSelbergOptimalX S R e *
          (∑ d ∈ C, if l ∣ d then
            (if d ∣ e then (μ (e / d) : ℝ) else 0) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d <;> by_cases hde : d ∣ e <;>
        simp [hld, hde, mul_comm]
    _ = ∑ e ∈ C, truncatedSelbergOptimalX S R e *
          (if e = l then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hinner e he]
    _ = truncatedSelbergOptimalX S R l := by
      simp_rw [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq' C l, if_pos (by simpa [C] using hl)]

/-- The reverse-divisor construction is normalized at one. -/
theorem truncatedSelbergOptimalLambda_one
    (S : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    truncatedSelbergOptimalLambda S R 1 = 1 := by
  let C := truncatedSelbergCarrier S R
  let G := truncatedSelbergDenominator S R
  have hG : 0 < G := truncatedSelbergDenominator_pos S hR
  have h1 : 1 ∈ C := by
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨one_dvd _, S.prodPrimes_ne_zero⟩, hR⟩
  rw [truncatedSelbergOptimalLambda, if_pos h1]
  have hsum :
      (∑ e ∈ C, if 1 ∣ e then
        (μ (e / 1) : ℝ) * truncatedSelbergOptimalX S R e else 0) = 1 := by
    calc
      (∑ e ∈ C, if 1 ∣ e then
          (μ (e / 1) : ℝ) * truncatedSelbergOptimalX S R e else 0) =
          ∑ e ∈ C, S.selbergTerms e / G := by
        apply Finset.sum_congr rfl
        intro e he
        have hesq : Squarefree e :=
          S.squarefree_of_mem_divisors_prodPrimes (Finset.mem_filter.mp he).1
        have hmu : ((μ e : ℤ) : ℝ) ^ 2 = 1 := by
          exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hesq
        rw [if_pos (one_dvd e), Nat.div_one, truncatedSelbergOptimalX, if_pos he]
        calc
          (μ e : ℝ) * ((μ e : ℝ) * S.selbergTerms e / G) =
              ((μ e : ℝ) ^ 2) * S.selbergTerms e / G := by ring
          _ = S.selbergTerms e / G := by rw [hmu, one_mul]
      _ = 1 := by
        rw [← Finset.sum_div, show (∑ e ∈ C, S.selbergTerms e) = G by rfl]
        exact div_self hG.ne'
  rw [hsum, S.nu_mult.map_one]
  norm_num

private theorem sum_nu_mul_truncatedSelbergOptimalLambda_eq_optimalX
    (S : BoundingSieve) (R l : ℕ) (hlP : l ∣ S.prodPrimes) :
    (∑ d ∈ S.prodPrimes.divisors,
      if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0) =
      truncatedSelbergOptimalX S R l := by
  by_cases hl : l ∈ truncatedSelbergCarrier S R
  · exact (truncatedSelbergOptimalX_eq_sum_nu_mul_lambda S R l hl).symm
  · rw [truncatedSelbergOptimalX, if_neg hl]
    apply Finset.sum_eq_zero
    intro d hd
    by_cases hld : l ∣ d
    · have hd0 : d ≠ 0 := Nat.ne_of_gt <|
        Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1
          (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)
      have hLam : truncatedSelbergOptimalLambda S R d = 0 := by
        apply truncatedSelbergOptimalLambda_eq_zero_of_not_mem
        intro hdC
        apply hl
        exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr
              ⟨hlP, S.prodPrimes_ne_zero⟩,
            (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) hld).trans
              (Finset.mem_filter.mp hdC).2⟩
      simp [hld, hLam]
    · simp [hld]

/-- Exact finite Selberg minimization for a cutoff-supported optimizer. -/
theorem mainSum_truncatedSelbergOptimalLambda
    (S : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) :
    S.mainSum (BoundingSieve.lambdaSquared (truncatedSelbergOptimalLambda S R)) =
      1 / truncatedSelbergDenominator S R := by
  let C := truncatedSelbergCarrier S R
  let G := truncatedSelbergDenominator S R
  have hG : 0 < G := truncatedSelbergDenominator_pos S hR
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hdiag :
      (∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
        (∑ d ∈ S.prodPrimes.divisors,
          if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0) ^ 2) =
        ∑ l ∈ C, S.selbergTerms l / G ^ 2 := by
    unfold C truncatedSelbergCarrier
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hlR : l ≤ R
    · rw [if_pos hlR]
      have hlP : l ∣ S.prodPrimes := (Nat.mem_divisors.mp hl).1
      have hlC : l ∈ truncatedSelbergCarrier S R :=
        Finset.mem_filter.mpr ⟨hl, hlR⟩
      rw [sum_nu_mul_truncatedSelbergOptimalLambda_eq_optimalX S R l hlP,
        truncatedSelbergOptimalX, if_pos hlC]
      have hterm : S.selbergTerms l ≠ 0 :=
        (S.selbergTerms_pos hlP).ne'
      have hmu : ((μ l : ℤ) : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree
          (S.squarefree_of_mem_divisors_prodPrimes hl)
      change (S.selbergTerms l)⁻¹ *
          ((μ l : ℝ) * S.selbergTerms l / G) ^ 2 =
        S.selbergTerms l / G ^ 2
      field_simp [hterm, hG.ne']
      rw [hmu]
    · rw [if_neg hlR]
      have hlP : l ∣ S.prodPrimes := (Nat.mem_divisors.mp hl).1
      rw [sum_nu_mul_truncatedSelbergOptimalLambda_eq_optimalX S R l hlP,
        truncatedSelbergOptimalX, if_neg]
      · simp
      · simp [truncatedSelbergCarrier, hlR]
  change
    (∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ *
      (∑ d ∈ S.prodPrimes.divisors,
        if l ∣ d then S.nu d * truncatedSelbergOptimalLambda S R d else 0) ^ 2) =
      1 / G
  rw [hdiag, ← Finset.sum_div]
  change (∑ l ∈ C, S.selbergTerms l) / G ^ 2 = 1 / G
  rw [show (∑ l ∈ C, S.selbergTerms l) = G by rfl]
  field_simp [hG.ne']

/-- The reciprocal truncated Selberg denominator is a lower bound for every
normalized weight supported on the truncated carrier. -/
theorem one_div_truncatedSelbergDenominator_le_mainSum
    (S : BoundingSieve) {R : ℕ} (w : ℕ → ℝ)
    (hw_one : w 1 = 1)
    (hw_support : ∀ {d : ℕ}, w d ≠ 0 → d ∈ truncatedSelbergCarrier S R) :
    1 / truncatedSelbergDenominator S R ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  let C := truncatedSelbergCarrier S R
  let x : ℕ → ℝ := fun l =>
    ∑ d ∈ S.prodPrimes.divisors, if l ∣ d then S.nu d * w d else 0
  have hC_subset : C ⊆ S.prodPrimes.divisors := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  have hx_zero : ∀ l ∈ S.prodPrimes.divisors, l ∉ C → x l = 0 := by
    intro l hlP hlC
    apply Finset.sum_eq_zero
    intro d hdP
    by_cases hld : l ∣ d
    · have hwd : w d = 0 := by
        by_contra hwd
        have hdC := hw_support hwd
        apply hlC
        exact Finset.mem_filter.mpr
          ⟨hlP, (Nat.le_of_dvd
            (Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hdP).1
              (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)) hld).trans
            (Finset.mem_filter.mp hdC).2⟩
      simp [hld, hwd]
    · simp [hld]
  have hMoebiusInvFull :
      ∑ l ∈ S.prodPrimes.divisors, (μ l : ℝ) * x l = 1 := by
    calc
      ∑ l ∈ S.prodPrimes.divisors, (μ l : ℝ) * x l =
          ∑ l ∈ S.prodPrimes.divisors,
            ∑ d ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by
            simp_rw [x, mul_sum]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            ∑ l ∈ S.prodPrimes.divisors,
              (μ l : ℝ) * (if l ∣ d then S.nu d * w d else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (∑ l ∈ d.divisors, (μ l : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            have hdvd : d ∣ S.prodPrimes := (Nat.mem_divisors.mp hd).1
            simp_rw [mul_ite, mul_zero]
            rw [← Finset.sum_filter,
              Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdvd,
              mul_sum]
            exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = ∑ d ∈ S.prodPrimes.divisors,
            S.nu d * w d * (if d = 1 then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [sum_moebius_eq_one]
      _ = S.nu 1 * w 1 := by
            have h1mem : (1 : ℕ) ∈ S.prodPrimes.divisors :=
              Nat.mem_divisors.mpr ⟨one_dvd S.prodPrimes, S.prodPrimes_ne_zero⟩
            simp_rw [mul_ite, mul_one, mul_zero]
            rw [Finset.sum_ite_eq_of_mem' _ _ _ h1mem]
      _ = 1 := by
            rw [S.nu_mult.map_one, hw_one]
            norm_num
  have hMoebiusInv : ∑ l ∈ C, (μ l : ℝ) * x l = 1 := by
    rw [← hMoebiusInvFull]
    apply Finset.sum_subset hC_subset
    intro l hlP hlC
    rw [hx_zero l hlP hlC]
    simp
  have hdiag_restrict :
      (∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (x l) ^ 2) =
        ∑ l ∈ C, (S.selbergTerms l)⁻¹ * (x l) ^ 2 := by
    symm
    apply Finset.sum_subset hC_subset
    intro l hlP hlC
    rw [hx_zero l hlP hlC]
    simp
  have hTitu :
      (∑ l ∈ C, (μ l : ℝ) * x l) ^ 2 /
          ∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2 ≤
        ∑ l ∈ C,
          ((μ l : ℝ) * x l) ^ 2 /
            (S.selbergTerms l * (μ l : ℝ) ^ 2) := by
    apply sq_sum_div_le_sum_sq_div
    intro l hl
    have hlP : l ∈ S.prodPrimes.divisors := hC_subset hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes hlP
    have hpos := S.selbergTerms_pos (Nat.mem_divisors.mp hlP).1
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
    exact hpos
  have hDenom :
      (∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2) =
        truncatedSelbergDenominator S R := by
    change (∑ l ∈ C, S.selbergTerms l * (μ l : ℝ) ^ 2) =
      ∑ l ∈ C, S.selbergTerms l
    apply Finset.sum_congr rfl
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes (hC_subset hl)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one]
  have hRHS :
      (∑ l ∈ C, ((μ l : ℝ) * x l) ^ 2 /
          (S.selbergTerms l * (μ l : ℝ) ^ 2)) =
        ∑ l ∈ C, (S.selbergTerms l)⁻¹ * (x l) ^ 2 := by
    apply Finset.sum_congr rfl
    intro l hl
    have hsq := S.squarefree_of_mem_divisors_prodPrimes (hC_subset hl)
    have hμsq : (μ l : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [hμsq, mul_one, mul_pow, hμsq, one_mul, div_eq_inv_mul]
  rw [hMoebiusInv, hDenom] at hTitu
  simp only [one_pow] at hTitu
  rw [hRHS, one_div] at hTitu
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  change
    1 / truncatedSelbergDenominator S R ≤
      ∑ l ∈ S.prodPrimes.divisors, (S.selbergTerms l)⁻¹ * (x l) ^ 2
  rw [hdiag_restrict]
  simpa only [one_div] using hTitu

/-- The truncated Selberg optimizer minimizes the main sum among all normalized
weights supported on the same carrier. -/
theorem mainSum_truncatedSelbergOptimalLambda_le_mainSum
    (S : BoundingSieve) {R : ℕ} (hR : 1 ≤ R) (w : ℕ → ℝ)
    (hw_one : w 1 = 1)
    (hw_support : ∀ {d : ℕ}, w d ≠ 0 → d ∈ truncatedSelbergCarrier S R) :
    S.mainSum (BoundingSieve.lambdaSquared (truncatedSelbergOptimalLambda S R)) ≤
      S.mainSum (BoundingSieve.lambdaSquared w) := by
  rw [mainSum_truncatedSelbergOptimalLambda S hR]
  exact one_div_truncatedSelbergDenominator_le_mainSum S w hw_one hw_support

private theorem truncatedSelberg_packet_le_denominator
    {S : BoundingSieve} {R d : ℕ} (hd : d ∈ truncatedSelbergCarrier S R) :
    (∑ e ∈ truncatedSelbergCarrier S R,
      if d ∣ e then S.selbergTerms e else 0) * (S.nu d)⁻¹ ≤
      truncatedSelbergDenominator S R := by
  let C := truncatedSelbergCarrier S R
  let D := C.filter (d ∣ ·)
  let P := D ×ˢ d.divisors
  let f : ℕ × ℕ → ℕ := fun x => (x.1 / d) * x.2
  have hdP : d ∣ S.prodPrimes :=
    (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
  have hd0 : d ≠ 0 := Nat.ne_of_gt <|
    Nat.pos_of_dvd_of_pos hdP (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)
  have hdivsum : (∑ k ∈ d.divisors, S.selbergTerms k) =
      S.selbergTerms d * (S.nu d)⁻¹ := by
    calc
      (∑ k ∈ d.divisors, S.selbergTerms k) =
          ∑ k ∈ S.prodPrimes.divisors, if k ∣ d then S.selbergTerms k else 0 := by
            rw [← Finset.sum_filter,
              Nat.divisors_filter_dvd_of_dvd S.prodPrimes_ne_zero hdP]
      _ = S.selbergTerms d * (S.nu d)⁻¹ :=
        S.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP
  have hpacket : ∀ e ∈ D,
      (∑ k ∈ d.divisors, S.selbergTerms ((e / d) * k)) =
        S.selbergTerms e * (S.nu d)⁻¹ := by
    intro e he
    have heC : e ∈ C := (Finset.mem_filter.mp he).1
    have hde : d ∣ e := (Finset.mem_filter.mp he).2
    have heP : e ∣ S.prodPrimes :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp heC).1).1
    have hesq : Squarefree e :=
      S.squarefree_of_mem_divisors_prodPrimes (by
        simpa [C] using (Finset.mem_filter.mp heC).1)
    have hemul : d * (e / d) = e := Nat.mul_div_cancel' hde
    have hcop : d.Coprime (e / d) := by
      apply Nat.coprime_of_squarefree_mul
      rwa [hemul]
    calc
      (∑ k ∈ d.divisors, S.selbergTerms ((e / d) * k)) =
          S.selbergTerms (e / d) * ∑ k ∈ d.divisors, S.selbergTerms k := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            exact S.selbergTerms_isMultiplicative.map_mul_of_coprime
              (hcop.symm.of_dvd_right (Nat.mem_divisors.mp hk).1)
      _ = S.selbergTerms (e / d) *
          (S.selbergTerms d * (S.nu d)⁻¹) := by rw [hdivsum]
      _ = S.selbergTerms e * (S.nu d)⁻¹ := by
        rw [← mul_assoc,
          ← S.selbergTerms_isMultiplicative.map_mul_of_coprime hcop.symm]
        rw [mul_comm (e / d) d, hemul]
  have hinj : Set.InjOn f P := by
    intro x hx y hy hxy
    change (x.1 / d) * x.2 = (y.1 / d) * y.2 at hxy
    have hxmem := Finset.mem_product.mp hx
    have hymem := Finset.mem_product.mp hy
    have hxde : d ∣ x.1 := (Finset.mem_filter.mp hxmem.1).2
    have hyde : d ∣ y.1 := (Finset.mem_filter.mp hymem.1).2
    have hxcop : (x.1 / d).Coprime d :=
      (Nat.coprime_of_squarefree_mul (by
        rw [Nat.mul_div_cancel' hxde]
        exact S.squarefree_of_mem_divisors_prodPrimes
          (Finset.mem_filter.mp (Finset.mem_filter.mp hxmem.1).1).1)).symm
    have hycop : (y.1 / d).Coprime d :=
      (Nat.coprime_of_squarefree_mul (by
        rw [Nat.mul_div_cancel' hyde]
        exact S.squarefree_of_mem_divisors_prodPrimes
          (Finset.mem_filter.mp (Finset.mem_filter.mp hymem.1).1).1)).symm
    have hk : x.2 = y.2 := by
      have hg := congrArg (fun n => Nat.gcd n d) hxy
      rw [Nat.gcd_mul_of_coprime_of_dvd hxcop (Nat.mem_divisors.mp hxmem.2).1,
        Nat.gcd_mul_of_coprime_of_dvd hycop (Nat.mem_divisors.mp hymem.2).1] at hg
      exact hg
    have hkpos : 0 < x.2 := Nat.pos_of_dvd_of_pos
      (Nat.mem_divisors.mp hxmem.2).1 (Nat.pos_of_ne_zero hd0)
    have hquot : x.1 / d = y.1 / d := by
      rw [hk] at hxy
      exact Nat.mul_right_cancel (hk ▸ hkpos) hxy
    apply Prod.ext
    · calc
        x.1 = d * (x.1 / d) := (Nat.mul_div_cancel' hxde).symm
        _ = d * (y.1 / d) := by rw [hquot]
        _ = y.1 := Nat.mul_div_cancel' hyde
    · exact hk
  have himage : P.image f ⊆ C := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨x, hx, rfl⟩ := hn
    have hxmem := Finset.mem_product.mp hx
    have hxC : x.1 ∈ C := (Finset.mem_filter.mp hxmem.1).1
    have hxde : d ∣ x.1 := (Finset.mem_filter.mp hxmem.1).2
    have hxeP : x.1 ∣ S.prodPrimes :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hxC).1).1
    have hfxe : f x ∣ x.1 := by
      rw [show x.1 = (x.1 / d) * d by exact (Nat.div_mul_cancel hxde).symm]
      exact Nat.mul_dvd_mul_left (x.1 / d) (Nat.mem_divisors.mp hxmem.2).1
    apply Finset.mem_filter.mpr
    refine ⟨Nat.mem_divisors.mpr ⟨hfxe.trans hxeP, S.prodPrimes_ne_zero⟩, ?_⟩
    exact (Nat.le_of_dvd (Nat.pos_of_dvd_of_pos hxeP
      (Nat.pos_of_ne_zero S.prodPrimes_ne_zero)) hfxe).trans (Finset.mem_filter.mp hxC).2
  have hnonneg : ∀ n ∈ C, 0 ≤ S.selbergTerms n := by
    intro n hn
    exact (S.selbergTerms_pos
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1).1).le
  change (∑ e ∈ C, if d ∣ e then S.selbergTerms e else 0) *
    (S.nu d)⁻¹ ≤ _
  rw [← Finset.sum_filter]
  change (∑ e ∈ D, S.selbergTerms e) * (S.nu d)⁻¹ ≤ _
  calc
    (∑ e ∈ D, S.selbergTerms e) * (S.nu d)⁻¹ =
        ∑ e ∈ D, ∑ k ∈ d.divisors, S.selbergTerms ((e / d) * k) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      exact (hpacket e he).symm
    _ = ∑ x ∈ P, S.selbergTerms (f x) := by
      exact (Finset.sum_product D d.divisors (fun x => S.selbergTerms (f x))).symm
    _ = ∑ n ∈ P.image f, S.selbergTerms n := by
      exact (Finset.sum_image hinj).symm
    _ ≤ ∑ n ∈ C, S.selbergTerms n :=
      Finset.sum_le_sum_of_subset_of_nonneg himage (fun n hn _ => hnonneg n hn)
    _ = truncatedSelbergDenominator S R := by rfl

/-- Every cutoff-supported finite optimal coefficient has the Selberg bound. -/
theorem abs_truncatedSelbergOptimalLambda_le_one
    (S : BoundingSieve) {R d : ℕ} (hR : 1 ≤ R) :
    |truncatedSelbergOptimalLambda S R d| ≤ 1 := by
  by_cases hd : d ∈ truncatedSelbergCarrier S R
  · let C := truncatedSelbergCarrier S R
    let G := truncatedSelbergDenominator S R
    have hG : 0 < G := truncatedSelbergDenominator_pos S hR
    have hdP : d ∣ S.prodPrimes :=
      (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
    have hnu : 0 < S.nu d := S.nu_pos_of_dvd_prodPrimes hdP
    have hsumabs :
        (∑ e ∈ C, |if d ∣ e then
          (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0|) =
          (∑ e ∈ C, if d ∣ e then S.selbergTerms e else 0) / G := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hde : d ∣ e
      · have hesq : Squarefree e :=
          S.squarefree_of_mem_divisors_prodPrimes (Finset.mem_filter.mp he).1
        have hqsq : Squarefree (e / d) :=
          hesq.squarefree_of_dvd (Nat.div_dvd_of_dvd hde)
        have hmue : |(μ e : ℝ)| = 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hesq
        have hmuq : |(μ (e / d) : ℝ)| = 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hqsq
        have hterm : 0 < S.selbergTerms e := S.selbergTerms_pos
          ((Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1)
        rw [if_pos hde, truncatedSelbergOptimalX, if_pos he, abs_mul, abs_div,
          abs_mul, hmuq, hmue, abs_of_pos hterm, abs_of_pos hG]
        rw [if_pos hde]
        ring
      · simp [hde]
    rw [truncatedSelbergOptimalLambda, if_pos hd, abs_div, abs_of_pos hnu]
    calc
      |∑ e ∈ C, if d ∣ e then
          (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0| / S.nu d ≤
          (∑ e ∈ C, |if d ∣ e then
            (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0|) / S.nu d :=
        div_le_div_of_nonneg_right
          (Finset.abs_sum_le_sum_abs (fun e => if d ∣ e then
            (μ (e / d) : ℝ) * truncatedSelbergOptimalX S R e else 0) C) hnu.le
      _ = ((∑ e ∈ C, if d ∣ e then S.selbergTerms e else 0) *
          (S.nu d)⁻¹) / G := by
        rw [hsumabs]
        field_simp [hG.ne', hnu.ne']
      _ ≤ G / G := div_le_div_of_nonneg_right
        (truncatedSelberg_packet_le_denominator hd) hG.le
      _ = 1 := div_self hG.ne'
  · rw [truncatedSelbergOptimalLambda_eq_zero_of_not_mem hd]
    simp

/-- The sole analytic statement left by the finite minimization: uniformly for
large `N`, the truncated weighted divisor sum dominates the sharp reciprocal
scale.  This is a lower bound on `G`, not the desired coefficient conclusion. -/
def LiuSelbergDenominatorLowerBound (delta epsilon : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, 2 ≤ N → Even N →
    1 ≤ paperQSourceCutoff N epsilon →
      Real.log N /
          ((8 + delta) *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N) ≤
        liuSelbergDenominator N epsilon

theorem one_div_liuSelbergDenominator_le
    {delta epsilon : ℝ} {N : ℕ}
    (hdelta : 0 < 8 + delta) (hN : 2 ≤ N) (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon)
    (hden :
      Real.log N /
          ((8 + delta) *
            MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N) ≤
        liuSelbergDenominator N epsilon) :
    1 / liuSelbergDenominator N epsilon ≤
      (8 + delta) *
        MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N / Real.log N := by
  have hG : 0 < liuSelbergDenominator N epsilon :=
    liuSelbergDenominator_pos hNeven hR
  have hlog : 0 < Real.log N := Real.log_pos <| by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hN)
  have hseries :
      0 < MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N :=
    MathlibNt.SieveTheory.SingularSeries.liuSingularSeries_pos N
  have hscale :
      0 < (8 + delta) *
        MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N :=
    mul_pos hdelta hseries
  apply (le_div_iff₀ hlog).2
  have hquot :
      Real.log N / liuSelbergDenominator N epsilon ≤
        (8 + delta) *
          MathlibNt.SieveTheory.SingularSeries.liuSingularSeries N := by
    apply (div_le_iff₀ hG).2
    have := (div_le_iff₀ hscale).mp hden
    simpa [mul_comm] using this
  simpa [div_eq_mul_inv, mul_comm] using hquot

private noncomputable def liuSelbergOptimalWeights
    (N : ℕ) (epsilon : ℝ) (hNeven : Even N)
    (hR : 1 ≤ paperQSourceCutoff N epsilon) :
    MathlibNt.SieveTheory.SelbergUpperBound.SelbergWeights N epsilon where
  lambda := liuSelbergOptimalLambda N epsilon
  lambda_one := liuSelbergOptimalLambda_one hNeven hR
  lambda_support := by
    intro d hd
    by_contra hne
    have hs := liuSelbergOptimalLambda_support hne
    rcases hd with hlarge | hndvd
    · exact (not_lt_of_ge (by
        simpa [paperQSourceCutoff] using hs.2)) hlarge
    · apply hndvd
      rw [LegacySelberg.selbergQ_eq_liuPaperQModulus]
      exact hs.1
  lambda_bounded := fun d => abs_liuSelbergOptimalLambda_le_one hNeven hR

theorem LegacySelberg.LiuOptimizedSelbergCoefficientEstimate.of_denominatorLowerBound
    {delta epsilon : ℝ} (hdelta : 0 < 8 + delta)
    (hden : LiuSelbergDenominatorLowerBound delta epsilon) :
    LegacySelberg.LiuOptimizedSelbergCoefficientEstimate delta epsilon := by
  filter_upwards [hden, eventually_ge_atTop (2 : ℕ)] with N hdenN hN
  intro hNeven hR
  let SW := liuSelbergOptimalWeights N epsilon hNeven hR
  refine ⟨SW, ?_⟩
  unfold LiuSelbergCoefficientFactorBound
  change liuSelbergCoefficientFactor N epsilon
      (liuSelbergOptimalLambda N epsilon) ≤ _
  rw [liuSelbergCoefficientFactor_optimalLambda hNeven hR]
  exact one_div_liuSelbergDenominator_le hdelta hN hNeven hR
    (hdenN hN hNeven hR)

theorem LegacySelberg.LiuOptimizedSelbergCoefficientInput.of_denominatorLowerBound
    (hden : ∀ delta > 0, ∃ epsilon0 > 0,
      ∀ epsilon, 0 < epsilon → epsilon ≤ epsilon0 →
        LiuSelbergDenominatorLowerBound delta epsilon) :
    LegacySelberg.LiuOptimizedSelbergCoefficientInput := by
  intro delta hdelta
  obtain ⟨epsilon0, hepsilon0, hden⟩ := hden delta hdelta
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro epsilon hepsilon hepsilon_le
  exact LegacySelberg.LiuOptimizedSelbergCoefficientEstimate.of_denominatorLowerBound
    (by linarith) (hden epsilon hepsilon hepsilon_le)

end MathlibNt.SieveTheory.LiuWeight
