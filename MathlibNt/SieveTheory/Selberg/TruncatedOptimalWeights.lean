import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Tactic

/-! # Finite Selberg optimization with an arbitrary cutoff

The reverse-divisor Möbius construction and its exact quadratic minimum are
proved once. The full-divisor and Liu-source optimizers specialize this result.
The finite algebra is independent of Wang 1962's analytic hypothesis (R*).
-/

open scoped BigOperators ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Finset

namespace AnalyticNumberTheory.Sieve

/-- Standard Moebius sum: `Σ_{d|n} μ(d) = [n=1]`. -/
lemma sum_moebius_eq_one {n : ℕ} :
    (∑ d ∈ n.divisors, (μ d : ℝ)) = if n = 1 then (1 : ℝ) else 0 := by
  simpa only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.intCoe_apply,
    ArithmeticFunction.one_apply] using
    congrArg (fun f : ArithmeticFunction ℝ => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℝ))


/-- For nonzero `e` with `d|e` and `l|e`,
`l|d ↔ e/d | e/l`. This quotient form converts divisibility
by `l` into divisibility of `e/l` for reindexing a restricted
Moebius sum. -/
lemma dvd_iff_div_dvd {e l d : ℕ} (he : e ≠ 0) (hd : d ∣ e) (hl : l ∣ e) :
    l ∣ d ↔ e / d ∣ e / l := by
  constructor
  · exact Nat.div_dvd_div_left hd
  · intro hdl
    have h := Nat.div_dvd_div_left (Nat.div_dvd_of_dvd hl) hdl
    simpa only [Nat.div_div_self hl he, Nat.div_div_self hd he] using h

/-- Restricted Moebius sum: for `l|e` and `e ≠ 0`,
`Σ_{d|e, l|d} μ(e/d) = [e=l]`. -/
lemma sum_moebius_quotient_of_dvd {e l : ℕ} (he : e ≠ 0) (hle : l ∣ e) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  -- Reindex d ↦ e/d: the condition [l|d] becomes [e/d | e/l].
  have hbij :
      (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
        ∑ d ∈ e.divisors, if d ∣ e / l then (μ d : ℝ) else 0 := by
    calc
      (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0)
          = ∑ d ∈ e.divisors, if e / d ∣ e / l then (μ (e / d) : ℝ) else 0 := by
              refine Finset.sum_congr rfl fun d hd => ?_
              simp only [dvd_iff_div_dvd he (Nat.mem_divisors.mp hd).1 hle]
      _ = ∑ d ∈ e.divisors, if d ∣ e / l then (μ d : ℝ) else 0 :=
        Nat.sum_div_divisors e (fun d => if d ∣ e / l then (μ d : ℝ) else 0)
  rw [hbij]
  -- The sum is now Σ_{d|e, d|e/l} μ(d); since e/l divides e, its index set is (e/l).divisors.
  have hfilter : e.divisors.filter (fun d => d ∣ e / l) = (e / l).divisors :=
    Nat.divisors_filter_dvd_of_dvd he (Nat.div_dvd_of_dvd hle)
  rw [← Finset.sum_filter]
  rw [hfilter]
  rw [sum_moebius_eq_one]
  by_cases hel : e = l
  · have hl0 : 0 < l := Nat.pos_of_dvd_of_pos hle (Nat.pos_of_ne_zero he)
    simp [hel]
    exact Nat.div_self hl0
  · have hdiv_ne : e / l ≠ 1 := by
      intro h
      apply hel
      calc
        e = l * (e / l) := by rw [mul_comm, Nat.div_mul_cancel hle]
        _ = l * 1 := by rw [h]
        _ = l := by rw [mul_one]
    simp [hdiv_ne, hel]

end AnalyticNumberTheory.Sieve

namespace MathlibNt.SieveTheory.LiuWeight

private lemma sum_moebius_quotient_of_dvd {e l : ℕ}
    (he : e ≠ 0) (hle : l ∣ e) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  exact AnalyticNumberTheory.Sieve.sum_moebius_quotient_of_dvd he hle

/-- Reverse-divisor Möbius cancellation, including the case `l ∤ e`. -/
private lemma sum_moebius_quotient {e l : ℕ} (he : e ≠ 0) :
    (∑ d ∈ e.divisors, if l ∣ d then (μ (e / d) : ℝ) else 0) =
      if e = l then (1 : ℝ) else 0 := by
  by_cases hle : l ∣ e
  · exact sum_moebius_quotient_of_dvd he hle
  · have hel : e ≠ l := fun h => hle (h ▸ dvd_refl l)
    rw [if_neg hel]
    apply Finset.sum_eq_zero
    intro d hd
    exact if_neg (fun hld => hle (hld.trans (Nat.mem_divisors.mp hd).1))

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

theorem truncatedSelbergOptimalX_eq_sum_nu_mul_lambda
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
        exact sum_moebius_quotient he0
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

theorem sum_nu_mul_truncatedSelbergOptimalLambda_eq_optimalX
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

end MathlibNt.SieveTheory.LiuWeight
