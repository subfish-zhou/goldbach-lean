import MathlibNt.SieveTheory.Switching.LogarithmicMesh

/-!
# Rosser boundary densities and dyadic tails

Dyadic log-ratio cells control far alternating pairs. Mesh corrections, atomic
bounds, and factorial density estimates majorize finite Rosser boundary chains.

All declarations retain the `MathlibNt.SieveTheory.SwitchingPrinciple` namespace.
-/

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

set_option maxHeartbeats 6000000

namespace MathlibNt.SieveTheory.SwitchingPrinciple

open Real Finset
open MeasureTheory intervalIntegral

open scoped Classical
open scoped Asymptotics

namespace Internal
end Internal

open Internal

/-- The dyadic cell containing a real number at least one.  It is used with
`x = log p / log q`, so the cells rescale with the current terminal prime
instead of with the global sieve cutoff. -/
noncomputable def upperRosserLogRatioDyadicCell (x : ℝ) : ℕ :=
  if hx : 1 ≤ x then
    Classical.choose
      (exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2))
  else 0

theorem upperRosserLogRatioDyadicCell_spec {x : ℝ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ upperRosserLogRatioDyadicCell x ≤ x ∧
      x < (2 : ℝ) ^ (upperRosserLogRatioDyadicCell x + 1) := by
  rw [upperRosserLogRatioDyadicCell, dif_pos hx]
  exact Classical.choose_spec
    (exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 2))

/-- A dyadic logarithmic-ratio cell has uniformly bounded normalized density
mass once the local-product correction is small at the cell's base prime. -/
theorem sum_nu_div_one_sub_le_logRatio_dyadicCell
    {S : BoundingSieve} {K η : ℝ} {q n : ℕ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hK : 0 ≤ K) (hq : q.Prime)
    (herror : K / Real.log q ≤ η)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hqT : ∀ p ∈ T, q < p) :
    ∑ p ∈ T.filter (fun p : ℕ =>
        upperRosserLogRatioDyadicCell
          (Real.log (p : ℝ) / Real.log q) = n),
      S.nu p / (1 - S.nu p) ≤ 1 + 2 * η := by
  let U : Finset ℕ := T.filter (fun p : ℕ =>
    upperRosserLogRatioDyadicCell
      (Real.log (p : ℝ) / Real.log q) = n)
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hpowOne : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
  have hpowStep :
      (2 : ℝ) ^ n ≤ (2 : ℝ) ^ (n + 1) := by
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hqpow :
      (2 : ℝ) ≤ (q : ℝ) ^ ((2 : ℝ) ^ n) := by
    calc
      (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
      _ = (q : ℝ) ^ (1 : ℝ) := by simp
      _ ≤ (q : ℝ) ^ ((2 : ℝ) ^ n) :=
        Real.rpow_le_rpow_of_exponent_le hqR.le hpowOne
  have hU : U ⊆ S.prodPrimes.primeFactors := by
    intro p hp
    exact hT (Finset.mem_filter.mp hp).1
  have hinterval : ∀ (p : ℕ), p ∈ U →
      (q : ℝ) ^ ((2 : ℝ) ^ n) ≤ (p : ℝ) ∧
        (p : ℝ) < (q : ℝ) ^ ((2 : ℝ) ^ (n + 1)) := by
    intro p hp
    have hpT := (Finset.mem_filter.mp hp).1
    have hpCell := (Finset.mem_filter.mp hp).2
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (hT hpT)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hratioOne : (1 : ℝ) ≤ Real.log p / Real.log q := by
      apply (le_div_iff₀ hlogq).2
      simpa using Real.strictMonoOn_log.monotoneOn hqpos hpR
        (by exact_mod_cast (hqT p hpT).le)
    have hcell :=
      upperRosserLogRatioDyadicCell_spec hratioOne
    rw [hpCell] at hcell
    have hrpow :
        (q : ℝ) ^ (Real.log p / Real.log q) = (p : ℝ) := by
      simpa [Real.logb] using
        (Real.rpow_logb hqpos (by exact_mod_cast hq.ne_one) hpR)
    constructor
    · calc
        (q : ℝ) ^ ((2 : ℝ) ^ n) ≤
            (q : ℝ) ^ (Real.log p / Real.log q) :=
          Real.rpow_le_rpow_of_exponent_le hqR.le hcell.1
        _ = (p : ℝ) := hrpow
    · calc
        (p : ℝ) = (q : ℝ) ^ (Real.log p / Real.log q) := hrpow.symm
        _ < (q : ℝ) ^ ((2 : ℝ) ^ (n + 1)) :=
          Real.rpow_lt_rpow_of_exponent_lt hqR hcell.2
  have hraw :
      ∑ p ∈ U, S.nu p / (1 - S.nu p) ≤
        ((2 : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ n) *
            (1 + K / (((2 : ℝ) ^ n) * Real.log q)) - 1 :=
    sum_nu_div_one_sub_le_of_rpow_interval hlocal hqR (by positivity) hpowStep
      hqpow hU hinterval
  have hcorrection :
      K / (((2 : ℝ) ^ n) * Real.log q) ≤ η := by
    have hmono :=
      localProduct_error_le_of_log_coordinate_lower hK hqR
        (c := (1 : ℝ)) (a := (2 : ℝ) ^ n) (by norm_num) hpowOne
    have herror' : K / ((1 : ℝ) * Real.log q) ≤ η := by
      simpa using herror
    exact hmono.trans herror'
  have hratio :
      ((2 : ℝ) ^ (n + 1)) / ((2 : ℝ) ^ n) = 2 := by
    rw [pow_succ]
    field_simp
  change ∑ p ∈ U, S.nu p / (1 - S.nu p) ≤ 1 + 2 * η
  rw [hratio] at hraw
  linarith

/-- A scale-adaptive inverse-log moment bound.  Unlike a fixed logarithmic
screen, the dyadic cells are based at `q`; hence the estimate remains uniform
when `log q / log z` tends to zero. -/
theorem sum_nu_div_one_sub_mul_inv_logRatio_le_geometric_tail
    {S : BoundingSieve} {K η : ℝ} {q m : ℕ} {T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hq : q.Prime)
    (herror : K / Real.log q ≤ η)
    (hT : T ⊆ S.prodPrimes.primeFactors)
    (hqT : ∀ p ∈ T, q < p)
    (hfar : ∀ p ∈ T,
      (2 : ℝ) ^ m ≤ Real.log p / Real.log q) :
    ∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
        (Real.log p / Real.log q)⁻¹ ≤
      2 * (1 + 2 * η) * (1 / 2 : ℝ) ^ m := by
  let rawCell : ℕ → ℕ := fun p =>
    upperRosserLogRatioDyadicCell
      (Real.log p / Real.log q)
  let cell : ℕ → ℕ := fun p => rawCell p - m
  let U : Finset ℕ := T.image cell
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hcell_ge : ∀ p ∈ T, m ≤ rawCell p := by
    intro p hp
    have hpPrime : p.Prime :=
      Nat.prime_of_mem_primeFactors (hT hp)
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hratioOne : (1 : ℝ) ≤ Real.log p / Real.log q := by
      apply (le_div_iff₀ hlogq).2
      simpa using Real.strictMonoOn_log.monotoneOn hqpos hpR
        (by exact_mod_cast (hqT p hp).le)
    have hspec :=
      upperRosserLogRatioDyadicCell_spec hratioOne
    by_contra hnot
    have hsucc : rawCell p + 1 ≤ m := by omega
    have hpow :
        (2 : ℝ) ^ (rawCell p + 1) ≤ (2 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) hsucc
    exact (not_lt_of_ge (hfar p hp))
      (hspec.2.trans_le hpow)
  have hdecomp :
      (∑ p ∈ T, (S.nu p / (1 - S.nu p)) *
          (Real.log p / Real.log q)⁻¹) =
        ∑ n ∈ U, ∑ p ∈ T.filter (fun p => cell p = n),
          (S.nu p / (1 - S.nu p)) *
            (Real.log p / Real.log q)⁻¹ := by
    have hfiberwise := Finset.sum_fiberwise_eq_sum_filter T U cell
      (fun p => (S.nu p / (1 - S.nu p)) *
        (Real.log p / Real.log q)⁻¹)
    have hfilter :
        T.filter (fun p => cell p ∈ U) = T := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    rw [hfilter] at hfiberwise
    exact hfiberwise.symm
  have hfiber : ∀ n ∈ U,
      (∑ p ∈ T.filter (fun p => cell p = n),
          (S.nu p / (1 - S.nu p)) *
            (Real.log p / Real.log q)⁻¹) ≤
        ((1 + 2 * η) * (1 / 2 : ℝ) ^ m) *
          (1 / 2 : ℝ) ^ n := by
    intro n hn
    let V : Finset ℕ := T.filter (fun p => cell p = n)
    have hV : V ⊆ S.prodPrimes.primeFactors := by
      intro p hp
      exact hT (Finset.mem_filter.mp hp).1
    have hqV : ∀ p ∈ V, q < p := by
      intro p hp
      exact hqT p (Finset.mem_filter.mp hp).1
    have hraw : ∀ p ∈ V, rawCell p = m + n := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hge := hcell_ge p hp'.1
      dsimp [cell] at hp'
      omega
    have hmass :
        ∑ p ∈ V, S.nu p / (1 - S.nu p) ≤ 1 + 2 * η := by
      have hcellMass :=
        sum_nu_div_one_sub_le_logRatio_dyadicCell
          hlocal hK hq herror hV hqV (n := m + n)
      rw [Finset.filter_eq_self.mpr] at hcellMass
      · exact hcellMass
      · intro p hp
        simpa [rawCell] using hraw p hp
    have hinv : ∀ p ∈ V,
        (Real.log p / Real.log q)⁻¹ ≤
          (1 / 2 : ℝ) ^ (m + n) := by
      intro p hp
      have hpT := (Finset.mem_filter.mp hp).1
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors (hT hpT)
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hratioPos : 0 < Real.log p / Real.log q :=
        div_pos (Real.log_pos (by exact_mod_cast hpPrime.one_lt)) hlogq
      have hratioOne : (1 : ℝ) ≤ Real.log p / Real.log q :=
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans (hfar p hpT)
      have hspec :=
        upperRosserLogRatioDyadicCell_spec hratioOne
      rw [show upperRosserLogRatioDyadicCell
          (Real.log p / Real.log q) = rawCell p by rfl,
        hraw p hp] at hspec
      calc
        (Real.log p / Real.log q)⁻¹ ≤
            ((2 : ℝ) ^ (m + n))⁻¹ :=
          (inv_le_inv₀ hratioPos (by positivity)).2 hspec.1
        _ = (1 / 2 : ℝ) ^ (m + n) := by norm_num [div_pow]
    change (∑ p ∈ V, (S.nu p / (1 - S.nu p)) *
        (Real.log p / Real.log q)⁻¹) ≤ _
    calc
      (∑ p ∈ V, (S.nu p / (1 - S.nu p)) *
          (Real.log p / Real.log q)⁻¹) ≤
          ∑ p ∈ V, (S.nu p / (1 - S.nu p)) *
            (1 / 2 : ℝ) ^ (m + n) := by
        apply Finset.sum_le_sum
        intro p hp
        exact mul_le_mul_of_nonneg_left (hinv p hp)
          (nu_div_one_sub_nonneg_of_mem (hV hp))
      _ = (1 / 2 : ℝ) ^ (m + n) *
          ∑ p ∈ V, S.nu p / (1 - S.nu p) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      _ ≤ (1 / 2 : ℝ) ^ (m + n) * (1 + 2 * η) :=
        mul_le_mul_of_nonneg_left hmass (by positivity)
      _ = ((1 + 2 * η) * (1 / 2 : ℝ) ^ m) *
          (1 / 2 : ℝ) ^ n := by
        rw [pow_add]
        ring
  have hsummable :
      Summable (fun n : ℕ =>
        ((1 + 2 * η) * (1 / 2 : ℝ) ^ m) *
          (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left _
  rw [hdecomp]
  calc
    (∑ n ∈ U, ∑ p ∈ T.filter (fun p => cell p = n),
        (S.nu p / (1 - S.nu p)) *
          (Real.log p / Real.log q)⁻¹) ≤
        ∑ n ∈ U, ((1 + 2 * η) * (1 / 2 : ℝ) ^ m) *
          (1 / 2 : ℝ) ^ n :=
      Finset.sum_le_sum hfiber
    _ ≤ ∑' n : ℕ, ((1 + 2 * η) * (1 / 2 : ℝ) ^ m) *
        (1 / 2 : ℝ) ^ n :=
      hsummable.sum_le_tsum U (fun n hn => by positivity)
    _ = 2 * (1 + 2 * η) * (1 / 2 : ℝ) ^ m := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)]
      norm_num
      ring

/-- The part of a discrete reverse Rosser pair whose larger logarithmic ratio
lies beyond the `m`-th dyadic scale has a uniform quadratic tail.  The proof
uses the alternating-prefix face `2x < y + r` to force `x < r`; the remaining
inverse-log moment is controlled by scale-adaptive cells based at `q`, not by a
fixed lower bound for `log q / log z`. -/
theorem upperRosserAlternatingPairDiscrete_quadratic_far_le
    {S : BoundingSieve} {K η r : ℝ} {q m : ℕ}
    {P T : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hr : 3 ≤ r) (hq : q.Prime)
    (herror : K / Real.log q ≤ η)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) (hT : T ⊆ P)
    (hfar : ∀ p ∈ T,
      (2 : ℝ) ^ m ≤ Real.log p / Real.log q) :
    ∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2 ≤
      18 * (1 + η) * (1 + 2 * η) *
        (1 / 2 : ℝ) ^ m * r ^ 2 := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have houter : ∀ p₀ ∈ T,
      (∑ p₁ ∈ P.filter (fun p₁ =>
          p₁ < p₀ ∧
            2 * (Real.log p₀ / Real.log q) <
              Real.log p₁ / Real.log q + r),
        (S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁)) *
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q)) ^ 2) ≤
        (9 * (1 + η) * r ^ 2) *
          ((S.nu p₀ / (1 - S.nu p₀)) *
            (Real.log p₀ / Real.log q)⁻¹) := by
    intro p₀ hp₀
    let x : ℝ := Real.log p₀ / Real.log q
    let V : Finset ℕ := P.filter (fun p₁ =>
      p₁ < p₀ ∧
        2 * (Real.log p₀ / Real.log q) <
          Real.log p₁ / Real.log q + r)
    have hp₀P : p₀ ∈ P := hT hp₀
    have hp₀Prime : p₀.Prime :=
      Nat.prime_of_mem_primeFactors (hP hp₀P)
    have hp₀pos : (0 : ℝ) < p₀ := by exact_mod_cast hp₀Prime.pos
    have hxpos : 0 < x := by
      exact div_pos (Real.log_pos (by exact_mod_cast hp₀Prime.one_lt)) hlogq
    have hxone : (1 : ℝ) ≤ x := by
      apply (le_div_iff₀ hlogq).2
      simpa [x] using Real.strictMonoOn_log.monotoneOn hqpos hp₀pos
        (by exact_mod_cast (hqP p₀ hp₀P).le)
    have hV : V ⊆ S.prodPrimes.primeFactors := by
      intro p hp
      exact hP (Finset.mem_filter.mp hp).1
    have hinterval : ∀ (p : ℕ), p ∈ V →
        (q : ℝ) ^ (1 : ℝ) ≤ (p : ℝ) ∧
          (p : ℝ) < (q : ℝ) ^ x := by
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpPrime : p.Prime :=
        Nat.prime_of_mem_primeFactors (hP hp'.1)
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hp₀rpow : (q : ℝ) ^ x = (p₀ : ℝ) := by
        dsimp [x]
        simpa [Real.logb] using
          (Real.rpow_logb hqpos (by exact_mod_cast hq.ne_one) hp₀pos)
      constructor
      · simpa using (show (q : ℝ) ≤ p by
          exact_mod_cast (hqP p hp'.1).le)
      · rw [hp₀rpow]
        exact_mod_cast hp'.2.1
    have hmassRaw :
        ∑ p ∈ V, S.nu p / (1 - S.nu p) ≤
          x * (1 + K / Real.log q) - 1 := by
      have hbound :=
        sum_nu_div_one_sub_le_of_rpow_interval hlocal hqR
          (by norm_num : (0 : ℝ) < 1) hxone
          (by simpa using hq.two_le) hV hinterval
      simpa [x] using hbound
    have hmass :
        ∑ p ∈ V, S.nu p / (1 - S.nu p) ≤ x * (1 + η) := by
      have hmul := mul_le_mul_of_nonneg_left herror hxpos.le
      linarith
    have hkernel : ∀ p₁ ∈ V,
        ((r + Real.log p₁ / Real.log q + x) / x) ^ 2 ≤
          9 * r ^ 2 * (x⁻¹) ^ 2 := by
      intro p₁ hp₁
      have hp₁' := Finset.mem_filter.mp hp₁
      have hp₁Prime : p₁.Prime :=
        Nat.prime_of_mem_primeFactors (hP hp₁'.1)
      have hp₁pos : (0 : ℝ) < p₁ := by exact_mod_cast hp₁Prime.pos
      let y : ℝ := Real.log p₁ / Real.log q
      have hypos : 0 < y :=
        div_pos (Real.log_pos (by exact_mod_cast hp₁Prime.one_lt)) hlogq
      have hyx : y < x := by
        apply (div_lt_div_iff_of_pos_right hlogq).2
        exact (Real.strictMonoOn_log.lt_iff_lt hp₁pos hp₀pos).2
          (by exact_mod_cast hp₁'.2.1)
      have hface : 2 * x < y + r := by
        simpa [x, y] using hp₁'.2.2
      have hxr : x < r := by linarith
      have hnum : r + y + x < 3 * r := by linarith
      have hquotNonneg : 0 ≤ (r + y + x) / x :=
        div_nonneg (by linarith) hxpos.le
      have hquot :
          (r + y + x) / x ≤ 3 * r * x⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hnum.le (inv_nonneg.mpr hxpos.le)
      calc
        ((r + Real.log p₁ / Real.log q + x) / x) ^ 2 =
            ((r + y + x) / x) ^ 2 := by rfl
        _ ≤ (3 * r * x⁻¹) ^ 2 :=
          pow_le_pow_left₀ hquotNonneg hquot 2
        _ = 9 * r ^ 2 * (x⁻¹) ^ 2 := by ring
    have hw₀ : 0 ≤ S.nu p₀ / (1 - S.nu p₀) :=
      nu_div_one_sub_nonneg_of_mem (hP hp₀P)
    change (∑ p₁ ∈ V,
        (S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁)) *
            ((r + Real.log p₁ / Real.log q + x) / x) ^ 2) ≤ _
    calc
      (∑ p₁ ∈ V,
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q + x) / x) ^ 2) ≤
          ∑ p₁ ∈ V,
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                (9 * r ^ 2 * (x⁻¹) ^ 2) := by
        apply Finset.sum_le_sum
        intro p₁ hp₁
        exact mul_le_mul_of_nonneg_left (hkernel p₁ hp₁)
          (mul_nonneg hw₀ (nu_div_one_sub_nonneg_of_mem (hV hp₁)))
      _ = ((S.nu p₀ / (1 - S.nu p₀)) *
          (9 * r ^ 2 * (x⁻¹) ^ 2)) *
            ∑ p₁ ∈ V, S.nu p₁ / (1 - S.nu p₁) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p₁ hp₁
        ring
      _ ≤ ((S.nu p₀ / (1 - S.nu p₀)) *
          (9 * r ^ 2 * (x⁻¹) ^ 2)) * (x * (1 + η)) := by
        apply mul_le_mul_of_nonneg_left hmass
        positivity
      _ = (9 * (1 + η) * r ^ 2) *
          ((S.nu p₀ / (1 - S.nu p₀)) * x⁻¹) := by
        field_simp [hxpos.ne']
  have hmoment :=
    sum_nu_div_one_sub_mul_inv_logRatio_le_geometric_tail
      hlocal hK hη hq herror (hT.trans hP)
        (fun p hp => hqP p (hT hp)) hfar
  calc
    (∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
        ∑ p₀ ∈ T, (9 * (1 + η) * r ^ 2) *
          ((S.nu p₀ / (1 - S.nu p₀)) *
            (Real.log p₀ / Real.log q)⁻¹) :=
      Finset.sum_le_sum houter
    _ = (9 * (1 + η) * r ^ 2) *
        ∑ p₀ ∈ T, (S.nu p₀ / (1 - S.nu p₀)) *
          (Real.log p₀ / Real.log q)⁻¹ := by
      rw [Finset.mul_sum]
    _ ≤ (9 * (1 + η) * r ^ 2) *
        (2 * (1 + 2 * η) * (1 / 2 : ℝ) ^ m) :=
      mul_le_mul_of_nonneg_left hmoment (by positivity)
    _ = 18 * (1 + η) * (1 + 2 * η) *
        (1 / 2 : ℝ) ^ m * r ^ 2 := by ring

/-- Uniform tightness of one discrete reverse Rosser pair.  Once the terminal
prime is above an absolute cutoff, the contribution of larger ratios outside a
fixed dyadic window is arbitrarily small relative to the quadratic envelope,
uniformly in the sieve, the terminal coordinate, and the state `r ≥ 3`. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_far_lt
    (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ Q : ℝ, 2 ≤ Q ∧ ∃ m : ℕ,
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P T : Finset ℕ),
        Q ≤ (q : ℝ) → HasDimensionOneLocalProductBound S K →
        3 ≤ r → q.Prime →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) → T ⊆ P →
        (∀ p ∈ T,
          (2 : ℝ) ^ m ≤ Real.log p / Real.log q) →
        (∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) <
          ρ * r ^ 2 := by
  obtain ⟨Q, hQ2, hQ⟩ :=
    exists_localProduct_error_cutoff
      (K := K) (η := (1 : ℝ)) (c := (1 : ℝ))
      (by norm_num) (by norm_num)
  have hpow :
      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled :
      Filter.Tendsto (fun m : ℕ => 108 * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow :
      Filter.Tendsto (fun m : ℕ => 108 * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds ((108 : ℝ) * 0)))
  have hevent := hscaled.eventually (Iio_mem_nhds hρ)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨m, hm⟩ := hevent
  refine ⟨Q, hQ2, m, ?_⟩
  intro S q r P T hQq hlocal hr hq hP hqP hT hfar
  have herror : K / Real.log q ≤ 1 := by
    have := hQ (q : ℝ) hQq
    simpa using this
  have hbound :=
    upperRosserAlternatingPairDiscrete_quadratic_far_le
      hlocal hK (by norm_num : (0 : ℝ) ≤ 1) hr hq herror hP hqP hT hfar
  have hcoefficient : 108 * (1 / 2 : ℝ) ^ m < ρ :=
    hm m le_rfl
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  calc
    (∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
        18 * (1 + (1 : ℝ)) * (1 + 2 * (1 : ℝ)) *
          (1 / 2 : ℝ) ^ m * r ^ 2 := hbound
    _ = (108 * (1 / 2 : ℝ) ^ m) * r ^ 2 := by ring
    _ < ρ * r ^ 2 := mul_lt_mul_of_pos_right hcoefficient hrsq

/-- Uniform tightness of one discrete reverse Rosser pair, including terminal
primes whose global logarithmic coordinate tends to zero.  The dyadic cutoff
depends only on `K` and the requested error. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_far_lt_uniform
    (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ m : ℕ,
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P T : Finset ℕ),
        HasDimensionOneLocalProductBound S K →
        3 ≤ r → q.Prime →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) → T ⊆ P →
        (∀ p ∈ T,
          (2 : ℝ) ^ m ≤ Real.log p / Real.log q) →
        (∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) <
          ρ * r ^ 2 := by
  let η : ℝ := K / Real.log 2
  let C : ℝ := 18 * (1 + η) * (1 + 2 * η)
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hη : 0 ≤ η := div_nonneg hK hlogTwo.le
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hpow :
      Filter.Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hscaled :
      Filter.Tendsto (fun m : ℕ => C * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hpow :
      Filter.Tendsto (fun m : ℕ => C * (1 / 2 : ℝ) ^ m)
        Filter.atTop (nhds (C * 0)))
  have hevent := hscaled.eventually (Iio_mem_nhds hρ)
  rw [Filter.eventually_atTop] at hevent
  obtain ⟨m, hm⟩ := hevent
  refine ⟨m, ?_⟩
  intro S q r P T hlocal hr hq hP hqP hT hfar
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hqTwo : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hlogq : 0 < Real.log q := Real.log_pos hqR
  have hlogTwoQ : Real.log 2 ≤ Real.log q :=
    Real.strictMonoOn_log.monotoneOn (by norm_num)
      (lt_trans (by norm_num) hqR) hqTwo
  have herror : K / Real.log q ≤ η := by
    exact div_le_div_of_nonneg_left hK hlogTwo hlogTwoQ
  have hbound :=
    upperRosserAlternatingPairDiscrete_quadratic_far_le
      hlocal hK hη hr hq herror hP hqP hT hfar
  have hcoefficient : C * (1 / 2 : ℝ) ^ m < ρ :=
    hm m le_rfl
  have hrsq : 0 < r ^ 2 := sq_pos_of_pos (by linarith)
  calc
    (∑ p₀ ∈ T, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
        18 * (1 + η) * (1 + 2 * η) *
          (1 / 2 : ℝ) ^ m * r ^ 2 := hbound
    _ = (C * (1 / 2 : ℝ) ^ m) * r ^ 2 := by rfl
    _ < ρ * r ^ 2 := mul_lt_mul_of_pos_right hcoefficient hrsq

/-- Splitting at a relative dyadic scale reduces the full discrete reverse-pair
sum to a compact-ratio part and an explicit geometric remainder. -/
theorem upperRosserAlternatingPairDiscrete_quadratic_le_near_add
    {S : BoundingSieve} {K η r : ℝ} {q m : ℕ} {P : Finset ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hK : 0 ≤ K) (hη : 0 ≤ η) (hr : 3 ≤ r) (hq : q.Prime)
    (herror : K / Real.log q ≤ η)
    (hP : P ⊆ S.prodPrimes.primeFactors)
    (hqP : ∀ p ∈ P, q < p) :
    (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2) ≤
      (∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
          Real.log (p₀ : ℝ) / Real.log q < (2 : ℝ) ^ m),
        ∑ p₁ ∈ P.filter (fun p₁ : ℕ =>
          p₁ < p₀ ∧
            2 * (Real.log (p₀ : ℝ) / Real.log q) <
              Real.log (p₁ : ℝ) / Real.log q + r),
        (S.nu p₀ / (1 - S.nu p₀)) *
          (S.nu p₁ / (1 - S.nu p₁)) *
            ((r + Real.log p₁ / Real.log q +
                Real.log p₀ / Real.log q) /
              (Real.log p₀ / Real.log q)) ^ 2) +
        18 * (1 + η) * (1 + 2 * η) *
          (1 / 2 : ℝ) ^ m * r ^ 2 := by
  let near : ℕ → Prop := fun p =>
    Real.log p / Real.log q < (2 : ℝ) ^ m
  let f : ℕ → ℝ := fun p₀ =>
    ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2
  let T := P.filter (fun p => ¬near p)
  have hfar : ∀ p ∈ T,
      (2 : ℝ) ^ m ≤ Real.log p / Real.log q := by
    intro p hp
    exact le_of_not_gt (Finset.mem_filter.mp hp).2
  have htail :
      ∑ p₀ ∈ T, f p₀ ≤
        18 * (1 + η) * (1 + 2 * η) *
          (1 / 2 : ℝ) ^ m * r ^ 2 := by
    exact upperRosserAlternatingPairDiscrete_quadratic_far_le
      hlocal hK hη hr hq herror hP hqP
        (Finset.filter_subset _ _) hfar
  have hsplit := Finset.sum_filter_add_sum_filter_not P near f
  change (∑ p₀ ∈ P, f p₀) ≤
    (∑ p₀ ∈ P.filter near, f p₀) +
      18 * (1 + η) * (1 + 2 * η) *
        (1 / 2 : ℝ) ^ m * r ^ 2
  rw [← hsplit]
  simpa [T, add_comm] using
    add_le_add_left htail (∑ p₀ ∈ P.filter near, f p₀)

/-- Uniform compactness reduction for the discrete reverse-pair operator.  A
single dyadic window, depending only on `K` and `ρ`, works for every sieve and
every terminal prime, even when its global logarithmic coordinate vanishes. -/
theorem exists_upperRosserAlternatingPairDiscrete_quadratic_le_near_add
    (K ρ : ℝ) (hK : 0 ≤ K) (hρ : 0 < ρ) :
    ∃ m : ℕ,
      ∀ (S : BoundingSieve) (q : ℕ) (r : ℝ) (P : Finset ℕ),
        HasDimensionOneLocalProductBound S K →
        3 ≤ r → q.Prime →
        P ⊆ S.prodPrimes.primeFactors →
        (∀ p ∈ P, q < p) →
        (∑ p₀ ∈ P, ∑ p₁ ∈ P.filter (fun p₁ =>
            p₁ < p₀ ∧
              2 * (Real.log p₀ / Real.log q) <
                Real.log p₁ / Real.log q + r),
          (S.nu p₀ / (1 - S.nu p₀)) *
            (S.nu p₁ / (1 - S.nu p₁)) *
              ((r + Real.log p₁ / Real.log q +
                  Real.log p₀ / Real.log q) /
                (Real.log p₀ / Real.log q)) ^ 2) <
          (∑ p₀ ∈ P.filter (fun p₀ : ℕ =>
              Real.log (p₀ : ℝ) / Real.log q < (2 : ℝ) ^ m),
            ∑ p₁ ∈ P.filter (fun p₁ : ℕ =>
              p₁ < p₀ ∧
                2 * (Real.log (p₀ : ℝ) / Real.log q) <
                  Real.log (p₁ : ℝ) / Real.log q + r),
            (S.nu p₀ / (1 - S.nu p₀)) *
              (S.nu p₁ / (1 - S.nu p₁)) *
                ((r + Real.log p₁ / Real.log q +
                    Real.log p₀ / Real.log q) /
                  (Real.log p₀ / Real.log q)) ^ 2) +
            ρ * r ^ 2 := by
  obtain ⟨m, hfar⟩ :=
    exists_upperRosserAlternatingPairDiscrete_quadratic_far_lt_uniform
      K ρ hK hρ
  refine ⟨m, ?_⟩
  intro S q r P hlocal hr hq hP hqP
  let near : ℕ → Prop := fun p =>
    Real.log p / Real.log q < (2 : ℝ) ^ m
  let f : ℕ → ℝ := fun p₀ =>
    ∑ p₁ ∈ P.filter (fun p₁ =>
        p₁ < p₀ ∧
          2 * (Real.log p₀ / Real.log q) <
            Real.log p₁ / Real.log q + r),
      (S.nu p₀ / (1 - S.nu p₀)) *
        (S.nu p₁ / (1 - S.nu p₁)) *
          ((r + Real.log p₁ / Real.log q +
              Real.log p₀ / Real.log q) /
            (Real.log p₀ / Real.log q)) ^ 2
  let T := P.filter (fun p => ¬near p)
  have htail : ∑ p₀ ∈ T, f p₀ < ρ * r ^ 2 := by
    apply hfar S q r P T hlocal hr hq hP hqP
      (Finset.filter_subset _ _)
    intro p hp
    exact le_of_not_gt (Finset.mem_filter.mp hp).2
  have hsplit := Finset.sum_filter_add_sum_filter_not P near f
  change (∑ p₀ ∈ P, f p₀) <
    (∑ p₀ ∈ P.filter near, f p₀) + ρ * r ^ 2
  rw [← hsplit]
  simpa [T, add_comm] using
    add_lt_add_left htail (∑ p₀ ∈ P.filter near, f p₀)

/-- On any fixed positive mesh, all local-product correction factors can be
removed from a bounded nonnegative Darboux sum at a prescribed total cost. -/
theorem exists_upperRosserFixedDepthMesh_correctedDarboux_le_add
    (m : ℕ) {K ρ B c : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hc : 0 < c) (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
      ∀ M : Fin (m + 1) → ℝ, (∀ i, 0 ≤ M i ∧ M i ≤ B) →
      (∑ i : Fin (m + 1), M i *
        (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i *
          (1 + K / (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1)) ≤
        (∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1)) + ρ := by
  let η := ρ /
    (((m : ℝ) + 1) * (B + 1) * (c⁻¹ + 1))
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hB1 : 0 < B + 1 := by linarith
  have hcInv : 0 < c⁻¹ := inv_pos.mpr hc
  have hden : 0 < ((m : ℝ) + 1) * (B + 1) * (c⁻¹ + 1) := by
    positivity
  have hη : 0 < η := div_pos hρ hden
  obtain ⟨z₀, hz₀, herror⟩ :=
    exists_localProduct_error_cutoff (K := K) (η := η) (c := c) hη hc
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz M hM
  have hz1 : 1 < z := lt_of_lt_of_le (by norm_num) (hz₀.trans hz)
  have hcell : ∀ i : Fin (m + 1),
      M i *
          (upperRosserFixedDepthMeshRight c m i /
              upperRosserFixedDepthMeshLeft c m i *
            (1 + K /
              (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1) ≤
        M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1) +
          (B + 1) * (c⁻¹ + 1) * η := by
    intro i
    let u := upperRosserFixedDepthMeshLeft c m i
    let v := upperRosserFixedDepthMeshRight c m i
    have hu : 0 < u :=
      hc.trans_le (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
    have hcu : c ≤ u := (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
    have huv : u ≤ v := upperRosserFixedDepthMeshLeft_le_right hc1 m i
    have hv : v ≤ 1 := upperRosserFixedDepthMeshRight_le_one hc1 m i
    have hratio : v / u ≤ c⁻¹ := by
      calc
        v / u ≤ 1 / u := (div_le_div_iff_of_pos_right hu).2 hv
        _ ≤ 1 / c := (one_div_le_one_div_of_le hc hcu)
        _ = c⁻¹ := one_div _
    have hratioNonneg : 0 ≤ v / u := div_nonneg (hu.le.trans huv) hu.le
    have herrorCell : K / (u * Real.log z) ≤ η :=
      (localProduct_error_le_of_log_coordinate_lower hK hz1 hc hcu).trans
        (herror z hz)
    have herrorNonneg : 0 ≤ K / (u * Real.log z) :=
      div_nonneg hK (mul_nonneg hu.le (Real.log_pos hz1).le)
    have hMr : M i * (v / u) ≤ B * c⁻¹ :=
      mul_le_mul (hM i).2 hratio hratioNonneg hB
    have hBInv : B * c⁻¹ ≤ (B + 1) * (c⁻¹ + 1) := by
      nlinarith
    have hprod :
        M i * (v / u) * (K / (u * Real.log z)) ≤
          (B + 1) * (c⁻¹ + 1) * η :=
      mul_le_mul (hMr.trans hBInv) herrorCell herrorNonneg
        (mul_nonneg (by positivity) (by positivity))
    dsimp [u, v] at hprod ⊢
    nlinarith
  calc
    (∑ i : Fin (m + 1), M i *
      (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i *
        (1 + K / (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1)) ≤
        ∑ i : Fin (m + 1),
          (M i * (upperRosserFixedDepthMeshRight c m i /
              upperRosserFixedDepthMeshLeft c m i - 1) +
            (B + 1) * (c⁻¹ + 1) * η) :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = (∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1)) +
        ((m : ℝ) + 1) * ((B + 1) * (c⁻¹ + 1) * η) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = (∑ i : Fin (m + 1), M i *
          (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1)) + ρ := by
      dsimp [η]
      field_simp

/-- The total uncorrected logarithmic increment of a fixed mesh is uniformly
bounded by the reciprocal of its positive lower endpoint. -/
theorem upperRosserFixedDepthMesh_incrementSum_le
    (m : ℕ) {c : ℝ} (hc : 0 < c) (hc1 : c < 1) :
    (∑ i : Fin (m + 1),
        (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1)) ≤ c⁻¹ := by
  have hcell : ∀ i : Fin (m + 1),
      upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1 ≤
        upperRosserFixedDepthMeshWidth c m / c := by
    intro i
    have hu : 0 < upperRosserFixedDepthMeshLeft c m i :=
      hc.trans_le (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
    have hh : 0 ≤ upperRosserFixedDepthMeshWidth c m :=
      (upperRosserFixedDepthMeshWidth_pos hc1 m).le
    calc
      upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i - 1 =
          upperRosserFixedDepthMeshWidth c m /
            upperRosserFixedDepthMeshLeft c m i := by
        rw [upperRosserFixedDepthMeshRight]
        field_simp
        ring
      _ ≤ upperRosserFixedDepthMeshWidth c m / c :=
        div_le_div_of_nonneg_left hh hc
          (upperRosserFixedDepthMeshLeft_mem hc1 m i).1
  calc
    (∑ i : Fin (m + 1),
        (upperRosserFixedDepthMeshRight c m i /
          upperRosserFixedDepthMeshLeft c m i - 1)) ≤
        ∑ _i : Fin (m + 1), upperRosserFixedDepthMeshWidth c m / c :=
      Finset.sum_le_sum fun i _ => hcell i
    _ = (1 - c) / c := by
      simp [upperRosserFixedDepthMeshWidth]
      field_simp
    _ ≤ c⁻¹ := by
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hc.le

/-- The corrected outer-mesh increments have bounded total mass.  This turns a
uniform additive error in every inner cell into one controlled outer error in
the two-partition Rosser successor. -/
theorem exists_upperRosserFixedDepthMesh_correctedIncrementSum_le
    (m : ℕ) {K ρ c : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    (hc : 0 < c) (hc1 : c < 1) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧ ∀ z : ℝ, z₀ ≤ z →
      (∑ i : Fin (m + 1),
        (upperRosserFixedDepthMeshRight c m i /
            upperRosserFixedDepthMeshLeft c m i *
          (1 + K /
            (upperRosserFixedDepthMeshLeft c m i * Real.log z)) - 1)) ≤
        c⁻¹ + ρ := by
  obtain ⟨z₀, hz₀, hcorrected⟩ :=
    exists_upperRosserFixedDepthMesh_correctedDarboux_le_add
      m hK hρ (by norm_num : (0 : ℝ) ≤ 1) hc hc1
  refine ⟨z₀, hz₀, ?_⟩
  intro z hz
  have hmain := upperRosserFixedDepthMesh_incrementSum_le m hc hc1
  have hcorr := hcorrected z hz (fun _ => (1 : ℝ)) (by simp)
  simp only [one_mul] at hcorr
  linarith

/-- Above any fixed positive logarithmic coordinate, every individual
normalized density atom is uniformly small once the global cutoff is large.
This controls the hyperplane and endpoint atoms in fixed-depth Darboux sums. -/
theorem exists_dimensionOne_atom_cutoff
    (K η c : ℝ) (hK : 1 ≤ K) (hη : 0 < η) (hc : 0 < c) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z : ℝ) (q : ℕ),
        z₀ ≤ z → HasDimensionOneLocalProductBound S K →
        q ∈ S.prodPrimes.primeFactors → z ^ c ≤ (q : ℝ) →
        S.nu q / (1 - S.nu q) ≤ η := by
  let ε := min 1 (η / 3)
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hη (by norm_num))
  have hεone : ε ≤ 1 := min_le_left _ _
  have hεeta : ε ≤ η / 3 := min_le_right _ _
  obtain ⟨z₀, hz₀, herror⟩ :=
    exists_localProduct_error_cutoff (K := K) (η := ε) (c := c) hε hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z q hz hlocal hq hqLower
  have hz2 : 2 ≤ z := hz₀.trans hz
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hqone : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
  have hlogq : 0 < Real.log q := Real.log_pos hqone
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hcoord : c ≤ Real.log q / Real.log z := by
    apply (le_div_iff₀ hlogz).2
    rw [← Real.log_rpow hzpos]
    exact Real.strictMonoOn_log.monotoneOn
      (Real.rpow_pos_of_pos hzpos c) hqpos hqLower
  have hKq : K / Real.log q ≤ ε := by
    have hcoordError :=
      localProduct_error_le_of_log_coordinate_lower
        (K := K) (z := z) (a := Real.log q / Real.log z) (c := c)
        hK0 (by linarith) hc hcoord
    have heq :
        K / ((Real.log q / Real.log z) * Real.log z) =
          K / Real.log q := by
      field_simp [hlogz.ne']
    rw [heq] at hcoordError
    exact hcoordError.trans (herror z hz)
  have hdelta :
      1 / ((q : ℝ) * Real.log q) ≤ ε := by
    have hinvq : 1 / (q : ℝ) ≤ 1 := by
      apply (div_le_iff₀ hqpos).2
      nlinarith [show (1 : ℝ) ≤ q by exact_mod_cast hqPrime.one_lt.le]
    have hdeltaK :
        1 / ((q : ℝ) * Real.log q) ≤ K / Real.log q := by
      rw [show 1 / ((q : ℝ) * Real.log q) =
        (1 / (q : ℝ)) / Real.log q by ring]
      exact div_le_div_of_nonneg_right (hinvq.trans hK) hlogq.le
    exact hdeltaK.trans hKq
  have hatom :=
    nu_div_one_sub_le_atomic_log_error hlocal hK0 hq
  calc
    S.nu q / (1 - S.nu q) ≤
        1 / ((q : ℝ) * Real.log q) +
          (1 + 1 / ((q : ℝ) * Real.log q)) *
            (K / Real.log q) := hatom
    _ ≤ ε + (1 + ε) * ε := by
      apply add_le_add hdelta
      exact mul_le_mul (by linarith [hdelta]) hKq
        (div_nonneg hK0 hlogq.le)
        (by positivity)
    _ ≤ η := by nlinarith [hε.le]

/-- At fixed Rosser depth, one cutoff makes the normalized density of the
distinguished prime and of every selected prime uniformly smaller than a
prescribed tolerance. -/
theorem exists_upperRosserBoundaryChains_fixed_length_atom_le
    (K η : ℝ) (k : ℕ) (hK : 1 ≤ K) (hη : 0 < η) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ) (q : ℕ) (l : List ℕ),
        z₀ ≤ z → 0 < Δ → s = Real.log Δ / Real.log z → 3 / 2 ≤ s →
        HasDimensionOneLocalProductBound S K →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        l ∈ LinearSieve.upperRosserBoundaryChains (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) →
        l.length = 2 * k →
        S.nu q / (1 - S.nu q) ≤ η ∧
          ∀ p ∈ l, S.nu p / (1 - S.nu p) ≤ η := by
  let c : ℝ := 1 / (2 * 3 ^ k)
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨z₀, hz₀, hatom⟩ :=
    exists_dimensionOne_atom_cutoff K η c hK hη hc
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s q l hz hΔ hs hslo hlocal hcut hq hl hlen
  have hz2 : 2 ≤ z := hz₀.trans hz
  have hz1 : 1 < z := by linarith
  have hzpos : 0 < z := by linarith
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hsupport :=
    upperRosserBoundaryChains_fixed_length_logarithmic_support
      hz2 hΔ hs hslo hcut hq hl hlen
  have hqLower : z ^ c ≤ (q : ℝ) := by
    calc
      z ^ c ≤ z ^ (Real.log q / Real.log z) :=
        (Real.rpow_lt_rpow_of_exponent_lt hz1 (by simpa [c] using hsupport.1)).le
      _ = (q : ℝ) := by
        simpa [Real.logb] using
          (Real.rpow_logb (x := (q : ℝ)) hzpos (ne_of_gt hz1) hqpos)
  refine ⟨hatom S z q hz hlocal hq hqLower, ?_⟩
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  have hqP : q ∉ P := by simp [P]
  have hqmin : ∀ p ∈ P, q ≤ p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2.le
  have hl' := (LinearSieve.mem_upperRosserBoundaryChains_iff
    hqP hqPrime hqmin).mp (by simpa [P] using hl)
  intro p hp
  have hpP : p ∈ P := hl'.2.2.1 (by simpa using hp)
  have hpS : p ∈ S.prodPrimes.primeFactors := (Finset.mem_filter.mp hpP).1
  have hpcoord :
      c < Real.log p / Real.log z := by
    simpa [c] using
      (hsupport.2 (Real.log p / Real.log z)
        (by
          apply List.mem_map.mpr
          exact ⟨p, hp, rfl⟩)).1
  have hpLower : z ^ c ≤ (p : ℝ) := by
    calc
      z ^ c ≤ z ^ (Real.log p / Real.log z) :=
        (Real.rpow_lt_rpow_of_exponent_lt hz1 hpcoord).le
      _ = (p : ℝ) := by
        simpa [Real.logb] using
          (Real.rpow_logb (x := (p : ℝ)) hzpos (ne_of_gt hz1)
            (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpS).pos))
  exact hatom S z p hz hlocal hpS hpLower

/-- On depth-`2k` boundary carriers, every local-product correction is at most
`2 * 3^k * K / log z`.  Thus the `K / log` errors are uniformly harmless after
the depth cutoff has been fixed. -/
theorem upperRosserBoundaryChains_fixed_length_localProduct_error_le
    {S : BoundingSieve} {K z Δ s : ℝ} {q k : ℕ} {l : List ℕ}
    (hK : 0 ≤ K) (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hs : s = Real.log Δ / Real.log z) (hslo : 3 / 2 ≤ s)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors)
    (hl : l ∈ LinearSieve.upperRosserBoundaryChains
      (Nat.floor Δ + 1) q
      (S.prodPrimes.primeFactors.filter (fun p => q < p)))
    (hlen : l.length = 2 * k) :
    K / ((Real.log q / Real.log z) * Real.log z) ≤
        (2 * 3 ^ k) * K / Real.log z ∧
      ∀ x ∈ LinearSieve.logarithmicCoordinates z l,
        K / (x * Real.log z) ≤ (2 * 3 ^ k) * K / Real.log z := by
  have hsupport := upperRosserBoundaryChains_fixed_length_logarithmic_support
    hz hΔ hs hslo hcut hq hl hlen
  have hbound {a : ℝ} (ha : 1 / (2 * 3 ^ k) < a) :
      K / (a * Real.log z) ≤ (2 * 3 ^ k) * K / Real.log z := by
    calc
      K / (a * Real.log z) ≤
          K / ((1 / (2 * 3 ^ k)) * Real.log z) :=
        localProduct_error_le_of_log_coordinate_lower hK (by linarith)
          (by positivity) ha.le
      _ = (2 * 3 ^ k) * K / Real.log z := by field_simp
  exact ⟨hbound hsupport.1, fun x hx => hbound (hsupport.2 x hx).1⟩

/-- After fixing the Rosser depth, one cutoff makes every local-product
correction on every boundary carrier smaller than a prescribed tolerance. -/
theorem exists_upperRosserBoundaryChains_fixed_length_localProduct_error_le
    (K η : ℝ) (k : ℕ) (hK : 0 ≤ K) (hη : 0 < η) :
    ∃ z₀ : ℝ, 2 ≤ z₀ ∧
      ∀ (S : BoundingSieve) (z Δ s : ℝ) (q : ℕ) (l : List ℕ),
        z₀ ≤ z → 0 < Δ → s = Real.log Δ / Real.log z → 3 / 2 ≤ s →
        (∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z) →
        q ∈ S.prodPrimes.primeFactors →
        l ∈ LinearSieve.upperRosserBoundaryChains (Nat.floor Δ + 1) q
          (S.prodPrimes.primeFactors.filter (fun p => q < p)) →
        l.length = 2 * k →
        K / ((Real.log q / Real.log z) * Real.log z) ≤ η ∧
          ∀ x ∈ LinearSieve.logarithmicCoordinates z l,
            K / (x * Real.log z) ≤ η := by
  obtain ⟨z₀, hz₀, herror⟩ := exists_localProduct_error_cutoff
    (K := K) (η := η) (c := 1 / (2 * 3 ^ k)) hη (by positivity)
  refine ⟨z₀, hz₀, ?_⟩
  intro S z Δ s q l hz hΔ hs hslo hcut hq hl hlen
  have hz2 : 2 ≤ z := hz₀.trans hz
  have hsupport := upperRosserBoundaryChains_fixed_length_logarithmic_support
    hz2 hΔ hs hslo hcut hq hl hlen
  have hbound {a : ℝ} (ha : 1 / (2 * 3 ^ k) < a) :
      K / (a * Real.log z) ≤ η :=
    (localProduct_error_le_of_log_coordinate_lower hK (by linarith)
      (by positivity) ha.le).trans (herror z hz)
  exact ⟨hbound hsupport.1, fun x hx => hbound (hsupport.2 x hx).1⟩

/-- The selected part of a fixed-depth Rosser boundary has factorial decay.
The base of the power is the dimension-one mass of the complete prime tail
above `q`; imposing the Rosser region can only decrease this mass. -/
theorem factorial_mul_upperRosserBoundaryChains_fixed_length_density_le
    {S : BoundingSieve} {K z : ℝ} {D q ell : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (ell.factorial : ℝ) *
        (∑ l ∈ (LinearSieve.upperRosserBoundaryChains D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p))).filter
            (fun l => l.length = ell),
          (l.map (fun p => S.nu p / (1 - S.nu p))).prod) ≤
      (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1)) - 1) ^ ell := by
  let P := S.prodPrimes.primeFactors.filter (fun p => q < p)
  let w : ℕ → ℝ := fun p => S.nu p / (1 - S.nu p)
  have hP : P ⊆ S.prodPrimes.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hw : ∀ p ∈ P, 0 ≤ w p := by
    intro p hp
    exact nu_div_one_sub_nonneg_of_mem (hP hp)
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqz : (q : ℝ) ≤ z := hcut q hq
  have hmass :
      ∑ p ∈ P, w p ≤
        Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1)) - 1 := by
    apply sum_nu_div_one_sub_le_of_subset_interval hlocal
        (z₁ := (q : ℝ) + 1) (z₂ := z + 1)
    · have hq2 := hqPrime.two_le
      exact_mod_cast (show 2 ≤ q + 1 by omega)
    · linarith
    · exact hP
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      constructor
      · exact_mod_cast (Nat.add_one_le_iff.mpr hp'.2)
      · linarith [hcut p hp'.1]
  have hsum_nonneg : 0 ≤ ∑ p ∈ P, w p := Finset.sum_nonneg hw
  calc
    (ell.factorial : ℝ) *
        (∑ l ∈ (LinearSieve.upperRosserBoundaryChains D q P).filter
            (fun l => l.length = ell), (l.map w).prod) ≤
      (∑ p ∈ P, w p) ^ ell :=
        LinearSieve.factorial_mul_sum_upperRosserBoundaryChains_fixed_length_le_pow_sum
          D q P w hw ell
    _ ≤ (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1)) - 1) ^ ell :=
      pow_le_pow_left₀ hsum_nonneg hmass ell

/-- Direct `M ^ ell / ell!` form of the dimension-one fixed-depth bound. -/
theorem upperRosserBoundaryChains_fixed_length_density_le_pow_div_factorial
    {S : BoundingSieve} {K z : ℝ} {D q ell : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (∑ l ∈ (LinearSieve.upperRosserBoundaryChains D q
          (S.prodPrimes.primeFactors.filter (fun p => q < p))).filter
            (fun l => l.length = ell),
          (l.map (fun p => S.nu p / (1 - S.nu p))).prod) ≤
      (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1)) - 1) ^ ell /
        (ell.factorial : ℝ) := by
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < ell.factorial)]
  simpa [mul_comm] using
    factorial_mul_upperRosserBoundaryChains_fixed_length_density_le
      hlocal hcut hq (ell := ell)

/-- A skipped complement in the tail above `q` is controlled by the
dimension-one product estimate on `[q + 1, z + 1)`. -/
theorem upperRosserTailComplement_invProduct_le
    {S : BoundingSieve} {K z : ℝ} {q : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) (s : Finset ℕ) :
    ∏ p ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)) \ s,
        (1 - S.nu p)⁻¹ ≤
      Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
        (1 + K / Real.log ((q : ℝ) + 1)) := by
  have hqPrime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqz : (q : ℝ) ≤ z := hcut q hq
  apply prod_inv_one_sub_nu_le_of_subset_interval hlocal
      (z₁ := (q : ℝ) + 1) (z₂ := z + 1)
  · have hq2 : 2 ≤ q := hqPrime.two_le
    have htwo : (2 : ℕ) ≤ q + 1 := by omega
    exact_mod_cast htwo
  · linarith
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1).1
  · intro p hp
    have hpTail := Finset.mem_filter.mp (Finset.mem_sdiff.mp hp).1
    constructor
    · exact_mod_cast (Nat.add_one_le_iff.mpr hpTail.2)
    · linarith [hcut p hpTail.1]

/-- On a logarithmic coordinate bounded away from zero, the skipped-prime tail
factor contributes at most one further reciprocal-coordinate factor, up to the
two uniform local-product errors.  This is the factor-bearing estimate needed
when the outer Rosser prime is inserted into a logarithmic mesh. -/
theorem upperRosserTailFactor_le_logCoordinate
    {K z η : ℝ} {q : ℕ}
    (hK : 0 ≤ K) (hz : 1 < z) (hq : q.Prime) (hη : 0 ≤ η)
    (hlogRatio : Real.log (z + 1) / Real.log z ≤ 1 + η)
    (herror : K / ((Real.log q / Real.log z) * Real.log z) ≤ η) :
    Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
        (1 + K / Real.log ((q : ℝ) + 1)) ≤
      (1 + η) ^ 2 * (Real.log q / Real.log z)⁻¹ := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hqone : (1 : ℝ) < q := by exact_mod_cast hq.one_lt
  have hlogq : 0 < Real.log q := Real.log_pos hqone
  have hlogq1 : 0 < Real.log ((q : ℝ) + 1) :=
    Real.log_pos (by linarith)
  have hlogmono : Real.log q ≤ Real.log ((q : ℝ) + 1) := by
    apply Real.strictMonoOn_log.monotoneOn
    · change (0 : ℝ) < q
      exact hqpos
    · change (0 : ℝ) < (q : ℝ) + 1
      linarith
    · linarith
  have hnum : 0 ≤ Real.log (z + 1) := Real.log_nonneg (by linarith)
  have hfirst :
      Real.log (z + 1) / Real.log ((q : ℝ) + 1) ≤
        (1 + η) * (Real.log q / Real.log z)⁻¹ := by
    calc
      Real.log (z + 1) / Real.log ((q : ℝ) + 1) ≤
          Real.log (z + 1) / Real.log q :=
        div_le_div_of_nonneg_left hnum hlogq hlogmono
      _ = (Real.log (z + 1) / Real.log z) *
          (Real.log q / Real.log z)⁻¹ := by
        field_simp [hlogz.ne', hlogq.ne']
      _ ≤ (1 + η) * (Real.log q / Real.log z)⁻¹ := by
        apply mul_le_mul_of_nonneg_right hlogRatio
        positivity
  have hsecond :
      1 + K / Real.log ((q : ℝ) + 1) ≤ 1 + η := by
    have hKmono : K / Real.log ((q : ℝ) + 1) ≤ K / Real.log q :=
      div_le_div_of_nonneg_left hK hlogq hlogmono
    have heq : K / Real.log q =
        K / ((Real.log q / Real.log z) * Real.log z) := by
      field_simp [hlogz.ne']
    linarith [hKmono, herror]
  have hsecondNonneg :
      0 ≤ 1 + K / Real.log ((q : ℝ) + 1) := by
    positivity
  have hfirstUpperNonneg :
      0 ≤ (1 + η) * (Real.log q / Real.log z)⁻¹ := by
    positivity
  calc
    Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
        (1 + K / Real.log ((q : ℝ) + 1)) ≤
      ((1 + η) * (Real.log q / Real.log z)⁻¹) * (1 + η) :=
        mul_le_mul hfirst hsecond hsecondNonneg hfirstUpperNonneg
    _ = (1 + η) ^ 2 * (Real.log q / Real.log z)⁻¹ := by ring

/-- The skipped-prime part of one Rosser boundary path can be replaced by the
dimension-one interval factor, leaving only the selected prime ratios. -/
theorem upperRosserBoundaryPathTerm_le
    {S : BoundingSieve} {K z : ℝ} {q : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) {s : Finset ℕ}
    (hs : s ⊆ S.prodPrimes.primeFactors.filter (fun p => q < p)) :
    (∏ p ∈ s, S.nu p / (1 - S.nu p)) *
          ∏ p ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)) \ s,
            (1 - S.nu p)⁻¹ ≤
      (∏ p ∈ s, S.nu p / (1 - S.nu p)) *
        (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) := by
  apply mul_le_mul_of_nonneg_left
    (upperRosserTailComplement_invProduct_le hlocal hcut hq s)
  apply Finset.prod_nonneg
  intro p hp
  have hp' : p ∈ S.prodPrimes.primeFactors :=
    (Finset.mem_filter.mp (hs hp)).1
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors hp'
  have hpdvd : p ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp' |>.2
  exact div_nonneg (S.nu_pos_of_prime p hpPrime hpdvd).le
    (sub_nonneg.mpr (S.nu_lt_one_of_prime p hpPrime hpdvd).le)

/-- Quantitative reduction of a normalized boundary mass to the selected
Rosser chains.  This removes all skipped primes using only the local-product
hypothesis; the remaining sum carries the cubic boundary condition. -/
theorem upperRosserBoundaryDensity_div_eulerProduct_le
    {S : BoundingSieve} {K z : ℝ} {D q : ℕ}
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hq : q ∈ S.prodPrimes.primeFactors) :
    (∑ s ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
          (LinearSieve.UpperRosserBoundarySet D q),
        ∏ p ∈ s, S.nu p) /
        ∏ p ∈ S.prodPrimes.primeFactors.filter (fun p => q < p),
          (1 - S.nu p) ≤
      (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) *
        ∑ s ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
            (LinearSieve.UpperRosserBoundarySet D q),
          ∏ p ∈ s, S.nu p / (1 - S.nu p) := by
  rw [LinearSieve.upperRosserBoundaryDensity_div_eulerProduct]
  calc
    ∑ s ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
          (LinearSieve.UpperRosserBoundarySet D q),
        (∏ p ∈ s, S.nu p / (1 - S.nu p)) *
          ∏ p ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)) \ s,
            (1 - S.nu p)⁻¹ ≤
        ∑ s ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
          (LinearSieve.UpperRosserBoundarySet D q),
          (∏ p ∈ s, S.nu p / (1 - S.nu p)) *
            (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
              (1 + K / Real.log ((q : ℝ) + 1))) := by
      apply Finset.sum_le_sum
      intro s hs
      exact upperRosserBoundaryPathTerm_le hlocal hcut hq
        (Finset.mem_powerset.mp (Finset.mem_filter.mp hs).1)
    _ = (Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
          (1 + K / Real.log ((q : ℝ) + 1))) *
        ∑ s ∈ (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
            (LinearSieve.UpperRosserBoundarySet D q),
          ∏ p ∈ s, S.nu p / (1 - S.nu p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring

/-- The normalized upper Rosser density is bounded by an explicit finite sum
over selected cubic-boundary chains.  All unselected Euler factors have been
absorbed by the dimension-one interval estimate. -/
theorem upperRosserSetDensityRatio_le_one_add_boundaryChains
    {S : BoundingSieve} {K z : ℝ} {D : ℕ} (hD : 1 < D)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D) :
    LinearSieve.upperRosserSetDensitySum S.nu D S.prodPrimes.primeFactors /
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤
      1 + ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ((Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
            (1 + K / Real.log ((q : ℝ) + 1))) *
            ∑ s ∈
                (S.prodPrimes.primeFactors.filter (fun p => q < p)).powerset.filter
                  (LinearSieve.UpperRosserBoundarySet D q),
              ∏ p ∈ s, S.nu p / (1 - S.nu p)) := by
  have hprime : ∀ p ∈ S.prodPrimes.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfactor : ∀ p ∈ S.prodPrimes.primeFactors, 1 - S.nu p ≠ 0 := by
    intro p hp
    have hpdvd : p ∣ S.prodPrimes :=
      (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hp |>.2
    exact ne_of_gt (sub_pos.mpr
      (S.nu_lt_one_of_prime p (hprime p hp) hpdvd))
  rw [LinearSieve.upperRosserSetDensityRatio_eq_one_add_sum_boundary
    S.nu S.prodPrimes.primeFactors hD hprime hlevel hfactor]
  refine add_le_add_right ?_ 1
  apply Finset.sum_le_sum
  intro q hq
  apply mul_le_mul_of_nonneg_left
    (upperRosserBoundaryDensity_div_eulerProduct_le hlocal hcut hq)
  have hpdvd : q ∣ S.prodPrimes :=
    (Nat.mem_primeFactors_of_ne_zero S.prodPrimes_ne_zero).mp hq |>.2
  exact div_nonneg (S.nu_pos_of_prime q (hprime q hq) hpdvd).le
    (sub_nonneg.mpr (S.nu_lt_one_of_prime q (hprime q hq) hpdvd).le)

/-- The normalized density bound grouped by the even length of each canonical
decreasing Rosser boundary chain.  This exposes exactly the finite depth
parameter to which the factorial estimate applies. -/
theorem upperRosserSetDensityRatio_le_one_add_boundaryChains_by_even_length
    {S : BoundingSieve} {K z : ℝ} {D : ℕ} (hD : 1 < D)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D) :
    LinearSieve.upperRosserSetDensitySum S.nu D S.prodPrimes.primeFactors /
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤
      1 + ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ((Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
            (1 + K / Real.log ((q : ℝ) + 1))) *
            ∑ ell ∈ (Finset.range
                ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1)).filter
                  Even,
              ∑ l ∈ (LinearSieve.upperRosserBoundaryChains D q
                (S.prodPrimes.primeFactors.filter (fun p => q < p))).filter
                  (fun l => l.length = ell),
                (l.map (fun p => S.nu p / (1 - S.nu p))).prod) := by
  have h :=
    upperRosserSetDensityRatio_le_one_add_boundaryChains hD hlocal hcut hlevel
  simpa only [LinearSieve.sum_upperRosserBoundary_eq_sum_chains,
    LinearSieve.sum_upperRosserBoundaryChains_by_even_length] using h

/-- The normalized upper Rosser density bound indexed directly by Buchstab pair
depth.  Each inner term is now exactly the quantity governed by
`upperRosserBoundaryChainsFixedDepthDensity_succ`. -/
theorem upperRosserSetDensityRatio_le_one_add_boundaryChains_by_depth
    {S : BoundingSieve} {K z : ℝ} {D : ℕ} (hD : 1 < D)
    (hlocal : HasDimensionOneLocalProductBound S K)
    (hcut : ∀ p ∈ S.prodPrimes.primeFactors, (p : ℝ) ≤ z)
    (hlevel : ∀ p ∈ S.prodPrimes.primeFactors, p < D) :
    LinearSieve.upperRosserSetDensitySum S.nu D S.prodPrimes.primeFactors /
          ∏ p ∈ S.prodPrimes.primeFactors, (1 - S.nu p) ≤
      1 + ∑ q ∈ S.prodPrimes.primeFactors,
        (S.nu q / (1 - S.nu q)) *
          ((Real.log (z + 1) / Real.log ((q : ℝ) + 1) *
            (1 + K / Real.log ((q : ℝ) + 1))) *
            ∑ k ∈ Finset.range
                ((S.prodPrimes.primeFactors.filter (fun p => q < p)).card + 1),
              LinearSieve.upperRosserBoundaryChainsFixedDepthDensity
                (fun p => S.nu p / (1 - S.nu p)) D q
                (S.prodPrimes.primeFactors.filter (fun p => q < p)) k) := by
  have h :=
    upperRosserSetDensityRatio_le_one_add_boundaryChains hD hlocal hcut hlevel
  simpa only [LinearSieve.sum_upperRosserBoundary_eq_sum_fixedDepthDensity] using h

/-- A sieve ratio strictly larger than one places every integer below the
sifting cutoff strictly below the natural Rosser level `⌊Δ⌋ + 1`. -/
theorem lt_floor_add_one_of_le_of_log_ratio
    {p : ℕ} {z Δ s : ℝ} (hz : 2 ≤ z) (hΔ : 0 < Δ)
    (hp : (p : ℝ) ≤ z) (hs : s = Real.log Δ / Real.log z)
    (hslo : 3 / 2 ≤ s) :
    p < Nat.floor Δ + 1 := by
  have hzpos : 0 < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hs1 : 1 < s := by linarith
  have hlogeq : Real.log Δ = s * Real.log z := by
    rw [hs]
    field_simp
  have hloglt : Real.log z < Real.log Δ := by
    rw [hlogeq]
    nlinarith
  have hzΔ : z < Δ :=
    (Real.strictMonoOn_log.lt_iff_lt hzpos hΔ).mp hloglt
  have hpΔ : (p : ℝ) < Δ := hp.trans_lt hzΔ
  have hΔfloor : Δ < (Nat.floor Δ + 1 : ℕ) :=
    by simpa using Nat.lt_floor_add_one Δ
  exact_mod_cast hpΔ.trans hΔfloor

/-- Dividing a strict real cutoff by a positive integer commutes exactly with the
`floor + 1` convention used for Rosser levels. -/
theorem ceilDiv_floor_add_one_eq_floor_div_add_one
    {Δ : ℝ} {c : ℕ} (hΔ : 0 ≤ Δ) (hc : 0 < c) :
    (Nat.floor Δ + 1) ⌈/⌉ c = Nat.floor (Δ / c) + 1 := by
  apply le_antisymm
  · rw [ceilDiv_le_iff_le_mul hc]
    apply Nat.add_one_le_iff.mpr
    apply (Nat.floor_lt hΔ).2
    calc
      Δ < (c : ℝ) * (Nat.floor (Δ / c) + 1) := by
        have h := Nat.lt_floor_add_one (Δ / c)
        rw [div_lt_iff₀ (by exact_mod_cast hc)] at h
        simpa [mul_comm] using h
      _ = (c * (Nat.floor (Δ / c) + 1) : ℕ) := by norm_num
  · apply Nat.add_one_le_iff.mpr
    apply lt_of_not_ge
    intro h
    have hceil : (Nat.floor Δ + 1) ⌈/⌉ c ≤ Nat.floor (Δ / c) := h
    rw [ceilDiv_le_iff_le_mul hc] at hceil
    have hΔlt : Δ < (Nat.floor Δ + 1 : ℕ) := by
      simpa using Nat.lt_floor_add_one Δ
    have hfloor : (Nat.floor (Δ / c) : ℝ) ≤ Δ / c :=
      Nat.floor_le (by positivity)
    have hcR : (0 : ℝ) < c := by exact_mod_cast hc
    have hmul : ((c * Nat.floor (Δ / c) : ℕ) : ℝ) ≤ Δ := by
      norm_num
      calc
        (c : ℝ) * Nat.floor (Δ / c) ≤ (c : ℝ) * (Δ / c) :=
          mul_le_mul_of_nonneg_left hfloor hcR.le
        _ = Δ := by field_simp
    have hceilR : ((Nat.floor Δ + 1 : ℕ) : ℝ) ≤
        ((c * Nat.floor (Δ / c) : ℕ) : ℝ) := by
      exact_mod_cast hceil
    linarith

end MathlibNt.SieveTheory.SwitchingPrinciple
