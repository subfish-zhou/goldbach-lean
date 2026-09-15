import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLPrefixBoundedHarmonicTail
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

open Complex Finset ZMod
open scoped BigOperators Real
open DirichletLAbelWeightVariation

namespace DirichletCharacter

variable {q : ℕ} [NeZero q]

omit [NeZero q] in
private lemma inv_zero_eq_zero {χ : DirichletCharacter ℂ q} (hq : 1 < q) :
    χ⁻¹ (0 : ZMod q) = 0 := by
  let hq' : Fact (1 < q) := ⟨hq⟩
  let := hq'
  simpa using (MulChar.map_nonunit χ⁻¹ (a := (0 : ZMod q)) not_isUnit_zero)

private lemma stdAddChar_mul_natCast_eq_pow (j : ZMod q) (n : ℕ) :
    stdAddChar (j * (n : ZMod q)) = stdAddChar j ^ n := by
  rw [mul_comm, ← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

omit [NeZero q] in
private lemma natCast_ne_zero_of_lt {n : ℕ} (hn1 : 1 ≤ n) (hnq : n < q) :
    (n : ZMod q) ≠ 0 := by
  intro h
  have hval := congrArg ZMod.val h
  have : n = 0 := by simpa [ZMod.val_natCast_of_lt hnq] using hval
  omega

private lemma stdAddChar_natCast_ne_one {n : ℕ} (hn1 : 1 ≤ n) (hnq : n < q) :
    stdAddChar (n : ZMod q) ≠ 1 := by
  intro h
  apply natCast_ne_zero_of_lt (q := q) hn1 hnq
  apply ZMod.injective_stdAddChar
  simpa using h

private lemma norm_stdAddChar_natCast_sub_one_eq {n : ℕ} :
    ‖stdAddChar (n : ZMod q) - 1‖ = ‖2 * Real.sin (π * (n : ℝ) / q)‖ := by
  have hcoe : stdAddChar (n : ZMod q) =
      Complex.exp (2 * π * I * ((n : ℤ) : ℂ) / (q : ℂ)) := by
    simpa using (ZMod.stdAddChar_coe (N := q) (n : ℤ))
  rw [hcoe]
  have harg : (2 * π * I * ((n : ℤ) : ℂ) / (q : ℂ)) =
      I * (((2 * π * (n : ℝ)) / q : ℝ) : ℂ) := by
    norm_num [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  congr 1
  ring

private lemma four_mul_min_div_q_le_norm_stdAddChar_natCast_sub_one
    {n : ℕ} (hn1 : 1 ≤ n) (hnq : n < q) :
    4 * (min n (q - n) : ℝ) / q ≤ ‖stdAddChar (n : ZMod q) - 1‖ := by
  let x : ℝ := π * (n : ℝ) / q
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hnp : 0 < n := Nat.succ_le_iff.mp hn1
  have hqnp : 0 < q - n := Nat.sub_pos_of_lt hnq
  have hden :
      ‖stdAddChar (n : ZMod q) - 1‖ = ‖2 * Real.sin x‖ := by
    simpa [x, mul_assoc, div_eq_mul_inv] using
      norm_stdAddChar_natCast_sub_one_eq (q := q) (n := n)
  by_cases hhalf : n ≤ q - n
  · have hmin : min n (q - n) = n := Nat.min_eq_left hhalf
    have hx0 : 0 ≤ x := by positivity
    have hxle : x ≤ π / 2 := by
      have hfrac : (n : ℝ) / q ≤ (1 : ℝ) / 2 := by
        have htwo : 2 * n ≤ q := by omega
        have htwoR : (2 : ℝ) * n ≤ q := by exact_mod_cast htwo
        rw [div_le_iff₀ hqpos]
        nlinarith
      have hfracπ := mul_le_mul_of_nonneg_left hfrac Real.pi_pos.le
      simpa [x, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfracπ
    have hjordan := Real.mul_le_sin hx0 hxle
    have hsin0 : 0 ≤ Real.sin x := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi hx0
      linarith [hxle, Real.pi_pos]
    have hhalfNatR : (n : ℝ) ≤ ((q - n : ℕ) : ℝ) := by exact_mod_cast hhalf
    have hhalfR : (n : ℝ) ≤ q - n := by
      simpa [Nat.cast_sub hnq.le] using hhalfNatR
    rw [hden, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hsin0),
      min_eq_left hhalfR]
    have h2j' := mul_le_mul_of_nonneg_left hjordan (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [x] at h2j' ⊢
    field_simp [Real.pi_ne_zero, ne_of_gt hqpos] at h2j'
    ring_nf at h2j'
    have h2j'' : 2 * (n : ℝ) ≤ q * Real.sin (π * (n : ℝ) / q) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2j'
    rw [div_le_iff₀ hqpos]
    nlinarith
  · have hhalf' : q - n ≤ n := le_of_not_ge hhalf
    have hmin : min n (q - n) = q - n := Nat.min_eq_right hhalf'
    let y : ℝ := π * ((q - n : ℕ) : ℝ) / q
    have hy0 : 0 ≤ y := by positivity
    have hyle : y ≤ π / 2 := by
      have hfrac : ((q - n : ℕ) : ℝ) / q ≤ (1 : ℝ) / 2 := by
        have htwo : 2 * (q - n) ≤ q := by omega
        have htwoR : (2 : ℝ) * ((q - n : ℕ) : ℝ) ≤ q := by exact_mod_cast htwo
        rw [div_le_iff₀ hqpos]
        nlinarith
      have hfracπ := mul_le_mul_of_nonneg_left hfrac Real.pi_pos.le
      simpa [y, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hfracπ
    have hjordan := Real.mul_le_sin hy0 hyle
    have hsin0 : 0 ≤ Real.sin y := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi hy0
      linarith [hyle, Real.pi_pos]
    have hxy' : x + y = π := by
      dsimp [x, y]
      field_simp [show (q : ℝ) ≠ 0 by exact_mod_cast NeZero.ne q]
      have hsum : (n : ℝ) + ((q - n : ℕ) : ℝ) = q := by
        exact_mod_cast Nat.add_sub_of_le hnq.le
      nlinarith
    have hxy : x = π - y := by linarith
    have hhalfNatR : (((q - n : ℕ) : ℝ)) ≤ (n : ℝ) := by exact_mod_cast hhalf'
    have hhalfR : q - n ≤ (n : ℝ) := by
      simpa [Nat.cast_sub hnq.le] using hhalfNatR
    rw [hden, Real.norm_eq_abs, hxy, Real.sin_pi_sub,
      abs_of_nonneg (mul_nonneg (by positivity) hsin0), min_eq_right hhalfR]
    have h2j' := mul_le_mul_of_nonneg_left hjordan (show (0 : ℝ) ≤ 2 by norm_num)
    dsimp [y] at h2j' ⊢
    field_simp [Real.pi_ne_zero, ne_of_gt hqpos] at h2j'
    ring_nf at h2j'
    have h2j'' : 2 * ((q - n : ℕ) : ℝ) ≤ q * Real.sin (π * ((q - n : ℕ) : ℝ) / q) := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h2j'
    have h2j''' : 2 * (q - n) ≤ q * Real.sin (π * ((q - n : ℕ) : ℝ) / q) := by
      simpa [Nat.cast_sub hnq.le] using h2j''
    rw [div_le_iff₀ hqpos]
    nlinarith

private lemma norm_sum_range_stdAddChar_natCast_le_q_div_min
    (M n : ℕ) (hn1 : 1 ≤ n) (hnq : n < q) :
    ‖∑ m ∈ range M, stdAddChar ((n : ZMod q) * (m : ZMod q))‖ ≤
      (q : ℝ) / min n (q - n) := by
  let z : ℂ := stdAddChar (n : ZMod q)
  have hzne : z ≠ 1 := by
    simpa [z] using stdAddChar_natCast_ne_one (q := q) hn1 hnq
  have hz1 : ‖z‖ = 1 := Circle.norm_coe (ZMod.toCircle (n : ZMod q))
  have hsum :
      (∑ m ∈ range M, stdAddChar ((n : ZMod q) * (m : ZMod q))) =
        ∑ m ∈ range M, z ^ m := by
    apply Finset.sum_congr rfl
    intro m hm
    simpa [z, mul_comm] using stdAddChar_mul_natCast_eq_pow (q := q) (n := m) (j := (n : ZMod q))
  have hnum : ‖z ^ M - 1‖ ≤ 2 := by
    calc
      ‖z ^ M - 1‖ ≤ ‖z ^ M‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hz1]; norm_num
  have hdenlower :
      2 * (min n (q - n) : ℝ) / q ≤ ‖z - 1‖ := by
    have hmin0 : 0 ≤ (min n (q - n) : ℝ) := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hqn0 : 0 ≤ (q : ℝ) - n := by
        have hle : (n : ℝ) ≤ q := by exact_mod_cast hnq.le
        linarith
      have : 0 ≤ min (n : ℝ) (q - n) := le_min hn0 hqn0
      simpa [Nat.cast_min, Nat.cast_sub hnq.le] using this
    have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
    have hfour :=
      (four_mul_min_div_q_le_norm_stdAddChar_natCast_sub_one (q := q) (n := n) hn1 hnq)
    have htwo : 2 * (min n (q - n) : ℝ) / q ≤ 4 * (min n (q - n) : ℝ) / q := by
      have hratio : 0 ≤ (min n (q - n) : ℝ) / q := by
        positivity
      have : 2 * ((min n (q - n) : ℝ) / q) ≤ 4 * ((min n (q - n) : ℝ) / q) := by
        nlinarith
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using this
    exact htwo.trans (by simpa [z] using hfour)
  have hminpos : 0 < (min n (q - n) : ℝ) := by
    have hn0 : 0 < (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hn1)
    have hqn0 : 0 < (q : ℝ) - n := by
      have hlt : (n : ℝ) < q := by exact_mod_cast hnq
      nlinarith
    have : 0 < min (n : ℝ) (q - n) := lt_min hn0 hqn0
    simpa [Nat.cast_min, Nat.cast_sub hnq.le] using this
  calc
    ‖∑ m ∈ range M, stdAddChar ((n : ZMod q) * (m : ZMod q))‖
        = ‖∑ m ∈ range M, z ^ m‖ := by rw [hsum]
    _ = ‖(z ^ M - 1) / (z - 1)‖ := by rw [geom_sum_eq hzne M]
    _ = ‖z ^ M - 1‖ / ‖z - 1‖ := by rw [norm_div]
    _ ≤ 2 / ‖z - 1‖ := div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ 2 / (2 * (min n (q - n) : ℝ) / q) := by
      have hmindivpos : 0 < 2 * (min n (q - n) : ℝ) / q := by
        exact div_pos (by nlinarith [hminpos]) hqpos
      exact div_le_div_of_nonneg_left (by norm_num) hmindivpos hdenlower
    _ = (q : ℝ) / min n (q - n) := by
      rw [Nat.cast_min, Nat.cast_sub hnq.le]
      let mR : ℝ := min (n : ℝ) (q - n)
      change 2 / (2 * mR / q) = (q : ℝ) / mR
      have hmRpos : 0 < mR := by
        simpa [mR] using hminpos
      field_simp [mR, ne_of_gt hqpos, ne_of_gt hmRpos]
where
  hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q

omit [NeZero q] in
private lemma q_div_min_le_q_mul_inv_add_inv {n : ℕ} (hn1 : 1 ≤ n) (_hnq : n < q) :
    (q : ℝ) / min n (q - n) ≤
      (q : ℝ) * (((n : ℝ)⁻¹) + (((q - n : ℕ) : ℝ)⁻¹)) := by
  have hq0 : 0 ≤ (q : ℝ) := by positivity
  by_cases h : n ≤ q - n
  · rw [Nat.min_eq_left h, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hq0
    have : 0 ≤ (((q - n : ℕ) : ℝ)⁻¹) := by positivity
    exact le_add_of_nonneg_right this
  · rw [Nat.min_eq_right (le_of_not_ge h), div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ hq0
    have : 0 ≤ ((n : ℝ)⁻¹) := by positivity
    exact le_add_of_nonneg_left this

private lemma sum_univ_zmod_eq_sum_range (f : ZMod q → ℝ) :
    (∑ j : ZMod q, f j) = ∑ n ∈ range q, f (n : ZMod q) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne q)
  calc
    ∑ j : ZMod r.succ, f j = ∑ i : Fin r.succ, f ((i : ℕ) : ZMod r.succ) := by
      symm
      apply Fintype.sum_equiv (ZMod.finEquiv r.succ).toEquiv
      intro i
      congr 1
      exact ZMod.natCast_zmod_val (ZMod.finEquiv r.succ i)
    _ = ∑ n ∈ range r.succ, f (n : ZMod r.succ) := by
      exact Fin.sum_univ_eq_sum_range (fun n : ℕ => f (n : ZMod r.succ)) r.succ

/-- Explicit scan-free weighted Fourier-kernel bound with generous constant `4`. -/
theorem IsPrimitive.norm_weighted_fourierKernel_sum_le_four_mul_q_mul_one_add_log
    {χ : DirichletCharacter ℂ q} (_hχ : χ.IsPrimitive) (hq : 1 < q) (M : ℕ) :
    ∑ j : ZMod q, ‖χ⁻¹ (-j) * ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖ ≤
      4 * (q : ℝ) * (1 + Real.log q) := by
  let F : ZMod q → ℝ := fun j =>
    ‖χ⁻¹ (-j) * ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖
  have hzero : F 0 = 0 := by
    simp [F, inv_zero_eq_zero (q := q) hq]
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hsum1 :
      ∑ n ∈ range (q - 1), (((q - (n + 1) : ℕ) : ℝ)⁻¹) =
        ∑ n ∈ range (q - 1), (((n + 1 : ℕ) : ℝ)⁻¹) := by
    calc
      ∑ n ∈ range (q - 1), (((q - (n + 1) : ℕ) : ℝ)⁻¹)
          = ∑ n ∈ range (q - 1), ((((q - 1 - 1 - n) + 1 : ℕ) : ℝ)⁻¹) := by
              refine Finset.sum_congr rfl ?_
              intro n hn
              have hn' : n < q - 1 := Finset.mem_range.mp hn
              rw [show q - (n + 1) = q - 1 - n by omega,
                show (q - 1 - 1 - n) + 1 = q - 1 - n by omega]
      _ = ∑ n ∈ range (q - 1), (((n + 1 : ℕ) : ℝ)⁻¹) :=
        Finset.sum_range_reflect (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) (q - 1)
  have hsplit :
      ∑ n ∈ range q, F (n : ZMod q) = F 0 + ∑ n ∈ range (q - 1), F ((n + 1 : ℕ) : ZMod q) := by
    simpa only [Nat.sub_add_cancel (Nat.one_le_of_lt hq), Nat.cast_zero, add_comm] using
      (Finset.sum_range_succ' (f := fun n : ℕ => F (n : ZMod q)) (q - 1))
  calc
    ∑ j : ZMod q, F j = ∑ n ∈ range q, F (n : ZMod q) := sum_univ_zmod_eq_sum_range (q := q) F
    _ = F 0 + ∑ n ∈ range (q - 1), F ((n + 1 : ℕ) : ZMod q) := hsplit
    _ = ∑ n ∈ range (q - 1), F ((n + 1 : ℕ) : ZMod q) := by simp [hzero]
    _ ≤ ∑ n ∈ range (q - 1),
        (q : ℝ) * ((((n + 1 : ℕ) : ℝ)⁻¹) + (((q - (n + 1) : ℕ) : ℝ)⁻¹)) := by
      refine Finset.sum_le_sum ?_
      intro n hn
      have hn1 : 1 ≤ n + 1 := Nat.succ_le_succ (Nat.zero_le n)
      have hnq : n + 1 < q := by
        have hn' : n < q - 1 := Finset.mem_range.mp hn
        omega
      calc
        F ((n + 1 : ℕ) : ZMod q) ≤ (q : ℝ) / min (n + 1) (q - (n + 1)) := by
          dsimp [F]
          calc
            ‖χ⁻¹ (-((n + 1 : ℕ) : ZMod q)) *
                ∑ m ∈ range M, stdAddChar (((n + 1 : ℕ) : ZMod q) * (m : ZMod q))‖
                ≤ ‖∑ m ∈ range M, stdAddChar (((n + 1 : ℕ) : ZMod q) * (m : ZMod q))‖ := by
                  rw [norm_mul]
                  exact mul_le_of_le_one_left (norm_nonneg _)
                    (DirichletCharacter.norm_le_one χ⁻¹ _)
            _ ≤ (q : ℝ) / min (n + 1) (q - (n + 1)) :=
              norm_sum_range_stdAddChar_natCast_le_q_div_min (q := q) M (n + 1) hn1 hnq
        _ ≤ (q : ℝ) * ((((n + 1 : ℕ) : ℝ)⁻¹) + (((q - (n + 1) : ℕ) : ℝ)⁻¹)) :=
          q_div_min_le_q_mul_inv_add_inv (q := q) hn1 hnq
    _ = (q : ℝ) * ∑ n ∈ range (q - 1),
          ((((n + 1 : ℕ) : ℝ)⁻¹) + (((q - (n + 1) : ℕ) : ℝ)⁻¹)) := by
      rw [Finset.mul_sum]
    _ = (q : ℝ) *
          (∑ n ∈ range (q - 1), (((n + 1 : ℕ) : ℝ)⁻¹) +
            ∑ n ∈ range (q - 1), (((q - (n + 1) : ℕ) : ℝ)⁻¹)) := by
      rw [Finset.sum_add_distrib]
    _ = (q : ℝ) * ((harmonic (q - 1) : ℝ) + (harmonic (q - 1) : ℝ)) := by
      rw [hsum1]
      simp [harmonic]
    _ = 2 * (q : ℝ) * (harmonic (q - 1) : ℝ) := by ring
    _ ≤ 2 * (q : ℝ) * (1 + Real.log q) := by
      have hharm : (harmonic (q - 1) : ℝ) ≤ 1 + Real.log q := by
        have hharm' : (harmonic (q - 1) : ℝ) ≤ 1 + Real.log (q - 1 : ℕ) := by
          exact_mod_cast harmonic_le_one_add_log (q - 1)
        have hlog : 1 + Real.log (q - 1 : ℕ) ≤ 1 + Real.log q := by
          have hqm1pos : (0 : ℝ) < (q - 1 : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt hq
          have hqle : ((q - 1 : ℕ) : ℝ) ≤ q := by
            exact_mod_cast Nat.sub_le q 1
          linarith [Real.log_le_log hqm1pos hqle]
        exact hharm'.trans hlog
      gcongr
    _ ≤ 4 * (q : ℝ) * (1 + Real.log q) := by
      have hlog0 : 0 ≤ 1 + Real.log q := by
        have : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast Nat.one_le_of_lt hq)
        linarith
      nlinarith

/-- Primitive-character prefix bound deduced from exact Fourier completion and the
weighted kernel estimate. -/
theorem IsPrimitive.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hq : 1 < q) (M : ℕ) :
    ‖∑ n ∈ range M, χ (n : ZMod q)‖ ≤ 4 * Real.sqrt q * (1 + Real.log q) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast NeZero.pos q
  have hfac0 : 0 ≤ (q : ℝ)⁻¹ * Real.sqrt q := by positivity
  have hqnorm : ‖((q : ℂ)⁻¹)‖ = (q : ℝ)⁻¹ := by
    rw [norm_inv, Complex.norm_natCast]
  rw [hχ.sum_range_fourier_completion M, norm_mul, norm_mul,
    hχ.norm_gaussSum_stdAddChar hq, hqnorm]
  calc
    (q : ℝ)⁻¹ * Real.sqrt q *
        ‖∑ j : ZMod q, χ⁻¹ (-j) * ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖
        ≤ (q : ℝ)⁻¹ * Real.sqrt q *
            ∑ j : ZMod q, ‖χ⁻¹ (-j) * ∑ n ∈ range M, stdAddChar (j * (n : ZMod q))‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) hfac0
    _ ≤ (q : ℝ)⁻¹ * Real.sqrt q * (4 * (q : ℝ) * (1 + Real.log q)) := by
      exact mul_le_mul_of_nonneg_left
        (hχ.norm_weighted_fourierKernel_sum_le_four_mul_q_mul_one_add_log hq M) hfac0
    _ = 4 * Real.sqrt q * (1 + Real.log q) := by
      field_simp [ne_of_gt hqpos]

/-- Integrated harmonic-tail bound from the explicit primitive prefix estimate. -/
theorem IsPrimitive.norm_LFunction_one_sub_harmonic_sum_le_eight_mul_sqrt_q_mul_one_add_log_div
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχne : χ ≠ 1)
    (hq : 1 < q) {m : ℕ} (hm : 1 ≤ m) :
    ‖χ.LFunction 1 - ∑ k ∈ range m, cpowWeight (1 : ℂ) k * χ k‖ ≤
      8 * Real.sqrt q * (1 + Real.log q) / (m : ℝ) := by
  have hprefix : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ 4 * Real.sqrt q * (1 + Real.log q) := by
    intro N
    simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq N
  have htail :=
    norm_LFunction_one_sub_harmonic_sum_le_of_prefix_bound
      χ hχne (4 * Real.sqrt q * (1 + Real.log q)) hprefix hm
  convert htail using 1
  ring

/-- Real quadratic truncation form of the same explicit harmonic-tail bound. -/
theorem IsPrimitive.abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le_eight_mul_sqrt_q_mul_one_add_log_div
    {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχne : χ ≠ 1)
    (hq : 1 < q) {m : ℕ} (hm : 1 ≤ m) :
    |(χ.LFunction 1).re - quadraticHarmonicTruncation χ m| ≤
      8 * Real.sqrt q * (1 + Real.log q) / (m : ℝ) := by
  have hprefix : ∀ N : ℕ, ‖∑ k ∈ range N, χ k‖ ≤ 4 * Real.sqrt q * (1 + Real.log q) := by
    intro N
    simpa using hχ.norm_sum_range_le_four_mul_sqrt_q_mul_one_add_log hq N
  have htail :=
    abs_LFunction_one_re_sub_quadraticHarmonicTruncation_le_of_prefix_bound
      χ hχne (4 * Real.sqrt q * (1 + Real.log q)) hprefix hm
  convert htail using 1
  ring

end DirichletCharacter
