import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryPoisson
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryCoprimeCount

/-!
# Arithmetic Poisson summation for the fixed dyadic cutoff

The finite natural progression is identified with the entire affine integer
lattice using the positive support of the cutoff. The error constant is chosen
before the scale, modulus, residue, and finite support set.
-/

noncomputable section

open scoped SchwartzMap FourierTransform

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

/-- One explicit finite set containing every natural point of the cutoff support. -/
def dyadicCutoffNatSupport (M : ℝ) : Finset ℕ :=
  Finset.Icc 0 (Nat.ceil (3 * M))

theorem scaledDyadicCutoff_mem_Icc_of_ne_zero {M x : ℝ} (hM : 0 < M)
    (hx : scaledDyadicCutoff M x ≠ 0) : x ∈ Set.Icc (M / 2) (3 * M) :=
  scaledDyadicCutoff_tsupport_subset hM (subset_closure hx)

theorem scaledDyadicCutoff_mem_natSupport {M : ℝ} (hM : 0 < M) (m : ℕ)
    (hm : scaledDyadicCutoff M m ≠ 0) : m ∈ dyadicCutoffNatSupport M := by
  apply Finset.mem_Icc.mpr
  refine ⟨Nat.zero_le _, ?_⟩
  have h := (scaledDyadicCutoff_mem_Icc_of_ne_zero hM hm).2
  exact_mod_cast h.trans (Nat.le_ceil (3 * M))

/-- The actual finite natural arithmetic progression equals the complete affine
integer lattice, even for negative representatives of the residue class. -/
theorem scaledDyadicCutoff_finset_progression_eq_tsum
    {M : ℝ} (hM : 0 < M) (S : Finset ℕ)
    (hS : ∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S)
    {q : ℕ} (hq : 0 < q) (a : ℤ) :
    (∑ m ∈ S, if Int.ModEq q (m : ℤ) a
      then (scaledDyadicCutoff M m : ℂ) else 0) =
        ∑' z : ℤ, (scaledDyadicCutoff M ((a : ℝ) + q * z) : ℂ) := by
  classical
  let f : ℕ → ℂ := fun m ↦
    if Int.ModEq q (m : ℤ) a then (scaledDyadicCutoff M m : ℂ) else 0
  let g : ℤ → ℂ := fun z ↦ (scaledDyadicCutoff M ((a : ℝ) + q * z) : ℂ)
  have hnonneg (z : Function.support g) : 0 ≤ a + (q : ℤ) * z.val := by
    have hz : scaledDyadicCutoff M ((a : ℝ) + q * z.val) ≠ 0 := by
      simpa only [g, Function.mem_support, ne_eq, Complex.ofReal_eq_zero] using z.property
    have hp := (scaledDyadicCutoff_mem_Icc_of_ne_zero hM hz).1
    have hp' : (0 : ℝ) ≤ a + (q : ℝ) * z.val := by linarith
    exact_mod_cast hp'
  let i : Function.support g → ℕ := fun z ↦ (a + (q : ℤ) * z.val).toNat
  have hcast (z : Function.support g) : (i z : ℤ) = a + (q : ℤ) * z.val :=
    Int.toNat_of_nonneg (hnonneg z)
  have hi : Function.Injective i := by
    intro z z' h
    have he := congrArg (fun n : ℕ ↦ (n : ℤ)) h
    rw [hcast, hcast] at he
    apply Subtype.ext
    exact mul_left_cancel₀ (by exact_mod_cast hq.ne') (add_left_cancel he)
  have hf : Function.support f ⊆ Set.range i := by
    intro m hm
    have hm' : Int.ModEq q (m : ℤ) a ∧ scaledDyadicCutoff M m ≠ 0 := by
      simpa only [f, Function.mem_support, ne_eq, ite_eq_right_iff,
        Complex.ofReal_eq_zero, Classical.not_imp] using hm
    obtain ⟨z, hz⟩ := Int.modEq_iff_dvd.mp hm'.1.symm
    have he : a + (q : ℤ) * z = m := by linarith
    have heR : (a : ℝ) + (q : ℝ) * z = m := by exact_mod_cast he
    have hg : z ∈ Function.support g := by
      simpa only [Function.mem_support, g, heR, ne_eq, Complex.ofReal_eq_zero] using hm'.2
    refine ⟨⟨z, hg⟩, ?_⟩
    simp only [i, he, Int.toNat_natCast]
  have hfg (z : Function.support g) : f (i z) = g z := by
    have hc : Int.ModEq q (i z : ℤ) a := by
      rw [hcast]
      apply Int.modEq_iff_dvd.mpr
      exact ⟨-z.val, by ring⟩
    have hr : (i z : ℝ) = (a : ℝ) + (q : ℝ) * z.val := by
      exact_mod_cast hcast z
    simp only [f, hc, if_pos, hr, g]
  calc
    _ = ∑' m : ℕ, f m := by
      symm
      apply tsum_eq_sum
      intro m hm
      have hw : scaledDyadicCutoff M m = 0 := by
        by_contra hw
        exact hm (hS m hw)
      simp [f, hw]
    _ = _ := tsum_eq_tsum_of_ne_zero_bij i hi hf hfg

/-- Canonical finite-support specialization of the arithmetic lattice bridge. -/
theorem scaledDyadicCutoff_progression_eq_tsum
    {M : ℝ} (hM : 0 < M) {q : ℕ} (hq : 0 < q) (a : ℤ) :
    (∑ m ∈ dyadicCutoffNatSupport M, if Int.ModEq q (m : ℤ) a
      then (scaledDyadicCutoff M m : ℂ) else 0) =
        ∑' z : ℤ, (scaledDyadicCutoff M ((a : ℝ) + q * z) : ℂ) :=
  scaledDyadicCutoff_finset_progression_eq_tsum hM _
    (scaledDyadicCutoff_mem_natSupport hM) hq a

/-- The real zero-frequency mass of the fixed, scale-independent cutoff. -/
def dyadicCutoffMass : ℝ := ((𝓕 dyadicCutoffSchwartz) 0).re

/-- Uniform arithmetic progression error for every support-containing finite set. -/
theorem scaledDyadicCutoff_finset_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      |(∑ m ∈ S, if Int.ModEq q (m : ℤ) a then scaledDyadicCutoff M m else 0) -
          (M / q) * dyadicCutoffMass| ≤ C := by
  classical
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_poisson_uniform_error
  refine ⟨C, hC, fun M hM S hS q hq a ↦ ?_⟩
  have h := hbound M q hM (by exact_mod_cast hq) a
  rw [← scaledDyadicCutoff_finset_progression_eq_tsum hM S hS hq a] at h
  apply (Complex.abs_re_le_norm _).trans h |>.trans_eq'
  congr 1
  simp only [Complex.sub_re, Complex.re_sum, apply_ite, Complex.ofReal_re,
    Complex.zero_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero, dyadicCutoffMass]

/-- The same constant bounds each sum over multiples, with no scale restriction. -/
theorem scaledDyadicCutoff_finset_multiples_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ d : ℕ, 0 < d →
      |(∑ m ∈ S, if d ∣ m then scaledDyadicCutoff M m else 0) -
          (M / d) * dyadicCutoffMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS d hd ↦ ?_⟩
  simpa only [Int.modEq_zero_iff_dvd, Int.natCast_dvd_natCast]
    using hbound M hM S hS d hd 0

/-- Smooth coprime counting, obtained from the already proved finite Mobius
identity and density. The universal error is at most `C` times the divisor count. -/
theorem scaledDyadicCutoff_finset_coprime_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q : ℕ, q ≠ 0 →
      |(∑ m ∈ S, if m.Coprime q then scaledDyadicCutoff M m else 0) -
          (M * dyadicCutoffMass) * (q.totient : ℝ) / q| ≤ C * q.divisors.card := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_multiples_uniform_error
  refine ⟨C, hC, fun M hM S hS q hq ↦ ?_⟩
  calc
    _ = |∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then scaledDyadicCutoff M m else 0) -
          (M / d) * dyadicCutoffMass)| := by
      rw [coprime_weight_eq_moebius S _ hq, mul_div_assoc, ← moebius_density hq,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ q.divisors, |(ArithmeticFunction.moebius d : ℝ) *
        ((∑ m ∈ S, if d ∣ m then scaledDyadicCutoff M m else 0) -
          (M / d) * dyadicCutoffMass)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ q.divisors, C := by
      apply Finset.sum_le_sum
      intro d hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa using mul_le_mul hmu (hbound M hM S hS d (Nat.pos_of_mem_divisors hd))
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp [mul_comm]

/-- The canonical finite arithmetic progression has a universal `O(1)` error. -/
theorem scaledDyadicCutoff_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ q : ℕ, 0 < q → ∀ a : ℤ,
      |(∑ m ∈ dyadicCutoffNatSupport M,
          if Int.ModEq q (m : ℤ) a then scaledDyadicCutoff M m else 0) -
        (M / q) * dyadicCutoffMass| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_progression_uniform_error
  exact ⟨C, hC, fun M hM q hq a ↦
    hbound M hM _ (scaledDyadicCutoff_mem_natSupport hM) q hq a⟩

/-- The canonical finite coprime sum supplies the smooth U counting estimate. -/
theorem scaledDyadicCutoff_coprime_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ q : ℕ, q ≠ 0 →
      |(∑ m ∈ dyadicCutoffNatSupport M,
          if m.Coprime q then scaledDyadicCutoff M m else 0) -
        (M * dyadicCutoffMass) * (q.totient : ℝ) / q| ≤ C * q.divisors.card := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_coprime_uniform_error
  exact ⟨C, hC, fun M hM q hq ↦
    hbound M hM _ (scaledDyadicCutoff_mem_natSupport hM) q hq⟩

/-- Bezout inverses and the Chinese remainder theorem combine the divisibility
condition and the product congruence into one actual residue class. -/
theorem exists_progression_for_divisor_congruence {q d n : ℕ}
    (hd : d.Coprime q) (hn : n.Coprime q) (a : ℤ) :
    ∃ b : ℤ, ∀ m : ℕ,
      (d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a) ↔ Int.ModEq (q * d : ℕ) (m : ℤ) b := by
  obtain ⟨y, hy⟩ := Int.mod_coprime (Nat.coprime_mul_iff_left.mpr ⟨hd, hn⟩)
  obtain ⟨v, hv⟩ := Int.mod_coprime hn
  let b : ℤ := d * y * a
  have hb : Int.ModEq q (b * n) a := by
    simpa only [b, Nat.cast_mul, one_mul, mul_one, mul_assoc, mul_comm, mul_left_comm]
      using hy.mul_right a
  have hb0 : Int.ModEq d b 0 := Int.modEq_zero_iff_dvd.mpr ⟨y * a, by dsimp [b]; ring⟩
  refine ⟨b, fun m ↦ ?_⟩
  have hc : Int.ModEq q ((m : ℤ) * n) a ↔ Int.ModEq q (m : ℤ) b := by
    constructor
    · intro h
      have h' := (h.trans hb.symm).mul_right v
      have hm' : Int.ModEq q ((m : ℤ) * n * v) m := by
        simpa only [mul_assoc, mul_one] using hv.mul_left (m : ℤ)
      have hb' : Int.ModEq q (b * n * v) b := by
        simpa only [mul_assoc, mul_one] using hv.mul_left b
      exact hm'.symm.trans (h'.trans hb')
    · intro h
      exact (h.mul_right n).trans hb
  have hd' : d ∣ m ↔ Int.ModEq d (m : ℤ) b := by
    rw [← Int.natCast_dvd_natCast, ← Int.modEq_zero_iff_dvd]
    exact ⟨fun h ↦ h.trans hb0.symm, fun h ↦ h.trans hb0⟩
  rw [hc, hd', and_comm]
  exact Int.modEq_and_modEq_iff_modEq_mul (by simpa using hd.symm)

/-- A mixed divisibility/congruence sum is estimated using its constructed
residue class modulo `q * d`, not an assumed progression-count formula. -/
theorem scaledDyadicCutoff_finset_divisor_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q d n : ℕ, 0 < q → 0 < d → d.Coprime q → n.Coprime q → ∀ a : ℤ,
      |(∑ m ∈ S,
          if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then scaledDyadicCutoff M m else 0) -
        (M * dyadicCutoffMass / q) / d| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS q d n hq hd hdq hn a ↦ ?_⟩
  obtain ⟨b, hb⟩ := exists_progression_for_divisor_congruence hdq hn a
  have h := hbound M hM S hS (q * d) (Nat.mul_pos hq hd) b
  simp_rw [← hb] at h
  have he : (M * dyadicCutoffMass / q) / d = M / (q * d : ℕ) * dyadicCutoffMass := by
    push_cast
    ring
  rw [he]
  exact h

/-- Finite Mobius inversion for the mixed term. Divisors sharing a factor with
`q` cannot occur because the product is congruent to a reduced residue. -/
theorem coprime_product_progression_weight_eq_moebius
    (S : Finset ℕ) (w : ℕ → ℝ) {q r n : ℕ} (hr : r ≠ 0)
    {a : ℤ} (ha : Int.gcd a q = 1) :
    (∑ m ∈ S, if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0) =
      ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q), (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0 := by
  classical
  calc
    _ = ∑ d ∈ r.divisors, (ArithmeticFunction.moebius d : ℝ) *
        ∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0 := by
      simp only [ite_and]
      exact coprime_weight_eq_moebius S
        (fun m ↦ if Int.ModEq q ((m : ℤ) * n) a then w m else 0) hr
    _ = _ := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro d _
      by_cases hdq : d.Coprime q
      · simp only [if_pos hdq]
      · rw [if_neg hdq]
        have hz : (∑ m ∈ S,
            if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a then w m else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro m _
          apply if_neg
          intro hm
          exact hdq (Nat.Coprime.of_dvd_left hm.1 (coprime_of_product_congruent ha hm.2).1)
        rw [hz, mul_zero]

/-- The smooth arithmetic V estimate, uniformly in the scale, both moduli,
the reduced residue, the invertible multiplier, and the finite support set. -/
theorem scaledDyadicCutoff_finset_coprime_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ S : Finset ℕ,
      (∀ m : ℕ, scaledDyadicCutoff M m ≠ 0 → m ∈ S) →
      ∀ q r n : ℕ, 0 < q → r ≠ 0 → n.Coprime q → ∀ a : ℤ, Int.gcd a q = 1 →
      |(∑ m ∈ S, if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
          then scaledDyadicCutoff M m else 0) -
        (M * dyadicCutoffMass / q) *
          ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
            (ArithmeticFunction.moebius d : ℝ) / d| ≤ C * r.divisors.card := by
  classical
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_divisor_progression_uniform_error
  refine ⟨C, hC, fun M hM S hS q r n hq hr hn a ha ↦ ?_⟩
  calc
    _ = |∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        (ArithmeticFunction.moebius d : ℝ) *
          ((∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - (M * dyadicCutoffMass / q) / d)| := by
      rw [coprime_product_progression_weight_eq_moebius S _ hr ha,
        Finset.mul_sum, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      ring
    _ ≤ ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
        |(ArithmeticFunction.moebius d : ℝ) *
          ((∑ m ∈ S, if d ∣ m ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) - (M * dyadicCutoffMass / q) / d)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ r.divisors.filter (fun d ↦ d.Coprime q), C := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdr, hdq⟩ := Finset.mem_filter.mp hd
      rw [abs_mul]
      have hmu : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := d))
      simpa using mul_le_mul hmu
        (hbound M hM S hS q d n hq (Nat.pos_of_mem_divisors hdr) hdq hn a)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = C * (r.divisors.filter (fun d ↦ d.Coprime q)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (by exact_mod_cast Finset.card_filter_le r.divisors (fun d ↦ d.Coprime q)) hC.le

/-- Canonical finite-support version of the arithmetic V estimate. -/
theorem scaledDyadicCutoff_coprime_progression_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M →
      ∀ q r n : ℕ, 0 < q → r ≠ 0 → n.Coprime q → ∀ a : ℤ, Int.gcd a q = 1 →
      |(∑ m ∈ dyadicCutoffNatSupport M,
          if m.Coprime r ∧ Int.ModEq q ((m : ℤ) * n) a
            then scaledDyadicCutoff M m else 0) -
        (M * dyadicCutoffMass / q) *
          ∑ d ∈ r.divisors.filter (fun d ↦ d.Coprime q),
            (ArithmeticFunction.moebius d : ℝ) / d| ≤ C * r.divisors.card := by
  obtain ⟨C, hC, hbound⟩ := scaledDyadicCutoff_finset_coprime_progression_uniform_error
  exact ⟨C, hC, fun M hM q r n hq hr hn a ha ↦
    hbound M hM _ (scaledDyadicCutoff_mem_natSupport hM) q r n hq hr hn a ha⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
