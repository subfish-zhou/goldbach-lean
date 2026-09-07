import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryArithmeticPoisson

/-!
# The full, unpruned W zero frequency

This is the signed finite expansion of Fouvry (1984), p. 235, (8.1), followed
by CRT and exact Poisson extraction. It supplies the zero-frequency content
underlying p. 238, (8.11), before any truncation or five-gcd pruning. It does
not identify the raw main term with the already-pruned expression (8.11).
The oscillatory remainder is retained. The crude uniform coefficient envelope
is not the Fouvry (1987) distribution estimate. No WF/SW or spectral estimate
is used, and neither (8.25) nor (9.1) is imported.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

/-- Cancellation uses a genuine Bezout inverse, including for integer operands. -/
theorem product_modEq_iff_of_coprime {q n : ℕ} (hn : n.Coprime q)
    {a b m : ℤ} (hb : Int.ModEq q (b * n) a) :
    Int.ModEq q (m * n) a ↔ Int.ModEq q m b := by
  obtain ⟨v, hv⟩ := Int.mod_coprime hn
  constructor
  · intro h
    have hm' : Int.ModEq q (m * n * v) m := by
      simpa only [mul_assoc, mul_one] using hv.mul_left m
    have hb' : Int.ModEq q (b * n * v) b := by
      simpa only [mul_assoc, mul_one] using hv.mul_left b
    exact hm'.symm.trans (((h.trans hb.symm).mul_right v).trans hb')
  · intro h
    exact (h.mul_right n).trans hb

/-- A common integer solution forces equality of the multipliers modulo the gcd.
Only reducedness modulo `q` is needed for this direction. -/
theorem product_congruences_compatible {q r n₁ n₂ : ℕ} (hq : 0 < q)
    {a m : ℤ} (ha : Int.gcd a q = 1)
    (h₁ : Int.ModEq q (m * n₁) a) (h₂ : Int.ModEq r (m * n₂) a) :
    Nat.ModEq (q.gcd r) n₁ n₂ := by
  have hdq : (q.gcd r : ℤ) ∣ q := by exact_mod_cast Nat.gcd_dvd_left q r
  have hdr : (q.gcd r : ℤ) ∣ r := by exact_mod_cast Nat.gcd_dvd_right q r
  have hag : Int.gcd a (q.gcd r) = 1 :=
    Nat.dvd_one.mp (ha ▸ Int.gcd_dvd_gcd_of_dvd_right a hdq)
  have hcross : Int.ModEq (q.gcd r) (a * n₁) (a * n₂) := by
    have hleft := (h₂.of_dvd hdr).mul_right (n₁ : ℤ)
    have hright := (h₁.of_dvd hdq).mul_right (n₂ : ℤ)
    exact hleft.symm.trans (by simpa [mul_assoc, mul_comm, mul_left_comm] using hright)
  have hgpos : (0 : ℤ) < q.gcd r := by
    exact_mod_cast Nat.gcd_pos_of_pos_left r hq
  apply Int.natCast_modEq_iff.mp
  simpa only [Int.gcd_comm (q.gcd r : ℤ) a, hag, Nat.cast_one, Int.ediv_one]
    using hcross.cancel_left_div_gcd hgpos

/-- General (not necessarily coprime-modulus) CRT constructs the multiplier
first; its Bezout inverse constructs an actual common product residue. -/
theorem exists_product_crt_residue {q r n₁ n₂ : ℕ}
    (h₁ : n₁.Coprime q) (h₂ : n₂.Coprime r)
    (hc : Nat.ModEq (q.gcd r) n₁ n₂) (a : ℤ) :
    ∃ b : ℤ, Int.ModEq q (b * n₁) a ∧ Int.ModEq r (b * n₂) a ∧
      ∀ m : ℤ, (Int.ModEq q (m * n₁) a ∧ Int.ModEq r (m * n₂) a) ↔
        Int.ModEq (q.lcm r) m b := by
  let t := Nat.chineseRemainder' hc
  have htq : t.val.Coprime q := by
    change t.val.gcd q = 1
    rw [t.property.1.gcd_eq, h₁.gcd_eq_one]
  have htr : t.val.Coprime r := by
    change t.val.gcd r = 1
    rw [t.property.2.gcd_eq, h₂.gcd_eq_one]
  obtain ⟨v, hv⟩ := Int.mod_coprime
    ((htq.mul_right htr).of_dvd_right (Nat.lcm_dvd_mul q r))
  let b : ℤ := a * v
  have hb : Int.ModEq (q.lcm r) (b * t.val) a := by
    simpa only [b, mul_assoc, mul_comm, mul_left_comm, mul_one, one_mul]
      using hv.mul_left a
  have hbq : Int.ModEq q (b * n₁) a :=
    ((Int.natCast_modEq_iff.mpr t.property.1).symm.mul_left b).trans
      (hb.of_dvd (by exact_mod_cast Nat.dvd_lcm_left q r))
  have hbr : Int.ModEq r (b * n₂) a :=
    ((Int.natCast_modEq_iff.mpr t.property.2).symm.mul_left b).trans
      (hb.of_dvd (by exact_mod_cast Nat.dvd_lcm_right q r))
  refine ⟨b, hbq, hbr, fun m ↦ ?_⟩
  rw [product_modEq_iff_of_coprime h₁ hbq, product_modEq_iff_of_coprime h₂ hbr]
  simpa only [Int.lcm, Int.natAbs_natCast] using
    (Int.modEq_and_modEq_iff_modEq_lcm (a := m) (b := b) (m := q) (n := r))

/-- Solvability over all integers is exactly the gcd compatibility condition. -/
theorem exists_product_congruences_iff {q r n₁ n₂ : ℕ} (hq : 0 < q)
    (h₁ : n₁.Coprime q) (h₂ : n₂.Coprime r) {a : ℤ}
    (ha : Int.gcd a q = 1) :
    (∃ m : ℤ, Int.ModEq q (m * n₁) a ∧ Int.ModEq r (m * n₂) a) ↔
      Nat.ModEq (q.gcd r) n₁ n₂ := by
  constructor
  · rintro ⟨m, hm₁, hm₂⟩
    exact product_congruences_compatible hq ha hm₁ hm₂
  · intro hc
    obtain ⟨b, hb₁, hb₂, _⟩ := exists_product_crt_residue h₁ h₂ hc a
    exact ⟨b, hb₁, hb₂⟩

/-- The original, unpruned inner sum in (8.1). -/
def productProgressionWeight (S : Finset ℕ) (w : ℕ → ℝ) (a : ℤ)
    (q r n₁ n₂ : ℕ) : ℝ :=
  ∑ m ∈ S, if Int.ModEq q ((m : ℤ) * n₁) a ∧
    Int.ModEq r ((m : ℤ) * n₂) a then w m else 0

theorem productProgressionWeight_eq_zero_of_incompatible
    (S : Finset ℕ) (w : ℕ → ℝ) {q r n₁ n₂ : ℕ} (hq : 0 < q)
    {a : ℤ} (ha : Int.gcd a q = 1) (hc : ¬Nat.ModEq (q.gcd r) n₁ n₂) :
    productProgressionWeight S w a q r n₁ n₂ = 0 := by
  apply Finset.sum_eq_zero
  intro m _
  exact if_neg fun h ↦ hc (product_congruences_compatible hq ha h.1 h.2)

private theorem progressionRow_eq_unrestricted (N Q : Finset ℕ)
    (β c : ℕ → ℝ) (a : ℤ) (m : ℕ) :
    progressionRow N Q β c a m =
      ∑ q ∈ reducedModuli Q a, c q * progressionMass N β a q m := by
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hm : m.Coprime q
  · simp only [if_pos hm]
  · rw [if_neg hm, progressionMass_eq_zero_of_not_coprime N β
      (Finset.mem_filter.mp hq).2 hm, mul_zero]

/-- Literal expansion of the actual signed dispersion W, before gcd pruning
or frequency truncation. Both necessary multiplier coprimalities are retained. -/
theorem dispersionW_eq_product_progression_sum
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ) :
    dispersionW S N Q w β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        ∑ n₁ ∈ N, ∑ n₂ ∈ N,
          if n₁.Coprime q ∧ n₂.Coprime r then
            (c q * c r * β n₁ * β n₂) * productProgressionWeight S w a q r n₁ n₂
          else 0 := by
  unfold dispersionW
  simp_rw [progressionRow_eq_unrestricted, pow_two, Finset.sum_mul_sum,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp_rw [progressionMass, mul_assoc, Finset.mul_sum, Finset.sum_mul,
    Finset.mul_sum]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2
    ext n
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hn : n₁.Coprime q ∧ n₂.Coprime r
  · rw [if_pos hn]
    unfold productProgressionWeight
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    split_ifs <;> simp_all
    ring
  · rw [if_neg hn]
    apply Finset.sum_eq_zero
    intro m _
    have hc : ¬(Int.ModEq q ((m : ℤ) * n₁) a ∧
        Int.ModEq r ((m : ℤ) * n₂) a) := fun h ↦ hn
      ⟨(coprime_of_product_congruent (Finset.mem_filter.mp hq).2 h.1).2,
        (coprime_of_product_congruent (Finset.mem_filter.mp hr).2 h.2).2⟩
    split_ifs <;> simp_all

/-- Exactly the arithmetic restrictions forced by the two product congruences. -/
def WCompatible (q r n₁ n₂ : ℕ) : Prop :=
  n₁.Coprime q ∧ n₂.Coprime r ∧ Nat.ModEq (q.gcd r) n₁ n₂

instance wCompatibleDecidable (q r n₁ n₂ : ℕ) : Decidable (WCompatible q r n₁ n₂) :=
  inferInstanceAs (Decidable (n₁.Coprime q ∧ n₂.Coprime r ∧ Nat.ModEq (q.gcd r) n₁ n₂))

/-- A representative chosen from the proved CRT construction, not a supplied
progression-representation premise. Its value on incompatible inputs is unused. -/
def productCRTResidue (q r n₁ n₂ : ℕ) (a : ℤ) : ℤ :=
  if h : WCompatible q r n₁ n₂ then
    Classical.choose (exists_product_crt_residue h.1 h.2.1 h.2.2 a)
  else 0

theorem productCRTResidue_spec {q r n₁ n₂ : ℕ} (a : ℤ)
    (hc : WCompatible q r n₁ n₂) :
    Int.ModEq q (productCRTResidue q r n₁ n₂ a * n₁) a ∧
      Int.ModEq r (productCRTResidue q r n₁ n₂ a * n₂) a ∧
      ∀ m : ℤ, (Int.ModEq q (m * n₁) a ∧ Int.ModEq r (m * n₂) a) ↔
        Int.ModEq (q.lcm r) m (productCRTResidue q r n₁ n₂ a) := by
  simpa only [productCRTResidue, dif_pos hc] using
    Classical.choose_spec (exists_product_crt_residue hc.1 hc.2.1 hc.2.2 a)

theorem productProgressionWeight_eq_crt_progression
    (S : Finset ℕ) (w : ℕ → ℝ) (a : ℤ) {q r n₁ n₂ : ℕ}
    (hc : WCompatible q r n₁ n₂) :
    productProgressionWeight S w a q r n₁ n₂ =
      ∑ m ∈ S, if Int.ModEq (q.lcm r) (m : ℤ) (productCRTResidue q r n₁ n₂ a)
        then w m else 0 := by
  unfold productProgressionWeight
  simp_rw [(productCRTResidue_spec a hc).2.2]

/-- Incompatible pairs vanish identically; no estimated or pruned term is lost. -/
theorem dispersionW_eq_compatible_sum
    (S N Q : Finset ℕ) (w β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    dispersionW S N Q w β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        ∑ n₁ ∈ N, ∑ n₂ ∈ N,
          if WCompatible q r n₁ n₂ then
            (c q * c r * β n₁ * β n₂) * productProgressionWeight S w a q r n₁ n₂
          else 0 := by
  classical
  rw [dispersionW_eq_product_progression_sum]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hc : Nat.ModEq (q.gcd r) n₁ n₂
  · simp only [WCompatible, hc, and_true]
  · rw [productProgressionWeight_eq_zero_of_incompatible S w
      (Nat.pos_of_ne_zero (hQ q (Finset.mem_filter.mp hq).1))
      (Finset.mem_filter.mp hq).2 hc]
    simp [WCompatible, hc]

/-- The real finite progression identity with its full oscillatory error. -/
theorem scaledDyadicCutoff_progression_eq_main_add_fourier
    {M : ℝ} (hM : 0 < M) {q : ℕ} (hq : 0 < q) (b : ℤ) :
    (∑ m ∈ dyadicCutoffNatSupport M,
      if Int.ModEq q (m : ℤ) b then scaledDyadicCutoff M m else 0) =
        (M / q) * dyadicCutoffMass +
          (∑' h : ℤ, dyadicCutoffPoissonRemainder (M / q) ((b : ℝ) / q) h).re := by
  have he := congrArg Complex.re
    (scaledDyadicCutoff_poisson_mainTerm (D := (q : ℝ)) hM
      (by exact_mod_cast hq) (b : ℝ))
  rw [← scaledDyadicCutoff_progression_eq_tsum hM hq b] at he
  simp only [Complex.sub_re, Complex.re_sum, apply_ite, Complex.ofReal_re,
    Complex.zero_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_im,
    zero_mul, sub_zero] at he
  exact (sub_eq_iff_eq_add.mp he).trans (add_comm _ _)

/-- The phase uses the actual constructed CRT residue modulo the lcm. -/
def wPoissonFrequency (M : ℝ) (a : ℤ) (q r n₁ n₂ : ℕ) (h : ℤ) : ℂ :=
  dyadicCutoffPoissonRemainder (M / (q.lcm r))
    ((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r)) h

@[simp] theorem wPoissonFrequency_zero
    (M : ℝ) (a : ℤ) (q r n₁ n₂ : ℕ) :
    wPoissonFrequency M a q r n₁ n₂ 0 = 0 := rfl

/-- Absolute convergence holds without a modulus-versus-scale restriction. -/
theorem wPoissonFrequency_summable_norm {M : ℝ} (hM : 0 < M)
    (a : ℤ) {q r : ℕ} (hq : q ≠ 0) (hr : r ≠ 0) (n₁ n₂ : ℕ) :
    Summable (fun h : ℤ ↦ ‖wPoissonFrequency M a q r n₁ n₂ h‖) := by
  obtain ⟨C, _, hbound⟩ := dyadicCutoffPoissonRemainder_uniform
  exact (hbound (M / (q.lcm r))
    (div_pos hM (by exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq hr)))
    ((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r))).1

theorem productProgressionWeight_eq_main_add_fourier
    {M : ℝ} (hM : 0 < M) (a : ℤ) {q r n₁ n₂ : ℕ}
    (hq : q ≠ 0) (hr : r ≠ 0) (hc : WCompatible q r n₁ n₂) :
    productProgressionWeight (dyadicCutoffNatSupport M)
        (fun m ↦ scaledDyadicCutoff M m) a q r n₁ n₂ =
      (M / (q.lcm r)) * dyadicCutoffMass +
        (∑' h : ℤ, wPoissonFrequency M a q r n₁ n₂ h).re := by
  rw [productProgressionWeight_eq_crt_progression _ _ a hc]
  exact scaledDyadicCutoff_progression_eq_main_add_fourier hM
    (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hq hr)) _

/-- The full raw zero mode; all original coefficient signs are retained.
No five-gcd restrictions or truncation errors have yet been introduced. -/
def smoothWMain (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  (M * dyadicCutoffMass) *
    ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
      (c q * c r / (q.lcm r : ℝ)) *
        ∑ n₁ ∈ N, ∑ n₂ ∈ N,
          if WCompatible q r n₁ n₂ then β n₁ * β n₂ else 0

/-- An exact nonzero-frequency remainder, not an absolute-value substitute. -/
def smoothWNonzeroMode (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    ∑ n₁ ∈ N, ∑ n₂ ∈ N,
      if WCompatible q r n₁ n₂ then
        (c q * c r * β n₁ * β n₂) * (∑' h : ℤ, wPoissonFrequency M a q r n₁ n₂ h).re
      else 0

theorem smoothWMain_eq_compatible_sum
    (M : ℝ) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    smoothWMain M N Q β c a =
      ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
        ∑ n₁ ∈ N, ∑ n₂ ∈ N,
          if WCompatible q r n₁ n₂ then
            (c q * c r * β n₁ * β n₂) * ((M / (q.lcm r)) * dyadicCutoffMass)
          else 0 := by
  classical
  unfold smoothWMain
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  split_ifs <;> ring

/-- Exact full W = raw zero mode + the CRT-phase nonzero Fourier remainder.
The residue `a` is arbitrary and may vary with all other inputs. -/
theorem dispersionW_eq_smoothWMain_add_nonzeroMode
    {M : ℝ} (hM : 0 < M) (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ)
    (hQ : ∀ q ∈ Q, q ≠ 0) :
    dispersionW (dyadicCutoffNatSupport M) N Q
        (fun m ↦ scaledDyadicCutoff M m) β c a =
      smoothWMain M N Q β c a + smoothWNonzeroMode M N Q β c a := by
  classical
  rw [dispersionW_eq_compatible_sum _ _ _ _ _ _ _ hQ,
    smoothWMain_eq_compatible_sum]
  unfold smoothWNonzeroMode
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro n₁ _
  apply Finset.sum_congr rfl
  intro n₂ _
  by_cases hc : WCompatible q r n₁ n₂
  · simp only [if_pos hc]
    rw [productProgressionWeight_eq_main_add_fourier hM a
      (hQ q (Finset.mem_filter.mp hq).1) (hQ r (Finset.mem_filter.mp hr).1) hc]
    ring
  · simp only [if_neg hc, add_zero]

/-- The unpruned absolute coefficient envelope. Its growth is not estimated. -/
def smoothWErrorEnvelope (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) : ℝ :=
  ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
    ∑ n₁ ∈ N, ∑ n₂ ∈ N,
      if WCompatible q r n₁ n₂ then |c q * c r * β n₁ * β n₂| else 0

theorem smoothWErrorEnvelope_nonneg
    (N Q : Finset ℕ) (β c : ℕ → ℝ) (a : ℤ) :
    0 ≤ smoothWErrorEnvelope N Q β c a := by
  classical
  exact Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
      by split_ifs <;> positivity

/-- A universal coarse error bound, chosen before every arithmetic input.
This is not sufficient for the F87 distribution theorem: the exact oscillatory
remainder above still needs cancellation estimates. -/
theorem dispersionW_smooth_uniform_error :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℝ, 0 < M → ∀ N Q : Finset ℕ,
      ∀ β c : ℕ → ℝ, ∀ a : ℤ, (∀ q ∈ Q, q ≠ 0) →
      |dispersionW (dyadicCutoffNatSupport M) N Q
          (fun m ↦ scaledDyadicCutoff M m) β c a - smoothWMain M N Q β c a| ≤
        C * smoothWErrorEnvelope N Q β c a := by
  classical
  obtain ⟨C, hC, hbound⟩ := dyadicCutoffPoissonRemainder_uniform
  refine ⟨C, hC, fun M hM N Q β c a hQ ↦ ?_⟩
  rw [dispersionW_eq_smoothWMain_add_nonzeroMode hM N Q β c a hQ,
    add_sub_cancel_left]
  unfold smoothWNonzeroMode smoothWErrorEnvelope
  simp only [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q hq
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro r hr
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n₁ _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro n₂ _
  by_cases hc : WCompatible q r n₁ n₂
  · simp only [if_pos hc]
    rw [abs_mul]
    have hp : 0 < (q.lcm r : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Nat.lcm_ne_zero
        (hQ q (Finset.mem_filter.mp hq).1) (hQ r (Finset.mem_filter.mp hr).1))
    have hb := (hbound (M / (q.lcm r)) (div_pos hM hp)
      ((productCRTResidue q r n₁ n₂ a : ℝ) / (q.lcm r))).2
    calc
      _ ≤ |c q * c r * β n₁ * β n₂| * C :=
        mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans hb) (abs_nonneg _)
      _ = _ := by ring
  · simp only [if_neg hc, abs_zero, mul_zero, le_refl]

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
