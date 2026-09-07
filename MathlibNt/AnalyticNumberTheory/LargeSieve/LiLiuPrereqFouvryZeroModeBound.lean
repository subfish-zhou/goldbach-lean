import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryHighDeltaWeights

/-!
# Full zero-mode estimate with the lcm weight retained

The all-positive-modulus beta-AP input in F87 (1.3) is applied at the actual
gcd, without a small/large gcd split. A fixed-order divisor majorant and the
harmonic lcm mean pay all modulus weights. This estimates the full unpruned
W zero mode minus U zero mode, not the nonzero Fourier remainder.
-/

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Finset

noncomputable section

theorem one_le_fouvryTau_succ (κ : ℕ) {q : ℕ} (hq : q ≠ 0) :
    1 ≤ fouvryTau (κ + 1) q := by
  rw [fouvryTau_succ]
  simpa only [fouvryTau_one] using
    (single_le_sum (f := fun d => fouvryTau κ d) (fun _ _ => Nat.zero_le _)
      (Nat.mem_divisors.mpr ⟨one_dvd q, hq⟩))

/-- The extra sieve-order weight costs only a fixed logarithmic power.
The successor majorant is essential at order zero, where `tau_0` itself
need not be at least one. No gcd is replaced by a cutoff. -/
theorem sum_abs_lcm_weight_mul_quotient_tau_le_log
    (j κ : ℕ) {L : ℝ} (hL : 1 ≤ L)
    (Q : Finset ℕ) (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (c : ℕ → ℝ)
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) :
    (∑ q ∈ Q, ∑ r ∈ Q,
      |c q * c r / (q.lcm r : ℝ)| *
        (fouvryTau κ (q / q.gcd r) : ℝ)) ≤
      (1 + Real.log L) ^ (2 * (j * (κ + 1)) ^ 2 + 1) := by
  let w : ℕ → ℝ := fun q => |c q| * (fouvryTau (κ + 1) q : ℝ)
  have hw (q : ℕ) : 0 ≤ w q := by dsimp [w]; positivity
  have hcw : ∀ q ∈ Q, |c q| ≤ w q := by
    intro q hq
    exact le_mul_of_one_le_right (abs_nonneg _) (by
      exact_mod_cast one_le_fouvryTau_succ κ (mem_Ioc.mp (hQ hq)).1.ne')
  calc
    _ ≤ ∑ q ∈ Q, ∑ r ∈ Q, |w q * w r / (q.lcm r : ℝ)| := by
      apply sum_le_sum
      intro q hq
      apply sum_le_sum
      intro r hr
      rw [abs_div, abs_mul, Nat.abs_cast,
        abs_of_nonneg (by positivity : 0 ≤ w q * w r / (q.lcm r : ℝ))]
      calc
        _ = (|c q| * (fouvryTau κ (q / q.gcd r) : ℝ)) *
            |c r| / (q.lcm r : ℝ) := by ring
        _ ≤ w q * w r / (q.lcm r : ℝ) := by
          apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
          apply mul_le_mul _ (hcw r hr) (abs_nonneg _) (hw q)
          exact mul_le_mul_of_nonneg_left (by
            exact_mod_cast fouvryTau_div_le_succ κ (mem_Ioc.mp (hQ hq)).1.ne'
              (Nat.gcd_dvd_left q r)) (abs_nonneg _)
    _ ≤ _ := by
      apply sum_abs_lcm_weight_le_log (j * (κ + 1)) hL Q hQ w
      intro q hq
      rw [abs_of_nonneg (hw q)]
      exact (mul_le_mul_of_nonneg_right (hc q hq) (Nat.cast_nonneg _)).trans
        (by exact_mod_cast fouvryTau_mul_le j (κ + 1) q)

/-- An independent AP bound, applied at every divisor of the given moduli,
pays the entire signed covariance sum. In particular no intermediate-gcd
error is left in this estimate. -/
theorem smoothWMain_sub_smoothUMain_abs_le_coprimeAP_lcm
    {k : ℕ} (hk : 1 ≤ k) (j κ : ℕ)
    {T L E : ℝ} (hT : 1 ≤ T) (hL : 1 ≤ L) (hE : 0 ≤ E)
    (M : ℝ) (N Q : Finset ℕ) (hN : N ⊆ Ioc 0 ⌊T⌋₊)
    (hQ : Q ⊆ Ioc 0 ⌊L⌋₊) (β c : ℕ → ℝ)
    (hβ : ∀ n ∈ N, |β n| ≤ (fouvryTau k n : ℝ))
    (hc : ∀ q ∈ Q, |c q| ≤ (fouvryTau j q : ℝ)) (a : ℤ)
    (hAP : ∀ q ∈ Q, ∀ δ : ℕ, δ ∣ q → 0 < δ →
      ∀ b ∈ betaReducedResidues δ,
        |betaCoprimeAPDiscrepancy N β δ (q / δ) b| ≤
          E * (fouvryTau κ (q / δ) : ℝ)) :
    |smoothWMain M N Q β c a - smoothUMain M N Q β c a| ≤
      2 * |M * dyadicCutoffMass| * E *
        (T * (1 + Real.log T) ^ (k - 1)) *
        (1 + Real.log L) ^ (2 * (j * (κ + 1)) ^ 2 + 1) := by
  let V := T * (1 + Real.log T) ^ (k - 1)
  have hV : 0 ≤ V := by
    dsimp [V]
    have := Real.log_nonneg hT
    positivity
  have hQ0 : ∀ q ∈ Q, q ≠ 0 := fun q hq => (mem_Ioc.mp (hQ hq)).1.ne'
  have hcov : ∀ q ∈ reducedModuli Q a, ∀ r ∈ reducedModuli Q a,
      |betaCovariance N β q r| ≤
        2 * (E * (fouvryTau κ (q / q.gcd r) : ℝ)) * V := by
    intro q hq r _
    have hq0 := Nat.pos_of_ne_zero (hQ0 q (mem_filter.mp hq).1)
    apply (betaCovariance_abs_le_coprimeAP_lone N β hq0
      (by positivity) (hAP q (mem_filter.mp hq).1 _
        (Nat.gcd_dvd_left q r) (Nat.gcd_pos_of_pos_left r hq0))).trans
    exact mul_le_mul_of_nonneg_left (sum_abs_le_fouvryTau_mean hk hT N hN β hβ)
      (by positivity)
  rw [smoothWMain_sub_smoothUMain_eq_betaCovariance M N Q β c a hQ0, abs_mul]
  calc
    _ ≤ |M * dyadicCutoffMass| *
        ∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          (2 * E * V) * (|c q * c r / (q.lcm r : ℝ)| *
            (fouvryTau κ (q / q.gcd r) : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro q hq
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro r hr
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hcov q hq r hr) (abs_nonneg _)).trans_eq
        (by ring)
    _ = |M * dyadicCutoffMass| * (2 * E * V) *
        (∑ q ∈ reducedModuli Q a, ∑ r ∈ reducedModuli Q a,
          |c q * c r / (q.lcm r : ℝ)| *
            (fouvryTau κ (q / q.gcd r) : ℝ)) := by simp only [mul_sum, mul_assoc]
    _ ≤ |M * dyadicCutoffMass| * (2 * E * V) *
        (1 + Real.log L) ^ (2 * (j * (κ + 1)) ^ 2 + 1) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_abs_lcm_weight_mul_quotient_tau_le_log j κ hL (reducedModuli Q a)
        ((filter_subset _ _).trans hQ) c (fun q hq => hc q (mem_filter.mp hq).1)
    _ = _ := by ring

end

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
