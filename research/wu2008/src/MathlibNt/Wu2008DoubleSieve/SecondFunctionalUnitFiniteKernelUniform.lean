import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitFiniteKernelBound

open scoped BigOperators Classical Topology
namespace SecondFunctionalUnitFiniteKernel
open SecondFunctionalUnitPrimeFibre Wu2008DoubleSieve LiLiuPrereqBuchstab Real Finset Filter

/-- Dimension and tolerance precede the scale; all finite masks and moving gates follow it. -/
theorem L1_uniform (m : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R →
      ∀ (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ),
        L1 R S phi b ≤ epsilon := by
  let A : ℝ := 5^(m+1)
  let B : ℝ := 5^m
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  let tau : ℝ := min 1 (epsilon / (80*A))
  let eta : ℝ := epsilon / (4800*B)
  have ht : 0 < tau := lt_min (by norm_num) (div_pos he (by positivity))
  have ht1 : tau ≤ 1 := min_le_left _ _
  have heta : 0 < eta := div_pos he (by positivity)
  have htpay : tau * (80*A) ≤ epsilon :=
    (le_div_iff₀ (by positivity : 0 < 80*A)).mp (min_le_right _ _)
  have hepay : eta * (4800*B) = epsilon := by
    exact div_mul_cancel₀ epsilon (ne_of_gt (by positivity : 0 < 4800*B))
  have hsmall : A*(20*tau) + 60*B*(20*eta) < epsilon := by nlinarith
  have hlim : Tendsto (fun R : ℝ => A*(20*tau + 20*R^(-eta)) +
      60*B*(20*eta + primeOrderedDiscrepancy R)) atTop
      (nhds (A*(20*tau) + 60*B*(20*eta))) := by
    simpa only [mul_zero, add_zero] using
      ((tendsto_const_nhds.add ((tendsto_rpow_neg_atTop heta).const_mul 20)).const_mul A).add
        ((tendsto_const_nhds.add primeOrderedDiscrepancy_tendsto).const_mul (60*B))
  have hall : ∀ᶠ R : ℝ in atTop, 1 < R ∧
      ∀ (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ),
        L1 R S phi b ≤ epsilon := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), L1_eventually_bound tau eta ht ht1 heta,
      hlim.eventually (gt_mem_nhds hsmall)] with R hR hbound hsmallR
    exact ⟨hR, fun S phi b => (hbound m S phi b).trans hsmallR.le⟩
  obtain ⟨T,hT⟩ := eventually_atTop.mp hall
  refine ⟨max T 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro R hR
  exact (hT R ((le_max_left T 2).trans hR)).2

/-- Exact reweighting is consumed before the finite triangle inequality. -/
theorem physical_error_le_L1 {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ) :
    |log R / R^phi *
      (∑ f ∈ S, ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) -
      ∑ f ∈ S, primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
        (coordinate f (Fin.last m)) b| ≤ L1 R S phi b := by
  rw [reweight_sum hR S (Fin.last m) phi b, ← sum_sub_distrib]
  calc
    _ ≤ ∑ f ∈ S, |primeSlabWeight R f * weight R (phi - ∑ i, coordinate f i)
        (coordinate f (Fin.last m)) b - primeSlabWeight R f *
        F (phi - ∑ i, coordinate f i) (coordinate f (Fin.last m)) b| := abs_sum_le_sum_abs _ _
    _ = L1 R S phi b := by
      apply sum_congr rfl
      intro f hf
      rw [← mul_sub, abs_mul, abs_of_nonneg (show 0 ≤ primeSlabWeight R f by
        unfold primeSlabWeight; positivity)]

/-- Joint endpoint: the identical threshold pays L1 and the literal closed physical count. -/
theorem physical_uniform (m : ℕ) (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R →
      ∀ (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ),
        L1 R S phi b ≤ epsilon ∧
        |log R / R^phi *
          (∑ f ∈ S, ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) -
          ∑ f ∈ S, primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
            (coordinate f (Fin.last m)) b| ≤ epsilon := by
  obtain ⟨T,hT,h⟩ := L1_uniform m epsilon he
  exact ⟨T,hT,fun R hR S phi b => ⟨h R hR S phi b,
    (physical_error_le_L1 (hT.trans_le hR) S phi b).trans (h R hR S phi b)⟩⟩

theorem physical_fin4 (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R →
      ∀ (S : Finset (Fin 4 → primeSlabPrimes R)) (phi b : ℝ),
        |log R / R^phi *
          (∑ f ∈ S, ((physical (prefixProduct f) (R^phi) (f (Fin.last 3)).val (R^b)).card : ℝ)) -
          ∑ f ∈ S, primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
            (coordinate f (Fin.last 3)) b| ≤ epsilon := by
  obtain ⟨T,hT,h⟩ := physical_uniform 3 epsilon he
  exact ⟨T,hT,fun R hR S phi b => (h R hR S phi b).2⟩

theorem physical_fin5 (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R →
      ∀ (S : Finset (Fin 5 → primeSlabPrimes R)) (phi b : ℝ),
        |log R / R^phi *
          (∑ f ∈ S, ((physical (prefixProduct f) (R^phi) (f (Fin.last 4)).val (R^b)).card : ℝ)) -
          ∑ f ∈ S, primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
            (coordinate f (Fin.last 4)) b| ≤ epsilon := by
  obtain ⟨T,hT,h⟩ := physical_uniform 4 epsilon he
  exact ⟨T,hT,fun R hR S phi b => (h R hR S phi b).2⟩

theorem L1_empty (m : ℕ) (R phi b : ℝ) :
    L1 R (∅ : Finset (Fin (m+1) → primeSlabPrimes R)) phi b = 0 := by
  simp [L1]

/-- The cap-order branch is empty in the original physical fibre, not a deleted source. -/
theorem physical_empty_order {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin (m+1) → primeSlabPrimes R) (phi b : ℝ)
    (hb : b ≤ coordinate f (Fin.last m)) :
    physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b) = ∅ := by
  rw [physical_power_eq hR f (Fin.last m) phi b]
  exact fibre_empty (rpow_nonneg (by linarith) _)
    (rpow_le_rpow_of_exponent_le hR.le ((min_le_right _ _).trans hb))

/-- Membership keeps the strict prime lower bound and both original closed upper bounds. -/
theorem physical_membership {m : ℕ} {R : ℝ} (hR : 1 < R)
    (f : Fin (m+1) → primeSlabPrimes R) (phi b : ℝ) (p : ℕ) :
    p ∈ physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b) ↔
      p.Prime ∧ ((f (Fin.last m)).val : ℝ) < (p : ℝ) ∧
      (p : ℝ) ≤ R^b ∧ prefixProduct f * (p : ℝ) ≤ R^phi := by
  simp only [physical, mem_filter, mem_primesIcc (rpow_nonneg (by linarith : 0 ≤ R) b)]
  constructor
  · rintro ⟨⟨hp,_,hb⟩,hl,hx⟩
    exact ⟨hp,hl,hb,hx⟩
  · rintro ⟨hp,hl,hb,hx⟩
    exact ⟨⟨hp,Nat.cast_nonneg _,hb⟩,hl,hx⟩

theorem physical_sum_empty (m : ℕ) (R phi b : ℝ) :
    log R / R^phi *
      (∑ f ∈ (∅ : Finset (Fin (m+1) → primeSlabPrimes R)),
        ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) -
      ∑ f ∈ (∅ : Finset (Fin (m+1) → primeSlabPrimes R)),
        primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
          (coordinate f (Fin.last m)) b = 0 := by simp

/-- An exact zero branch, derived without deleting any physical prime or any prefix. -/
theorem degenerate_sum {m : ℕ} {R : ℝ} (hR : 1 < R)
    (S : Finset (Fin (m+1) → primeSlabPrimes R)) (phi b : ℝ)
    (hb : ∀ f ∈ S, b ≤ coordinate f (Fin.last m)) :
    L1 R S phi b = 0 ∧
      (∑ f ∈ S, ((physical (prefixProduct f) (R^phi) (f (Fin.last m)).val (R^b)).card : ℝ)) = 0 ∧
      (∑ f ∈ S, primeSlabWeight R f * F (phi - ∑ i, coordinate f i)
        (coordinate f (Fin.last m)) b) = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · apply sum_eq_zero
    intro f hf
    rw [weight_empty_order hR (hb f hf), F_empty_order (hb f hf)]
    simp
  · apply sum_eq_zero
    intro f hf
    rw [physical_empty_order hR f phi b (hb f hf)]
    simp
  · apply sum_eq_zero
    intro f hf
    rw [F_empty_order (hb f hf), mul_zero]
end SecondFunctionalUnitFiniteKernel
