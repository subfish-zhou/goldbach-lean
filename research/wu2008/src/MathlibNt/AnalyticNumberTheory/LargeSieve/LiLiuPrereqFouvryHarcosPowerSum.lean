import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Field.GeomSum

/-!
# Finite power sums detect the modulus of every root

This supplies the growth-to-root-modulus implication used on page 1 of
Harcos, *Weil's bound for Kloosterman sums* (`pages/harcos-weil-01.png`).
Cesàro averages isolate all copies of a maximal-modulus root simultaneously;
their positive multiplicity prevents cancellation. No distinctness is needed.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Filter Finset
open scoped Topology

/-- Away from `1`, the Cesàro averages of powers in the closed unit disk tend to zero. -/
theorem harcos_cesaro_powers_tendsto_zero {z : ℂ} (hz : ‖z‖ ≤ 1) (hz1 : z ≠ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 0) := by
  have hbound (n : ℕ) :
      ‖((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k‖ ≤
        (n : ℝ)⁻¹ * (2 / ‖z - 1‖) := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), geom_sum_eq hz1, norm_div]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ ≤ 2 := by
        rw [norm_pow, norm_one]
        have := pow_le_one₀ (n := n) (norm_nonneg z) hz
        linarith
  apply squeeze_zero_norm hbound
  simpa using
    ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul_const
      (2 / ‖z - 1‖))

/-- Cesàro averaging retains precisely the copies of the root `1`. -/
theorem harcos_cesaro_powers_tendsto {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ k ∈ range n, z ^ k)
      atTop (𝓝 (if z = 1 then 1 else 0)) := by
  classical
  by_cases hz1 : z = 1
  · subst z
    simpa using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℂ)) atTop (𝓝 1)).cesaro_smul
  · simpa only [if_neg hz1] using harcos_cesaro_powers_tendsto_zero hz hz1

/-- A geometric bound on all sufficiently large power sums bounds every root.
The indexing map may have repetitions: maximal equal roots contribute their
positive integer multiplicity to a Cesàro limit, rather than canceling. -/
theorem harcos_norm_le_of_finset_power_sum_bound {ι : Type*} (s : Finset ι)
    (z : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ᶠ n : ℕ in atTop, ‖∑ i ∈ s, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i ∈ s, ‖z i‖ ≤ R := by
  classical
  intro i hi
  by_contra hbad
  have hiR : R < ‖z i‖ := lt_of_not_ge hbad
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image (fun k ↦ ‖z k‖) ⟨i, hi⟩
  have hjR : R < ‖z j‖ := hiR.trans_le (hmax i hi)
  have hjpos : 0 < ‖z j‖ := hR.trans hjR
  have hj0 : z j ≠ 0 := norm_pos_iff.mp hjpos
  have hratio : 0 ≤ R / ‖z j‖ := div_nonneg hR.le (norm_nonneg _)
  have hratio1 : R / ‖z j‖ < 1 := (div_lt_one hjpos).mpr hjR
  have hdecay : Tendsto (fun n : ℕ ↦ C * (R / ‖z j‖) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hratio hratio1).const_mul C
  have hzero : Tendsto (fun n : ℕ ↦ ∑ k ∈ s, (z k / z j) ^ n)
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hdecay
    filter_upwards [hbound] with n hn
    calc
      ‖∑ k ∈ s, (z k / z j) ^ n‖ = ‖∑ k ∈ s, z k ^ n‖ / ‖z j‖ ^ n := by
        simp_rw [div_pow, div_eq_mul_inv]
        rw [← Finset.sum_mul, norm_mul, norm_inv, norm_pow]
      _ ≤ C * R ^ n / ‖z j‖ ^ n :=
        div_le_div_of_nonneg_right hn (by positivity)
      _ = C * (R / ‖z j‖) ^ n := by rw [div_pow]; ring
  have hterm (k : ι) (hk : k ∈ s) :
      Tendsto (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m)
        atTop (𝓝 (if z k / z j = 1 then 1 else 0)) := by
    apply harcos_cesaro_powers_tendsto
    rw [norm_div]
    exact (div_le_one hjpos).mpr (hmax k hk)
  have hlimit := tendsto_finsetSum s hterm
  have hmeans :
      (fun n : ℕ ↦ ((n : ℝ)⁻¹) • ∑ m ∈ range n, ∑ k ∈ s, (z k / z j) ^ m) =
      (fun n : ℕ ↦ ∑ k ∈ s, ((n : ℝ)⁻¹) • ∑ m ∈ range n, (z k / z j) ^ m) := by
    funext n
    rw [Finset.sum_comm, Finset.smul_sum]
  have heq := tendsto_nhds_unique (hmeans ▸ hzero.cesaro_smul) hlimit
  rw [Finset.sum_boole] at heq
  have hcard : 0 < (s.filter (fun k ↦ z k / z j = 1)).card :=
    Finset.card_pos.mpr ⟨j, by simp [hj, hj0]⟩
  exact (Nat.ne_of_gt hcard) (by exact_mod_cast heq.symm)

/-- Existential growth formulation for an arbitrary finite indexed family,
with no injectivity or distinctness hypothesis. -/
theorem harcos_norm_le_of_power_sum_growth {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {R : ℝ} (hR : 0 < R)
    (hgrowth : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ n : ℕ in atTop, ‖∑ i, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i, ‖z i‖ ≤ R := by
  obtain ⟨C, _, hC⟩ := hgrowth
  intro i
  exact harcos_norm_le_of_finset_power_sum_bound univ z hR hC i (mem_univ i)

/-- The Harcos application only needs powers of degree at least four. -/
theorem harcos_norm_le_of_power_sum_bound_from_four {ι : Type*} [Fintype ι]
    (z : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ n : ℕ, 4 ≤ n → ‖∑ i, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i, ‖z i‖ ≤ R := by
  intro i
  apply harcos_norm_le_of_finset_power_sum_bound univ z (C := C) hR _ i (mem_univ i)
  exact (eventually_ge_atTop 4).mono hbound

/-- The paired-root form of Harcos's trace: no separation between the two
families, or between roots within either family, is assumed. -/
theorem harcos_pair_norm_le_of_power_sum_bound_from_four {ι : Type*} [Fintype ι]
    (α β : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ n : ℕ, 4 ≤ n → ‖∑ i, (α i ^ n + β i ^ n)‖ ≤ C * R ^ n) :
    ∀ i, ‖α i‖ ≤ R ∧ ‖β i‖ ≤ R := by
  let z : ι × Bool → ℂ := fun k ↦ if k.2 then α k.1 else β k.1
  have hsum (n : ℕ) : ∑ k, z k ^ n = ∑ i, (α i ^ n + β i ^ n) := by
    simp [z, Fintype.sum_prod_type]
  have hz : ∀ k, ‖z k‖ ≤ R :=
    harcos_norm_le_of_power_sum_bound_from_four z hR (by
      intro n hn
      rw [hsum]
      exact hbound n hn)
  intro i
  exact ⟨hz (i, true), hz (i, false)⟩

/-- A reciprocal product upgrades the individual upper bounds to equality. -/
theorem harcos_pair_norm_eq_of_power_sum_bound_from_four {ι : Type*} [Fintype ι]
    (α β : ι → ℂ) {R C : ℝ} (hR : 0 < R)
    (hprod : ∀ i, α i * β i = ((R ^ 2 : ℝ) : ℂ))
    (hbound : ∀ n : ℕ, 4 ≤ n → ‖∑ i, (α i ^ n + β i ^ n)‖ ≤ C * R ^ n) :
    ∀ i, ‖α i‖ = R ∧ ‖β i‖ = R := by
  have hle := harcos_pair_norm_le_of_power_sum_bound_from_four α β hR hbound
  intro i
  have hmul : ‖α i‖ * ‖β i‖ = R ^ 2 := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg R)]
      using congrArg norm (hprod i)
  have ha := mul_le_mul_of_nonneg_left (hle i).2 (norm_nonneg (α i))
  have hb := mul_le_mul_of_nonneg_right (hle i).1 (norm_nonneg (β i))
  constructor <;> nlinarith [(hle i).1, (hle i).2]

/-- Exactly `2 * (p - 1)` indexed roots, retaining the `n ≥ 4` hypothesis. -/
theorem harcos_two_mul_sub_one_roots_norm_le (p : ℕ)
    (z : Fin (2 * (p - 1)) → ℂ) {R C : ℝ} (hR : 0 < R)
    (hbound : ∀ n : ℕ, 4 ≤ n → ‖∑ i, z i ^ n‖ ≤ C * R ^ n) :
    ∀ i, ‖z i‖ ≤ R :=
  harcos_norm_le_of_power_sum_bound_from_four z hR hbound

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
