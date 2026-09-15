import MathlibNt.Wu2008DoubleSieve.Omega3R1Prefix
import MathlibNt.Wu2008DoubleSieve.Omega3R2Source

/-!
# Balanced distribution on the actual switched sieve moduli

Wu (2004), (5.5)--(5.7): consume the frozen prime-count-centered producer.
The residue is completed by 1 off the moduli coprime to N. The actual
interval is the difference of two closed prefixes, with the complete
cofactor sum kept inside each absolute value.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter Wu2004MeanValue
open scoped Classical Topology

def omega3ReducedResidue (N q : ℕ) : ℕ :=
  if N.Coprime q then N else 1

theorem omega3ReducedResidue_coprime (N q : ℕ) :
    (omega3ReducedResidue N q).Coprime q := by
  unfold omega3ReducedResidue
  split_ifs with h
  · exact h
  · exact Nat.coprime_one_left q

theorem omega3ReducedResidue_eq {N D q : ℕ} {Z : ℝ}
    (hq : q ∈ omega3SieveModuli N D Z) : omega3ReducedResidue N q = N := by
  exact if_pos (omega3SieveModuli_properties hq).2.2.1.symm

theorem omega3SieveModuli_weight {N D q : ℕ} {Z : ℝ}
    (hq : q ∈ omega3SieveModuli N D Z) :
    wuModulusWeight q = (3 : ℝ) ^ q.primeFactors.card := by
  simp only [wuModulusWeight,
    MathlibNt.SieveTheory.SwitchingPrinciple.moebius_sq_eq_one_of_squarefree
      (omega3SieveModuli_properties hq).2.1, one_mul]

theorem omega3SieveModuli_subset_Icc (N : ℕ) (Q Z : ℝ) :
    omega3SieveModuli N (⌊Q⌋₊ + 1) Z ⊆ Icc 1 ⌊Q⌋₊ := by
  intro q hq
  have h := omega3SieveModuli_properties hq
  exact mem_Icc.mpr ⟨h.1, by omega⟩

theorem omega3_primeCentered_moduli_le (N : ℕ) (Q Z : ℝ)
    (S : Finset ℕ) (f r : ℕ → ℝ) :
    (∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) Z,
      (3 : ℝ) ^ q.primeFactors.card * |primeCenteredAPSum S f r q N|) ≤
      ∑ q ∈ Icc 1 ⌊Q⌋₊, wuModulusWeight q *
        |primeCenteredAPSum S f r q (omega3ReducedResidue N q)| := by
  calc
    _ = ∑ q ∈ omega3SieveModuli N (⌊Q⌋₊ + 1) Z, wuModulusWeight q *
        |primeCenteredAPSum S f r q (omega3ReducedResidue N q)| := by
      apply sum_congr rfl
      intro q hq
      rw [omega3SieveModuli_weight hq, omega3ReducedResidue_eq hq]
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (omega3SieveModuli_subset_Icc N Q Z)
      (fun q _ _ => mul_nonneg (wuModulusWeight_nonneg q) (abs_nonneg _))

theorem omega3_source_level_eventually (B : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ : ℝ) ≤
      sqrt N / log (N : ℝ) ^ B := by
  filter_upwards [eventually_log_rpow_le_rpow B hδ,
    eventually_ge_atTop (2 : ℕ)] with N hlog hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  apply (Nat.floor_le (rpow_nonneg hN0.le _)).trans
  apply (le_div_iff₀ (rpow_pos_of_pos hl B)).mpr
  calc
    _ ≤ (N : ℝ) ^ (1 / 2 - δ) * (N : ℝ) ^ δ :=
      mul_le_mul_of_nonneg_left hlog (rpow_nonneg hN0.le _)
    _ = sqrt N := by
      rw [← rpow_add hN0, show (1 / 2 - δ) + δ = (1 / 2 : ℝ) by ring,
        ← sqrt_eq_rpow]

/-- Uniform in every common support and both real endpoints. The bounded
raw coefficient is consumed with F itself, without an extra factor F. -/
theorem omega3_balanced_interval_distribution (A η F : ℝ) {δ : ℝ}
    (hA : 0 < A) (hη : 0 < η) (hF : 0 ≤ F) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (S : Finset ℕ) (f a b : ℕ → ℝ),
      (∀ e ∈ S, (N : ℝ) ^ η ≤ e ∧ (e : ℝ) ≤ (N : ℝ) ^ (1 - η)) →
      (∀ e ∈ S, |f e| ≤ F) →
      (∀ e ∈ S, 2 ≤ a e ∧ a e ≤ b e ∧ (e : ℝ) * b e ≤ N) →
      ∀ Z : ℝ,
      (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
        (3 : ℝ) ^ q.primeFactors.card *
          |∑ e ∈ S.filter (fun e => e.Coprime q),
            f e * omega3ProfileError N q e (a e) (b e)|) ≤
        C * N / log (N : ℝ) ^ A := by
  obtain ⟨B, C, _, hC, T1, hT1⟩ :=
    balanced_common_profile_primeCentered_natural A η F hA hη hF
  obtain ⟨T2, hT2⟩ := eventually_atTop.mp (omega3_source_level_eventually B hδ)
  refine ⟨2 * C, by positivity, max 4 (max T1 T2), le_max_left _ _, ?_⟩
  intro N hN S f a b hS hf hab Z
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : T2 ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hepos : ∀ e ∈ S, 0 < e := by
    intro e he
    have hpow : 0 < (N : ℝ) ^ η := rpow_pos_of_pos (by positivity) _
    exact_mod_cast hpow.trans_le (hS e he).1
  have hbN : ∀ e ∈ S, b e ≤ N := by
    intro e he
    have he1 : (1 : ℝ) ≤ e := by exact_mod_cast hepos e he
    have hb0 : 0 ≤ b e := by linarith [(hab e he).1, (hab e he).2.1]
    exact (le_mul_of_one_le_left hb0 he1).trans (hab e he).2.2
  have hupper := hT1 N hN1 ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ S f b
    (omega3ReducedResidue N) (hT2 N hN2) hS hf
    (fun e he => ⟨(hab e he).1.trans (hab e he).2.1, (hab e he).2.2⟩)
    (fun q _ => omega3ReducedResidue_coprime N q)
  have hlower := hT1 N hN1 ⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ S f a
    (omega3ReducedResidue N) (hT2 N hN2) hS hf
    (fun e he => ⟨(hab e he).1,
      (mul_le_mul_of_nonneg_left (hab e he).2.1 (Nat.cast_nonneg e)).trans (hab e he).2.2⟩)
    (fun q _ => omega3ReducedResidue_coprime N q)
  calc
    _ ≤ ∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
        (3 : ℝ) ^ q.primeFactors.card *
          (|primeCenteredAPSum S f b q N| + |primeCenteredAPSum S f a q N|) := by
      apply sum_le_sum
      intro q _
      exact mul_le_mul_of_nonneg_left
        (abs_sum_omega3ProfileError_le_primeCenteredAPSum_add S f a b N q
          hepos (fun e he => by linarith [(hab e he).1])
          (fun e he => (hab e he).2.1) hbN) (by positivity)
    _ = (∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
        (3 : ℝ) ^ q.primeFactors.card * |primeCenteredAPSum S f b q N|) +
        ∑ q ∈ omega3SieveModuli N (⌊(N : ℝ) ^ (1 / 2 - δ)⌋₊ + 1) Z,
          (3 : ℝ) ^ q.primeFactors.card * |primeCenteredAPSum S f a q N| := by
      simp only [mul_add, sum_add_distrib]
    _ ≤ C * N / log (N : ℝ) ^ A + C * N / log (N : ℝ) ^ A :=
      add_le_add
        ((omega3_primeCentered_moduli_le N _ Z S f b).trans hupper)
        ((omega3_primeCentered_moduli_le N _ Z S f a).trans hlower)
    _ = _ := by ring

end Wu2008DoubleSieve
