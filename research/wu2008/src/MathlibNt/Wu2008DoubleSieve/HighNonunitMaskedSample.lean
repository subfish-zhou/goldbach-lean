import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitLegalMass
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalUnitMaskedPayment

open scoped BigOperators Classical Topology
namespace Wu2008DoubleSieve.HighNonunitMasked
open Set MeasureTheory Filter HighNonunitLegal

variable {m r : ℕ}

def mask (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) : Prop :=
  ∀ q, (∑ i, C q i * t i) ≤ gamma q

noncomputable def F (j : Fin (m+1)) (phi : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) : ℝ :=
  if mask C gamma t then G j phi t else 0

noncomputable def slope (m : ℕ) (Phi : ℝ) : ℝ :=
  100 * ((m+1 : ℝ) + 1) + 1000 * Phi

noncomputable def envelope (j : Fin (m+1)) (Phi h phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (t : Fin (m+1) → ℝ) : ℝ :=
  slope m Phi*h +
  (if |(∑ i, coefficients j i*t i)-phi| ≤ (m+2 : ℝ)*h then 10 else 0) +
  ∑ q, (if |(∑ i, C q i*t i)-gamma q| ≤ (∑ i, |C q i|)*h then 10 else 0)

theorem F_bounds (j : Fin (m+1)) (phi : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) {t : Fin (m+1) → ℝ} (ht : t ∈ continuousCube (m+1)) :
    0 ≤ F j phi C gamma t ∧ F j phi C gamma t ≤ 10 := by
  unfold F
  split_ifs
  · exact G_bounds j phi ht
  · norm_num

theorem F_measurable (j : Fin (m+1)) (phi : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) : Measurable (F j phi C gamma) := by
  have hm : MeasurableSet {t | mask C gamma t} := by
    simp only [mask, ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    apply measurableSet_le _ measurable_const
    fun_prop
  exact Measurable.ite hm (G_measurable j phi) measurable_const

theorem F_integrable (j : Fin (m+1)) (phi : ℝ) (C : Fin r → Fin (m+1) → ℝ)
    (gamma : Fin r → ℝ) :
    IntegrableOn (fun t => F j phi C gamma t * continuousDensity t) (continuousCube (m+1)) := by
  apply continuousDensity_mul_integrable (F_measurable j phi C gamma) (K := 10)
  intro t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (F_bounds j phi C gamma ht).1]
  exact (F_bounds j phi C gamma ht).2

theorem oscillation (j : Fin (m+1)) {Phi phi h : ℝ} (hPhi : 2 ≤ Phi)
    (hphi : phi ∈ Icc 2 Phi) (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ)
    {x y : Fin (m+1) → ℝ} (hh : 0 ≤ h)
    (hx : x ∈ continuousCube (m+1)) (hy : y ∈ continuousCube (m+1))
    (hxy : ∀ i, |x i-y i| ≤ h) :
    |F j phi C gamma x - F j phi C gamma y| ≤ envelope j Phi h phi C gamma x := by
  have hb : 0 ≤ slope m Phi*h := by unfold slope; positivity
  have hl0 : 0 ≤ (if |(∑ i, coefficients j i*x i)-phi| ≤ (m+2 : ℝ)*h then (10 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hq0 (q : Fin r) : 0 ≤ (if |(∑ i, C q i*x i)-gamma q| ≤ (∑ i, |C q i|)*h then (10 : ℝ) else 0) := by
    split_ifs <;> norm_num
  have hs0 := Finset.sum_nonneg (fun q (_ : q ∈ Finset.univ) => hq0 q)
  have hjump : |F j phi C gamma x - F j phi C gamma y| ≤ 10 := by
    have ha := F_bounds j phi C gamma hx
    have hb' := F_bounds j phi C gamma hy
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  unfold envelope
  by_cases hl : |(∑ i, coefficients j i*x i)-phi| ≤ (m+2 : ℝ)*h
  · rw [if_pos hl]; linarith
  by_cases hr : ∃ q, |(∑ i, C q i*x i)-gamma q| ≤ (∑ i, |C q i|)*h
  · obtain ⟨q,hq⟩ := hr
    have hs := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) => hq0 q) (Finset.mem_univ q)
    rw [if_pos hq] at hs
    linarith
  have hs : ∀ q, ¬ |(∑ i, C q i*x i)-gamma q| ≤ (∑ i, |C q i|)*h := by simpa using hr
  rw [if_neg hl]
  simp only [if_neg (hs _), Finset.sum_const_zero, add_zero]
  have hlEq : x ∈ legal j phi ↔ y ∈ legal j phi := by
    rw [legal_eq_affine]
    by_contra hc
    have hh' := SecondFunctionalUnitKernel.affine_change_band false (coefficients j) x y phi hxy hc
    apply hl
    simpa only [continuousBand, Set.mem_ofPred_eq, SecondFunctionalUnitKernel.dot, coefficients_l1, Nat.cast_add, Nat.cast_one,
      show (m : ℝ)+1+1 = m+2 by ring] using hh'
  have hmEq : mask C gamma x ↔ mask C gamma y := by
    apply forall_congr'
    intro q
    by_contra hc
    exact hs q (SecondFunctionalUnitKernel.affine_change_band false (C q) x y (gamma q) hxy hc)
  unfold F
  by_cases hm : mask C gamma x
  · rw [if_pos hm, if_pos (hmEq.mp hm)]
    by_cases ha : x ∈ legal j phi
    · simpa only [slope, Nat.cast_add, Nat.cast_one] using
        G_oscillation hPhi hphi hx hy ha (hlEq.mp ha) hxy
    · rw [G_of_illegal ha, G_of_illegal (fun hy' => ha (hlEq.mpr hy')), sub_self, abs_zero]
      exact hb
  · rw [if_neg hm, if_neg (fun hy' => hm (hmEq.mpr hy')), sub_self, abs_zero]
    exact hb

noncomputable def sample (j : Fin (m+1)) (k : ℕ) (phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (a : GridIndex (m+1) k) : ℝ :=
  F j phi C gamma (gridCenter a)

noncomputable def primeSum (j : Fin (m+1)) (R phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) : ℝ :=
  ∑ f : Fin (m+1) → primeSlabPrimes R, primeSlabWeight R f * F j phi C gamma (gridCoordinates R f)

noncomputable def integral (j : Fin (m+1)) (phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) : ℝ :=
  ∫ t in continuousCube (m+1), F j phi C gamma t * continuousDensity t

theorem sample_bound (j : Fin (m+1)) (k : ℕ) (phi : ℝ)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ) (a : GridIndex (m+1) k) :
    |sample j k phi C gamma a| ≤ 10 := by
  have hr := F_bounds j phi C gamma (gridClosed_subset_cube a (gridCell_subset_closed a (gridCenter_mem a)))
  exact (abs_of_nonneg hr.1).trans_le hr.2

theorem sampling_pointwise (j : Fin (m+1)) (k : ℕ) {Phi phi : ℝ}
    (hPhi : 2 ≤ Phi) (hphi : phi ∈ Icc 2 Phi)
    (C : Fin r → Fin (m+1) → ℝ) (gamma : Fin r → ℝ)
    {t : Fin (m+1) → ℝ} (ht : t ∈ continuousCube (m+1)) :
    |F j phi C gamma t - gridStep (sample j k phi C gamma) t| ≤
      envelope j Phi (gridWidth k) phi C gamma t := by
  obtain ⟨a,ha,_⟩ := (gridCell_partition (k := k)).mp ht
  rw [gridStep_on_cell _ a ha]
  exact oscillation j hPhi hphi C gamma (gridWidth_pos k).le ht
    (gridClosed_subset_cube a (gridCell_subset_closed a (gridCenter_mem a)))
    (gridCell_oscillation ha (gridCenter_mem a))

end Wu2008DoubleSieve.HighNonunitMasked
