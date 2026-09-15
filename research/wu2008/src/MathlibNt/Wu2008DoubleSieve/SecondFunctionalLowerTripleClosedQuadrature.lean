import MathlibNt.Wu2008DoubleSieve.SecondFunctionalLowerTripleContinuousKernel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedQuadrature

/-! One fixed row matrix and a threshold uniform over the six original bands.
The closed slab sums here are not the shifted actual finite main. -/
namespace Wu2008DoubleSieve.LowerTripleContinuous
open Set MeasureTheory
open scoped BigOperators Classical

abbrev Row := Fin 2 ⊕ (Fin 3 × Bool)

noncomputable def C : Row → Point
  | .inl k => fun i => gridFaceCoeff k.castSucc i - gridFaceCoeff k.succ i
  | .inr (k, false) => fun i => -gridFaceCoeff k i
  | .inr (k, true) => gridFaceCoeff k

def gamma (lo hi : Point) : Row → ℝ
  | .inl _ => 0
  | .inr (k, false) => -lo k
  | .inr (k, true) => hi k

theorem C_nonzero (q : Row) : ∃ i, 1 ≤ |C q i| := by
  cases q with
  | inl k =>
    refine ⟨k.castSucc, ?_⟩
    have h : k.castSucc ≠ k.succ := by
      intro he
      have hv := congrArg Fin.val he
      exact Nat.ne_add_one k.val hv
    simp [C, gridFaceCoeff, h]
  | inr p =>
    rcases p with ⟨k, b⟩
    cases b <;> exact ⟨k, by simp [C, gridFaceCoeff]⟩

theorem C_adjacent (k : Fin 2) (t : Point) :
    (∑ i, C (.inl k) i * t i) = t k.castSucc - t k.succ := by
  simp only [C, sub_mul, Finset.sum_sub_distrib, gridFaceCoeff_sum]

theorem rows_iff (lo hi t : Point) :
    (∀ q, (∑ i, C q i * t i) ≤ gamma lo hi q) ↔
      (∀ k : Fin 2, t k.castSucc ≤ t k.succ) ∧
      ∀ k, lo k ≤ t k ∧ t k ≤ hi k := by
  simp only [Sum.forall, C_adjacent, gamma, sub_nonpos, Prod.forall, Bool.forall_bool]
  simp [C, Finset.sum_neg_distrib, gridFaceCoeff_sum]

def vec (a b c : ℝ) : Point := Fin.cases a (Fin.cases b (fun _ => c))

noncomputable def bandGamma (a b c e f : ℝ) (j : Fin 6) : Row → ℝ :=
  let v := LowerTripleGrouped.bands a b c e f j
  gamma (vec v.1 v.2.2.1 v.2.2.2.2.1) (vec v.2.1 v.2.2.2.1 v.2.2.2.2.2)

theorem D_eq_rows (a b c e f : ℝ) (j : Fin 6) :
    D a b c e f j = {t | ∀ q, (∑ i, C q i * t i) ≤ bandGamma a b c e f j q} := by
  ext t
  simp only [bandGamma, rows_iff, D, mem_ofPred_eq,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [vec, Fin.cases]
  tauto

/-- Full reciprocal prime product on the literal closed mask; no atom is removed. -/
noncomputable def closedPrimeK (s : Set Point) (R phi : ℝ) : ℝ :=
  ∑ p : Fin 3 → primeSlabPrimes R,
    primeSlabWeight R p * s.indicator (G phi) (gridCoordinates R p)

theorem closedPrimeK_nonneg (s : Set Point) {R : ℝ} (hR : 1 < R) (phi : ℝ) :
    0 ≤ closedPrimeK s R phi := by
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (gridWeight_nonneg R p)
  by_cases hp : gridCoordinates R p ∈ s
  · rw [Set.indicator_of_mem hp]
    exact (HighNonunitLegal.G_bounds 1 phi (gridCoordinates_mem hR p)).1
  · rw [Set.indicator_of_notMem hp]

theorem integral_mask_literal (s : Set Point) (hs : MeasurableSet s)
    (hsub : s ⊆ continuousCube 3) (phi : ℝ) :
    (∫ t in s, G phi t * continuousDensity t) =
      ∫ t in continuousCube 3, s.indicator (G phi) t * continuousDensity t := by
  have h := setIntegral_indicator (μ := volume) (s := continuousCube 3)
    (f := fun t => G phi t * continuousDensity t) hs
  rw [inter_eq_right.mpr hsub] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ s <;> simp [ht]

theorem closedPrimeK_rows (g : Row → ℝ) (R phi : ℝ) :
    closedPrimeK {t | ∀ q, (∑ i, C q i * t i) ≤ g q} R phi =
      ∑ p : Fin 3 → primeSlabPrimes R, primeSlabWeight R p *
        (if ∀ q, (∑ i, C q i * gridCoordinates R p i) ≤ g q
          then HighNonunitLegal.G 1 phi (gridCoordinates R p) else 0) := by
  simp only [closedPrimeK, Set.indicator_apply, mem_ofPred_eq, G]

noncomputable def closedPrimeKj (R a b c e f : ℝ) (j : Fin 6) (phi : ℝ) : ℝ :=
  closedPrimeK (D a b c e f j) R phi

theorem closedPrimeKj_nonneg {R : ℝ} (hR : 1 < R) (a b c e f : ℝ)
    (j : Fin 6) (phi : ℝ) : 0 ≤ closedPrimeKj R a b c e f j phi :=
  closedPrimeK_nonneg _ hR phi

theorem K_mask_literal {a b c e f : ℝ} (hp : CompactParameters a b c e f)
    (j : Fin 6) (phi : ℝ) :
    K a b c e f j phi = ∫ t in continuousCube 3,
      (if ∀ q, (∑ i, C q i * t i) ≤ bandGamma a b c e f j q
        then HighNonunitLegal.G 1 phi t else 0) * continuousDensity t := by
  rw [K, integral_mask_literal _ (D_measurable a b c e f j) (D_subset_cube hp j), D_eq_rows]
  simp only [Set.indicator_apply, mem_ofPred_eq, G]

/-- Each j receives epsilon; no total-six epsilon claim is made. Same actual phi
occurs on both sides. Phi only controls the uniform error threshold. -/
theorem closedPrimeK_six_uniform (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ a b c e f : ℝ, CompactParameters a b c e f → ∀ j : Fin 6,
        |closedPrimeKj R a b c e f j phi - K a b c e f j phi| < epsilon := by
  obtain ⟨T, hT, h⟩ := HighNonunitMasked.uniform_finite_rows 2 1 C C_nonzero
    Phi hPhi epsilon he
  refine ⟨T, hT, ?_⟩
  intro R hR phi hphi a b c e f hp j
  rw [closedPrimeKj, D_eq_rows, closedPrimeK_rows, K_mask_literal hp]
  exact h R hR phi hphi (bandGamma a b c e f j)

end Wu2008DoubleSieve.LowerTripleContinuous
