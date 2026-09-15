import MathlibNt.Wu2008DoubleSieve.SecondFunctionalFourPrimeContinuousKernel
import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitClosedQuadrature

/-! A fixed nonzero row matrix for all four literal closed domains. -/
namespace Wu2008DoubleSieve.FourPrimeContinuous
open Set MeasureTheory
open scoped BigOperators Classical

abbrev Row := Fin 3 ⊕ (Fin 4 × Bool)

noncomputable def C : Row → Point
  | .inl k => fun i => gridFaceCoeff k.castSucc i - gridFaceCoeff k.succ i
  | .inr (k, false) => fun i => -gridFaceCoeff k i
  | .inr (k, true) => gridFaceCoeff k

def gamma (lo hi : Point) : Row → ℝ
  | .inl _ => 0
  | .inr (k, false) => -lo k
  | .inr (k, true) => hi k

/-- Every face has an explicitly nonzero coordinate, including every endpoint face. -/
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

theorem C_adjacent (k : Fin 3) (t : Point) :
    (∑ i, C (.inl k) i * t i) = t k.castSucc - t k.succ := by
  simp only [C, sub_mul, Finset.sum_sub_distrib, gridFaceCoeff_sum]

theorem rows_iff (lo hi t : Point) :
    (∀ q, (∑ i, C q i * t i) ≤ gamma lo hi q) ↔
      (∀ k : Fin 3, t k.castSucc ≤ t k.succ) ∧
      ∀ k, lo k ≤ t k ∧ t k ≤ hi k := by
  simp only [Sum.forall, C_adjacent, gamma, sub_nonpos, Prod.forall, Bool.forall_bool]
  simp [C, Finset.sum_neg_distrib, gridFaceCoeff_sum]

/-- Fixed coordinate construction, not a numerical search. -/
def vec (a b c d : ℝ) : Point :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

def gamma16 (c e : ℝ) : Row → ℝ := gamma (vec c c c c) (vec e e e e)

theorem D16_eq_rows (c e : ℝ) :
    D16 c e = {t | ∀ q, (∑ i, C q i * t i) ≤ gamma16 c e q} := by
  ext t
  simp only [gamma16, rows_iff, D16, mem_ofPred_eq,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [vec, Fin.cases]
  dsimp
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4⟩
    repeat' constructor
    all_goals linarith
  · rintro ⟨⟨h01, h12, h23⟩, h0, h1, h2, h3⟩
    rcases h0 with ⟨hl0, hu0⟩
    rcases h1 with ⟨hl1, hu1⟩
    rcases h2 with ⟨hl2, hu2⟩
    rcases h3 with ⟨hl3, hu3⟩
    repeat' constructor
    all_goals linarith

def gamma17 (c e f : ℝ) : Row → ℝ := gamma (vec c c c e) (vec e e e f)

theorem D17_eq_rows (c e f : ℝ) :
    D17 c e f = {t | ∀ q, (∑ i, C q i * t i) ≤ gamma17 c e f q} := by
  ext t
  simp only [gamma17, rows_iff, D17, mem_ofPred_eq,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [vec, Fin.cases]
  dsimp
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    repeat' constructor
    all_goals linarith
  · rintro ⟨⟨h01, h12, h23⟩, h0, h1, h2, h3⟩
    rcases h0 with ⟨hl0, hu0⟩
    rcases h1 with ⟨hl1, hu1⟩
    rcases h2 with ⟨hl2, hu2⟩
    rcases h3 with ⟨hl3, hu3⟩
    repeat' constructor
    all_goals linarith

def gamma18 (c e f : ℝ) : Row → ℝ := gamma (vec c c e e) (vec e e f f)

theorem D18_eq_rows (c e f : ℝ) :
    D18 c e f = {t | ∀ q, (∑ i, C q i * t i) ≤ gamma18 c e f q} := by
  ext t
  simp only [gamma18, rows_iff, D18, mem_ofPred_eq,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [vec, Fin.cases]
  dsimp
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5⟩
    repeat' constructor
    all_goals linarith
  · rintro ⟨⟨h01, h12, h23⟩, h0, h1, h2, h3⟩
    rcases h0 with ⟨hl0, hu0⟩
    rcases h1 with ⟨hl1, hu1⟩
    rcases h2 with ⟨hl2, hu2⟩
    rcases h3 with ⟨hl3, hu3⟩
    repeat' constructor
    all_goals linarith

def gamma19 (b c e f : ℝ) : Row → ℝ := gamma (vec b e e e) (vec c f f f)

theorem D19_eq_rows (b c e f : ℝ) (hce : c ≤ e) :
    D19 b c e f = {t | ∀ q, (∑ i, C q i * t i) ≤ gamma19 b c e f q} := by
  ext t
  simp only [gamma19, rows_iff, D19, mem_ofPred_eq,
    Fin.forall_fin_succ, Fin.forall_fin_zero, and_true]
  norm_num [vec, Fin.cases]
  dsimp
  constructor
  · intro h
    rcases h with ⟨h0, h1, h2, h3, h4, h5, h6⟩
    repeat' constructor
    all_goals linarith
  · rintro ⟨⟨h01, h12, h23⟩, h0, h1, h2, h3⟩
    rcases h0 with ⟨hl0, hu0⟩
    rcases h1 with ⟨hl1, hu1⟩
    rcases h2 with ⟨hl2, hu2⟩
    rcases h3 with ⟨hl3, hu3⟩
    repeat' constructor
    all_goals linarith

/-- Full reciprocal prime product on the literal closed mask; no finite atom is removed. -/
noncomputable def closedPrimeK (s : Set Point) (R phi : ℝ) : ℝ :=
  ∑ p : Fin 4 → primeSlabPrimes R,
    primeSlabWeight R p * s.indicator (G phi) (gridCoordinates R p)

theorem closedPrimeK_nonneg (s : Set Point) {R : ℝ} (hR : 1 < R) (phi : ℝ) :
    0 ≤ closedPrimeK s R phi := by
  apply Finset.sum_nonneg
  intro p _
  apply mul_nonneg (gridWeight_nonneg R p)
  by_cases hp : gridCoordinates R p ∈ s
  · rw [Set.indicator_of_mem hp]
    exact (HighNonunitLegal.G_bounds 2 phi (gridCoordinates_mem hR p)).1
  · rw [Set.indicator_of_notMem hp]

/-- Integral-to-cube rewriting retains the exact domain indicator. -/
theorem integral_mask_literal (s : Set Point) (hs : MeasurableSet s)
    (hsub : s ⊆ continuousCube 4) (phi : ℝ) :
    (∫ t in s, G phi t * continuousDensity t) =
      ∫ t in continuousCube 4, s.indicator (G phi) t * continuousDensity t := by
  have h := setIntegral_indicator (μ := volume) (s := continuousCube 4)
    (f := fun t => G phi t * continuousDensity t) hs
  rw [inter_eq_right.mpr hsub] at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ s <;> simp [ht]

theorem closedPrimeK_rows (g : Row → ℝ) (R phi : ℝ) :
    closedPrimeK {t | ∀ q, (∑ i, C q i * t i) ≤ g q} R phi =
      ∑ p : Fin 4 → primeSlabPrimes R, primeSlabWeight R p *
        (if ∀ q, (∑ i, C q i * gridCoordinates R p i) ≤ g q
          then HighNonunitLegal.G 2 phi (gridCoordinates R p) else 0) := by
  simp only [closedPrimeK, Set.indicator_apply, mem_ofPred_eq, G]

noncomputable def closedPrimeK16 (R c e phi : ℝ) : ℝ :=
  closedPrimeK (D16 c e) R phi

theorem closedPrimeK16_nonneg {R : ℝ} (hR : 1 < R) (c e phi : ℝ) :
    0 ≤ closedPrimeK16 R c e phi := closedPrimeK_nonneg _ hR phi

theorem K16_mask_literal {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    K16 c e phi = ∫ t in continuousCube 4,
      (if ∀ q, (∑ i, C q i * t i) ≤ gamma16 c e q
        then HighNonunitLegal.G 2 phi t else 0) * continuousDensity t := by
  rw [K16, integral_mask_literal _ (D16_measurable c e) (D16_subset_cube hp),
    D16_eq_rows c e]
  simp only [Set.indicator_apply, mem_ofPred_eq, G]

noncomputable def closedPrimeK17 (R c e f phi : ℝ) : ℝ :=
  closedPrimeK (D17 c e f) R phi

theorem closedPrimeK17_nonneg {R : ℝ} (hR : 1 < R) (c e f phi : ℝ) :
    0 ≤ closedPrimeK17 R c e f phi := closedPrimeK_nonneg _ hR phi

theorem K17_mask_literal {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    K17 c e f phi = ∫ t in continuousCube 4,
      (if ∀ q, (∑ i, C q i * t i) ≤ gamma17 c e f q
        then HighNonunitLegal.G 2 phi t else 0) * continuousDensity t := by
  rw [K17, integral_mask_literal _ (D17_measurable c e f) (D17_subset_cube hp),
    D17_eq_rows c e f]
  simp only [Set.indicator_apply, mem_ofPred_eq, G]

noncomputable def closedPrimeK18 (R c e f phi : ℝ) : ℝ :=
  closedPrimeK (D18 c e f) R phi

theorem closedPrimeK18_nonneg {R : ℝ} (hR : 1 < R) (c e f phi : ℝ) :
    0 ≤ closedPrimeK18 R c e f phi := closedPrimeK_nonneg _ hR phi

theorem K18_mask_literal {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    K18 c e f phi = ∫ t in continuousCube 4,
      (if ∀ q, (∑ i, C q i * t i) ≤ gamma18 c e f q
        then HighNonunitLegal.G 2 phi t else 0) * continuousDensity t := by
  rw [K18, integral_mask_literal _ (D18_measurable c e f) (D18_subset_cube hp),
    D18_eq_rows c e f]
  simp only [Set.indicator_apply, mem_ofPred_eq, G]

noncomputable def closedPrimeK19 (R b c e f phi : ℝ) : ℝ :=
  closedPrimeK (D19 b c e f) R phi

theorem closedPrimeK19_nonneg {R : ℝ} (hR : 1 < R) (b c e f phi : ℝ) :
    0 ≤ closedPrimeK19 R b c e f phi := closedPrimeK_nonneg _ hR phi

theorem K19_mask_literal {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    K19 b c e f phi = ∫ t in continuousCube 4,
      (if ∀ q, (∑ i, C q i * t i) ≤ gamma19 b c e f q
        then HighNonunitLegal.G 2 phi t else 0) * continuousDensity t := by
  rw [K19, integral_mask_literal _ (D19_measurable b c e f) (D19_subset_cube hp),
    D19_eq_rows b c e f hp.2.2.1]
  simp only [Set.indicator_apply, mem_ofPred_eq, G]

/-- One threshold precedes every compact parameter and all four complete words. -/
theorem closedPrimeK_four_uniform (Phi : ℝ) (hPhi : 2 ≤ Phi)
    (epsilon : ℝ) (he : 0 < epsilon) :
    ∃ T : ℝ, 1 < T ∧ ∀ R : ℝ, T ≤ R → ∀ phi : ℝ, phi ∈ Icc 2 Phi →
      ∀ b c e f : ℝ, CompactParameters b c e f →
        |closedPrimeK16 R c e phi - K16 c e phi| < epsilon ∧
        |closedPrimeK17 R c e f phi - K17 c e f phi| < epsilon ∧
        |closedPrimeK18 R c e f phi - K18 c e f phi| < epsilon ∧
        |closedPrimeK19 R b c e f phi - K19 b c e f phi| < epsilon := by
  obtain ⟨T, hT, h⟩ := HighNonunitMasked.uniform_finite_rows 3 2 C C_nonzero
    Phi hPhi epsilon he
  refine ⟨T, hT, ?_⟩
  intro R hR phi hphi b c e f hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [closedPrimeK16, D16_eq_rows c e,
      closedPrimeK_rows, K16_mask_literal hp]
    exact h R hR phi hphi (gamma16 c e)
  · rw [closedPrimeK17, D17_eq_rows c e f,
      closedPrimeK_rows, K17_mask_literal hp]
    exact h R hR phi hphi (gamma17 c e f)
  · rw [closedPrimeK18, D18_eq_rows c e f,
      closedPrimeK_rows, K18_mask_literal hp]
    exact h R hR phi hphi (gamma18 c e f)
  · rw [closedPrimeK19, D19_eq_rows b c e f hp.2.2.1,
      closedPrimeK_rows, K19_mask_literal hp]
    exact h R hR phi hphi (gamma19 b c e f)

end Wu2008DoubleSieve.FourPrimeContinuous
