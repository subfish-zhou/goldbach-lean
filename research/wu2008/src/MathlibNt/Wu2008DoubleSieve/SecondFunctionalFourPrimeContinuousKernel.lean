import MathlibNt.Wu2008DoubleSieve.SecondFunctionalHighNonunitLegalMass

/-! Literal four-prime closed domains. No equality with strict finite carriers is asserted. -/
namespace Wu2008DoubleSieve.FourPrimeContinuous
open Set MeasureTheory
open scoped BigOperators

abbrev Point := Fin 4 → ℝ

def CompactParameters (b c e f : ℝ) : Prop :=
  1 / 10 ≤ b ∧ b ≤ c ∧ c ≤ e ∧ e ≤ f ∧ f ≤ 1 / 2

def D16 (c e : ℝ) : Set Point :=
  {t | c ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ e}
def D17 (c e f : ℝ) : Set Point :=
  {t | c ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ e ∧ e ≤ t 3 ∧ t 3 ≤ f}
def D18 (c e f : ℝ) : Set Point :=
  {t | c ≤ t 0 ∧ t 0 ≤ t 1 ∧ t 1 ≤ e ∧ e ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ f}
def D19 (b c e f : ℝ) : Set Point :=
  {t | b ≤ t 0 ∧ t 0 ≤ c ∧ c ≤ e ∧ e ≤ t 1 ∧ t 1 ≤ t 2 ∧ t 2 ≤ t 3 ∧ t 3 ≤ f}

/-- The selected coordinate is p3; q is coordinate 3, not a residual. -/
noncomputable abbrev G (phi : ℝ) : Point → ℝ := HighNonunitLegal.G 2 phi

theorem legal_literal (phi : ℝ) (t : Point) :
    t ∈ HighNonunitLegal.legal 2 phi ↔ (∑ i, t i) + t 2 ≤ phi := Iff.rfl

theorem G_measurable (phi : ℝ) : Measurable (G phi) := HighNonunitLegal.G_measurable 2 phi

theorem weighted_measurable (phi : ℝ) :
    Measurable (fun t : Point => G phi t * continuousDensity t) := by
  apply (G_measurable phi).mul
  unfold continuousDensity
  fun_prop

theorem D16_closed (c e : ℝ) : IsClosed (D16 c e) := by
  unfold D16
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem D16_measurable (c e : ℝ) : MeasurableSet (D16 c e) :=
  (D16_closed c e).measurableSet

theorem D16_subset_cube {b c e f : ℝ} (hp : CompactParameters b c e f) :
    D16 c e ⊆ continuousCube 4 := by
  intro t ht
  rcases hp with ⟨hb, hbc, hce, hef, hf⟩
  rcases ht with ⟨h0, h1, h2, h3, h4⟩
  simp only [continuousCube, mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp
  repeat' constructor
  all_goals linarith

noncomputable def K16 (c e phi : ℝ) : ℝ :=
  ∫ t in D16 c e, G phi t * continuousDensity t

theorem K16_integrable {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    IntegrableOn (fun t => G phi t * continuousDensity t) (D16 c e) :=
  HighNonunitLegal.weighted_integrable_on 2 phi (D16_subset_cube hp)

theorem K16_bounds {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    0 ≤ K16 c e phi ∧ K16 c e phi ≤ 10 * (4 : ℝ) ^ 4 :=
  HighNonunitLegal.integral_bounds 2 phi (D16_measurable c e) (D16_subset_cube hp)

theorem D17_closed (c e f : ℝ) : IsClosed (D17 c e f) := by
  unfold D17
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem D17_measurable (c e f : ℝ) : MeasurableSet (D17 c e f) :=
  (D17_closed c e f).measurableSet

theorem D17_subset_cube {b c e f : ℝ} (hp : CompactParameters b c e f) :
    D17 c e f ⊆ continuousCube 4 := by
  intro t ht
  rcases hp with ⟨hb, hbc, hce, hef, hf⟩
  rcases ht with ⟨h0, h1, h2, h3, h4, h5⟩
  simp only [continuousCube, mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp
  repeat' constructor
  all_goals linarith

noncomputable def K17 (c e f phi : ℝ) : ℝ :=
  ∫ t in D17 c e f, G phi t * continuousDensity t

theorem K17_integrable {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    IntegrableOn (fun t => G phi t * continuousDensity t) (D17 c e f) :=
  HighNonunitLegal.weighted_integrable_on 2 phi (D17_subset_cube hp)

theorem K17_bounds {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    0 ≤ K17 c e f phi ∧ K17 c e f phi ≤ 10 * (4 : ℝ) ^ 4 :=
  HighNonunitLegal.integral_bounds 2 phi (D17_measurable c e f) (D17_subset_cube hp)

theorem D18_closed (c e f : ℝ) : IsClosed (D18 c e f) := by
  unfold D18
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem D18_measurable (c e f : ℝ) : MeasurableSet (D18 c e f) :=
  (D18_closed c e f).measurableSet

theorem D18_subset_cube {b c e f : ℝ} (hp : CompactParameters b c e f) :
    D18 c e f ⊆ continuousCube 4 := by
  intro t ht
  rcases hp with ⟨hb, hbc, hce, hef, hf⟩
  rcases ht with ⟨h0, h1, h2, h3, h4, h5⟩
  simp only [continuousCube, mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp
  repeat' constructor
  all_goals linarith

noncomputable def K18 (c e f phi : ℝ) : ℝ :=
  ∫ t in D18 c e f, G phi t * continuousDensity t

theorem K18_integrable {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    IntegrableOn (fun t => G phi t * continuousDensity t) (D18 c e f) :=
  HighNonunitLegal.weighted_integrable_on 2 phi (D18_subset_cube hp)

theorem K18_bounds {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    0 ≤ K18 c e f phi ∧ K18 c e f phi ≤ 10 * (4 : ℝ) ^ 4 :=
  HighNonunitLegal.integral_bounds 2 phi (D18_measurable c e f) (D18_subset_cube hp)

theorem D19_closed (b c e f : ℝ) : IsClosed (D19 b c e f) := by
  unfold D19
  simp only [ofPred_and]
  repeat' apply IsClosed.inter
  all_goals apply isClosed_le <;> fun_prop

theorem D19_measurable (b c e f : ℝ) : MeasurableSet (D19 b c e f) :=
  (D19_closed b c e f).measurableSet

theorem D19_subset_cube {b c e f : ℝ} (hp : CompactParameters b c e f) :
    D19 b c e f ⊆ continuousCube 4 := by
  intro t ht
  rcases hp with ⟨hb, hbc, hce, hef, hf⟩
  rcases ht with ⟨h0, h1, h2, h3, h4, h5, h6⟩
  simp only [continuousCube, mem_pi, mem_univ, forall_const, Fin.forall_fin_succ,
    Fin.forall_fin_zero, and_true]
  dsimp
  repeat' constructor
  all_goals linarith

noncomputable def K19 (b c e f phi : ℝ) : ℝ :=
  ∫ t in D19 b c e f, G phi t * continuousDensity t

theorem K19_integrable {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    IntegrableOn (fun t => G phi t * continuousDensity t) (D19 b c e f) :=
  HighNonunitLegal.weighted_integrable_on 2 phi (D19_subset_cube hp)

theorem K19_bounds {b c e f : ℝ} (hp : CompactParameters b c e f) (phi : ℝ) :
    0 ≤ K19 b c e f phi ∧ K19 b c e f phi ≤ 10 * (4 : ℝ) ^ 4 :=
  HighNonunitLegal.integral_bounds 2 phi (D19_measurable b c e f) (D19_subset_cube hp)

/-- The actual weighted kernel, with precisely the p3 coordinate squared. -/
theorem weighted_legal_literal {phi : ℝ} {t : Point}
    (hl : t ∈ HighNonunitLegal.legal 2 phi) :
    G phi t * continuousDensity t =
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) := by
  rw [HighNonunitLegal.weighted_formula hl]
  have hs : (∑ i, t i) = t 0 + t 1 + t 2 + t 3 := by
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    change t 0 + (t 1 + (t 2 + t 3)) = _
    ring
  have hd : t 2 * (∏ i, t i) = t 0 * t 1 * t 2 ^ 2 * t 3 := by
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    change t 2 * (t 0 * (t 1 * (t 2 * t 3))) = _
    ring
  rw [hs, hd]

/-- The legal indicator is retained before restricting the genuine integral. -/
theorem integral_legal_literal (s : Set Point) (hs : MeasurableSet s) (phi : ℝ) :
    (∫ t in s, G phi t * continuousDensity t) =
      ∫ t in s ∩ HighNonunitLegal.legal 2 phi,
        LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
          (t 0 * t 1 * t 2 ^ 2 * t 3) := by
  have he : (∫ t in s, G phi t * continuousDensity t) =
      ∫ t in s ∩ HighNonunitLegal.legal 2 phi, G phi t * continuousDensity t := by
    rw [← setIntegral_indicator (HighNonunitLegal.legal_measurable 2 phi)]
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases hl : t ∈ HighNonunitLegal.legal 2 phi
    · simp only [Set.indicator_of_mem hl]
    · simp only [Set.indicator_of_notMem hl, HighNonunitLegal.G_of_illegal hl, G, zero_mul]
  rw [he]
  apply setIntegral_congr_fun (hs.inter (HighNonunitLegal.legal_measurable 2 phi))
  intro t ht
  exact weighted_legal_literal ht.2

theorem K16_literal (c e phi : ℝ) :
    K16 c e phi = ∫ t in D16 c e ∩ HighNonunitLegal.legal 2 phi,
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) :=
  integral_legal_literal (D16 c e) (D16_measurable c e) phi

theorem K17_literal (c e f phi : ℝ) :
    K17 c e f phi = ∫ t in D17 c e f ∩ HighNonunitLegal.legal 2 phi,
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) :=
  integral_legal_literal (D17 c e f) (D17_measurable c e f) phi

theorem K18_literal (c e f phi : ℝ) :
    K18 c e f phi = ∫ t in D18 c e f ∩ HighNonunitLegal.legal 2 phi,
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) :=
  integral_legal_literal (D18 c e f) (D18_measurable c e f) phi

theorem K19_literal (b c e f phi : ℝ) :
    K19 b c e f phi = ∫ t in D19 b c e f ∩ HighNonunitLegal.legal 2 phi,
      LiLiuPrereqBuchstab.buchstab ((phi - (t 0 + t 1 + t 2 + t 3)) / t 2) /
        (t 0 * t 1 * t 2 ^ 2 * t 3) :=
  integral_legal_literal (D19 b c e f) (D19_measurable b c e f) phi

end Wu2008DoubleSieve.FourPrimeContinuous
