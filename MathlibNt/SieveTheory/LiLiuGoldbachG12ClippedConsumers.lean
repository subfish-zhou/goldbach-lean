import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedMass

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

/-- The high specialization retains the original normalized product coefficient. -/
theorem high_admissible {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) :
    Admissible N ε (goldbachG12NormalizedCoefficient N)
      (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) := by
  intro m hm
  exact ⟨⟨(goldbachG12NormalizedCoefficient_bounds N m).1, le_rfl⟩,
    (G12LowHighOutput.highLo_bounds hN hm).1,
    (G12LowHighOutput.highLo_bounds hN hm).2, le_rfl⟩

theorem high_window (N m : ℕ) (ε : ℝ) :
    window N (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) m =
      G12LowHighOutput.highWindow N ε m := by
  ext r
  simp only [window, mem_filter, G12LowHighOutput.mem_highWindow]

/-- This is the actual high AP count, not a residual defined by subtraction from low. -/
def highAPResidual (N : ℕ) (ε : ℝ) (d b : ℕ) : ℝ :=
  ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
    goldbachG12NormalizedCoefficient N m *
      ((((G12LowHighOutput.highWindow N ε m).filter
        (fun r => Nat.ModEq d (m*r) b)).card : ℝ) -
        ((G12LowHighOutput.highWindow N ε m).card : ℝ) / (d.totient : ℝ))

/-- The actual high AP producer is consumed at the unchanged inverse residue. -/
theorem highAPResidual_eq {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) (d b : ℕ) :
    highAPResidual N ε d b = residual N (goldbachG12NormalizedCoefficient N)
      (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) d b := by
  unfold highAPResidual residual
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm,hmd⟩ := mem_filter.mp hm
  rw [G12LowHighOutput.highAPWindow_card_eq_inverse d b hN hm hmd]
  have hc := window_card hN (high_admissible hN ε) hm
  rw [high_window] at hc
  rw [hc]

/-- A weighted estimate for the literal high AP residual with one common source. -/
theorem highAPResidual_weighted (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ) (b : ℕ → ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * |highAPResidual N ε d (b d)|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B,C,hB,hC,K,hK,h⟩ := residual_weighted A hA
  refine ⟨B,C,hB,hC,K,hK,?_⟩
  intro N hN ε Q b hQ hb
  have hN2 : 2 ≤ N := by omega
  simp_rw [highAPResidual_eq hN2]
  exact h N hN _ _ _ ε Q b (high_admissible hN2 ε) hQ hb

/-- The actual high mass is independent of d. -/
def highMass (N : ℕ) (ε : ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m * (G12LowHighOutput.highWindow N ε m).card

def highCommonResidual (N : ℕ) (ε : ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG12ActiveProductSupport N,
    goldbachG12NormalizedCoefficient N m *
      (((G12LowHighOutput.highWindow N ε m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
    highMass N ε / (d.totient : ℝ)

theorem highCommonResidual_eq (N : ℕ) (ε : ℝ) (d : ℕ) :
    highCommonResidual N ε d = commonResidual N (goldbachG12NormalizedCoefficient N)
      (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) d := by
  simp only [highCommonResidual, commonResidual, highMass, mass, high_window]

/-- Exact bridge from the actual high AP consumer to its common mass. -/
theorem highCommonResidual_eq_AP {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) (d : ℕ)
    (hNd : N.Coprime d) :
    highCommonResidual N ε d = highAPResidual N ε d N -
      gateLoss N (goldbachG12NormalizedCoefficient N)
        (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) d := by
  rw [highCommonResidual_eq, commonResidual_eq hN (high_admissible hN ε),
    divisorResidual_eq hN (high_admissible hN ε) d hNd, highAPResidual_eq hN]

/-- Paid high common-mass distribution. It is not full upper bound minus low upper bound. -/
theorem highCommonResidual_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q, |highCommonResidual N ε d|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B,C,hB,hC,K,hK,h⟩ := commonResidual_log_saving A hA
  refine ⟨B,C,hB,hC,K,hK,?_⟩
  intro N hN ε Q hQ
  have hN2 : 2 ≤ N := by omega
  have heq : ∀ d ∈ goldbachG11LinkedModuli N Q,
      highCommonResidual N ε d = commonResidual N (goldbachG12NormalizedCoefficient N)
        (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) d := by
    intro d hd
    rw [highCommonResidual_eq_AP hN2 ε d (mem_filter.mp hd).2.2,
      highAPResidual_eq hN2, commonResidual_eq hN2 (high_admissible hN2 ε),
      divisorResidual_eq hN2 (high_admissible hN2 ε) d (mem_filter.mp hd).2.2]
  calc
    _ = ∑ d ∈ goldbachG11LinkedModuli N Q,
        |commonResidual N (goldbachG12NormalizedCoefficient N)
          (G12LowHighOutput.highLo N ε) (goldbachG11PiLiHi N) d| :=
      sum_congr rfl (fun d hd => congrArg abs (heq d hd))
    _ ≤ _ := h N hN _ _ _ ε Q (high_admissible hN2 ε) hQ

/-- Only the long cofactor is masked; no short-prime selection is hidden here. -/
def longMask (N : ℕ) (cellLong longOK : ℕ → Prop) (m : ℕ) : ℝ :=
  if cellLong m ∧ ¬longOK m then goldbachG12NormalizedCoefficient N m else 0

/-- Normalize an empty upper window to oldLo, rather than asserting an unchecked endpoint ≥ 2. -/
def clampUpper (N : ℕ) (ε : ℝ) (V : ℕ → ℝ) (m : ℕ) : ℝ :=
  max (goldbachG11PiLiLo N ε m) (min (goldbachG11PiLiHi N m) (V m))

def clampLower (N : ℕ) (ε : ℝ) (T V : ℕ → ℝ) (m : ℕ) : ℝ :=
  min (clampUpper N ε V m) (max (goldbachG11PiLiLo N ε m) (T m))

theorem clamp_admissible {N : ℕ} (hN : 2 ≤ N) (ε : ℝ)
    (cellLong longOK : ℕ → Prop) (T V : ℕ → ℝ) :
    Admissible N ε (longMask N cellLong longOK)
      (clampLower N ε T V) (clampUpper N ε V) := by
  intro m hm
  have ho := (goldbachG12PiLiEndpoints_bounds (ε := ε) hN hm).2.1
  refine ⟨?_,?_,min_le_left _ _,?_⟩
  · unfold longMask
    split_ifs
    · exact ⟨(goldbachG12NormalizedCoefficient_bounds N m).1,le_rfl⟩
    · exact ⟨le_rfl,(goldbachG12NormalizedCoefficient_bounds N m).1⟩
  · exact le_min (le_max_left _ _) (le_max_left _ _)
  · exact max_le ho ((min_le_left _ _).trans le_rfl)

theorem clampUpper_eq_raw {N m : ℕ} {ε : ℝ} {V : ℕ → ℝ}
    (hN : 2 ≤ N) (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hV : goldbachG11PiLiLo N ε m ≤ V m) :
    clampUpper N ε V m = min (goldbachG11PiLiHi N m) (V m) := by
  exact max_eq_right (le_min (goldbachG12PiLiEndpoints_bounds hN hm).2.1 hV)

theorem clamp_empty_below_oldLo {N m : ℕ} {ε : ℝ} {T V : ℕ → ℝ}
    (hV : V m ≤ goldbachG11PiLiLo N ε m) :
    clampLower N ε T V m = goldbachG11PiLiLo N ε m ∧
      clampUpper N ε V m = goldbachG11PiLiLo N ε m := by
  have hu : clampUpper N ε V m = goldbachG11PiLiLo N ε m :=
    max_eq_left ((min_le_right _ _).trans hV)
  exact ⟨by rw [clampLower, hu, min_eq_left (le_max_left _ _)], hu⟩

/-- Even the empty-window endpoints meet the producer's lower endpoint requirement. -/
theorem clamp_endpoints_two {N : ℕ} (hN : 2 ≤ N)
    (hz : 2 ≤ (N : ℝ)^(4/53 : ℝ)) (ε : ℝ) (T V : ℕ → ℝ)
    {m : ℕ} (hm : m ∈ goldbachG12ActiveProductSupport N) :
    2 ≤ clampLower N ε T V m ∧ 2 ≤ clampUpper N ε V m := by
  have h := clamp_admissible hN ε (fun _ => True) (fun _ => False) T V m hm
  have hlo := (goldbachG12Linked_profiles_and_coefficient (ε := ε) hN hz hm).2.1.1
  exact ⟨hlo.trans h.2.1, (hlo.trans h.2.1).trans h.2.2.1⟩

/-- The generic common-mass estimate applies uniformly to every pure long mask and cell. -/
theorem longMask_common_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (cellLong longOK : ℕ → Prop) (T V : ℕ → ℝ) (ε : ℝ) (Q : ℕ),
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ)^B →
      (∑ d ∈ goldbachG11LinkedModuli N Q,
        |commonResidual N (longMask N cellLong longOK)
          (clampLower N ε T V) (clampUpper N ε V) d|) ≤
        C * N / Real.log (N : ℝ)^A := by
  obtain ⟨B,C,hB,hC,K,hK,h⟩ := commonResidual_log_saving A hA
  refine ⟨B,C,hB,hC,K,hK,?_⟩
  intro N hN cellLong longOK T V ε Q hQ
  exact h N hN _ _ _ ε Q (clamp_admissible (by omega) ε cellLong longOK T V) hQ

end G12ClippedWindow
