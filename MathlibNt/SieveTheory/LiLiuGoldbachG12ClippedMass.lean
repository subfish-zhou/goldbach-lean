import MathlibNt.SieveTheory.LiLiuGoldbachG12ClippedDistribution

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open Wu2004MeanValue AnalyticNumberTheory.Sieve AnalyticNumberTheory.LargeSieve
namespace G12ClippedWindow

/-- The common mass has no modulus argument. -/
def mass (N : ℕ) (g L U : ℕ → ℝ) : ℝ :=
  ∑ m ∈ goldbachG12ActiveProductSupport N, g m * (window N L U m).card

def gateLoss (N : ℕ) (g L U : ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => ¬m.Coprime d),
    g m * (window N L U m).card) / (d.totient : ℝ)

def divisorResidual (N : ℕ) (g L U : ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
  (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
    g m * (PanPrincipal.primeCount ⌊U m⌋₊ -
      PanPrincipal.primeCount ⌊L m⌋₊)) / (d.totient : ℝ)

/-- Actual full-support divisor count, centered at one modulus-independent mass. -/
def commonResidual (N : ℕ) (g L U : ℕ → ℝ) (d : ℕ) : ℝ :=
  (∑ m ∈ goldbachG12ActiveProductSupport N, g m *
    (((window N L U m).filter (fun r => d ∣ N-r*m)).card : ℝ)) -
    mass N g L U / (d.totient : ℝ)

variable {N : ℕ} {ε : ℝ} {g L U : ℕ → ℝ}

theorem mass_nonneg (h : Admissible N ε g L U) : 0 ≤ mass N g L U :=
  sum_nonneg fun m hm => mul_nonneg (h m hm).1.1 (Nat.cast_nonneg _)

theorem gateLoss_nonneg (h : Admissible N ε g L U) (d : ℕ) :
    0 ≤ gateLoss N g L U d :=
  div_nonneg (sum_nonneg fun m hm =>
    mul_nonneg (h m (mem_filter.mp hm).1).1.1 (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Both the coefficient and the literal window are dominated by the old gate. -/
theorem gateLoss_le (h : Admissible N ε g L U) (d : ℕ) :
    gateLoss N g L U d ≤ goldbachG12PrimeWindowGateLoss N ε d := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply sum_le_sum
  intro m hm
  have hs := (mem_filter.mp hm).1
  exact mul_le_mul (h m hs).1.2
    (by exact_mod_cast card_le_card (window_subset h hs)) (Nat.cast_nonneg _)
    (goldbachG12NormalizedCoefficient_bounds N m).1

theorem mass_eq_gated_add (N d : ℕ) (g L U : ℕ → ℝ) :
    mass N g L U =
      (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
        g m * (window N L U m).card) +
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => ¬m.Coprime d),
        g m * (window N L U m).card := by
  rw [mass, sum_filter, sum_filter, ← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  by_cases h : m.Coprime d <;> simp [h]

theorem apWindow_eq_output_dvd (h : Admissible N ε g L U) (d : ℕ)
    {m : ℕ} (hm : m ∈ goldbachG12ActiveProductSupport N) :
    (window N L U m).filter (fun r => Nat.ModEq d (m*r) N) =
      (window N L U m).filter (fun r => d ∣ N-r*m) := by
  apply Finset.ext
  intro r
  simp only [Finset.mem_filter]
  apply and_congr_right
  intro hr
  rw [Nat.mul_comm m r, Nat.modEq_iff_dvd'
    (goldbachG12LinkedPrimeWindow_product_le hm (window_subset h hm hr))]

theorem outputDivisors_empty (h : Admissible N ε g L U) {m d : ℕ}
    (hm : m ∈ goldbachG12ActiveProductSupport N)
    (hNd : N.Coprime d) (hmd : ¬m.Coprime d) :
    (window N L U m).filter (fun r => d ∣ N-r*m) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro r hr
  have hx := (filter_subset_filter (fun r => d ∣ N-r*m) (window_subset h hm)) hr
  rw [goldbachG12Linked_outputDivisors_empty hm hNd hmd] at hx
  exact Finset.notMem_empty r hx

theorem divisorResidual_eq (hN : 2 ≤ N) (h : Admissible N ε g L U)
    (d : ℕ) (hNd : N.Coprime d) :
    divisorResidual N g L U d = residual N g L U d N := by
  have hc : (∑ m ∈ goldbachG12ActiveProductSupport N,
      g m * (((window N L U m).filter (fun r => d ∣ N-r*m)).card : ℝ)) =
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
      g m * (((window N L U m).filter (fun r => d ∣ N-r*m)).card : ℝ) := by
    rw [sum_filter]
    apply sum_congr rfl
    intro m hm
    by_cases hmd : m.Coprime d
    · simp only [if_pos hmd]
    · rw [if_neg hmd, outputDivisors_empty h hm hNd hmd]
      simp
  unfold divisorResidual residual
  rw [hc, Finset.sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m hm
  obtain ⟨hm, hmd⟩ := mem_filter.mp hm
  have hcount := apWindow_card_eq_inverse h d N hN hm hmd
  rw [apWindow_eq_output_dvd h d hm] at hcount
  rw [hcount]
  ring

theorem commonResidual_eq (hN : 2 ≤ N) (h : Admissible N ε g L U) (d : ℕ) :
    commonResidual N g L U d = divisorResidual N g L U d - gateLoss N g L U d := by
  have hmass : (∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
      g m * (PanPrincipal.primeCount ⌊U m⌋₊ - PanPrincipal.primeCount ⌊L m⌋₊)) =
      ∑ m ∈ (goldbachG12ActiveProductSupport N).filter (fun m => m.Coprime d),
      g m * (window N L U m).card := by
    apply sum_congr rfl
    intro m hm
    rw [window_card hN h (mem_filter.mp hm).1]
  unfold commonResidual divisorResidual gateLoss
  rw [hmass, mass_eq_gated_add N d g L U]
  ring

theorem commonResidual_sum_le (hN : 2 ≤ N) (h : Admissible N ε g L U) (Q : ℕ) :
    (∑ d ∈ goldbachG11LinkedModuli N Q, |commonResidual N g L U d|) ≤
      (∑ d ∈ goldbachG11LinkedModuli N Q, |residual N g L U d N|) +
      ∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d := by
  calc
    _ ≤ ∑ d ∈ goldbachG11LinkedModuli N Q,
        (|residual N g L U d N| + goldbachG12PrimeWindowGateLoss N ε d) := by
      apply sum_le_sum
      intro d hd
      rw [commonResidual_eq hN h, divisorResidual_eq hN h d (mem_filter.mp hd).2.2]
      exact (abs_sub _ _).trans (add_le_add le_rfl
        (by simpa only [abs_of_nonneg (gateLoss_nonneg h d)] using gateLoss_le h d))
    _ = (∑ d ∈ goldbachG11LinkedModuli N Q, |residual N g L U d N|) +
        ∑ d ∈ goldbachG11LinkedModuli N Q, goldbachG12PrimeWindowGateLoss N ε d :=
      sum_add_distrib
    _ ≤ _ := add_le_add le_rfl
      (sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun d _ _ => goldbachG12PrimeWindowGateLoss_nonneg N d ε))

/-- The cutoff precedes every coefficient, endpoint, epsilon and modulus cutoff. -/
theorem commonResidual_log_saving (A : ℝ) (hA : 0 < A) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N ≥ N₀, ∀ (g L U : ℕ → ℝ) (ε : ℝ) (Q : ℕ),
      Admissible N ε g L U →
      (Q : ℝ) ≤ Real.sqrt N / Real.log (N : ℝ) ^ B →
      (∑ d ∈ goldbachG11LinkedModuli N Q, |commonResidual N g L U d|) ≤
        C * N / Real.log (N : ℝ) ^ A := by
  obtain ⟨B, C, hB, hC, M, hM4, hdist⟩ := residual_squarefree A hA
  obtain ⟨K, _, hgate⟩ := goldbachG12PrimeWindowGateLoss_log_saving A
  have hlogevent : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  obtain ⟨J, hJ⟩ := eventually_atTop.mp hlogevent
  refine ⟨B, C + 1, hB, by positivity, max M (max K J),
    hM4.trans (le_max_left _ _), ?_⟩
  intro N hN g L U ε Q had hQ
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNK : K ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNJ : J ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : 2 ≤ N := by omega
  have hQN := goldbachG11LinkedLevel_le hN2 hB (hJ N hNJ) hQ
  calc
    _ ≤ (∑ d ∈ goldbachG11LinkedModuli N Q, |residual N g L U d N|) +
        ∑ d ∈ Icc 1 Q, goldbachG12PrimeWindowGateLoss N ε d :=
      commonResidual_sum_le hN2 had Q
    _ ≤ C * N / Real.log (N : ℝ) ^ A + N / Real.log (N : ℝ) ^ A :=
      add_le_add (hdist N hNM g L U ε Q had hQ) (hgate N hNK ε Q hQN)
    _ = (C + 1) * N / Real.log (N : ℝ) ^ A := by ring

end G12ClippedWindow
