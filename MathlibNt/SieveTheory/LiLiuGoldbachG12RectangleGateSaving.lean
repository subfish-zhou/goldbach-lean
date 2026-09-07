import MathlibNt.SieveTheory.LiLiuGoldbachG12RectangleGate
import MathlibNt.SieveTheory.LiLiuGoldbachG67NormalizedLower

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
open MathlibNt.SieveTheory.LiLiuPrereqWF
open AnalyticNumberTheory.LargeSieve MathlibNt.SieveTheory

namespace G12RectangleGate

/-- The cutoff depends only on the requested logarithmic saving. -/
theorem numerical_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀,
      (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 ≤
        N/Real.log (N : ℝ)^U := by
  have hgrowth : ∀ᶠ N : ℕ in atTop, (3200 : ℝ) ≤ (N : ℝ)^(2/53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2/53)).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  have hlogevent : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop 1)
  have hevent : ∀ᶠ N : ℕ in atTop, 4 ≤ N ∧ 1 ≤ Real.log (N : ℝ) ∧
      (3200 : ℝ) ≤ (N : ℝ)^(2/53 : ℝ) ∧
      Real.log (N : ℝ)^(U+2) ≤ (N : ℝ)^(2/53 : ℝ) := by
    filter_upwards [eventually_ge_atTop 4, hlogevent, hgrowth,
      PanPrincipal.eventually_log_rpow_le_rpow (U+2) (2/53) (by norm_num)]
      with N hN hl hc hp
    exact ⟨hN,hl,hc,hp⟩
  obtain ⟨M,hM⟩ := eventually_atTop.mp hevent
  refine ⟨max 4 M, le_max_left _ _, ?_⟩
  intro N hN
  obtain ⟨hN4,hl1,hc,hp⟩ := hM N ((le_max_right _ _).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log (N : ℝ) := by linarith
  have hz := Real.rpow_pos_of_pos hNpos (4/53 : ℝ)
  have hbudget : 3200*Real.log (N : ℝ)^2*Real.log (N : ℝ)^U ≤
      (N : ℝ)^(4/53 : ℝ) := by
    calc
      _ = 3200*Real.log (N : ℝ)^(U+2) := by
        rw [Real.rpow_add hl, Real.rpow_ofNat]
        ring
      _ ≤ (N : ℝ)^(2/53 : ℝ)*(N : ℝ)^(2/53 : ℝ) :=
        mul_le_mul hc hp (Real.rpow_nonneg hl.le _) (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ)^(4/53 : ℝ) := by rw [← Real.rpow_add hNpos]; norm_num
  have hsquare : (1+Real.log (N : ℝ))^2 ≤ 4*Real.log (N : ℝ)^2 := by
    calc
      _ ≤ (2*Real.log (N : ℝ))^2 := by gcongr; linarith
      _ = _ := by ring
  calc
    _ ≤ (800*N/(N : ℝ)^(4/53 : ℝ))*(4*Real.log (N : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hsquare (by positivity)
    _ ≤ N/Real.log (N : ℝ)^U := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hl U)).mpr
      calc
        _ = (N : ℝ)*(3200*Real.log (N : ℝ)^2*Real.log (N : ℝ)^U)/
            (N : ℝ)^(4/53 : ℝ) := by ring
        _ ≤ (N : ℝ)*(N : ℝ)^(4/53 : ℝ)/(N : ℝ)^(4/53 : ℝ) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hbudget hNpos.le) hz.le
        _ = N := mul_div_cancel_right₀ _ (ne_of_gt hz)

/-- Uniform in the atom subset, window, modulus carrier and full signed coefficient. -/
theorem gate_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (A : Finset (ℕ × ℕ))
      (Q : Finset ℕ) (c : ℕ → ℝ),
      linkEmbed A ⊆ goldbachG12LinkedAtoms N ε → Q ⊆ Icc 1 N →
      (∀ d ∈ reducedModuli Q (N : ℤ), |c d| ≤ 1) →
      |G12RectangleWF.gate N A Q c| ≤ N/Real.log (N : ℝ)^U := by
  obtain ⟨N₀,hN₀,h⟩ := numerical_log_saving U
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε A Q c hA hQ hc
  exact (gate_le (by omega) le_rfl hA hQ hc).trans (h N hN)

/-- Original body multiplicity 400 is included in the actual singular-series scale. -/
theorem gate_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (A : Finset (ℕ × ℕ))
      (Q : Finset ℕ) (c : ℕ → ℝ),
      linkEmbed A ⊆ goldbachG12LinkedAtoms N ε → Q ⊆ Icc 1 N →
      (∀ d ∈ reducedModuli Q (N : ℤ), |c d| ≤ 1) →
      400*|G12RectangleWF.gate N A Q c| ≤
        δ*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨K,hK,hg⟩ := gate_log_saving 3
  obtain ⟨L,hL⟩ := eventually_atTop.mp (goldbachBV_logCube_normalized 400 δ hδ)
  refine ⟨max K L,by omega,?_⟩
  intro N hN ε A Q c hA hQ hc
  have h := hg N (by omega) ε A Q c hA hQ hc
  simp only [Real.rpow_ofNat] at h
  calc
    _ ≤ 400*(N/Real.log (N : ℝ)^3) := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 400*N/Real.log (N : ℝ)^3 := by ring
    _ ≤ _ := hL N (by omega)

/-- Full real-level interval: no primorial or squarefree mask is introduced. -/
theorem real_interval_subset {N : ℕ} {Q : ℝ} (hQ : Q ≤ N) :
    Ioc 0 ⌊Q⌋₊ ⊆ Icc 1 N := by
  intro d hd
  obtain ⟨hd0,hdQ⟩ := mem_Ioc.mp hd
  have hf : ⌊Q⌋₊ ≤ N := by simpa only [Nat.floor_natCast] using Nat.floor_mono hQ
  exact mem_Icc.mpr ⟨hd0,hdQ.trans hf⟩

/-- WF1 is used only for its coefficient bound, at the absolute-gate payment step. -/
theorem gate_wellFactorable {N : ℕ} {ε Q : ℝ} {A : Finset (ℕ × ℕ)}
    {f : ArithmeticFunction ℝ} (hN : 2 ≤ N) (hQ : Q ≤ N)
    (hA : linkEmbed A ⊆ goldbachG12LinkedAtoms N ε) (hf : WellFactorable f Q) :
    |G12RectangleWF.gate N A (Ioc 0 ⌊Q⌋₊) f| ≤
      (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 :=
  gate_le hN le_rfl hA (real_interval_subset hQ) (fun d _ => hf.2.1 d)

/-- Literal original rectangle, under its already-proved inclusion geometry. -/
theorem rectangle_gate_le {N : ℕ} (hN : 2 ≤ N) (ε : ℝ) (M T : ℕ)
    (hlow : (N : ℝ)^(4/53 : ℝ) ≤ T)
    (hhigh : (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ))
    {Q : ℝ} (hQ : Q ≤ N) {f : ArithmeticFunction ℝ} (hf : WellFactorable f Q) :
    |G12RectangleWF.gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) f| ≤
      (800*N/(N : ℝ)^(4/53 : ℝ))*(1+Real.log (N : ℝ))^2 :=
  gate_wellFactorable hN hQ (G12RectangleWF.rectangle_image_subset N ε M T hlow hhigh) hf

/-- Fixed logarithmic saving for the actual full real-level rectangle gate. -/
theorem rectangle_gate_log_saving (U : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (M T : ℕ),
      (N : ℝ)^(4/53 : ℝ) ≤ T → (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ) →
      ∀ (Q : ℝ) (f : ArithmeticFunction ℝ), Q ≤ N → WellFactorable f Q →
      |G12RectangleWF.gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) f| ≤
        N/Real.log (N : ℝ)^U := by
  obtain ⟨N₀,hN₀,h⟩ := gate_log_saving U
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε M T hlo hhi Q f hQ hf
  exact h N hN ε _ _ f (G12RectangleWF.rectangle_image_subset N ε M T hlo hhi)
    (real_interval_subset hQ) (fun d _ => hf.2.1 d)

/-- The normalization cutoff is selected before every changing rectangle and WF member. -/
theorem rectangle_gate_normalized (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (ε : ℝ) (M T : ℕ),
      (N : ℝ)^(4/53 : ℝ) ≤ T → (2*T : ℕ) < (N : ℝ)^(1/10 : ℝ) →
      ∀ (Q : ℝ) (f : ArithmeticFunction ℝ), Q ≤ N → WellFactorable f Q →
      400*|G12RectangleWF.gate N (G12LowRectangle.rectangle N ε M T) (Ioc 0 ⌊Q⌋₊) f| ≤
        δ*(SingularSeries.liuSingularSeries N*N/Real.log (N : ℝ)^2) := by
  obtain ⟨N₀,hN₀,h⟩ := gate_normalized δ hδ
  refine ⟨N₀,hN₀,?_⟩
  intro N hN ε M T hlo hhi Q f hQ hf
  exact h N hN ε _ _ f (G12RectangleWF.rectangle_image_subset N ε M T hlo hhi)
    (real_interval_subset hQ) (fun d _ => hf.2.1 d)

end G12RectangleGate
