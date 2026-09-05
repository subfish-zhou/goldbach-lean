import MathlibNt.AnalyticNumberTheory.Chen1973.Chen1973Lemma6Equation21ActualShift
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section
open Filter
open scoped Topology
namespace AnalyticNumberTheory.LargeSieve

/-- The correctly transcribed exponent pays the source width for every later
conductor and cell, with a cutoff depending only on the positive constant. -/
theorem chen1973Lemma6_eq21_printedWidth_eventually
    {c : ℝ} (hc : 0 < c) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L : ℕ,
      (L : ℝ) ≤ Real.log x ^ (100 : ℕ) →
      Chen1973Lemma6Eq21ZeroFreeContourBridge x L c := by
  have hlim : Tendsto (fun x : ℕ => Real.log (x : ℝ) ^ (-(1 / 6 : ℝ)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 6)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  rw [← Filter.eventually_atTop]
  filter_upwards [hlim.eventually_le_const hc, Filter.eventually_ge_atTop (3 : ℕ)]
    with x hsmall hx
  intro L hL d hd
  have hlog : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hd0 : (0 : ℝ) < d := by
    exact_mod_cast (lt_trans Nat.zero_lt_one (chen1973Lemma6_eq21_one_lt_conductor hd))
  have hdL : (d : ℝ) ≤ L := by exact_mod_cast chen1973Lemma6_eq21_conductor_le hd
  have hdle : (d : ℝ) ≤ Real.log x ^ (100 : ℕ) := hdL.trans hL
  have hpow : (d : ℝ) ^ ((1 : ℝ) / 300) ≤ Real.log x ^ ((1 : ℝ) / 3) := by
    calc
      _ ≤ (Real.log x ^ (100 : ℕ)) ^ ((1 : ℝ) / 300) :=
        Real.rpow_le_rpow hd0.le hdle (by positivity)
      _ = Real.log x ^ ((1 : ℝ) / 3) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le]
        norm_num
  have hscale : Real.log x ^ ((1 : ℝ) / 3) ≤ c * Real.sqrt (Real.log x) := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 hlog)).mp
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hlog]
    norm_num at hsmall ⊢
    exact hsmall
  apply (div_le_div_iff₀ (Real.sqrt_pos.2 hlog)
    (Real.rpow_pos_of_pos hd0 _)).mpr
  simpa using hpow.trans hscale

/-- The corrected printed region contains every actual source shell. -/
theorem chen1973Lemma6_eq21_actualShell_subset_primeRegion (x B k m : ℕ) :
    chen1973Lemma6PrimePairShell x B k m ⊆ chen1973Lemma6Eq21PrimeRegion x := by
  intro pp hpp
  have hp : pp ∈ chen1973Lemma5PrimePairs x :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hpp).1).1
  have hconditions := (Finset.mem_filter.mp hp).2
  apply Finset.mem_filter.mpr
  refine ⟨hp, hconditions.2.2.1, hconditions.2.2.2.1,
    hconditions.2.2.2.2.1, ?_⟩
  simpa only [Real.sqrt_eq_rpow] using hconditions.2.2.2.2.2

/-- Corrected transcription eliminates both the extra width bridge and the
shell-region hypothesis. Full-height zero-freeness, boundary payments, and the
primitive vertical estimate are still genuine inputs. -/
theorem chen1973Lemma6_equation21_levelZero_eventually_of_source_analytic_inputs
    (Cvert c : ℝ) (hc : 0 < c) :
    ∃ x₀ : ℕ, ∀ x ≥ x₀, ∀ L B k m l₂ : ℕ,
      Chen1973Lemma6Eq21SourceParameters x L B k m l₂ →
      Chen1973Lemma6Eq21ZeroFreeInput x L c →
      (∀ d ∈ chen1973Lemma6ConductorBlock x L 0,
        ∀ χ : PrimitiveCharacter d, ∀ pp ∈ chen1973Lemma6PrimePairShell x B k m,
          Chen1973Lemma6Eq21TermBoundaryPayments x d χ pp) →
      Chen1973Lemma6Eq21PrimitiveVerticalEstimate Cvert x L B k m →
      chen1973Lemma6NmBlockActual x L 0 B k m ≤
        (x : ℝ) / Real.log x ^ (20 : ℕ) := by
  obtain ⟨x₁, hwidth⟩ := chen1973Lemma6_eq21_printedWidth_eventually hc
  obtain ⟨x₂, hfinal⟩ :=
    chen1973Lemma6_equation21_levelZero_eventually_of_boundary_inputs Cvert
  refine ⟨max x₁ x₂, ?_⟩
  intro x hx L B k m l₂ P hzero hboundary hvert
  exact hfinal x ((le_max_right _ _).trans hx) L B k m l₂ c P
    (chen1973Lemma6_eq21_actualShell_subset_primeRegion x B k m) hzero
    (hwidth x ((le_max_left _ _).trans hx) L P.hL_lower) hboundary hvert

end AnalyticNumberTheory.LargeSieve