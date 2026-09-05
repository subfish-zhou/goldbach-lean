import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiCanonicalXiConstruction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Order.ProjIcc

open Set Filter Topology MeasureTheory intervalIntegral
open scoped Interval

namespace Section10Lemma1022

set_option autoImplicit false
set_option maxHeartbeats 800000

open Section10CanonicalXi

/-- Suzuki's phase in Lemma 10.22, with the harmless `s + exp 1`
normalization already built in. -/
noncomputable def lowerPhase (b c s : ℝ) : ℝ :=
  (∫ t in b..s, xi (t / b)) + c * Real.log (s + Real.exp 1)

lemma lowerPhase_continuousOn {s₀ b c : ℝ} (hs₀ : 0 ≤ s₀) :
    ContinuousOn (lowerPhase b c) (Ici s₀) := by
  have hxi : Continuous (fun t : ℝ => xi (t / b)) :=
    xi_continuous.comp (continuous_id.div_const b)
  have hprimitive : Continuous (fun s : ℝ => ∫ t in b..s, xi (t / b)) :=
    intervalIntegral.continuous_primitive
      (fun a d => hxi.intervalIntegrable a d) b
  have harg : Continuous (fun s : ℝ => s + Real.exp 1) :=
    continuous_id.add continuous_const
  intro s hs
  have hne : s + Real.exp 1 ≠ 0 := by
    have : 0 < s + Real.exp 1 := add_pos_of_nonneg_of_pos (hs₀.trans hs) (Real.exp_pos 1)
    exact ne_of_gt this
  exact hprimitive.continuousAt.add
    ((harg.continuousAt.log hne).const_mul c) |>.continuousWithinAt

/-- The weighted function used in the least-downward-crossing argument. -/
noncomputable def lowerWeighted (f : ℝ → ℝ) (b c s : ℝ) : ℝ :=
  f s * Real.exp (lowerPhase b c s)

lemma lowerWeighted_continuousOn {f : ℝ → ℝ} {s₀ b c : ℝ}
    (hs₀ : 0 ≤ s₀) (hf : ContinuousOn f (Ici s₀)) :
    ContinuousOn (lowerWeighted f b c) (Ici s₀) := by
  exact hf.mul ((Real.continuous_exp.comp_continuousOn
    (lowerPhase_continuousOn hs₀)))

/-- Abstract topological core of Suzuki's least-downward-crossing argument.
The `hboost` premise is the strict one-step estimate (10.38), not a barrier
conclusion or a pre-packaged first-crossing exclusion. -/
lemma least_downward_crossing
    {g : ℝ → ℝ} {S L : ℝ}
    (hcont : ContinuousOn g (Ici (S - 1)))
    (hinit : ∀ t ∈ Icc (S - 1) S, L ≤ g t)
    (hboost : ∀ s, S ≤ s →
      (∀ t ∈ Icc (s - 1) s, L ≤ g t) → L < g s) :
    ∀ s, S ≤ s → L < g s := by
  intro x hx
  by_contra hnot
  have hxL : g x ≤ L := le_of_not_gt hnot
  have hGS : L < g S := hboost S le_rfl hinit
  have hcross : ∃ z ∈ Icc S x, g z = L := by
    have himage := intermediate_value_Icc' hx
      (hcont.mono (by intro u hu; exact le_trans (by linarith [hu.1]) hu.1))
    have hLI : L ∈ Icc (g x) (g S) := ⟨hxL, hGS.le⟩
    rcases himage hLI with ⟨z, hz, hzeq⟩
    exact ⟨z, hz, hzeq⟩
  let G : ℝ → ℝ := fun u => g (max (S - 1) u)
  let B : Set ℝ := Icc S x ∩ {u | G u = L}
  have hBne : B.Nonempty := by
    rcases hcross with ⟨z, hz, hzeq⟩
    refine ⟨z, hz, ?_⟩
    dsimp only [G]
    change g (max (S - 1) z) = L
    rw [max_eq_right (by linarith [hz.1])]
    exact hzeq
  have hG : Continuous (fun u : ℝ => g (max (S - 1) u)) := by
    change Continuous (g ∘ fun u : ℝ => max (S - 1) u)
    apply continuousOn_univ.mp
    exact hcont.comp
      (continuous_const.max continuous_id).continuousOn
      (by intro u _; simp)
  have hbadClosed : IsClosed {u : ℝ | G u = L} := by
    exact isClosed_eq hG continuous_const
  have hBcompact : IsCompact B := isCompact_Icc.inter_right hbadClosed
  obtain ⟨z, hzleast⟩ := hBcompact.exists_isLeast hBne
  have hzB := hzleast.1
  have hzS : S ≤ z := hzB.1.1
  have hzg : g z = L := by
    have := hzB.2
    dsimp only [G] at this
    change g (max (S - 1) z) = L at this
    rw [max_eq_right (by linarith [hzS])] at this
    exact this
  have hwindow : ∀ t ∈ Icc (z - 1) z, L ≤ g t := by
    intro t ht
    by_cases htS : t < S
    · exact hinit t ⟨by linarith [ht.1, hzS], le_of_lt htS⟩
    · have htS' : S ≤ t := le_of_not_gt htS
      by_cases htz : t = z
      · subst t
        exact hzg.ge
      · have htz' : t < z := lt_of_le_of_ne ht.2 htz
        by_contra htbad
        have htbad' : g t < L := lt_of_not_ge htbad
        have himage := intermediate_value_Icc' htS'
          (hcont.mono (by intro u hu; exact le_trans (by linarith [hu.1]) hu.1))
        have hLI : L ∈ Icc (g t) (g S) := ⟨htbad'.le, hGS.le⟩
        rcases himage hLI with ⟨y, hy, hyeq⟩
        have hyB : y ∈ B := by
          refine ⟨⟨hy.1, le_trans hy.2 (le_trans ht.2 hzB.1.2)⟩, ?_⟩
          dsimp only [G]
          change g (max (S - 1) y) = L
          rw [max_eq_right (by linarith [hy.1])]
          exact hyeq
        have hzy := hzleast.2 hyB
        linarith [hy.2]
  exact (not_lt_of_ge hzg.le) (hboost z hzS hwindow)



end Section10Lemma1022
