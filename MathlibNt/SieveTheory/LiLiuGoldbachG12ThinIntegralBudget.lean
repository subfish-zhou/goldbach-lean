import MathlibNt.SieveTheory.LiLiuGoldbachG12ThinCofactorMass
import MathlibNt.SieveTheory.LiLiuGoldbachG12PrimeKernelIntegralBound

open Finset Set Filter LiLiuPrereqBuchstab
open scoped BigOperators Topology
noncomputable section
namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

/-- Real differences retain the two original integer rough counts. The
endpoints may vary with each original label; no uniformity in e0 at zero. -/
def goldbachG12ThinSum (N : ℕ) (l₁ l₂ : GoldbachG11Label → ℝ) : ℝ :=
  ∑ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
    ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
      ((roughCount (l₂ v*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) -
        (roughCount (l₁ v*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ))

theorem goldbachG12ThinSum_le_kernel
    (e₀ : ℝ) (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1)
    (w : ℝ) (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ l₁ l₂ : GoldbachG11Label → ℝ,
      (∀ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
        e₀ ≤ l₁ v ∧ l₁ v ≤ l₂ v ∧ l₂ v ≤ 1 ∧ l₂ v-l₁ v ≤ w) →
      Real.log (N : ℝ)/(N : ℝ)*goldbachG12ThinSum N l₁ l₂ ≤
        ((564383/1000000 : ℝ)*w+η)*goldbachG12PrimeKernel (fun _ => 1) N := by
  obtain ⟨N₀,hN₀,hb⟩ := goldbachG12Thin_cofactor_budget e₀ he₀ he₁ η hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN l₁ l₂ hs
  have hN4 : 4 ≤ N := hN₀.trans hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  unfold goldbachG12ThinSum goldbachG12PrimeKernel
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v hv
  obtain ⟨hl,hle,hh,hw⟩ := hs v hv
  have hg := goldbachG12PrimeKernel_logGeometry hN4 hv
  have hp := hb N hN v hv (l₁ v) (l₂ v) hl hle hh
  have hm : (roughCount (l₂ v*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) -
      (roughCount (l₁ v*((N : ℝ)/goldbachG11LabelProd v)) v.2.2.2 : ℝ) ≤
      ((564383/1000000 : ℝ)*w+η)*((N : ℝ)/goldbachG11LabelProd v)/
        Real.log (v.2.2.2 : ℝ) := hp.trans (by gcongr)
  calc
    _ ≤ Real.log (N : ℝ)/(N : ℝ)*
        (((564383/1000000 : ℝ)*w+η)*((N : ℝ)/goldbachG11LabelProd v)/
          Real.log (v.2.2.2 : ℝ)) := mul_le_mul_of_nonneg_left hm (div_nonneg hlog hNp.le)
    _ = (((564383/1000000 : ℝ)*w+η)*Real.log (N : ℝ)/
        ((goldbachG11LabelProd v : ℝ)*Real.log (v.2.2.2 : ℝ)))*((N : ℝ)/N) := by ring
    _ = _ := by rw [div_self hNp.ne']; ring

/-- Aggregate thin-window budget at the raw-mother normalization log(N)/N.
This consumes both actual Buchstab counts and original cross quadrature.
It deliberately asserts neither a second logarithm nor an output-prime bound. -/
theorem goldbachG12ThinSum_integral_budget
    (e₀ : ℝ) (he₀ : 0 < e₀) (he₁ : e₀ ≤ 1)
    (w : ℝ) (hw : 0 ≤ w) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ l₁ l₂ : GoldbachG11Label → ℝ,
      (∀ v ∈ goldbachG12Labels N ((N : ℝ)^(4/53 : ℝ))
        ((N : ℝ)^(4/33 : ℝ)) ((N : ℝ)^(3/11 : ℝ)),
        e₀ ≤ l₁ v ∧ l₁ v ≤ l₂ v ∧ l₂ v ≤ 1 ∧ l₂ v-l₁ v ≤ w) →
      Real.log (N : ℝ)/(N : ℝ)*goldbachG12ThinSum N l₁ l₂ ≤
        (564383/1000000 : ℝ)*w*goldbachG12PrimeIntegral (fun _ => 1)+δ := by
  let W : ℝ := 564383/1000000
  let I := goldbachG12PrimeIntegral (fun _ => 1)
  have hc : ContinuousAt (fun t : ℝ => (W*w+t)*(I+t)) 0 := by fun_prop
  obtain ⟨r,hr,hs⟩ := Metric.continuousAt_iff.mp hc δ hδ
  let η := r/2
  have hη : 0 < η := half_pos hr
  have hh := hs (show dist η 0 < r by simp only [Real.dist_eq,sub_zero,abs_of_pos hη]; dsimp [η]; linarith)
  have he : (W*w+η)*(I+η) ≤ W*w*I+δ := by
    rw [Real.dist_eq] at hh
    have := (abs_lt.mp hh).2
    nlinarith only [this]
  obtain ⟨N₁,hN₁,hb⟩ := goldbachG12ThinSum_le_kernel e₀ he₀ he₁ w η hη
  obtain ⟨N₂,hN₂,hk⟩ := goldbachG12PrimeKernel_one_le_integral_eventually η hη
  refine ⟨max N₁ N₂, hN₁.trans (le_max_left _ _), ?_⟩
  intro N hN l₁ l₂ hsc
  have h₁ := hb N ((le_max_left _ _).trans hN) l₁ l₂ hsc
  have h₂ := mul_le_mul_of_nonneg_left (hk N ((le_max_right _ _).trans hN))
    (show 0 ≤ W*w+η by dsimp [W]; positivity)
  exact h₁.trans (h₂.trans he)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
