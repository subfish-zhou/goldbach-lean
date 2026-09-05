/-
Temporary κ = 1 finite-source package for Suzuki, Proposition 9.3.
The proofs use the source-correct recursion through `KappaOneModel.layer`.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayersKappaOne

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

open KappaOneModel

noncomputable section

private lemma parityDomain_eq_of_mod_eq {β : ℝ} {m n : ℕ}
    (h : m % 2 = n % 2) : parityDomain β m = parityDomain β n := by
  simp only [parityDomain, h]

private lemma sourceTerm_continuousOn {β : ℝ} (hβ : 1 < β) (N n : ℕ) :
    ContinuousOn (fun s => if n % 2 = N % 2 then suzukiLayer 1 β n s else 0)
      (parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := continuousOn_parityDomain hβ n
    rw [parityDomain_eq_of_mod_eq h] at hn
    exact hn.congr fun s _ => (layer_eq_suzukiLayer β n s).symm
  · simp only [h, if_false]
    exact continuousOn_const

private lemma sourceTerm_nonneg {β : ℝ} (hβ : 1 < β) (N n : ℕ)
    {s : ℝ} (hs : s ∈ parityDomain β N) :
    0 ≤ (if n % 2 = N % 2 then suzukiLayer 1 β n s else 0) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    rw [← layer_eq_suzukiLayer]
    apply nonneg_on_parityDomain hβ n s
    rwa [parityDomain_eq_of_mod_eq h]
  · simp [h]

private lemma sourceTerm_weighted_antitone {β : ℝ} (hβ : 1 < β) (N n : ℕ) :
    AntitoneOn
      (fun s => s * (if n % 2 = N % 2 then suzukiLayer 1 β n s else 0))
      (parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := weighted_antitoneOn_parityDomain hβ n
    rw [parityDomain_eq_of_mod_eq h] at hn
    intro s hs t ht hst
    simpa only [← layer_eq_suzukiLayer] using hn hs ht hst
  · simp only [h, if_false, mul_zero]
    intro s hs t ht hst
    exact le_rfl

private lemma sourceTerm_antitone {β : ℝ} (hβ : 1 < β) (N n : ℕ) :
    AntitoneOn
      (fun s => if n % 2 = N % 2 then suzukiLayer 1 β n s else 0)
      (parityDomain β N) := by
  by_cases h : n % 2 = N % 2
  · simp only [h, if_true]
    have hn := antitoneOn_parityDomain hβ n
    rw [parityDomain_eq_of_mod_eq h] at hn
    intro s hs t ht hst
    simpa only [← layer_eq_suzukiLayer] using hn hs ht hst
  · simp only [h, if_false]
    intro s hs t ht hst
    exact le_rfl

/-- Proposition 9.3, κ=1: the finite source layer is continuous on its exact
Suzuki parity domain. -/
theorem finiteSourceLayer_continuousOn_parityDomain {β : ℝ} (hβ : 1 < β)
    (N : ℕ) : ContinuousOn (finiteSourceLayer 1 β N) (parityDomain β N) := by
  classical
  unfold finiteSourceLayer
  induction Finset.Icc 1 N using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact continuousOn_const
  | @insert n S hn ih =>
      simp only [Finset.sum_insert hn]
      exact (sourceTerm_continuousOn hβ N n).add ih

/-- Proposition 9.3, κ=1: finite source layers are nonnegative on their exact
Suzuki parity domains. -/
theorem finiteSourceLayer_nonneg_on_parityDomain {β : ℝ} (hβ : 1 < β)
    (N : ℕ) {s : ℝ} (hs : s ∈ parityDomain β N) :
    0 ≤ finiteSourceLayer 1 β N s := by
  unfold finiteSourceLayer
  exact Finset.sum_nonneg fun n _ => sourceTerm_nonneg hβ N n hs

/-- Proposition 9.3, κ=1: the source-weighted finite layer is antitone on the
exact parity domain. -/
theorem finiteSourceLayer_weighted_antitoneOn_parityDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (fun s => s * finiteSourceLayer 1 β N s) (parityDomain β N) := by
  intro s hs t ht hst
  unfold finiteSourceLayer
  simp only [Finset.mul_sum]
  exact Finset.sum_le_sum fun n _ =>
    sourceTerm_weighted_antitone hβ N n hs ht hst

/-- Proposition 9.3, κ=1: the finite source layer itself is antitone on the
exact parity domain. -/
theorem finiteSourceLayer_antitoneOn_parityDomain
    {β : ℝ} (hβ : 1 < β) (N : ℕ) :
    AntitoneOn (finiteSourceLayer 1 β N) (parityDomain β N) := by
  intro s hs t ht hst
  unfold finiteSourceLayer
  exact Finset.sum_le_sum fun n _ => sourceTerm_antitone hβ N n hs ht hst

/-- Support vanishing: after the largest source endpoint every summand, hence
its finite parity sum, is zero.  No parity-domain hypothesis is needed. -/
theorem finiteSourceLayer_eq_zero_of_le (β : ℝ) (N : ℕ) {s : ℝ}
    (hs : β + N ≤ s) : finiteSourceLayer 1 β N s = 0 := by
  classical
  unfold finiteSourceLayer
  apply Finset.sum_eq_zero
  intro n hn
  have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
  have hcast : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
  have hβnN : β + (n : ℝ) ≤ β + (N : ℝ) := by linarith
  have hns : β + n ≤ s := hβnN.trans hs
  rw [suzukiLayer_eq_zero_of_le 1 β n hns]
  split <;> rfl

/-- Finite parity step identity: increasing the source cutoff by two preserves
its parity and adds exactly the new terminal source layer. -/
theorem finiteSourceLayer_add_two (β : ℝ) (N : ℕ) (s : ℝ) :
    finiteSourceLayer 1 β (N + 2) s =
      finiteSourceLayer 1 β N s + suzukiLayer 1 β (N + 2) s := by
  unfold finiteSourceLayer
  have hpar : (N + 2) % 2 = N % 2 := by omega
  rw [hpar]
  rw [show N + 2 = (N + 1) + 1 by omega]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1 + 1)]
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
  have hskip : (N + 1) % 2 ≠ N % 2 := by omega
  have htake : (N + 1 + 1) % 2 = N % 2 := by omega
  simp only [hskip, htake, if_false, if_true, add_zero]

end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
