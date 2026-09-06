import MathlibNt.AnalyticNumberTheory.DirichletL.DirichletLActualCompletedArchimedeanBridge
import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.Liouville
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# Local finite-disk zero factorization

This module replaces a global Hadamard product by the divisor on one bounded
complex disk.  The resulting factorization and logarithmic-derivative formula
are obtained from analyticity and isolated zeros; no explicit-formula equality
is supplied as a hypothesis.
-/

open Complex Filter Function Metric Set
open scoped Classical Topology

namespace AnalyticNumberTheory.LargeSieve
namespace TatuzawaZeroContribution

noncomputable section

private lemma logDeriv_sub_pow (ρ s : ℂ) (n : ℕ) (hs : s ≠ ρ) :
    logDeriv ((fun z : ℂ ↦ z - ρ) ^ n) s = (n : ℂ) / (s - ρ) := by
  rw [logDeriv_apply]
  change deriv ((fun z : ℂ ↦ id z - ρ) ^ n) s /
      ((fun z : ℂ ↦ id z - ρ) ^ n) s = _
  rw [(((hasDerivAt_id s).sub_const ρ).pow n).deriv]
  simp only [Pi.pow_apply, id_eq, mul_one]
  by_cases hn : n = 0
  · simp [hn]
  have hsub : s - ρ ≠ 0 := sub_ne_zero.mpr hs
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simp only [Nat.succ_sub_one, pow_succ]
  field_simp

private lemma logDeriv_finite_zeroProduct
    (S : Finset ℂ) (m : ℂ → ℕ) (s : ℂ) (hs : ∀ ρ ∈ S, s ≠ ρ) :
    logDeriv (fun z : ℂ ↦ ∏ ρ ∈ S, (z - ρ) ^ m ρ) s =
      ∑ ρ ∈ S, (m ρ : ℂ) / (s - ρ) := by
  rw [logDeriv_prod]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    exact logDeriv_sub_pow ρ s (m ρ) (hs ρ hρ)
  · intro ρ hρ
    exact pow_ne_zero _ (sub_ne_zero.mpr (hs ρ hρ))
  · intro ρ hρ
    fun_prop

/-- An entire nonzero complex function has, on every positive-radius disk, a
finite zero divisor and a factorization by that divisor times a nonvanishing
analytic function.  Multiplicities are the integer values of `D`; they are
nonnegative and `S` is exactly their finite support. -/
theorem localFiniteDisk_zeroFactorization
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ (D : ℂ → ℤ) (S : Finset ℂ) (g : ℂ → ℂ),
      (∀ z, 0 ≤ D z) ∧
      (S : Set ℂ) = D.support ∧
      (∀ z, z ∈ S ↔ z ∈ ball c R ∧ f z = 0) ∧
      AnalyticOnNhd ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, g z ≠ 0) ∧
      (∀ z ∈ ball c R,
        f z = (∏ ρ ∈ S, (z - ρ) ^ (D ρ).toNat) * g z) := by
  let U : Set ℂ := ball c R
  have hfa : AnalyticOnNhd ℂ f U := fun z _ ↦ hf.analyticAt z
  let D₀ := MeromorphicOn.divisor f U
  have hfaClosed : AnalyticOnNhd ℂ f (closedBall c R) := fun z _ ↦ hf.analyticAt z
  have hDfin : D₀.support.Finite :=
    hfaClosed.meromorphicOn.divisor_support_finite_of_subset
      (V := U) (isCompact_closedBall c R) ball_subset_closedBall
  have hDnonneg : ∀ z, 0 ≤ D₀ z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa
  have hfne : f ≠ 0 := by
    intro hzero
    apply hz₀
    rw [hzero]
    rfl
  -- Nontriviality rules out infinite zero order at every point.
  have hfiniteOrder : ∀ z, analyticOrderAt f z ≠ ⊤ := fun z ↦
    (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (𝕜 := ℂ) (f := f)
      z (fun w ↦ hf.analyticAt w)).not.mpr hfne
  have horder : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ := by
    intro u
    rw [(hf.analyticAt u).meromorphicOrderAt_eq, ne_eq, ENat.map_eq_top_iff]
    exact hfiniteOrder u
  obtain ⟨g, hg, hg0, hfg⟩ :=
    hfa.meromorphicOn.extract_zeros_poles horder hDfin
  let P : ℂ → ℂ := ∏ᶠ ρ, (· - ρ) ^ D₀ ρ
  have hPa : AnalyticOnNhd ℂ P U := fun z _ ↦
    Function.FactorizedRational.analyticAt (hDnonneg z)
  have hprodA : AnalyticOnNhd ℂ (P * g) U := hPa.mul hg
  have hcU : c ∈ U := mem_ball_self hR
  have hacc : AccPt c (𝓟 U) := accPt_iff_frequently_nhdsNE.mpr
    (eventually_nhdsWithin_of_eventually_nhds (ball_mem_nhds c hR)).frequently
  have hnear : f =ᶠ[𝓝[≠] c] (P * g) :=
    (hfa.meromorphicOn c hcU).eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin
      (hprodA.meromorphicOn c hcU) hcU hacc
        (by simpa only [Pi.smul_apply', smul_eq_mul, P, D₀] using hfg)
  have hpoint : Set.EqOn f (P * g) U :=
    hfa.eqOn_of_preconnected_of_frequently_eq hprodA isPreconnected_ball hcU hnear.frequently
  let S : Finset ℂ := hDfin.toFinset
  have hPprod : P = fun z ↦ ∏ ρ ∈ S, (z - ρ) ^ (D₀ ρ).toNat := by
    dsimp only [P]
    rw [Function.FactorizedRational.finprod_eq_fun hDfin]
    funext z
    rw [finprod_eq_prod_of_mulSupport_subset (s := S)]
    · apply Finset.prod_congr rfl
      intro ρ hρ
      rw [← zpow_natCast, Int.toNat_of_nonneg (hDnonneg ρ)]
    · intro ρ hρ
      change ρ ∈ hDfin.toFinset
      rw [hDfin.mem_toFinset, Function.mem_support]
      intro hzero
      apply hρ
      simp [hzero]
  refine ⟨D₀, S, g, hDnonneg, ?_, ?_, hg, ?_, ?_⟩
  · simp [S]
  · intro z
    rw [show z ∈ S ↔ D₀ z ≠ 0 by simp [S, Function.mem_support]]
    constructor
    · intro hz
      have hzU := D₀.supportWithinDomain hz
      refine ⟨hzU, ?_⟩
      by_contra hfz
      apply hz
      dsimp only [D₀]
      rw [hfa.meromorphicOn.divisor_apply hzU,
        (hf.analyticAt z).meromorphicOrderAt_eq,
        (hf.analyticAt z).analyticOrderAt_eq_zero.mpr hfz]
      simp
    · rintro ⟨hzU, hfz⟩
      dsimp only [D₀]
      rw [hfa.meromorphicOn.divisor_apply hzU,
        (hf.analyticAt z).meromorphicOrderAt_eq]
      have hne0 := (hf.analyticAt z).analyticOrderAt_ne_zero.mpr hfz
      simp [WithTop.untop₀_eq_zero, ENat.map_eq_top_iff, hne0, hfiniteOrder z]
  · intro z hz
    exact hg0 ⟨z, hz⟩
  · intro z hz
    simpa only [Pi.mul_apply, hPprod] using hpoint hz

/-- The local finite-zero explicit formula attached to the factorization above.
At every nonzero point of the disk, the logarithmic derivative is the finite
sum of reciprocal zero distances (with multiplicity), plus the analytic
nonvanishing remainder `g'/g`. -/
theorem localFiniteDisk_explicitFormula
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {z₀ : ℂ} (hz₀ : f z₀ ≠ 0)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ (D : ℂ → ℤ) (S : Finset ℂ) (g : ℂ → ℂ),
      (∀ z, 0 ≤ D z) ∧
      (∀ z, z ∈ S ↔ z ∈ ball c R ∧ f z = 0) ∧
      AnalyticOnNhd ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, g z ≠ 0) ∧
      ∀ s ∈ ball c R, f s ≠ 0 →
        logDeriv f s =
          ∑ ρ ∈ S, ((D ρ).toNat : ℂ) / (s - ρ) + logDeriv g s := by
  obtain ⟨D, S, g, hD, hS, hzeros, hg, hg0, hfactor⟩ :=
    localFiniteDisk_zeroFactorization f hf hz₀ c hR
  refine ⟨D, S, g, hD, hzeros, hg, hg0, ?_⟩
  intro s hs hfs
  have hgs := hg0 s hs
  have hPs : (∏ ρ ∈ S, (s - ρ) ^ (D ρ).toNat) ≠ 0 := by
    intro hP
    apply hfs
    rw [hfactor s hs, hP, zero_mul]
  have hsρ : ∀ ρ ∈ S, s ≠ ρ := by
    intro ρ hρ hsr
    apply hfs
    rw [hsr]
    exact (hzeros ρ).mp hρ |>.2
  let Pfun : ℂ → ℂ := fun z ↦ ∏ ρ ∈ S, (z - ρ) ^ (D ρ).toNat
  have hev : f =ᶠ[𝓝 s] (fun z ↦ Pfun z * g z) := by
    filter_upwards [isOpen_ball.mem_nhds hs] with z hz
    exact hfactor z hz
  -- Differentiate the local factorization, then expand the finite zero product.
  calc
    logDeriv f s = logDeriv (fun z ↦ Pfun z * g z) s := by
      rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.self_of_nhds]
    _ = logDeriv Pfun s + logDeriv g s :=
      logDeriv_mul (f := Pfun) (g := g) s hPs hgs
        (by dsimp [Pfun]; fun_prop) (hg s hs).differentiableAt
    _ = ∑ ρ ∈ S, ((D ρ).toNat : ℂ) / (s - ρ) + logDeriv g s :=
      congrArg (· + logDeriv g s)
        (logDeriv_finite_zeroProduct S (fun ρ ↦ (D ρ).toNat) s hsρ)

/-- Cauchy control of the nonvanishing remainder from one circle value
bound and one interior lower bound.  This is the local replacement for the
usual global Hadamard remainder estimate. -/
theorem norm_logDeriv_le_of_circleBounds
    (g : ℂ → ℂ) (s : ℂ) {r M m : ℝ} (hr : 0 < r) (hM : 0 ≤ M) (hm : 0 < m)
    (hg : DiffContOnCl ℂ g (ball s r))
    (hcircle : ∀ z ∈ sphere s r, ‖g z‖ ≤ M)
    (hlower : m ≤ ‖g s‖) :
    ‖logDeriv g s‖ ≤ (M / r) / m := by
  have hd : ‖deriv g s‖ ≤ M / r :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hg hcircle
  rw [logDeriv_apply, norm_div]
  calc
    ‖deriv g s‖ / ‖g s‖ ≤ (M / r) / ‖g s‖ :=
      div_le_div_of_nonneg_right hd (norm_nonneg _)
    _ ≤ (M / r) / m := by
      exact div_le_div_of_nonneg_left (div_nonneg hM hr.le) hm hlower

/-- Character-specific specialization for the actual symmetrically completed
Dirichlet L-function.  Nontriviality is proved at `s = 2` from the standard
nonvanishing theorem for `L(s,χ)` and the nonzero gamma factor. -/
theorem symmetricCompletedLFunction_localFiniteDisk_explicitFormula
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ (D : ℂ → ℤ) (S : Finset ℂ) (g : ℂ → ℂ),
      (∀ z, 0 ≤ D z) ∧
      (∀ z, z ∈ S ↔ z ∈ ball c R ∧ symmetricCompletedLFunction χ z = 0) ∧
      AnalyticOnNhd ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, g z ≠ 0) ∧
      ∀ s ∈ ball c R, symmetricCompletedLFunction χ s ≠ 0 →
        logDeriv (symmetricCompletedLFunction χ) s =
          ∑ ρ ∈ S, ((D ρ).toNat : ℂ) / (s - ρ) + logDeriv g s := by
  have hL : χ.LFunction (2 : ℂ) ≠ 0 :=
    χ.LFunction_ne_zero_of_one_le_re (Or.inl hχ) (by norm_num)
  have hγ : χ.gammaFactor (2 : ℂ) ≠ 0 := gammaFactor_ne_zero_of_pos χ (by norm_num)
  have hcompleted : χ.completedLFunction (2 : ℂ) ≠ 0 := by
    intro hzero
    apply hL
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ 2 (Or.inl (by norm_num))]
    simp [hzero]
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have hpow : (q : ℂ) ^ ((2 : ℂ) / 2) ≠ 0 := by
    simp [hq]
  exact localFiniteDisk_explicitFormula (symmetricCompletedLFunction χ)
    (differentiable_symmetricCompletedLFunction hχ) (mul_ne_zero hpow hcompleted) c hR

end
end TatuzawaZeroContribution
end AnalyticNumberTheory.LargeSieve
