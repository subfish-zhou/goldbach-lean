import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiSection13PairingZero
import Mathlib.Analysis.SpecialFunctions.PolynomialExp

open scoped Classical BigOperators Interval
open Set Filter Topology MeasureTheory intervalIntegral

namespace MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne

set_option maxHeartbeats 800000

/-- The κ=1 positive-sign standard adjoint. -/
noncomputable def section13AdjointPlus (s : ℝ) : ℝ := s ^ 2 - 2 * s + 1 / 2

/-- The κ=1 negative-sign standard adjoint. -/
def section13AdjointMinus (_s : ℝ) : ℝ := 1

theorem section13AdjointPlus_dde (s : ℝ) :
    HasDerivAt (fun u => u * section13AdjointPlus u)
      (2 * section13AdjointPlus s + section13AdjointPlus (s + 1)) s := by
  have h := (hasDerivAt_id s).mul
    (((hasDerivAt_pow 2 s).sub ((hasDerivAt_id s).const_mul 2)).add_const (1 / 2))
  change HasDerivAt (id * fun u : ℝ => u ^ 2 - 2 * u + 1 / 2)
    (2 * section13AdjointPlus s + section13AdjointPlus (s + 1)) s
  apply h.congr_deriv
  norm_num [section13AdjointPlus]
  ring

theorem section13AdjointMinus_dde (s : ℝ) :
    HasDerivAt (fun u => u * section13AdjointMinus u)
      (2 * section13AdjointMinus s - section13AdjointMinus (s + 1)) s := by
  have heq : (fun u : ℝ => u * section13AdjointMinus u) = id := by
    funext u
    simp [section13AdjointMinus]
  rw [heq]
  apply (hasDerivAt_id s).congr_deriv
  norm_num [section13AdjointMinus]

/-- Source-faithful Section 13 hat package at `κ = 1`.  The inherited contract
contains (T1)--(T4) and the weak weighted limit formerly used for tails; the
extra field is precisely the original exponential-decay assertion (T5).
Pairing-zero is deliberately a theorem below, not a field of this contract. -/
structure Section13HatSourceContract (H : Section13HatLayers) : Prop
    extends Section13HatContract H 2 where
  t5 : Section13HatExponentialDecay H

/-- The explicit polynomial adjoint `q₊` has quadratic growth, both at the
current point and uniformly over the moving unit window. -/
theorem section13AdjointPlus_eventual_bounds :
    (∀ᶠ s : ℝ in atTop, |section13AdjointPlus s| ≤ 4 * s ^ 2) ∧
    (∀ᶠ s : ℝ in atTop, ∀ t ∈ Ι (s - 1) s,
      |section13AdjointPlus (t + 1)| ≤ 4 * s ^ 2) := by
  constructor
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
    rw [abs_of_nonneg]
    · dsimp [section13AdjointPlus]
      nlinarith
    · dsimp [section13AdjointPlus]
      nlinarith [sq_nonneg (s - 1)]
  · filter_upwards [eventually_ge_atTop (3 : ℝ)] with s hs
    intro t ht
    have hab : s - 1 ≤ s := by linarith
    have ht' : t ∈ Ioc (s - 1) s := by
      simpa [uIoc_of_le hab] using ht
    rw [abs_of_nonneg]
    · norm_num [section13AdjointPlus]
      have hprod : 0 ≤ (s - t) * (s + t) :=
        mul_nonneg (by linarith [ht'.2]) (by linarith [ht'.1])
      nlinarith
    · norm_num [section13AdjointPlus]
      ring_nf
      have ht1 : (1 : ℝ) ≤ t := by linarith [ht'.1]
      have hsq : (1 : ℝ) ≤ t ^ 2 := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ t * t := mul_le_mul ht1 ht1 (by norm_num) (by linarith)
          _ = t ^ 2 := by ring
      linarith

/-- The constant adjoint `q₋ = 1` satisfies the corresponding moving-window
bounds with constant one. -/
theorem section13AdjointMinus_eventual_bounds :
    (∀ᶠ s : ℝ in atTop, |section13AdjointMinus s| ≤ 1 * s ^ 2) ∧
    (∀ᶠ s : ℝ in atTop, ∀ t ∈ Ι (s - 1) s,
      |section13AdjointMinus (t + 1)| ≤ 1 * s ^ 2) := by
  constructor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    rw [section13AdjointMinus, abs_one, one_mul]
    nlinarith [sq_nonneg (s - 1)]
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    intro t _ht
    rw [section13AdjointMinus, abs_one, one_mul]
    nlinarith [sq_nonneg (s - 1)]

/-- Signwise source (T5) passes to the symmetric `Q̂` combination. -/
theorem section13Qhat_exponential_decay
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ s : ℝ in atTop, |section13Qhat H s| ≤ C * Real.exp (-s) := by
  rcases hH.t5 .plus with ⟨Cp, hCp, hp⟩
  rcases hH.t5 .minus with ⟨Cm, hCm, hm⟩
  refine ⟨Cp + Cm, add_nonneg hCp hCm, ?_⟩
  filter_upwards [hp, hm] with s hps hms
  calc
    |section13Qhat H s| ≤ |H.T .plus s| + |H.T .minus s| := by
      exact abs_add_le _ _
    _ ≤ Cp * Real.exp (-s) + Cm * Real.exp (-s) := add_le_add hps hms
    _ = (Cp + Cm) * Real.exp (-s) := by ring

/-- Signwise source (T5) also passes to the antisymmetric `P̂` combination. -/
theorem section13Phat_exponential_decay
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ s : ℝ in atTop, |section13Phat H s| ≤ C * Real.exp (-s) := by
  rcases hH.t5 .plus with ⟨Cp, hCp, hp⟩
  rcases hH.t5 .minus with ⟨Cm, hCm, hm⟩
  refine ⟨Cp + Cm, add_nonneg hCp hCm, ?_⟩
  filter_upwards [hp, hm] with s hps hms
  calc
    |section13Phat H s| ≤ |H.T .plus s| + |H.T .minus s| := abs_sub _ _
    _ ≤ Cp * Real.exp (-s) + Cm * Real.exp (-s) := add_le_add hps hms
    _ = (Cp + Cm) * Real.exp (-s) := by ring

/-- Exponential decay of the DDE solution and quadratic growth of its adjoint
force the full moving-window pairing to tend to zero. -/
theorem section10SignedPairing_tendsto_zero_of_exp_bound
    {R q : ℝ → ℝ} {b C K : ℝ}
    (hb : |b| ≤ 1) (hC : 0 ≤ C) (hK : 0 ≤ K)
    (hR : ∀ᶠ s in atTop, |R s| ≤ C * Real.exp (-s))
    (hq : ∀ᶠ s in atTop, |q s| ≤ K * s ^ 2)
    (hqwin : ∀ᶠ s in atTop, ∀ t ∈ Ι (s - 1) s, |q (t + 1)| ≤ K * s ^ 2) :
    Tendsto (section10SignedPairing b R q) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hrhs : Tendsto (fun s : ℝ =>
      (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))))
      atTop (𝓝 0) := by
    have h2 : Tendsto (fun s : ℝ => Real.exp 1 * (s ^ 2 * Real.exp (-s)))
        atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2) :
          Tendsto (fun s : ℝ => Real.exp 1 * (s ^ 2 * Real.exp (-s))) atTop
            (𝓝 (Real.exp 1 * 0)))
    have hsum := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3).add h2
    have hmul : Tendsto (fun s : ℝ => (C * K) *
        (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))))
        atTop (𝓝 ((C * K) * (0 + 0))) := tendsto_const_nhds.mul hsum
    simpa using hmul
  apply squeeze_zero' (Eventually.of_forall fun s => norm_nonneg _)
    (show ∀ᶠ s in atTop,
      ‖section10SignedPairing b R q s‖ ≤
        (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))) from ?_)
    hrhs
  rcases eventually_atTop.1 hR with ⟨A, hA⟩
  filter_upwards [hq, hqwin, eventually_ge_atTop (max 1 (A + 1))] with s hqs hqw hs
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hAs : A + 1 ≤ s := le_trans (le_max_right _ _) hs
  have hs0 : 0 ≤ s := by linarith
  have hab : s - 1 ≤ s := by linarith
  have hint :
      ‖∫ t in s - 1..s, q (t + 1) * R t‖ ≤
        (K * s ^ 2 * (C * Real.exp 1 * Real.exp (-s))) * |s - (s - 1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    have ht' : t ∈ Ioc (s - 1) s := by simpa [uIoc_of_le hab] using ht
    have hRt' : |R t| ≤ C * Real.exp (-t) := hA t (by linarith [ht'.1])
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |q (t + 1)| * |R t| ≤ (K * s ^ 2) * (C * Real.exp (-t)) :=
        mul_le_mul (hqw t ht) hRt' (abs_nonneg _) (mul_nonneg hK (sq_nonneg s))
      _ ≤ (K * s ^ 2) * (C * Real.exp 1 * Real.exp (-s)) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hK (sq_nonneg s))
        calc
          C * Real.exp (-t) ≤ C * (Real.exp 1 * Real.exp (-s)) := by
            apply mul_le_mul_of_nonneg_left _ hC
            rw [← Real.exp_add]
            exact Real.exp_le_exp.mpr (by linarith [ht'.1])
          _ = C * Real.exp 1 * Real.exp (-s) := by ring
  rw [show |s - (s - 1)| = 1 by rw [abs_eq_self.mpr] <;> linarith, mul_one] at hint
  simp only [section10SignedPairing]
  calc
    ‖s * q s * R s - b * ∫ t in s - 1..s, q (t + 1) * R t‖ ≤
        ‖s * q s * R s‖ + ‖b * ∫ t in s - 1..s, q (t + 1) * R t‖ := norm_sub_le _ _
    _ ≤ (s * (K * s ^ 2) * (C * Real.exp (-s))) +
        (K * s ^ 2 * (C * Real.exp 1 * Real.exp (-s))) := by
      gcongr
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hs0]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hqs hs0) (hA s (by linarith))
          (abs_nonneg _) (mul_nonneg hs0 (mul_nonneg hK (sq_nonneg s)))
      · rw [norm_mul, Real.norm_eq_abs]
        calc
          |b| * ‖∫ t in s - 1..s, q (t + 1) * R t‖ ≤
              1 * ‖∫ t in s - 1..s, q (t + 1) * R t‖ :=
            mul_le_mul_of_nonneg_right hb (norm_nonneg _)
          _ ≤ K * s ^ 2 * (C * Real.exp 1 * Real.exp (-s)) := by simpa using hint
    _ = (C * K) * (s ^ 3 * Real.exp (-s) + Real.exp 1 * (s ^ 2 * Real.exp (-s))) := by ring

private def clampAboveTwo (R : ℝ → ℝ) (s : ℝ) : ℝ := R (max s 2)

private theorem clampAboveTwo_continuous {R : ℝ → ℝ}
    (hR : ContinuousOn R (Ioi 0)) : Continuous (clampAboveTwo R) := by
  change Continuous (R ∘ fun s : ℝ => max s 2)
  apply hR.comp_continuous (continuous_id.max continuous_const)
  intro s
  exact lt_of_lt_of_le (by norm_num) (le_max_right s 2)

private theorem pairing_clampAboveTwo {R q : ℝ → ℝ} {b s : ℝ} (hs : 3 < s) :
    section10SignedPairing b (clampAboveTwo R) q s = section10SignedPairing b R q s := by
  have hs2 : 2 ≤ s := by linarith
  simp only [section10SignedPairing, clampAboveTwo, max_eq_left hs2]
  have hi :
      (∫ t in s - 1..s, q (t + 1) * R (max t 2)) =
        ∫ t in s - 1..s, q (t + 1) * R t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hab : s - 1 ≤ s := by linarith
    have ht' : t ∈ Icc (s - 1) s := by simpa [uIcc_of_le hab] using ht
    have ht2 : 2 ≤ t := by linarith [ht'.1]
    simp [max_eq_left ht2]
  rw [hi]

/-- Constancy on the legal Section-13 range, obtained from the DDE without
requiring a fictitious global continuity field. -/
theorem section10SignedPairing_eq_of_dde_on_section13_range
    {b x y : ℝ} {R q : ℝ → ℝ}
    (hxy : x ≤ y) (hx : 3 < x)
    (hRcont : ContinuousOn R (Ioi 0)) (hqcont : Continuous q)
    (hR : ∀ s, 3 < s → HasDerivAt R (-(2 * R s + b * R (s - 1)) / s) s)
    (hq : ∀ s, 0 < s → HasDerivAt (fun u => u * q u) (2 * q s + b * q (s + 1)) s) :
    section10SignedPairing b R q y = section10SignedPairing b R q x := by
  let Rc := clampAboveTwo R
  have hRccont : Continuous Rc := clampAboveTwo_continuous hRcont
  have hRc : ∀ s, 3 < s →
      HasDerivAt Rc (-(2 * Rc s + b * Rc (s - 1)) / s) s := by
    intro s hs
    have hs2 : 2 < s := by linarith
    have hsm2 : 2 < s - 1 := by linarith
    have hev : Rc =ᶠ[𝓝 s] R := by
      filter_upwards [eventually_gt_nhds hs2] with z hz
      simp [Rc, clampAboveTwo, max_eq_left hz.le]
    have hd := (hR s hs).congr_of_eventuallyEq hev
    apply hd.congr_deriv
    simp [Rc, clampAboveTwo, max_eq_left hs2.le, max_eq_left hsm2.le]
  have hc := section10SignedPairing_eq_of_dde hxy (by norm_num : (1 : ℝ) ≤ 3) hx
    hRccont hqcont hRc hq
  rw [pairing_clampAboveTwo (R := R) (q := q) (b := b) (s := y) (hx.trans_le hxy),
      pairing_clampAboveTwo (R := R) (q := q) (b := b) (s := x) hx] at hc
  exact hc

/-- The `Q̂,q₊` pairing tends to zero by source (T5). -/
theorem section13Qhat_pairing_tendsto_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (section10SignedPairing 1 (section13Qhat H) section13AdjointPlus)
      atTop (𝓝 0) := by
  rcases section13Qhat_exponential_decay hH with ⟨C, hC, hdec⟩
  rcases section13AdjointPlus_eventual_bounds with ⟨hq, hqwin⟩
  exact section10SignedPairing_tendsto_zero_of_exp_bound (by norm_num) hC
    (by norm_num : (0 : ℝ) ≤ 4) hdec hq hqwin

/-- The `P̂,q₋` pairing tends to zero by source (T5). -/
theorem section13Phat_pairing_tendsto_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H) :
    Tendsto (section10SignedPairing (-1) (section13Phat H) section13AdjointMinus)
      atTop (𝓝 0) := by
  rcases section13Phat_exponential_decay hH with ⟨C, hC, hdec⟩
  rcases section13AdjointMinus_eventual_bounds with ⟨hq, hqwin⟩
  exact section10SignedPairing_tendsto_zero_of_exp_bound (by norm_num) hC
    (by norm_num : (0 : ℝ) ≤ 1) hdec hq hqwin

/-- Source (13.8), `Q̂` branch: constancy plus (T5) gives pairing zero at every
legal parameter, rather than assuming it in a bridge record. -/
theorem section13Qhat_pairing_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 3 < s) :
    section10SignedPairing 1 (section13Qhat H) section13AdjointPlus s = 0 := by
  let F := section10SignedPairing 1 (section13Qhat H) section13AdjointPlus
  have hzero : Tendsto F atTop (𝓝 0) := section13Qhat_pairing_tendsto_zero hH
  have hev : F =ᶠ[atTop] fun _ => F s := by
    filter_upwards [eventually_ge_atTop s] with y hy
    exact section10SignedPairing_eq_of_dde_on_section13_range hy hs
      (section13Qhat_continuousOn hH.toSection13HatContract)
      ((continuous_id.pow 2).sub (continuous_const.mul continuous_id) |>.add continuous_const)
      (fun u hu => (section13Qhat_dde hH.toSection13HatContract hu).congr_deriv (by ring))
      (fun u hu => (section13AdjointPlus_dde u).congr_deriv (by ring))
  have hconst : Tendsto F atTop (𝓝 (F s)) := tendsto_const_nhds.congr' hev.symm
  exact (tendsto_nhds_unique hzero hconst).symm

/-- Source (13.8), `P̂` branch: pairing zero for every legal parameter. -/
theorem section13Phat_pairing_zero
    {H : Section13HatLayers} (hH : Section13HatSourceContract H)
    {s : ℝ} (hs : 3 < s) :
    section10SignedPairing (-1) (section13Phat H) section13AdjointMinus s = 0 := by
  let F := section10SignedPairing (-1) (section13Phat H) section13AdjointMinus
  have hzero : Tendsto F atTop (𝓝 0) := section13Phat_pairing_tendsto_zero hH
  have hPcont : ContinuousOn (section13Phat H) (Ioi 0) :=
    (hH.continuous .plus).sub (hH.continuous .minus)
  have hqcont : Continuous section13AdjointMinus := continuous_const
  have hev : F =ᶠ[atTop] fun _ => F s := by
    filter_upwards [eventually_ge_atTop s] with y hy
    exact section10SignedPairing_eq_of_dde_on_section13_range hy hs hPcont hqcont
      (fun u hu => (section13Phat_dde hH.toSection13HatContract hu).congr_deriv (by ring))
      (fun u hu => (section13AdjointMinus_dde u).congr_deriv (by ring))
  have hconst : Tendsto F atTop (𝓝 (F s)) := tendsto_const_nhds.congr' hev.symm
  exact (tendsto_nhds_unique hzero hconst).symm


end MathlibNt.SieveTheory.SwitchingPrinciple.SuzukiLemma144KappaOne
