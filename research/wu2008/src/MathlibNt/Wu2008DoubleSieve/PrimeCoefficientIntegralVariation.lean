import MathlibNt.Wu2008DoubleSieve.PrimeCoefficientIntegral
import MathlibNt.Wu2008DoubleSieve.ReboxingRepeatedPrimes

/-!
# Uniform variation payment for the exact prime kernel

The coefficient may have jumps and may be signed. A bounded antitone
coefficient times a positive antitone kernel has uniformly bounded finite
variation. This pays the actual finite PNT quadrature error without selecting
a prime-distribution threshold after the coefficient.
-/

namespace Wu2008DoubleSieve

open Finset Set Filter Real
open scoped Classical Topology
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

private theorem sum_forward_sub (u : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, (u n - u (n + 1)) = u a - u b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

theorem primeWeightVariation_mul_le {u v : ℕ → ℝ} {a b : ℕ} (hab : a ≤ b)
    (hu : AntitoneOn u (Set.Icc (a + 1) (b + 1)))
    (hv : AntitoneOn v (Set.Icc (a + 1) (b + 1)))
    {B : ℝ} (hB : 0 ≤ B)
    (hub : ∀ n ∈ Set.Icc (a + 1) (b + 1), |u n| ≤ B)
    (hv0 : ∀ n ∈ Set.Icc (a + 1) (b + 1), 0 ≤ v n) :
    primeWeightVariation (fun n => u n * v n) a b ≤ 5 * B * v (a + 1) := by
  have hleft : a + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨le_rfl, by omega⟩
  have hright : b + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by omega, le_rfl⟩
  have hvl := hv0 _ hleft
  have hvr := hv0 _ hright
  have hvrl := hv hleft hright (by omega)
  have hsum :
      (∑ n ∈ Finset.Ico (a + 1) (b + 1),
        |u (n + 1) * v (n + 1) - u n * v n|) ≤
      v (a + 1) * (u (a + 1) - u (b + 1)) +
        B * (v (a + 1) - v (b + 1)) := by
    calc
      _ ≤ ∑ n ∈ Finset.Ico (a + 1) (b + 1),
          (v (a + 1) * (u n - u (n + 1)) + B * (v n - v (n + 1))) := by
        apply Finset.sum_le_sum
        intro n hn
        have hn' := Finset.mem_Ico.mp hn
        have hn0 : n ∈ Set.Icc (a + 1) (b + 1) := ⟨hn'.1, hn'.2.le⟩
        have hn1 : n + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨by omega, by omega⟩
        have hun := hu hn0 hn1 (by omega)
        have hvn := hv hn0 hn1 (by omega)
        have hvln := hv hleft hn1 (by omega)
        have heq : u (n + 1) * v (n + 1) - u n * v n =
            (u (n + 1) - u n) * v (n + 1) + u n * (v (n + 1) - v n) := by ring
        rw [heq]
        calc
          _ ≤ |(u (n + 1) - u n) * v (n + 1)| +
              |u n * (v (n + 1) - v n)| := abs_add_le _ _
          _ = (u n - u (n + 1)) * v (n + 1) +
              |u n| * (v n - v (n + 1)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg (hv0 _ hn1),
              abs_of_nonpos (sub_nonpos.mpr hun), abs_of_nonpos (sub_nonpos.mpr hvn)]
            ring
          _ ≤ _ := by
            have h1 := mul_le_mul_of_nonneg_left hvln (sub_nonneg.mpr hun)
            have h2 := mul_le_mul_of_nonneg_right (hub n hn0) (sub_nonneg.mpr hvn)
            nlinarith only [h1, h2]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
          sum_forward_sub u (by omega), sum_forward_sub v (by omega)]
  have hends : |u (a + 1) * v (a + 1)| + |u (b + 1) * v (b + 1)| ≤
      2 * B * v (a + 1) := by
    rw [abs_mul, abs_mul, abs_of_nonneg hvl, abs_of_nonneg hvr]
    have h1 := mul_le_mul_of_nonneg_right (hub _ hleft) hvl
    have h2 := mul_le_mul_of_nonneg_right (hub _ hright) hvr
    have h3 := mul_le_mul_of_nonneg_left hvrl hB
    linarith
  have hub1 := (abs_le.mp (hub _ hleft)).2
  have hub2 := (abs_le.mp (hub _ hright)).1
  have hcoef : v (a + 1) * (u (a + 1) - u (b + 1)) ≤
      2 * B * v (a + 1) := by nlinarith
  have hlast : B * (v (a + 1) - v (b + 1)) ≤ B * v (a + 1) := by
    nlinarith
  unfold primeWeightVariation
  linarith

/-- Positivity and antitonicity of the exact `p-2` kernel on the
square-root range. The mild `2 ≤ log q` condition is quantitative. -/
theorem wuPrimeKernel_le {q p r : ℝ} (hq : 1 < q) (hlogq : 2 ≤ log q)
    (hp : 4 ≤ p) (hpr : p ≤ r) (hr : r ≤ q ^ (1 / 2 : ℝ)) :
    0 ≤ 1 / ((r - 2) * (1 - log r / log q)) ∧
      1 / ((r - 2) * (1 - log r / log q)) ≤
        1 / ((p - 2) * (1 - log p / log q)) := by
  have hp0 : 0 < p := by linarith
  have hr0 : 0 < r := hp0.trans_le hpr
  have hlq : 0 < log q := log_pos hq
  have hrhalf := reboxing_log_ratio_half hq hr0 hr
  have hphalf := reboxing_log_ratio_half hq hp0 (hpr.trans hr)
  have hdenp : 0 < (p - 2) * (1 - log p / log q) :=
    mul_pos (by linarith) (by linarith)
  have hdenr : 0 < (r - 2) * (1 - log r / log q) :=
    mul_pos (by linarith) (by linarith)
  refine ⟨by positivity, one_div_le_one_div_of_le hdenp ?_⟩
  have hlog := log_le_sub_one_of_pos (div_pos hr0 hp0)
  rw [log_div hr0.ne' hp0.ne'] at hlog
  have hlog' : (log r - log p) * p ≤ r - p := by
    have := (le_div_iff₀ hp0).mp (show log r - log p ≤ (r - p) / p by
      convert hlog using 1; field_simp)
    exact this
  have hlognonneg : 0 ≤ log r - log p := sub_nonneg.mpr (log_le_log hp0 hpr)
  have hlog'' : (p - 2) * (log r - log p) ≤ r - p := by nlinarith
  have hhalf : (r - p) * (log q - log r) ≥ (r - p) * (log q / 2) := by
    have hrlog : log r ≤ log q / 2 :=
      (div_le_iff₀ hlq).mp (by linarith : log r / log q ≤ 1 / 2) |>.trans_eq (by ring)
    exact mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hpr)
  have hprod : r - p ≤ (r - p) * (log q / 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hpr) (show 0 ≤ log q - 2 by linarith)]
  apply (mul_le_mul_iff_left₀ hlq).mp
  field_simp
  nlinarith only [hlog'', hhalf, hprod]

/-- The source's exact kernel has bounded variation for every bounded
monotone coefficient, even when the coefficient is signed or discontinuous. -/
theorem wuPrimeCoefficientWeight_variation_le {f : ℝ → ℝ} {q B : ℝ}
    (hf : MonotoneOn f (Set.Icc 1 10))
    (hB : 0 ≤ B) (hfb : ∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B)
    {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) (hq : 1 < q) (hlogq : 2 ≤ log q)
    (hb : ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ))
    (haq : log q / log (a + 1 : ℕ) - 1 ≤ 10) :
    primeWeightVariation (wuPrimeCoefficientWeight f q) a b ≤
      20 * B / (a + 1 : ℕ) := by
  let u : ℕ → ℝ := fun n => f (log q / log n - 1)
  let v : ℕ → ℝ := fun n => 1 / (((n : ℝ) - 2) * (1 - log n / log q))
  have hlarge (n : ℕ) (hn : n ∈ Set.Icc (a + 1) (b + 1)) : (4 : ℝ) ≤ n := by
    have := hn.1
    exact_mod_cast (show 4 ≤ n by omega)
  have hlog (n : ℕ) (hn : n ∈ Set.Icc (a + 1) (b + 1)) : 0 < log (n : ℝ) :=
    log_pos (by linarith [hlarge n hn])
  have hlq : 0 < log q := log_pos hq
  have hanti : AntitoneOn (fun n : ℕ => log q / log n - 1)
      (Set.Icc (a + 1) (b + 1)) := by
    intro n hn m _ hnm
    have hlognm : log (n : ℝ) ≤ log (m : ℝ) :=
      log_le_log (by linarith [hlarge n hn]) (by exact_mod_cast hnm)
    exact sub_le_sub_right (div_le_div_of_nonneg_left hlq.le (hlog n hn) hlognm) 1
  have hleft : a + 1 ∈ Set.Icc (a + 1) (b + 1) := ⟨le_rfl, by omega⟩
  have hdomain (n : ℕ) (hn : n ∈ Set.Icc (a + 1) (b + 1)) :
      log q / log n - 1 ∈ Set.Icc (1 : ℝ) 10 := by
    refine ⟨?_, (hanti hleft hn hn.1).trans haq⟩
    have hnq : (n : ℝ) ≤ q ^ (1 / 2 : ℝ) :=
      (by exact_mod_cast hn.2 : (n : ℝ) ≤ (b + 1 : ℕ)).trans hb
    have hln := log_le_log (by linarith [hlarge n hn] : (0 : ℝ) < n) hnq
    rw [log_rpow (by linarith : 0 < q)] at hln
    have : 2 ≤ log q / log n := (le_div_iff₀ (hlog n hn)).2 (by linarith)
    linarith
  have hu : AntitoneOn u (Set.Icc (a + 1) (b + 1)) := by
    intro n hn m hm hnm
    exact hf (hdomain m hm) (hdomain n hn) (hanti hn hm hnm)
  have hv : AntitoneOn v (Set.Icc (a + 1) (b + 1)) := by
    intro n hn m hm hnm
    exact (wuPrimeKernel_le hq hlogq (hlarge n hn) (by exact_mod_cast hnm)
      ((by exact_mod_cast hm.2 : (m : ℝ) ≤ (b + 1 : ℕ)).trans hb)).2
  have hv0 : ∀ n ∈ Set.Icc (a + 1) (b + 1), 0 ≤ v n := by
    intro n hn
    exact (wuPrimeKernel_le hq hlogq (hlarge n hn) le_rfl
      ((by exact_mod_cast hn.2 : (n : ℝ) ≤ (b + 1 : ℕ)).trans hb)).1
  have hvar := primeWeightVariation_mul_le hab hu hv hB
    (fun n hn => hfb _ (hdomain n hn)) hv0
  have hvleft : v (a + 1) ≤ 4 / (a + 1 : ℕ) :=
    (reboxing_prime_weight_le_four_div hq (hlarge _ hleft)
      ((by exact_mod_cast hleft.2 : ((a + 1 : ℕ) : ℝ) ≤ (b + 1 : ℕ)).trans hb)).2
  have heq : wuPrimeCoefficientWeight f q = fun n => u n * v n := by
    funext n
    unfold wuPrimeCoefficientWeight u v
    ring
  rw [heq]
  apply hvar.trans
  have hmul := mul_le_mul_of_nonneg_left hvleft (show 0 ≤ 5 * B by positivity)
  convert hmul using 1; ring

/-- A fully paid local PNT quadrature error, uniform over the whole
bounded-monotone class. It retains the literal `p-2` denominator. -/
theorem primeCoefficient_trueLi_quadrature (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      ∀ (f : ℝ → ℝ) (B q : ℝ), MonotoneOn f (Set.Icc 1 10) →
        0 ≤ B → (∀ t ∈ Set.Icc (1 : ℝ) 10, |f t| ≤ B) →
      ∀ a b : ℕ, 3 ≤ a → a ≤ b → b ≤ X → 1 < q → 2 ≤ log q →
        ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a + 1 : ℕ) - 1 ≤ 10 →
        |(∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
            wuPrimeCoefficientWeight f q (n + 1)) -
          ∑ n ∈ Finset.Ico a b,
            (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
              wuPrimeCoefficientWeight f q (n + 1)| ≤
          (C * (X : ℝ) / log X ^ A) * (20 * B / (a + 1 : ℕ)) := by
  obtain ⟨C, hC, X0, hPNT⟩ := primeWeight_trueLi_quadrature A hA
  refine ⟨C, hC, X0, ?_⟩
  intro X hX f B q hf hB hfb a b ha hab hb hq hlq hqb haq
  have hE : 0 ≤ C * (X : ℝ) / log X ^ A := by
    have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
    exact div_nonneg (mul_nonneg hC.le (Nat.cast_nonneg X))
      (rpow_nonneg (log_nonneg hX1) A)
  exact (hPNT X hX a b (by omega) hab hb (wuPrimeCoefficientWeight f q)).trans
    (mul_le_mul_of_nonneg_left
      (wuPrimeCoefficientWeight_variation_le hf hB hfb ha hab hq hlq hqb haq) hE)

/-- The preceding PNT estimate for Wu's actual finite-threshold functions.
Both thresholds are chosen before `N0`, the endpoints, or the source scale. -/
theorem wuEffectiveCoefficient_trueLi_quadrature (upper : Bool)
    (k : ℕ) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδhi : δ < 1 / 2)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ X0 T : ℕ, ∀ N0 : ℕ, T ≤ N0 →
      ∀ X : ℕ, X0 ≤ X → ∀ q : ℝ, ∀ a b : ℕ,
        3 ≤ a → a ≤ b → b ≤ X → 1 < q → 2 ≤ log q →
        ((b + 1 : ℕ) : ℝ) ≤ q ^ (1 / 2 : ℝ) →
        log q / log (a + 1 : ℕ) - 1 ≤ 10 →
        |(∑ n ∈ (Finset.Ico a b).filter (fun n => (n + 1).Prime),
            wuPrimeCoefficientWeight (wuEffectiveCoefficient upper k δ N0) q (n + 1)) -
          ∑ n ∈ Finset.Ico a b,
            (logarithmicIntegral (n + 1) - logarithmicIntegral n) *
              wuPrimeCoefficientWeight (wuEffectiveCoefficient upper k δ N0) q (n + 1)| ≤
          (C * (X : ℝ) / log X ^ A) * (2200 / (a + 1 : ℕ)) := by
  obtain ⟨C, hC, X0, hPNT⟩ := primeCoefficient_trueLi_quadrature A hA
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (wuEffectiveCoefficient_uniform_monotone_bound upper k hk hδ hδhi)
  refine ⟨C, hC, X0, T, ?_⟩
  intro N0 hN0 X hX q a b ha hab hb hq hlq hqb haq
  simpa only [show (20 : ℝ) * 110 = 2200 by norm_num] using
    hPNT X hX (wuEffectiveCoefficient upper k δ N0) 110 q (hT N0 hN0).1
      (by norm_num) (hT N0 hN0).2 a b ha hab hb hq hlq hqb haq

end Wu2008DoubleSieve
