/-
A temporary, independent κ = 1 reconstruction of Suzuki (9.1)--(9.2).
Crucially, (9.2) integrates the *normalized* preceding layer.
-/
import MathlibNt.SieveTheory.LinearSieve.Suzuki.SuzukiFiniteContinuousLayers
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.KappaOneModel

open MeasureTheory intervalIntegral
open scoped Interval

noncomputable section

/-- Suzuki's ε_n (zero for even n, one for odd n). -/
def eps (n : ℕ) : ℕ := n % 2

/-- Closed envelope of Suzuki's parity domain.  For odd n this includes the
left endpoint β-1; the exact source domain below removes it. -/
def closedDomain (β : ℝ) (n : ℕ) : Set ℝ := Set.Ici (β - eps n)

/-- The exact parity domain I_n from Suzuki: `(β-1,∞)` for odd n and
`[β,∞)` for even n. -/
def parityDomain (β : ℝ) (n : ℕ) : Set ℝ :=
  if n % 2 = 1 then Set.Ioi (β - 1) else Set.Ici β

/-- Clipped lower endpoint, implementing the empty-interval convention. -/
def lower (β s : ℝ) (n : ℕ) : ℝ :=
  min (max s (β + eps n)) (β + n)

/-- Correct normalized κ=1 layers.  In the recursive clause the integrand is
`layer β (n+1)`, not its weighted numerator. -/
noncomputable def layer (β : ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 0
  | 1, s => s⁻¹ * ∫ _t in min s (β + 1)..(β + 1), (1 : ℝ)
  | n + 2, s =>
      s⁻¹ * ∫ t in lower β s (n + 2)..(β + (n + 2)), layer β (n + 1) (t - 1)

lemma eps_succ_add (n : ℕ) : eps (n + 1) + eps n = 1 := by
  unfold eps
  omega

lemma eps_succ_succ_add (n : ℕ) : eps (n + 2) + eps (n + 1) = 1 := by
  simpa [Nat.add_assoc] using eps_succ_add (n + 1)

lemma parityDomain_subset_closedDomain (β : ℝ) (n : ℕ) :
    parityDomain β n ⊆ closedDomain β n := by
  intro s hs
  change β - ((n % 2 : ℕ) : ℝ) ≤ s
  unfold parityDomain at hs
  split at hs
  · simp only [Set.mem_Ioi] at hs
    norm_num [*]
    linarith
  · simp only [Set.mem_Ici] at hs ⊢
    have hn : n % 2 = 0 := by omega
    rw [hn]
    norm_num at hs ⊢
    exact hs

lemma closedDomain_pos {β : ℝ} (hβ : 1 < β) {n : ℕ} {s : ℝ}
    (hs : s ∈ closedDomain β n) : 0 < s := by
  unfold closedDomain eps at hs
  simp only [Set.mem_Ici] at hs
  have heN : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
  have he : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast (Nat.le_of_lt_succ heN)
  linarith

lemma lower_mem (β s : ℝ) (n : ℕ) :
    lower β s n ∈ Set.Icc (β + eps n) (β + n) := by
  unfold lower
  constructor
  · apply le_min
    · exact le_max_right _ _
    · have : eps n ≤ n := by
        unfold eps
        omega
      have hcast : (eps n : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
      simpa [add_comm] using add_le_add_left hcast β
  · exact min_le_right _ _

lemma lower_mono (β : ℝ) (n : ℕ) : Monotone (fun s => lower β s n) := by
  intro s t hst
  exact min_le_min_right _ (max_le_max_right _ hst)

lemma lower_continuous (β : ℝ) (n : ℕ) : Continuous (fun s => lower β s n) := by
  unfold lower
  exact (continuous_id.max continuous_const).min continuous_const

/-- Continuity of a variable-lower-endpoint integral, requiring continuity
only on the compact interval actually traversed. -/
lemma continuousOn_integral_to_const {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b)) :
    ContinuousOn (fun x => ∫ t in x..b, f t) (Set.Icc a b) := by
  have hInt : IntegrableOn f (Set.Icc a b) := hf.integrableOn_Icc
  have hp := intervalIntegral.continuousOn_primitive hInt
  have hprim : ContinuousOn (fun x => ∫ t in a..x, f t) (Set.Icc a b) := by
    apply hp.congr
    intro x hx
    change (∫ t in a..x, f t) = ∫ t in Set.Ioc a x, f t
    rw [intervalIntegral.integral_of_le hx.1]
  have htotal : ContinuousOn (fun _x : ℝ => ∫ t in a..b, f t) (Set.Icc a b) :=
    continuousOn_const
  apply (htotal.sub hprim).congr
  intro x hx
  have habInt : IntervalIntegrable f MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    rwa [Set.uIcc_of_le hab]
  have haxInt : IntervalIntegrable f MeasureTheory.volume a x :=
    habInt.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.1]
      exact Set.Icc_subset_Icc_right hx.2)
  change (∫ t in x..b, f t) = (∫ t in a..b, f t) - ∫ t in a..x, f t
  rw [eq_sub_iff_add_eq]
  simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals haxInt
    (habInt.mono_set (by
      rw [Set.uIcc_of_le hab, Set.uIcc_of_le hx.2]
      exact Set.Icc_subset_Icc_left hx.1))

structure Regular (β : ℝ) (n : ℕ) : Prop where
  continuous : ContinuousOn (layer β n) (closedDomain β n)
  nonneg : ∀ s ∈ closedDomain β n, 0 ≤ layer β n s
  weighted_antitone : AntitoneOn (fun s => s * layer β n s) (closedDomain β n)

lemma shifted_mem_previous {β : ℝ} {n : ℕ} {t : ℝ}
    (ht : β + eps (n + 2) ≤ t) : t - 1 ∈ closedDomain β (n + 1) := by
  unfold closedDomain
  simp only [Set.mem_Ici]
  have he := eps_succ_succ_add n
  have heR : (eps (n + 2) : ℝ) + eps (n + 1) = 1 := by exact_mod_cast he
  linarith

lemma regular_zero (β : ℝ) : Regular β 0 := by
  constructor
  · exact continuousOn_const
  · simp [layer]
  · intro a ha b hb hab
    simp [layer]

lemma regular_one {β : ℝ} (hβ : 1 < β) : Regular β 1 := by
  let a : ℝ := β - 1
  let b : ℝ := β + 1
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hF : ContinuousOn (fun x => ∫ _t in x..b, (1 : ℝ)) (Set.Icc a b) :=
    continuousOn_integral_to_const hab continuousOn_const
  have hmin_cont : ContinuousOn (fun s => min s b) (closedDomain β 1) :=
    (continuous_id.min continuous_const).continuousOn
  have hmin_map : Set.MapsTo (fun s => min s b) (closedDomain β 1) (Set.Icc a b) := by
    intro s hs
    change a ≤ min s b ∧ min s b ≤ b
    constructor
    · apply le_min
      · simpa [closedDomain, eps, a] using hs
      · exact hab
    · exact min_le_right _ _
  have hnum : ContinuousOn (fun s => ∫ _t in min s b..b, (1 : ℝ))
      (closedDomain β 1) := by
    change ContinuousOn ((fun x => ∫ _t in x..b, (1 : ℝ)) ∘ fun s => min s b)
      (closedDomain β 1)
    exact hF.comp hmin_cont hmin_map
  constructor
  · rw [show layer β 1 = (fun s => s⁻¹ * ∫ _t in min s b..b, (1 : ℝ)) by
      funext s; rfl]
    exact (continuousOn_id.inv₀ (fun s hs => ne_of_gt (closedDomain_pos hβ hs))).mul hnum
  · intro s hs
    rw [layer]
    exact mul_nonneg (le_of_lt (inv_pos.mpr (closedDomain_pos hβ hs)))
      (intervalIntegral.integral_nonneg (min_le_right _ _) (by simp))
  · intro s hs t ht hst
    have hspos := closedDomain_pos hβ hs
    have htpos := closedDomain_pos hβ ht
    simp only [layer]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul,
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hspos), one_mul]
    apply intervalIntegral.integral_mono_interval
        (min_le_min_right b hst) (min_le_right _ _) le_rfl
    · filter_upwards [] with x
      norm_num
    · exact continuous_const.intervalIntegrable _ _

lemma regular_step {β : ℝ} (hβ : 1 < β) (n : ℕ)
    (ih : Regular β (n + 1)) : Regular β (n + 2) := by
  let a : ℝ := β + eps (n + 2)
  let b : ℝ := β + (n + 2)
  let g : ℝ → ℝ := fun t => layer β (n + 1) (t - 1)
  have hab : a ≤ b := by
    dsimp [a, b]
    have : eps (n + 2) ≤ n + 2 := by unfold eps; omega
    have hcast : (eps (n + 2) : ℝ) ≤ (n + 2 : ℕ) := by exact_mod_cast this
    simpa [add_comm, Nat.cast_add, Nat.cast_ofNat] using add_le_add_left hcast β
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ih.continuous.comp (continuous_id.sub continuous_const).continuousOn
    intro t ht
    exact shifted_mem_previous ht.1
  have hg_nonneg : ∀ t ∈ Set.Icc a b, 0 ≤ g t := by
    intro t ht
    exact ih.nonneg _ (shifted_mem_previous ht.1)
  have hF : ContinuousOn (fun x => ∫ t in x..b, g t) (Set.Icc a b) :=
    continuousOn_integral_to_const hab hg
  have hnum : Continuous (fun s => ∫ t in lower β s (n + 2)..b, g t) := by
    apply hF.comp_continuous (lower_continuous β (n + 2))
    intro s
    simpa [a, b] using lower_mem β s (n + 2)
  constructor
  · have hinv : ContinuousOn (fun s : ℝ => s⁻¹) (closedDomain β (n + 2)) :=
      continuousOn_id.inv₀ (fun s hs => ne_of_gt (closedDomain_pos hβ hs))
    rw [show layer β (n + 2) =
      (fun s => s⁻¹ * ∫ t in lower β s (n + 2)..b, g t) by funext s; rfl]
    exact hinv.mul hnum.continuousOn
  · intro s hs
    rw [layer]
    have hl := lower_mem β s (n + 2)
    have hI : 0 ≤ ∫ t in lower β s (n + 2)..(β + (n + 2 : ℕ)),
        layer β (n + 1) (t - 1) :=
      intervalIntegral.integral_nonneg hl.2 (by
        intro t ht
        apply hg_nonneg t
        constructor
        · exact hl.1.trans ht.1
        · simpa [b, Nat.cast_add, Nat.cast_ofNat] using ht.2)
    exact mul_nonneg (le_of_lt (inv_pos.mpr (closedDomain_pos hβ hs)))
      (by simpa [Nat.cast_add, Nat.cast_ofNat] using hI)
  · intro s hs t ht hst
    have hspos := closedDomain_pos hβ hs
    have htpos := closedDomain_pos hβ ht
    simp only [layer]
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt htpos), one_mul,
      ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hspos), one_mul]
    have hmono :
        (∫ x in lower β t (n + 2)..(β + (n + 2 : ℕ)), layer β (n + 1) (x - 1)) ≤
        ∫ x in lower β s (n + 2)..(β + (n + 2 : ℕ)), layer β (n + 1) (x - 1) := by
      apply intervalIntegral.integral_mono_interval
          (lower_mono β (n + 2) hst) (lower_mem β t (n + 2)).2 le_rfl
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
        apply hg_nonneg x
        constructor
        · exact (lower_mem β s (n + 2)).1.trans hx.1.le
        · simpa [b, Nat.cast_add, Nat.cast_ofNat] using hx.2
      · apply ContinuousOn.intervalIntegrable
        rw [Set.uIcc_of_le (lower_mem β s (n + 2)).2]
        apply hg.mono
        intro x hx
        constructor
        · exact (lower_mem β s (n + 2)).1.trans hx.1
        · simpa [b, Nat.cast_add, Nat.cast_ofNat] using hx.2
    simpa [Nat.cast_add, Nat.cast_ofNat] using hmono

/-- κ=1 basic regularity on the closed envelope; hence, in particular, on the
exact source parity domain. -/
theorem regular {β : ℝ} (hβ : 1 < β) (n : ℕ) : Regular β n := by
  induction n using Nat.twoStepInduction with
  | zero => exact regular_zero β
  | one => exact regular_one hβ
  | more n _ ih => exact regular_step hβ n ih

theorem continuousOn_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    ContinuousOn (layer β n) (parityDomain β n) :=
  (regular hβ n).continuous.mono (parityDomain_subset_closedDomain β n)

theorem nonneg_on_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    ∀ s ∈ parityDomain β n, 0 ≤ layer β n s := by
  intro s hs
  exact (regular hβ n).nonneg s (parityDomain_subset_closedDomain β n hs)

theorem weighted_antitoneOn_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    AntitoneOn (fun s => s * layer β n s) (parityDomain β n) :=
  (regular hβ n).weighted_antitone.mono (parityDomain_subset_closedDomain β n)

/-- The unweighted assertion in Proposition 9.2(iii) follows from weighted
antitonicity, positivity of the domain, and nonnegativity of the layer. -/
theorem antitoneOn_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    AntitoneOn (layer β n) (parityDomain β n) := by
  intro s hs t ht hst
  have hs' := parityDomain_subset_closedDomain β n hs
  have ht' := parityDomain_subset_closedDomain β n ht
  have hweighted := (regular hβ n).weighted_antitone hs' ht' hst
  have hscale : s * layer β n t ≤ t * layer β n t :=
    mul_le_mul_of_nonneg_right hst ((regular hβ n).nonneg t ht')
  nlinarith [hscale.trans hweighted, closedDomain_pos hβ hs']

/-- Proposition 9.2(i): clipping the lower endpoint makes the layer vanish
once `s ≥ β+n`.  This statement does not require a domain hypothesis. -/
theorem layer_eq_zero_of_upper (β : ℝ) (n : ℕ) {s : ℝ}
    (hs : β + n ≤ s) : layer β n s = 0 := by
  cases n with
  | zero => simp [layer]
  | succ n =>
      cases n with
      | zero =>
          have hs' : β + 1 ≤ s := by norm_num at hs ⊢; exact hs
          simp [layer, min_eq_right hs']
      | succ n =>
          have hlower : lower β s (n + 2) = β + (n + 2 : ℕ) := by
            unfold lower
            apply min_eq_right
            exact hs.trans (le_max_left _ _)
          simp [layer, hlower]

/-- The specialized κ=1 model is definitionally the source-correct general layer. -/
theorem layer_eq_suzukiLayer (β : ℝ) (n : ℕ) (s : ℝ) :
    layer β n s = MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer 1 β n s := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => rfl
  | one =>
      simp [layer, MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer,
        MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.baseLower,
        MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.dPowDensity]
  | more n _ ih =>
      rw [layer, MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.suzukiLayer]
      have hinv : s⁻¹ = (s ^ (1 : ℝ))⁻¹ := by norm_num
      rw [← hinv]
      have hlower : lower β s (n + 2) =
          MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.recursionLower β s (n + 2) := rfl
      rw [hlower]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp
      rw [ih]
      norm_num [MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.dPowDensity]

end
end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers.KappaOneModel

namespace MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers

/-- Exact parity domain for the dimension-one finite layer. -/
abbrev suzukiParityDomainOne := KappaOneModel.parityDomain

/-- Proposition 9.2(ii), continuity on the exact parity domain, for κ=1. -/
theorem suzukiLayer_one_continuousOn_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    ContinuousOn (suzukiLayer 1 β n) (suzukiParityDomainOne β n) := by
  exact (KappaOneModel.continuousOn_parityDomain hβ n).congr
    (fun s _ => (KappaOneModel.layer_eq_suzukiLayer β n s).symm)

/-- Proposition 9.2(ii), nonnegativity on the exact parity domain, for κ=1. -/
theorem suzukiLayer_one_nonneg_on_parityDomain {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    ∀ s ∈ suzukiParityDomainOne β n, 0 ≤ suzukiLayer 1 β n s := by
  simpa only [KappaOneModel.layer_eq_suzukiLayer] using
    KappaOneModel.nonneg_on_parityDomain hβ n

/-- Proposition 9.2(iii), weighted antitonicity on the exact parity domain. -/
theorem suzukiLayer_one_weighted_antitoneOn_parityDomain
    {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    AntitoneOn (fun s => s * suzukiLayer 1 β n s) (suzukiParityDomainOne β n) := by
  simpa only [KappaOneModel.layer_eq_suzukiLayer] using
    KappaOneModel.weighted_antitoneOn_parityDomain hβ n

/-- Proposition 9.2(iii), ordinary antitonicity on the exact parity domain. -/
theorem suzukiLayer_one_antitoneOn_parityDomain
    {β : ℝ} (hβ : 1 < β) (n : ℕ) :
    AntitoneOn (suzukiLayer 1 β n) (suzukiParityDomainOne β n) := by
  intro a ha b hb hab
  rw [← KappaOneModel.layer_eq_suzukiLayer,
    ← KappaOneModel.layer_eq_suzukiLayer]
  exact KappaOneModel.antitoneOn_parityDomain hβ n ha hb hab

end MathlibNt.SieveTheory.SuzukiFiniteContinuousLayers
