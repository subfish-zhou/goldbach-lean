import MathlibNt.SieveTheory.LiuPrimePairLogGridLimit
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

open MeasureTheory Set Finset
open scoped BigOperators Interval NNReal
noncomputable section
namespace LiLiuGoldbachLogDarboux

def grid (a b : ℝ) (n i : ℕ) : ℝ := a + (i : ℝ) * (b - a) / n

def cell (a b c d : ℝ) (n : ℕ) (q : Fin n × Fin n) : Set (ℝ × ℝ) :=
  Ioc (grid a b n q.1) (grid a b n (q.1.val + 1)) ×ˢ
  Ioc (grid c d n q.2) (grid c d n (q.2.val + 1))

def corner (a b c d : ℝ) (n : ℕ) (q : Fin n × Fin n) : ℝ × ℝ :=
  (grid a b n (q.1.val + 1), grid c d n (q.2.val + 1))

def oscillation (a b c d : ℝ) (L : ℝ≥0) (n : ℕ) : ℝ :=
  L * ((b-a) + (d-c)) / n

def coefficient (a b c d : ℝ) (K : ℝ × ℝ → ℝ) (L : ℝ≥0)
    (n : ℕ) (q : Fin n × Fin n) : ℝ :=
  max 0 (K (corner a b c d n q) - oscillation a b c d L n)

lemma grid_zero (a b : ℝ) (n : ℕ) : grid a b n 0 = a := by simp [grid]
lemma grid_last (a b : ℝ) {n : ℕ} (hn : 0 < n) : grid a b n n = b := by
  unfold grid
  field_simp
  ring

lemma grid_mono {a b : ℝ} (hab : a ≤ b) (n : ℕ) : Monotone (grid a b n) := by
  intro i j hij
  unfold grid
  exact add_le_add_right (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ (j:ℝ) by exact_mod_cast hij) (sub_nonneg.mpr hab))
    (Nat.cast_nonneg n)) a

lemma grid_step (a b : ℝ) (n i : ℕ) :
    grid a b n (i+1) - grid a b n i = (b-a)/n := by
  simp only [grid, Nat.cast_add, Nat.cast_one]
  ring

lemma grid_strict {a b : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n) (i : ℕ) :
    grid a b n i < grid a b n (i+1) := by
  have := div_pos (sub_pos.mpr hab) (show (0:ℝ)<n by exact_mod_cast hn)
  linarith [grid_step a b n i]

lemma grid_bounds {a b : ℝ} (hab : a ≤ b) {n i : ℕ} (hn : 0 < n) (hi : i ≤ n) :
    a ≤ grid a b n i ∧ grid a b n i ≤ b := by
  constructor
  · simpa only [grid_zero] using grid_mono hab n (Nat.zero_le i)
  · simpa only [grid_last a b hn] using grid_mono hab n hi

lemma cell_subset {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    cell a b c d n q ⊆ Ioc a b ×ˢ Ioc c d := by
  intro x hx
  exact ⟨⟨lt_of_le_of_lt (grid_bounds hab hn (Nat.le_of_lt q.1.isLt)).1 hx.1.1,
    hx.1.2.trans (grid_bounds hab hn (Nat.succ_le_of_lt q.1.isLt)).2⟩,
    ⟨lt_of_le_of_lt (grid_bounds hcd hn (Nat.le_of_lt q.2.isLt)).1 hx.2.1,
    hx.2.2.trans (grid_bounds hcd hn (Nat.succ_le_of_lt q.2.isLt)).2⟩⟩

lemma cell_disjoint {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (n : ℕ) :
    (Set.univ : Set (Fin n × Fin n)).Pairwise
      (Function.onFun Disjoint (cell a b c d n)) := by
  intro q _ r _ hqr
  change Disjoint (cell a b c d n q) (cell a b c d n r)
  rw [Set.disjoint_left]
  intro x hx hy
  by_cases hi : q.1 = r.1
  · have hj : q.2 ≠ r.2 := fun h => hqr (Prod.ext hi h)
    rcases lt_or_gt_of_ne hj with h | h
    · have H := grid_mono hcd n (show q.2.val+1 ≤ r.2.val by exact h)
      exact (not_lt_of_ge H) (hy.2.1.trans_le hx.2.2)
    · have H := grid_mono hcd n (show r.2.val+1 ≤ q.2.val by exact h)
      exact (not_lt_of_ge H) (hx.2.1.trans_le hy.2.2)
  · rcases lt_or_gt_of_ne hi with h | h
    · have H := grid_mono hab n (show q.1.val+1 ≤ r.1.val by exact h)
      exact (not_lt_of_ge H) (hy.1.1.trans_le hx.1.2)
    · have H := grid_mono hab n (show r.1.val+1 ≤ q.1.val by exact h)
      exact (not_lt_of_ge H) (hx.1.1.trans_le hy.1.2)

lemma exists_grid_cell {a b x : ℝ} (hab : a < b) {n : ℕ} (hn : 0 < n)
    (hx : x ∈ Ioc a b) : ∃ i : Fin n, x ∈ Ioc (grid a b n i) (grid a b n (i.val+1)) := by
  have he : a + (n:ℝ)*((b-a)/n) = b := by
    simpa only [grid, mul_div_assoc] using grid_last a b hn
  obtain ⟨i, hi, hl, hu⟩ := MathlibNt.SieveTheory.LiuWeight.exists_nat_cell n
    (div_pos (sub_pos.mpr hab) (by exact_mod_cast hn)) hx.1 (he.symm ▸ hx.2)
  exact ⟨⟨i,hi⟩, by simpa only [grid, mul_div_assoc, Set.mem_Ioc] using And.intro hl hu⟩

lemma cells_union {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {n : ℕ} (hn : 0 < n) :
    (⋃ q ∈ (Finset.univ : Finset (Fin n × Fin n)), cell a b c d n q) =
      Ioc a b ×ˢ Ioc c d := by
  ext x
  simp only [Set.mem_iUnion, Finset.mem_univ, exists_prop, true_and]
  constructor
  · rintro ⟨q,hq⟩; exact cell_subset hab.le hcd.le hn q hq
  · intro hx
    obtain ⟨i,hi⟩ := exists_grid_cell hab hn hx.1
    obtain ⟨j,hj⟩ := exists_grid_cell hcd hn hx.2
    exact ⟨(i,j),hi,hj⟩

/-- A generic finite fixed-grid integral decomposition; no prime arithmetic. -/
theorem integral_eq_sum_cells {a b c d : ℝ} (hab : a < b) (hcd : c < d)
    {n : ℕ} (hn : 0 < n) {f : ℝ × ℝ → ℝ}
    (hf : IntegrableOn f (Ioc a b ×ˢ Ioc c d)) :
    (∫ x in Ioc a b ×ˢ Ioc c d, f x) =
      ∑ q : Fin n × Fin n, ∫ x in cell a b c d n q, f x := by
  rw [← cells_union hab hcd hn]
  exact integral_biUnion_finset Finset.univ
    (fun _ _ => measurableSet_Ioc.prod measurableSet_Ioc)
    (by simpa using cell_disjoint hab.le hcd.le n)
    (fun q _ => hf.mono_set (cell_subset hab.le hcd.le hn q))

lemma corner_dist {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {n : ℕ} (q : Fin n × Fin n) {x : ℝ × ℝ} (hx : x ∈ cell a b c d n q) :
    dist x (corner a b c d n q) ≤ ((b-a)+(d-c))/n := by
  have ha : 0 ≤ (b-a)/(n:ℝ) := div_nonneg (sub_nonneg.mpr hab) (Nat.cast_nonneg n)
  have hc : 0 ≤ (d-c)/(n:ℝ) := div_nonneg (sub_nonneg.mpr hcd) (Nat.cast_nonneg n)
  rw [Prod.dist_eq, max_le_iff]
  change dist x.1 (grid a b n (q.1.val+1)) ≤ _ ∧ dist x.2 (grid c d n (q.2.val+1)) ≤ _
  rw [Real.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.1.2),
    abs_of_nonpos (sub_nonpos.mpr hx.2.2), add_div]
  constructor
  · linarith [grid_step a b n q.1.val, hx.1.1]
  · linarith [grid_step c d n q.2.val, hx.2.1]

lemma coefficient_bounds {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {K : ℝ × ℝ → ℝ} {L : ℝ≥0} (hK : LipschitzWith L K)
    (hpos : ∀ x ∈ Ioc a b ×ˢ Ioc c d, 0 ≤ K x)
    {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) {x : ℝ × ℝ}
    (hx : x ∈ cell a b c d n q) :
    0 ≤ coefficient a b c d K L n q ∧
    coefficient a b c d K L n q ≤ K x ∧
    K x - 2 * oscillation a b c d L n ≤ coefficient a b c d K L n q := by
  have H := (hK.dist_le_mul x (corner a b c d n q)).trans
    (mul_le_mul_of_nonneg_left (corner_dist hab hcd q hx) L.coe_nonneg)
  rw [Real.dist_eq, ← mul_div_assoc, ← oscillation] at H
  have H1 := (abs_le.mp H).1
  have H2 := (abs_le.mp H).2
  refine ⟨le_max_left _ _, max_le (hpos x (cell_subset hab hcd hn q hx)) ?_, ?_⟩
  · linarith
  · exact le_trans (by linarith) (le_max_right _ _)

/-- Integrability is derived from continuity on the positive closed rectangle. -/
lemma weighted_integrable {a b c d : ℝ} (ha : 0 < a) (hc : 0 < c)
    {K : ℝ × ℝ → ℝ} (hK : Continuous K) :
    IntegrableOn (fun x => K x / (x.1*x.2)) (Ioc a b ×ˢ Ioc c d) := by
  have H : ContinuousOn (fun x : ℝ × ℝ => K x / (x.1*x.2)) (Icc a b ×ˢ Icc c d) :=
    hK.continuousOn.div (continuous_fst.mul continuous_snd).continuousOn
      (fun x hx => ne_of_gt (mul_pos (ha.trans_le hx.1.1) (hc.trans_le hx.2.1)))
  exact (H.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

lemma integral_eq_iterated {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {f : ℝ × ℝ → ℝ} (hf : IntegrableOn f (Ioc a b ×ˢ Ioc c d)) :
    (∫ x in Ioc a b ×ˢ Ioc c d, f x) = ∫ u in a..b, ∫ v in c..d, f (u,v) := by
  rw [intervalIntegral.integral_of_le hab]
  simp_rw [intervalIntegral.integral_of_le hcd]
  rw [MeasureTheory.Measure.volume_eq_prod ℝ ℝ] at hf ⊢
  exact setIntegral_prod f hf

open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.PrimeReciprocalLogRectangle

def cellMass (a b c d : ℝ) (n : ℕ) (q : Fin n × Fin n) : ℝ :=
  logarithmicRectangleMass (grid a b n q.1) (grid a b n (q.1.val+1))
    (grid c d n q.2) (grid c d n (q.2.val+1))

lemma cellMass_eq {a b c d : ℝ} (ha : 0 < a) (hab : a < b) (hc : 0 < c)
    (hcd : c < d) {n : ℕ} (hn : 0 < n) (q : Fin n × Fin n) :
    cellMass a b c d n q = ∫ x in cell a b c d n q, 1/(x.1*x.2) := by
  exact logarithmicRectangleMass_eq_setIntegral
    (ha.trans_le (grid_bounds hab.le hn (Nat.le_of_lt q.1.isLt)).1)
    (grid_strict hab hn _) (hc.trans_le (grid_bounds hcd.le hn (Nat.le_of_lt q.2.isLt)).1)
    (grid_strict hcd hn _)

/-- Explicit error bound for the concrete nonnegative lower coefficients.
The factor two arises from using the upper-right sample minus the oscillation. -/
theorem darboux_explicit {a b c d : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) {K : ℝ × ℝ → ℝ} {L : ℝ≥0}
    (hK : LipschitzWith L K) (hpos : ∀ x ∈ Ioc a b ×ˢ Ioc c d, 0 ≤ K x)
    {n : ℕ} (hn : 0 < n) :
    (∫ u in a..b, ∫ v in c..d, K (u,v)/(u*v)) -
      2 * oscillation a b c d L n * logarithmicRectangleMass a b c d ≤
    ∑ q : Fin n × Fin n, coefficient a b c d K L n q * cellMass a b c d n q := by
  let e := 2 * oscillation a b c d L n
  have hki := weighted_integrable (b := b) (d := d) ha hc hK.continuous
  have hdi := weighted_integrable (b := b) (d := d) ha hc (continuous_const : Continuous (fun _ : ℝ × ℝ => (1:ℝ)))
  have hfi := weighted_integrable (b := b) (d := d) ha hc (hK.continuous.sub continuous_const : Continuous (fun x => K x - e))
  simp only [Pi.sub_apply] at hfi
  have hid : (∫ x in Ioc a b ×ˢ Ioc c d, 1/(x.1*x.2)) =
      logarithmicRectangleMass a b c d :=
    (logarithmicRectangleMass_eq_setIntegral ha hab hc hcd).symm
  have heq : (∫ x in Ioc a b ×ˢ Ioc c d, (K x-e)/(x.1*x.2)) =
      (∫ u in a..b, ∫ v in c..d, K (u,v)/(u*v)) - e * logarithmicRectangleMass a b c d := by
    simp_rw [sub_div, div_eq_mul_one_div e]
    rw [integral_sub hki (hdi.const_mul e), integral_const_mul, hid,
      integral_eq_iterated hab.le hcd.le hki]
  rw [← heq, integral_eq_sum_cells hab hcd hn hfi]
  apply Finset.sum_le_sum
  intro q _
  rw [cellMass_eq ha hab hc hcd hn q, ← integral_const_mul]
  apply setIntegral_mono_on (hfi.mono_set (cell_subset hab.le hcd.le hn q))
    ((hdi.mono_set (cell_subset hab.le hcd.le hn q)).const_mul _)
    (measurableSet_Ioc.prod measurableSet_Ioc)
  intro x hx
  have H := (coefficient_bounds hab.le hcd.le hK hpos hn q hx).2.2
  have hx' := cell_subset hab.le hcd.le hn q hx
  have hd : 0 ≤ x.1*x.2 := (mul_pos (ha.trans hx'.1.1) (hc.trans hx'.2.1)).le
  calc
    (K x - e) / (x.1*x.2) ≤ coefficient a b c d K L n q / (x.1*x.2) :=
      div_le_div_of_nonneg_right H hd
    _ = coefficient a b c d K L n q * (1 / (x.1*x.2)) := div_eq_mul_one_div _ _

/-- Finite logarithmic-density Darboux lower approximation on any positive rectangle.
The coefficient is a kernel value, not a density-weighted kernel value. -/
theorem exists_darboux {a b c d : ℝ} (ha : 0 < a) (hab : a < b)
    (hc : 0 < c) (hcd : c < d) {K : ℝ × ℝ → ℝ} {L : ℝ≥0}
    (hK : LipschitzWith L K) (hpos : ∀ x ∈ Ioc a b ×ˢ Ioc c d, 0 ≤ K x)
    {η : ℝ} (hη : 0 < η) :
    ∃ (n : ℕ), 0 < n ∧ ∃ coeff : Fin n × Fin n → ℝ,
      (∀ q, 0 ≤ coeff q) ∧
      (∀ q x, x ∈ cell a b c d n q → coeff q ≤ K x) ∧
      (∫ u in a..b, ∫ v in c..d, K (u,v)/(u*v)) - η ≤
        ∑ q : Fin n × Fin n, coeff q * cellMass a b c d n q := by
  let A : ℝ := 2 * (L:ℝ) * ((b-a)+(d-c)) * logarithmicRectangleMass a b c d
  obtain ⟨m, hm⟩ := exists_nat_gt (A/η)
  let n := m+1
  have hn : 0 < n := Nat.succ_pos m
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  have hmn : (m:ℝ) < n := by exact_mod_cast Nat.lt_succ_self m
  have hsmall : A/(n:ℝ) < η := by
    apply (div_lt_iff₀ hn').mpr
    have H := (div_lt_iff₀ hη).mp (hm.trans hmn)
    nlinarith
  have he : 2 * oscillation a b c d L n * logarithmicRectangleMass a b c d = A/n := by
    dsimp [oscillation, A]
    ring
  refine ⟨n, hn, coefficient a b c d K L n, ?_, ?_, ?_⟩
  · intro q; exact le_max_left _ _
  · intro q x hx; exact (coefficient_bounds hab.le hcd.le hK hpos hn q hx).2.1
  · have H := darboux_explicit ha hab hc hcd hK hpos hn
    rw [he] at H
    linarith

end LiLiuGoldbachLogDarboux
