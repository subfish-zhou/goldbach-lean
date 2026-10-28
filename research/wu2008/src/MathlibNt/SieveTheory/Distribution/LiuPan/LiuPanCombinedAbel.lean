import MathlibNt.SieveTheory.Distribution.LiuPan.LiuPanCombinedInverseLog
import Mathlib.Algebra.BigOperators.Module

/-!
# Exact Abel reduction for Liu's combined inverse-log discrepancy

This file applies finite summation by parts to the complete arithmetic-progression
von Mangoldt sum.  Its main route forms the source aggregate before taking an
absolute value: quotient shells and prefix swaps are exact finite identities.
The older sourcewise triangle route is retained below only as a diagnostic.  It
is analytically too strong because the empty-progression tail with `q > y / a`
survives after taking absolute values source by source.
-/

open scoped BigOperators

namespace MathlibNt.SieveTheory.LiuWeight

open Filter Finset ArithmeticFunction
open AnalyticNumberTheory.Sieve

/-! ## Complete AP psi sums and finite Abel summation -/

/-- The complete von Mangoldt sum in one arithmetic progression, including the
harmless indices `0` and `1`. -/
noncomputable def liuPanAPPsi (y q l : ℕ) : ℝ :=
  ∑ n ∈ range (y + 1), if n ≡ l [MOD q] then Λ n else 0

/-- The complete AP psi discrepancy from the uniform main term `y / phi(q)`. -/
noncomputable def liuPanAPPsiDiscrepancy (y q l : ℕ) : ℝ :=
  liuPanAPPsi y q l - (y : ℝ) / Nat.totient q

/-- The finite Abel weight for `1 / log`.  It is explicitly zero at `0` and `1`. -/
noncomputable def liuPanInverseLogAbelWeight (n : ℕ) : ℝ :=
  if 2 ≤ n then
    (Real.log (n : ℝ))⁻¹ - (Real.log (n + 1 : ℕ))⁻¹
  else 0

/-- The discrete main term obtained by applying the same Abel transform to `x`. -/
noncomputable def liuPanDiscreteInverseLogMain (y : ℕ) : ℝ :=
  (Real.log (y : ℝ))⁻¹ * y +
    ∑ n ∈ range y, liuPanInverseLogAbelWeight n * n

@[simp] theorem liuPanAPPsi_zero (q l : ℕ) :
    liuPanAPPsi 0 q l = 0 := by
  simp [liuPanAPPsi]

@[simp] theorem liuPanAPPsi_one (q l : ℕ) :
    liuPanAPPsi 1 q l = 0 := by
  unfold liuPanAPPsi
  apply sum_eq_zero
  intro n hn
  have hnlt : n < 2 := mem_range.mp hn
  interval_cases n <;> simp

@[simp] theorem liuPanInverseLogAbelWeight_zero :
    liuPanInverseLogAbelWeight 0 = 0 := by
  simp [liuPanInverseLogAbelWeight]

@[simp] theorem liuPanInverseLogAbelWeight_one :
    liuPanInverseLogAbelWeight 1 = 0 := by
  simp [liuPanInverseLogAbelWeight]





/-! ## Aggregate-before-absolute-value Abel identities -/

/-- The source-aggregated AP psi discrepancy up to `A`.  The residue attached
to a source index `a` is the canonical representative of `a⁻¹ l (mod q)`. -/
noncomputable def liuPanAggregateAPPsiDiscrepancy
    (t A q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 A, if a.Coprime q then
    f a * liuPanAPPsiDiscrepancy t q (natInvMod q a * l % q)
  else 0

/-- The source cutoff in the quotient shell indexed by `k`.  The value at zero
is deliberately the full source endpoint. -/
def liuPanAbelSourceCutoff (y X k : ℕ) : ℕ :=
  if k = 0 then X else min X (y / k)

@[simp] theorem liuPanAbelSourceCutoff_zero (y X : ℕ) :
    liuPanAbelSourceCutoff y X 0 = X := by
  simp [liuPanAbelSourceCutoff]

theorem liuPanAbelSourceCutoff_of_pos
    (y X k : ℕ) (hk : 0 < k) :
    liuPanAbelSourceCutoff y X k = min X (y / k) := by
  simp [liuPanAbelSourceCutoff, hk.ne']

@[simp] theorem liuPanAbelSourceCutoff_succ (y X k : ℕ) :
    liuPanAbelSourceCutoff y X (k + 1) = min X (y / (k + 1)) := by
  exact liuPanAbelSourceCutoff_of_pos y X (k + 1) (by omega)

theorem liuPanAbelSourceCutoff_le (y X k : ℕ) :
    liuPanAbelSourceCutoff y X k ≤ X := by
  unfold liuPanAbelSourceCutoff
  split_ifs <;> simp_all

theorem le_liuPanAbelSourceCutoff_iff
    (y X a k : ℕ) (hk : 0 < k) (haX : a ≤ X) (ha : 0 < a) :
    a ≤ liuPanAbelSourceCutoff y X k ↔ k ≤ y / a := by
  rw [liuPanAbelSourceCutoff_of_pos y X k hk, Nat.le_min]
  simp only [haX, true_and]
  rw [Nat.le_div_iff_mul_le hk, Nat.le_div_iff_mul_le ha]
  exact mul_comm a k ▸ Iff.rfl

private theorem sum_Icc_eq_sum_Icc_indicator
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) (A X : ℕ) (hAX : A ≤ X) :
    (∑ a ∈ Icc 1 A, F a) =
      ∑ a ∈ Icc 1 X, if a ≤ A then F a else 0 := by
  rw [← sum_filter]
  apply sum_congr
  · ext a
    simp only [mem_Icc, mem_filter]
    omega
  · intro a ha
    rfl

private theorem sum_range_eq_sum_range_indicator
    {M : Type*} [AddCommMonoid M] (F : ℕ → M) (d y : ℕ) (hdy : d ≤ y) :
    (∑ n ∈ range d, F n) =
      ∑ n ∈ range y, if n < d then F n else 0 := by
  rw [← sum_filter]
  apply sum_congr
  · ext n
    simp only [mem_range, mem_filter]
    omega
  · intro n hn
    rfl

/-- Quotient fibers are exactly the successive source-cutoff shells.  The
assumption `g 0 = 0` disposes of the sources with `y / a = 0` exactly. -/
theorem sum_source_eq_sum_quotient_shells
    {R : Type*} [CommRing R]
    (y X : ℕ) (g : ℕ → R) (F : ℕ → ℕ → R) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, g (y / a) * F (y / a) a) =
      ∑ k ∈ Icc 1 y, g k *
        ((∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X k), F k a) -
          ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (k + 1)), F k a) := by
  symm
  calc
    _ = ∑ k ∈ Icc 1 y, ∑ a ∈ Icc 1 X,
          if y / a = k then g k * F k a else 0 := by
      apply sum_congr rfl
      intro k hk
      have hkpos : 0 < k := (mem_Icc.mp hk).1
      rw [sum_Icc_eq_sum_Icc_indicator (F k) _ X
          (liuPanAbelSourceCutoff_le y X k),
        sum_Icc_eq_sum_Icc_indicator (F k) _ X
          (liuPanAbelSourceCutoff_le y X (k + 1)),
        mul_sub, mul_sum, mul_sum, ← sum_sub_distrib]
      apply sum_congr rfl
      intro a ha
      have haX : a ≤ X := (mem_Icc.mp ha).2
      have hapos : 0 < a := (mem_Icc.mp ha).1
      have hc :=
        le_liuPanAbelSourceCutoff_iff y X a k hkpos haX hapos
      have hcn :=
        le_liuPanAbelSourceCutoff_iff y X a (k + 1) (by omega) haX hapos
      by_cases hdiv : y / a = k
      · have hac : a ≤ liuPanAbelSourceCutoff y X k := hc.mpr (by omega)
        have hanc : ¬a ≤ liuPanAbelSourceCutoff y X (k + 1) :=
          hcn.not.mpr (by omega)
        rw [if_pos hac, if_neg hanc, if_pos hdiv]
        ring
      · by_cases hle : k ≤ y / a
        · have hnext : k + 1 ≤ y / a := by omega
          have hac := hc.mpr hle
          have hacn := hcn.mpr hnext
          rw [if_pos hac, if_pos hacn, if_neg hdiv]
          ring
        · have hac : ¬a ≤ liuPanAbelSourceCutoff y X k :=
            hc.not.mpr hle
          have hacn : ¬a ≤ liuPanAbelSourceCutoff y X (k + 1) :=
            hcn.not.mpr (by omega)
          rw [if_neg hac, if_neg hacn, if_neg hdiv]
          simp
    _ = ∑ a ∈ Icc 1 X, ∑ k ∈ Icc 1 y,
          if y / a = k then g k * F k a else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      by_cases hd0 : y / a = 0
      · simp [hd0, hg0]
      · have hdpos : 0 < y / a := Nat.pos_of_ne_zero hd0
        have hdle : y / a ≤ y := Nat.div_le_self y a
        rw [sum_eq_single (y / a)]
        · simp
        · intro b hb hne
          simp [Ne.symm hne]
        · intro hnot
          exact (hnot (mem_Icc.mpr ⟨hdpos, hdle⟩)).elim

/-- Swapping a source sum with quotient prefixes replaces each prefix by one
source aggregate at the cutoff `A_{n+1}`. -/
theorem sum_source_prefix_eq_sum_aggregate_prefix
    {R : Type*} [CommRing R]
    (y X : ℕ) (w : ℕ → R) (F : ℕ → ℕ → R) :
    (∑ a ∈ Icc 1 X, ∑ n ∈ range (y / a), w n * F n a) =
      ∑ n ∈ range y, w n *
        ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (n + 1)), F n a := by
  symm
  calc
    _ = ∑ n ∈ range y, ∑ a ∈ Icc 1 X,
          if n < y / a then w n * F n a else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [sum_Icc_eq_sum_Icc_indicator (F n) _ X
          (liuPanAbelSourceCutoff_le y X (n + 1)), mul_sum]
      apply sum_congr rfl
      intro a ha
      have haX : a ≤ X := (mem_Icc.mp ha).2
      have hapos : 0 < a := (mem_Icc.mp ha).1
      have hc :=
        le_liuPanAbelSourceCutoff_iff y X a (n + 1) (by omega) haX hapos
      by_cases hlt : n < y / a
      · have hac := hc.mpr (by omega)
        rw [if_pos hac, if_pos hlt]
      · have hnac := hc.not.mpr (by omega)
        rw [if_neg hnac, if_neg hlt]
        simp
    _ = ∑ a ∈ Icc 1 X, ∑ n ∈ range y,
          if n < y / a then w n * F n a else 0 := by
      rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      rw [← sum_range_eq_sum_range_indicator
        (fun n => w n * F n a) (y / a) y (Nat.div_le_self y a)]





/-- The aggregate psi contribution after both exact finite rearrangements. -/
noncomputable def liuPanAggregateInverseLogPsiTerm
    (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  (∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
    (liuPanAggregateAPPsiDiscrepancy k
        (liuPanAbelSourceCutoff y X k) q l f -
      liuPanAggregateAPPsiDiscrepancy k
        (liuPanAbelSourceCutoff y X (k + 1)) q l f)) +
  ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
    liuPanAggregateAPPsiDiscrepancy n
      (liuPanAbelSourceCutoff y X (n + 1)) q l f

/-- The deterministic source-weighted difference between the discrete Abel main
term and Liu's logarithmic integral. -/
noncomputable def liuPanAggregateInverseLogDeterministicTerm
    (kappa : ℝ) (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 X, if a.Coprime q then
    f a * (liuPanDiscreteInverseLogMain (y / a) -
      liuLogarithmicIntegral kappa ((y : ℝ) / a))
  else 0



/-! ## Canonical aggregate maxima -/

/-- Canonical reduced-residue maximum of the absolute aggregate psi term. -/
noncomputable def liuPanAggregateInverseLogPsiMaxL
    (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l => |liuPanAggregateInverseLogPsiTerm y X q l f|)).max'
      (Finset.image_nonempty.mpr h)
  else 0

/-- Canonical maximum over `y ≤ x` of the absolute aggregate psi term. -/
noncomputable def liuPanAggregateInverseLogPsiMaxY
    (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanAggregateInverseLogPsiMaxL y X q f)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

/-- Canonical reduced-residue maximum of the deterministic term.  The term is
independent of the residue, but the empty residue set at modulus zero is kept
canonical. -/
noncomputable def liuPanAggregateInverseLogDeterministicMaxL
    (kappa : ℝ) (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  if (unitResidues q).Nonempty then
    |liuPanAggregateInverseLogDeterministicTerm kappa y X q f|
  else 0

/-- Canonical maximum over `y ≤ x` of the deterministic source error. -/
noncomputable def liuPanAggregateInverseLogDeterministicMaxY
    (kappa : ℝ) (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanAggregateInverseLogDeterministicMaxL kappa y X q f)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] theorem liuPanAggregateInverseLogPsiMaxL_zero
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiMaxL y X 0 f = 0 := by
  simp [liuPanAggregateInverseLogPsiMaxL]

@[simp] theorem liuPanAggregateInverseLogPsiMaxL_one
    (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiMaxL y X 1 f =
      |liuPanAggregateInverseLogPsiTerm y X 1 0 f| := by
  simp [liuPanAggregateInverseLogPsiMaxL]

@[simp] theorem liuPanAggregateInverseLogPsiMaxY_zero
    (X x : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiMaxY X 0 x f = 0 := by
  simp [liuPanAggregateInverseLogPsiMaxY,
    Finset.image_const (by simp : (range (x + 1)).Nonempty)]

@[simp] theorem liuPanAggregateInverseLogPsiMaxY_one
    (X x : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogPsiMaxY X 1 x f =
      ((range (x + 1)).image (fun y =>
        |liuPanAggregateInverseLogPsiTerm y X 1 0 f|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanAggregateInverseLogPsiMaxY
  simp only [liuPanAggregateInverseLogPsiMaxL_one]

@[simp] theorem liuPanAggregateInverseLogDeterministicMaxL_zero
    (kappa : ℝ) (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogDeterministicMaxL kappa y X 0 f = 0 := by
  simp [liuPanAggregateInverseLogDeterministicMaxL]

@[simp] theorem liuPanAggregateInverseLogDeterministicMaxL_one
    (kappa : ℝ) (y X : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogDeterministicMaxL kappa y X 1 f =
      |liuPanAggregateInverseLogDeterministicTerm kappa y X 1 f| := by
  simp [liuPanAggregateInverseLogDeterministicMaxL]

@[simp] theorem liuPanAggregateInverseLogDeterministicMaxY_zero
    (kappa : ℝ) (X x : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogDeterministicMaxY kappa X 0 x f = 0 := by
  simp [liuPanAggregateInverseLogDeterministicMaxY,
    Finset.image_const (by simp : (range (x + 1)).Nonempty)]

@[simp] theorem liuPanAggregateInverseLogDeterministicMaxY_one
    (kappa : ℝ) (X x : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogDeterministicMaxY kappa X 1 x f =
      ((range (x + 1)).image (fun y =>
        |liuPanAggregateInverseLogDeterministicTerm kappa y X 1 f|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanAggregateInverseLogDeterministicMaxY
  simp only [liuPanAggregateInverseLogDeterministicMaxL_one]



/-! ## Aggregate fixed-source and source-family bounds -/








/-! ## Sourcewise diagnostic (analytically overstrong) -/

/-- The pointwise Abel majorant.  Its three summands are respectively the
endpoint psi discrepancy divided by `log y`, a finite nonnegative weighted sum
of prefix psi discrepancies, and the deterministic discrete-main error.  Taking
this majorant source by source is retained only for comparison; it is not the
analytic frontier. -/
noncomputable def liuPanPsiAbelMajorant
    (kappa : ℝ) (y : ℕ) (x : ℝ) (q l : ℕ) : ℝ :=
  |liuPanAPPsiDiscrepancy y q l| / Real.log (y : ℝ) +
    ∑ n ∈ range y,
      liuPanInverseLogAbelWeight n *
        |liuPanAPPsiDiscrepancy n q l| +
    |liuPanDiscreteInverseLogMain y -
        liuLogarithmicIntegral kappa x| / Nat.totient q



/-! ## Diagnostic source-weighted maxima -/

/-- Diagnostic sourcewise Abel majorant.  Although the source coefficient
remains visible, the triangle inequality has already destroyed cancellation
between distinct source indices. -/
noncomputable def liuPanSourceWeightedPsiAbelMajorant
    (kappa : ℝ) (y X q l : ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ a ∈ Icc 1 X, if a.Coprime q then
    |f a| *
      liuPanPsiAbelMajorant kappa (y / a) ((y : ℝ) / a) q
        (natInvMod q a * l % q)
  else 0



/-- Canonical maximum of the source-weighted psi majorant over reduced
residues. -/
noncomputable def liuPanSourceWeightedPsiAbelMaxL
    (kappa : ℝ) (y X q : ℕ) (f : ℕ → ℝ) : ℝ :=
  let S := unitResidues q
  if h : S.Nonempty then
    (S.image (fun l =>
      liuPanSourceWeightedPsiAbelMajorant kappa y X q l f)).max'
        (Finset.image_nonempty.mpr h)
  else 0

/-- Canonical maximum of the source-weighted psi majorant over `y ≤ x`. -/
noncomputable def liuPanSourceWeightedPsiAbelMaxY
    (kappa : ℝ) (X q x : ℕ) (f : ℕ → ℝ) : ℝ :=
  ((range (x + 1)).image (fun y =>
    liuPanSourceWeightedPsiAbelMaxL kappa y X q f)).max'
      (Finset.image_nonempty.mpr ⟨0, by simp⟩)

@[simp] theorem liuPanSourceWeightedPsiAbelMaxL_zero
    (kappa : ℝ) (y X : ℕ) (f : ℕ → ℝ) :
    liuPanSourceWeightedPsiAbelMaxL kappa y X 0 f = 0 := by
  simp [liuPanSourceWeightedPsiAbelMaxL]

@[simp] theorem liuPanSourceWeightedPsiAbelMaxL_one
    (kappa : ℝ) (y X : ℕ) (f : ℕ → ℝ) :
    liuPanSourceWeightedPsiAbelMaxL kappa y X 1 f =
      liuPanSourceWeightedPsiAbelMajorant kappa y X 1 0 f := by
  simp [liuPanSourceWeightedPsiAbelMaxL]

@[simp] theorem liuPanSourceWeightedPsiAbelMaxY_zero
    (kappa : ℝ) (X x : ℕ) (f : ℕ → ℝ) :
    liuPanSourceWeightedPsiAbelMaxY kappa X 0 x f = 0 := by
  simp [liuPanSourceWeightedPsiAbelMaxY,
    Finset.image_const (by simp : (range (x + 1)).Nonempty)]




/-! ## Overstrong diagnostic source-family predicate -/






end MathlibNt.SieveTheory.LiuWeight
