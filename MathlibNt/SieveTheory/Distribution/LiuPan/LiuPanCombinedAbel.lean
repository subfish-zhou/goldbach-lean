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

theorem liuPanInverseLogAbelWeight_nonneg (n : ℕ) :
    0 ≤ liuPanInverseLogAbelWeight n := by
  unfold liuPanInverseLogAbelWeight
  split_ifs with hn
  · rw [sub_nonneg]
    have hnpos : (0 : ℝ) < n := by
      exact_mod_cast (show 0 < n by omega)
    have hsuccpos : (0 : ℝ) < (n + 1 : ℕ) := by
      exact_mod_cast (show 0 < n + 1 by omega)
    have hlogn : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogmono :
        Real.log (n : ℝ) ≤ Real.log (n + 1 : ℕ) := by
      exact Real.strictMonoOn_log.monotoneOn hnpos hsuccpos
        (by exact_mod_cast (Nat.le_succ n))
    exact inv_anti₀ hlogn hlogmono
  · exact le_rfl

private theorem natCast_log_nonneg (n : ℕ) :
    0 ≤ Real.log (n : ℝ) := by
  cases n with
  | zero => simp
  | succ n =>
      exact Real.log_nonneg
        (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))

/-- Exact finite discrete Abel summation for the AP sum of `Λ(n) / log n`.
The exceptional terms `n = 0, 1` vanish before a logarithmic denominator is
used, and the displayed prefix weights are nonnegative. -/
theorem apLogVonMangoldt_eq_discreteAbel (y q l : ℕ) :
    apLogVonMangoldt y q l =
      (Real.log (y : ℝ))⁻¹ * liuPanAPPsi y q l +
        ∑ n ∈ range y,
          liuPanInverseLogAbelWeight n * liuPanAPPsi n q l := by
  let c : ℕ → ℝ := fun n => if n ≡ l [MOD q] then Λ n else 0
  have h := Finset.sum_range_by_parts
    (fun n : ℕ => (Real.log (n : ℝ))⁻¹) c (y + 1)
  simp only [Nat.add_sub_cancel, smul_eq_mul] at h
  rw [show apLogVonMangoldt y q l =
      ∑ n ∈ range (y + 1), (Real.log (n : ℝ))⁻¹ * c n by
    unfold apLogVonMangoldt c
    apply sum_congr rfl
    intro n hn
    by_cases hmod : n ≡ l [MOD q] <;>
      simp [hmod, div_eq_inv_mul]]
  rw [h]
  change
    (Real.log (y : ℝ))⁻¹ * liuPanAPPsi y q l -
        ∑ n ∈ range y,
          ((Real.log (n + 1 : ℕ))⁻¹ - (Real.log (n : ℝ))⁻¹) *
            liuPanAPPsi n q l =
      _
  rw [sub_eq_add_neg, ← sum_neg_distrib]
  congr 1
  apply sum_congr rfl
  intro n hn
  by_cases hn2 : 2 ≤ n
  · simp only [liuPanInverseLogAbelWeight, if_pos hn2]
    ring
  · interval_cases n <;> simp [liuPanInverseLogAbelWeight]

/-- Exact decomposition of the inverse-log discrepancy into the endpoint psi
discrepancy, all preceding psi discrepancies, and the deterministic discrete
main-term error.  This identity is valid for every modulus, including `0` and
`1`. -/
theorem apLogVonMangoldt_sub_liuLogarithmicIntegral_eq_discreteAbel
    (kappa : ℝ) (y : ℕ) (x : ℝ) (q l : ℕ) :
    apLogVonMangoldt y q l -
        liuLogarithmicIntegral kappa x / Nat.totient q =
      (Real.log (y : ℝ))⁻¹ * liuPanAPPsiDiscrepancy y q l +
        ∑ n ∈ range y,
          liuPanInverseLogAbelWeight n *
            liuPanAPPsiDiscrepancy n q l +
        (liuPanDiscreteInverseLogMain y -
            liuLogarithmicIntegral kappa x) / Nat.totient q := by
  rw [apLogVonMangoldt_eq_discreteAbel]
  have hpsi : ∀ n : ℕ,
      liuPanAPPsi n q l =
        liuPanAPPsiDiscrepancy n q l +
          (n : ℝ) / Nat.totient q := by
    intro n
    unfold liuPanAPPsiDiscrepancy
    ring
  have hsum :
      (∑ n ∈ range y,
          liuPanInverseLogAbelWeight n *
            ((n : ℝ) / Nat.totient q)) =
        (∑ n ∈ range y,
          liuPanInverseLogAbelWeight n * (n : ℝ)) /
            Nat.totient q := by
    rw [Finset.sum_div]
    apply sum_congr rfl
    intro n hn
    ring
  rw [hpsi y]
  simp_rw [hpsi, mul_add]
  rw [Finset.sum_add_distrib, hsum]
  unfold liuPanDiscreteInverseLogMain
  ring

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

/-- Exact endpoint shell identity for the source-aggregated AP psi
discrepancy. -/
theorem liuPanAggregateAPPsiDiscrepancy_endpoint_shell
    (y X q l : ℕ) (f g : ℕ → ℝ) (hg0 : g 0 = 0) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * g (y / a) *
        liuPanAPPsiDiscrepancy (y / a) q (natInvMod q a * l % q)
    else 0) =
      ∑ k ∈ Icc 1 y, g k *
        (liuPanAggregateAPPsiDiscrepancy k
            (liuPanAbelSourceCutoff y X k) q l f -
          liuPanAggregateAPPsiDiscrepancy k
            (liuPanAbelSourceCutoff y X (k + 1)) q l f) := by
  simpa only [liuPanAggregateAPPsiDiscrepancy, mul_assoc, mul_left_comm,
    mul_comm, mul_ite, mul_zero] using
    (sum_source_eq_sum_quotient_shells y X g
      (fun k a => if a.Coprime q then
        f a * liuPanAPPsiDiscrepancy k q (natInvMod q a * l % q)
      else 0) hg0)

/-- The endpoint shell identity at the inverse-log weight. -/
theorem liuPanAggregateAPPsiDiscrepancy_inverseLog_endpoint_shell
    (y X q l : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (Real.log (y / a : ℕ))⁻¹ *
        liuPanAPPsiDiscrepancy (y / a) q (natInvMod q a * l % q)
    else 0) =
      ∑ k ∈ Icc 1 y, (Real.log (k : ℝ))⁻¹ *
        (liuPanAggregateAPPsiDiscrepancy k
            (liuPanAbelSourceCutoff y X k) q l f -
          liuPanAggregateAPPsiDiscrepancy k
            (liuPanAbelSourceCutoff y X (k + 1)) q l f) := by
  exact liuPanAggregateAPPsiDiscrepancy_endpoint_shell y X q l f
    (fun k => (Real.log (k : ℝ))⁻¹) (by simp)

/-- Exact prefix swap for the source-aggregated AP psi discrepancy. -/
theorem liuPanAggregateAPPsiDiscrepancy_prefix_swap
    (y X q l : ℕ) (f w : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), w n *
        liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q))
    else 0) =
      ∑ n ∈ range y, w n *
        liuPanAggregateAPPsiDiscrepancy n
          (liuPanAbelSourceCutoff y X (n + 1)) q l f := by
  calc
    _ = ∑ a ∈ Icc 1 X, ∑ n ∈ range (y / a), w n *
          (if a.Coprime q then
            f a * liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q)
          else 0) := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, Finset.mul_sum]
        apply sum_congr rfl
        intro n hn
        ring
      · simp [hcop]
    _ = ∑ n ∈ range y, w n *
          ∑ a ∈ Icc 1 (liuPanAbelSourceCutoff y X (n + 1)),
            (if a.Coprime q then
              f a * liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q)
            else 0) :=
      sum_source_prefix_eq_sum_aggregate_prefix y X w
        (fun n a => if a.Coprime q then
          f a * liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q)
        else 0)
    _ = _ := by rfl

/-- The exact prefix swap at the nonnegative Abel weights used above. -/
theorem liuPanAggregateAPPsiDiscrepancy_abel_prefix_swap
    (y X q l : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Icc 1 X, if a.Coprime q then
      f a * (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
        liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q))
    else 0) =
      ∑ n ∈ range y, liuPanInverseLogAbelWeight n *
        liuPanAggregateAPPsiDiscrepancy n
          (liuPanAbelSourceCutoff y X (n + 1)) q l f :=
  liuPanAggregateAPPsiDiscrepancy_prefix_swap y X q l f
    liuPanInverseLogAbelWeight

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

/-- Exact aggregate-before-absolute-value decomposition of the combined
inverse-log discrepancy.  It remains valid for moduli `0` and `1`. -/
theorem liuPanCombinedInverseLogDiscrepancy_eq_aggregateAbel
    (kappa : ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogDiscrepancy
        (liuLogarithmicIntegral kappa) y X q l f u v =
      |liuPanAggregateInverseLogPsiTerm y X q l f +
        liuPanAggregateInverseLogDeterministicTerm kappa y X q f /
          Nat.totient q| := by
  rw [liuPanCombinedInverseLogDiscrepancy_eq]
  congr 1
  calc
    _ = ∑ a ∈ Icc 1 X, if a.Coprime q then f a *
          ((Real.log (y / a : ℕ))⁻¹ *
              liuPanAPPsiDiscrepancy (y / a) q
                (natInvMod q a * l % q) +
            (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
              liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q)) +
            (liuPanDiscreteInverseLogMain (y / a) -
              liuLogarithmicIntegral kappa ((y : ℝ) / a)) /
                Nat.totient q)
        else 0 := by
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop]
        rw [apLogVonMangoldt_sub_liuLogarithmicIntegral_eq_discreteAbel]
      · simp [hcop]
    _ = (∑ a ∈ Icc 1 X, if a.Coprime q then f a *
            (Real.log (y / a : ℕ))⁻¹ *
              liuPanAPPsiDiscrepancy (y / a) q
                (natInvMod q a * l % q)
          else 0) +
        (∑ a ∈ Icc 1 X, if a.Coprime q then f a *
            (∑ n ∈ range (y / a), liuPanInverseLogAbelWeight n *
              liuPanAPPsiDiscrepancy n q (natInvMod q a * l % q))
          else 0) +
        (∑ a ∈ Icc 1 X, if a.Coprime q then f a *
            (liuPanDiscreteInverseLogMain (y / a) -
              liuLogarithmicIntegral kappa ((y : ℝ) / a))
          else 0) / Nat.totient q := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      apply sum_congr rfl
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop]
        ring
      · simp [hcop]
    _ = _ := by
      rw [liuPanAggregateAPPsiDiscrepancy_inverseLog_endpoint_shell,
        liuPanAggregateAPPsiDiscrepancy_abel_prefix_swap]
      rfl

/-- The pointwise aggregate bound keeps the only analytic absolute value outside
the full source convolution and separates the deterministic error. -/
theorem liuPanCombinedInverseLogDiscrepancy_le_aggregateAbel
    (kappa : ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogDiscrepancy
        (liuLogarithmicIntegral kappa) y X q l f u v ≤
      |liuPanAggregateInverseLogPsiTerm y X q l f| +
        |liuPanAggregateInverseLogDeterministicTerm kappa y X q f| /
          Nat.totient q := by
  rw [liuPanCombinedInverseLogDiscrepancy_eq_aggregateAbel]
  calc
    _ ≤ |liuPanAggregateInverseLogPsiTerm y X q l f| +
        |liuPanAggregateInverseLogDeterministicTerm kappa y X q f /
          Nat.totient q| :=
      abs_add_le _ _
    _ = _ := by
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.totient q)]

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
  unfold liuPanAggregateInverseLogPsiMaxY
  apply le_antisymm
  · apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · apply le_max'
    exact mem_image.mpr ⟨0, by simp, by simp⟩

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
  unfold liuPanAggregateInverseLogDeterministicMaxY
  apply le_antisymm
  · apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · apply le_max'
    exact mem_image.mpr ⟨0, by simp, by simp⟩

@[simp] theorem liuPanAggregateInverseLogDeterministicMaxY_one
    (kappa : ℝ) (X x : ℕ) (f : ℕ → ℝ) :
    liuPanAggregateInverseLogDeterministicMaxY kappa X 1 x f =
      ((range (x + 1)).image (fun y =>
        |liuPanAggregateInverseLogDeterministicTerm kappa y X 1 f|)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanAggregateInverseLogDeterministicMaxY
  simp only [liuPanAggregateInverseLogDeterministicMaxL_one]

/-- The pointwise aggregate bound lifted through the canonical residue maximum. -/
theorem liuPanCombinedInverseLogMaxL_le_aggregateAbel
    (kappa : ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL
        (liuLogarithmicIntegral kappa) y X q f u v ≤
      liuPanAggregateInverseLogPsiMaxL y X q f +
        liuPanAggregateInverseLogDeterministicMaxL kappa y X q f /
          Nat.totient q := by
  unfold liuPanCombinedInverseLogMaxL
    liuPanAggregateInverseLogPsiMaxL
    liuPanAggregateInverseLogDeterministicMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS, if_pos hS]
    apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨l, hl, rfl⟩
    exact
      (liuPanCombinedInverseLogDiscrepancy_le_aggregateAbel
        kappa y X q l f u v).trans
        (add_le_add
          (le_max'
            ((unitResidues q).image (fun r =>
              |liuPanAggregateInverseLogPsiTerm y X q r f|))
            |liuPanAggregateInverseLogPsiTerm y X q l f|
            (mem_image.mpr ⟨l, hl, rfl⟩))
          le_rfl)
  · simp [hS]

/-- The aggregate bound lifted through the canonical `y` maximum, without
introducing any sourcewise triangle inequality. -/
theorem liuPanCombinedInverseLogMaxY_le_aggregateAbel
    (kappa : ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxY
        (liuLogarithmicIntegral kappa) X q x f u v ≤
      liuPanAggregateInverseLogPsiMaxY X q x f +
        liuPanAggregateInverseLogDeterministicMaxY kappa X q x f /
          Nat.totient q := by
  unfold liuPanCombinedInverseLogMaxY
    liuPanAggregateInverseLogPsiMaxY
    liuPanAggregateInverseLogDeterministicMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  calc
    liuPanCombinedInverseLogMaxL
        (liuLogarithmicIntegral kappa) y X q f u v ≤
      liuPanAggregateInverseLogPsiMaxL y X q f +
        liuPanAggregateInverseLogDeterministicMaxL kappa y X q f /
          Nat.totient q :=
      liuPanCombinedInverseLogMaxL_le_aggregateAbel
        kappa y X q f u v
    _ ≤ ((range (x + 1)).image (fun t =>
            liuPanAggregateInverseLogPsiMaxL t X q f)).max'
            (Finset.image_nonempty.mpr ⟨0, by simp⟩) +
          ((range (x + 1)).image (fun t =>
            liuPanAggregateInverseLogDeterministicMaxL kappa t X q f)).max'
              (Finset.image_nonempty.mpr ⟨0, by simp⟩) /
            Nat.totient q := by
      apply add_le_add
      · apply le_max'
        exact mem_image.mpr ⟨y, hy, rfl⟩
      · apply div_le_div_of_nonneg_right
        · apply le_max'
          exact mem_image.mpr ⟨y, hy, rfl⟩
        · positivity

/-! ## Aggregate fixed-source and source-family bounds -/

/-- The modulus-weighted aggregate psi average at a fixed source. -/
noncomputable def liuMainPanAggregateInverseLogPsiAverage
    (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanAggregateInverseLogPsiMaxY N q N f

/-- The separately visible modulus-weighted deterministic average. -/
noncomputable def liuMainPanAggregateInverseLogDeterministicAverage
    (kappa : ℝ) (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      (liuPanAggregateInverseLogDeterministicMaxY kappa N q N f /
        Nat.totient q)

/-- Fixed-`N` aggregate psi estimate, with the absolute value only after the
source aggregation. -/
def LiuMainPanAggregateInverseLogPsiBoundAt
    (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) : Prop :=
  liuMainPanAggregateInverseLogPsiAverage N f B ≤
    C * N / Real.log N ^ A

/-- Fixed-`N` deterministic source-error estimate. -/
def LiuMainPanAggregateInverseLogDeterministicBoundAt
    (kappa : ℝ) (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) : Prop :=
  liuMainPanAggregateInverseLogDeterministicAverage kappa N f B ≤
    C * N / Real.log N ^ A

/-- The corrected aggregate source-family input.  Its psi and deterministic
components have separate constants and separate displayed bounds, while the
source `f_N` is specialized inside the universal quantifier over `N`. -/
def LiuMainPanAggregateInverseLogSourceFamilyBound (kappa : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A →
    ∃ Cpsi : ℝ, 0 < Cpsi ∧ ∃ Cdet : ℝ, 0 < Cdet ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      LiuMainPanAggregateInverseLogPsiBoundAt N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cpsi ∧
        LiuMainPanAggregateInverseLogDeterministicBoundAt kappa N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B Cdet

/-- The exact combined average is bounded by the aggregate psi average plus the
separate deterministic average. -/
theorem liuMainPanCombinedInverseLogAverage_le_aggregateAbel
    (kappa : ℝ) (N : ℕ) (B : ℝ) (u v : ℕ) :
    liuMainPanCombinedInverseLogAverage kappa N B u v ≤
      liuMainPanAggregateInverseLogPsiAverage N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
        liuMainPanAggregateInverseLogDeterministicAverage kappa N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B := by
  unfold liuMainPanCombinedInverseLogAverage
    liuMainPanAggregateInverseLogPsiAverage
    liuMainPanAggregateInverseLogDeterministicAverage
  rw [← Finset.sum_add_distrib]
  apply sum_le_sum
  intro q hq
  convert mul_le_mul_of_nonneg_left
      (liuPanCombinedInverseLogMaxY_le_aggregateAbel
        kappa N q N
          (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v)
      (panTypeI_weight_nonneg q) using 1
  all_goals ring

/-- The corrected aggregate psi hypothesis together with its separately
bounded deterministic component implies the combined inverse-log family
bound.  This theorem does not assert either analytic input. -/
theorem LiuMainPanAggregateInverseLogSourceFamilyBound.to_combinedInverseLog
    {kappa : ℝ} (hagg : LiuMainPanAggregateInverseLogSourceFamilyBound kappa)
    (u v : ℕ) :
    LiuMainPanCombinedInverseLogSourceFamilyBound kappa u v := by
  intro A hA
  rcases hagg A hA with
    ⟨Cpsi, hCpsi, Cdet, hCdet, B, hB, N0, hN⟩
  refine ⟨Cpsi + Cdet, add_pos hCpsi hCdet, B, hB, N0, ?_⟩
  intro N hN0
  have hbounds := hN N hN0
  unfold LiuMainPanAggregateInverseLogPsiBoundAt
    LiuMainPanAggregateInverseLogDeterministicBoundAt at hbounds
  unfold LiuMainPanCombinedInverseLogBoundAt
  calc
    liuMainPanCombinedInverseLogAverage kappa N B u v ≤
        liuMainPanAggregateInverseLogPsiAverage N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B +
          liuMainPanAggregateInverseLogDeterministicAverage kappa N
            (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B :=
      liuMainPanCombinedInverseLogAverage_le_aggregateAbel
        kappa N B u v
    _ ≤ Cpsi * N / Real.log N ^ A + Cdet * N / Real.log N ^ A :=
      add_le_add hbounds.1 hbounds.2
    _ = (Cpsi + Cdet) * N / Real.log N ^ A := by ring

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

theorem liuPanPsiAbelMajorant_nonneg
    (kappa : ℝ) (y : ℕ) (x : ℝ) (q l : ℕ) :
    0 ≤ liuPanPsiAbelMajorant kappa y x q l := by
  unfold liuPanPsiAbelMajorant
  exact add_nonneg
    (add_nonneg
      (div_nonneg (abs_nonneg _) (natCast_log_nonneg y))
      (sum_nonneg fun n _ =>
        mul_nonneg (liuPanInverseLogAbelWeight_nonneg n) (abs_nonneg _)))
    (div_nonneg (abs_nonneg _) (by positivity))

/-- Pointwise inverse-log discrepancy bound obtained from the exact Abel
identity, with no distribution estimate assumed. -/
theorem abs_apLogVonMangoldt_sub_liuLogarithmicIntegral_le_psiAbelMajorant
    (kappa : ℝ) (y : ℕ) (x : ℝ) (q l : ℕ) :
    |apLogVonMangoldt y q l -
        liuLogarithmicIntegral kappa x / Nat.totient q| ≤
      liuPanPsiAbelMajorant kappa y x q l := by
  rw [apLogVonMangoldt_sub_liuLogarithmicIntegral_eq_discreteAbel]
  have hend :
      |(Real.log (y : ℝ))⁻¹ * liuPanAPPsiDiscrepancy y q l| =
        |liuPanAPPsiDiscrepancy y q l| / Real.log (y : ℝ) := by
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (natCast_log_nonneg y))]
    ring
  have hsum :
      |∑ n ∈ range y,
          liuPanInverseLogAbelWeight n *
            liuPanAPPsiDiscrepancy n q l| ≤
        ∑ n ∈ range y,
          liuPanInverseLogAbelWeight n *
            |liuPanAPPsiDiscrepancy n q l| := by
    calc
      _ ≤ ∑ n ∈ range y,
          |liuPanInverseLogAbelWeight n *
            liuPanAPPsiDiscrepancy n q l| :=
        abs_sum_le_sum_abs _ _
      _ = _ := by
        apply sum_congr rfl
        intro n hn
        rw [abs_mul,
          abs_of_nonneg (liuPanInverseLogAbelWeight_nonneg n)]
  have htotient : 0 ≤ (Nat.totient q : ℝ) := by positivity
  have hdet :
      |(liuPanDiscreteInverseLogMain y -
          liuLogarithmicIntegral kappa x) / Nat.totient q| =
        |liuPanDiscreteInverseLogMain y -
          liuLogarithmicIntegral kappa x| / Nat.totient q := by
    rw [abs_div, abs_of_nonneg htotient]
  unfold liuPanPsiAbelMajorant
  calc
    _ ≤
        |(Real.log (y : ℝ))⁻¹ * liuPanAPPsiDiscrepancy y q l +
          ∑ n ∈ range y,
            liuPanInverseLogAbelWeight n *
              liuPanAPPsiDiscrepancy n q l| +
        |(liuPanDiscreteInverseLogMain y -
          liuLogarithmicIntegral kappa x) / Nat.totient q| :=
      abs_add_le _ _
    _ ≤
        (|(Real.log (y : ℝ))⁻¹ * liuPanAPPsiDiscrepancy y q l| +
          |∑ n ∈ range y,
            liuPanInverseLogAbelWeight n *
              liuPanAPPsiDiscrepancy n q l|) +
        |(liuPanDiscreteInverseLogMain y -
          liuLogarithmicIntegral kappa x) / Nat.totient q| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ _ := by
      rw [hend, hdet]
      exact add_le_add (add_le_add le_rfl hsum) le_rfl

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

theorem liuPanSourceWeightedPsiAbelMajorant_nonneg
    (kappa : ℝ) (y X q l : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuPanSourceWeightedPsiAbelMajorant kappa y X q l f := by
  unfold liuPanSourceWeightedPsiAbelMajorant
  apply sum_nonneg
  intro a ha
  split_ifs
  · exact mul_nonneg (abs_nonneg _)
      (liuPanPsiAbelMajorant_nonneg _ _ _ _ _)
  · exact le_rfl

/-- The exact combined discrepancy is bounded by the diagnostic sourcewise
majorant.  This valid inequality is analytically too costly in the
empty-progression tail. -/
theorem liuPanCombinedInverseLogDiscrepancy_le_sourceWeightedPsiAbelMajorant
    (kappa : ℝ) (y X q l : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogDiscrepancy
        (liuLogarithmicIntegral kappa) y X q l f u v ≤
      liuPanSourceWeightedPsiAbelMajorant kappa y X q l f := by
  rw [liuPanCombinedInverseLogDiscrepancy_eq]
  unfold liuPanSourceWeightedPsiAbelMajorant
  calc
    |∑ a ∈ Icc 1 X, if a.Coprime q then
        f a * (apLogVonMangoldt (y / a) q
            (natInvMod q a * l % q) -
          liuLogarithmicIntegral kappa ((y : ℝ) / a) /
            Nat.totient q)
      else 0| ≤
        ∑ a ∈ Icc 1 X, |if a.Coprime q then
          f a * (apLogVonMangoldt (y / a) q
              (natInvMod q a * l % q) -
            liuLogarithmicIntegral kappa ((y : ℝ) / a) /
              Nat.totient q)
        else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply sum_le_sum
      intro a ha
      by_cases hcop : a.Coprime q
      · simp only [if_pos hcop, abs_mul]
        exact mul_le_mul_of_nonneg_left
          (abs_apLogVonMangoldt_sub_liuLogarithmicIntegral_le_psiAbelMajorant
            kappa (y / a) ((y : ℝ) / a) q
              (natInvMod q a * l % q))
          (abs_nonneg (f a))
      · simp [hcop]

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
  unfold liuPanSourceWeightedPsiAbelMaxY
  apply le_antisymm
  · apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨y, hy, rfl⟩
    simp
  · apply le_max'
    exact mem_image.mpr ⟨0, by simp, by simp⟩

theorem liuPanSourceWeightedPsiAbelMaxY_one
    (kappa : ℝ) (X x : ℕ) (f : ℕ → ℝ) :
    liuPanSourceWeightedPsiAbelMaxY kappa X 1 x f =
      ((range (x + 1)).image (fun y =>
        liuPanSourceWeightedPsiAbelMajorant kappa y X 1 0 f)).max'
          (Finset.image_nonempty.mpr ⟨0, by simp⟩) := by
  unfold liuPanSourceWeightedPsiAbelMaxY
  simp only [liuPanSourceWeightedPsiAbelMaxL_one]

theorem liuPanCombinedInverseLogMaxL_le_sourceWeightedPsiAbelMaxL
    (kappa : ℝ) (y X q : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxL
        (liuLogarithmicIntegral kappa) y X q f u v ≤
      liuPanSourceWeightedPsiAbelMaxL kappa y X q f := by
  unfold liuPanCombinedInverseLogMaxL
    liuPanSourceWeightedPsiAbelMaxL
  dsimp only
  by_cases hS : (unitResidues q).Nonempty
  · simp only [dif_pos hS]
    apply max'_le
    intro z hz
    rcases mem_image.mp hz with ⟨l, hl, rfl⟩
    exact
      (liuPanCombinedInverseLogDiscrepancy_le_sourceWeightedPsiAbelMajorant
        kappa y X q l f u v).trans
        (le_max'
          ((unitResidues q).image (fun r =>
            liuPanSourceWeightedPsiAbelMajorant kappa y X q r f))
          (liuPanSourceWeightedPsiAbelMajorant kappa y X q l f)
          (mem_image.mpr ⟨l, hl, rfl⟩))
  · simp [hS]

theorem liuPanCombinedInverseLogMaxY_le_sourceWeightedPsiAbelMaxY
    (kappa : ℝ) (X q x : ℕ) (f : ℕ → ℝ) (u v : ℕ) :
    liuPanCombinedInverseLogMaxY
        (liuLogarithmicIntegral kappa) X q x f u v ≤
      liuPanSourceWeightedPsiAbelMaxY kappa X q x f := by
  unfold liuPanCombinedInverseLogMaxY
    liuPanSourceWeightedPsiAbelMaxY
  apply max'_le
  intro z hz
  rcases mem_image.mp hz with ⟨y, hy, rfl⟩
  exact
    (liuPanCombinedInverseLogMaxL_le_sourceWeightedPsiAbelMaxL
      kappa y X q f u v).trans
      (le_max'
        ((range (x + 1)).image (fun t =>
          liuPanSourceWeightedPsiAbelMaxL kappa t X q f))
        (liuPanSourceWeightedPsiAbelMaxL kappa y X q f)
        (mem_image.mpr ⟨y, hy, rfl⟩))

/-! ## Overstrong diagnostic source-family predicate -/

/-- The source-weighted maximal psi functional averaged over Pan moduli. -/
noncomputable def liuMainPanPsiAbelAverage
    (kappa : ℝ) (N : ℕ) (f : ℕ → ℝ) (B : ℝ) : ℝ :=
  ∑ q ∈ range (panModulusCutoff N B + 1),
    (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2) *
      (3 : ℝ) ^ q.primeFactors.card *
      liuPanSourceWeightedPsiAbelMaxY kappa N q N f

/-- A fixed-`N`, fixed-source estimate for the overstrong sourcewise
functional. -/
def LiuMainPanPsiAbelBoundAt
    (kappa : ℝ) (N : ℕ) (f : ℕ → ℝ) (A B C : ℝ) : Prop :=
  liuMainPanPsiAbelAverage kappa N f B ≤
    C * N / Real.log N ^ A

/-- An intentionally retained overstrong diagnostic, not the remaining analytic
input.  For `q > y / a`, the empty-progression contribution survives the
sourcewise absolute value; averaged over reduced residues this prevents the
claimed arbitrary logarithmic saving.  The source weight `f_N` is nevertheless
quantified correctly inside `∀ N`, so finite consequences remain reusable. -/
def LiuMainPanPsiAbelSourceFamilyBound (kappa : ℝ) : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N →
      LiuMainPanPsiAbelBoundAt kappa N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) A B C

/-- The overstrong diagnostic functional dominates the combined inverse-log
average for every fixed `N`. -/
theorem liuMainPanCombinedInverseLogAverage_le_psiAbelAverage
    (kappa : ℝ) (N : ℕ) (B : ℝ) (u v : ℕ) :
    liuMainPanCombinedInverseLogAverage kappa N B u v ≤
      liuMainPanPsiAbelAverage kappa N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) B := by
  unfold liuMainPanCombinedInverseLogAverage
    liuMainPanPsiAbelAverage
  apply sum_le_sum
  intro q hq
  exact mul_le_mul_of_nonneg_left
    (liuPanCombinedInverseLogMaxY_le_sourceWeightedPsiAbelMaxY
      kappa N q N
        (liuWeight N (liuSourceZ10 N) (liuSourceY3 N)) u v)
    (panTypeI_weight_nonneg q)

/-- The overstrong diagnostic predicate has the stated finite implication.  It
is not proposed as the analytic Bombieri--Vinogradov frontier. -/
theorem LiuMainPanPsiAbelSourceFamilyBound.to_combinedInverseLog
    {kappa : ℝ} (hpsi : LiuMainPanPsiAbelSourceFamilyBound kappa)
    (u v : ℕ) :
    LiuMainPanCombinedInverseLogSourceFamilyBound kappa u v := by
  intro A hA
  rcases hpsi A hA with ⟨C, hC, B, hB, N0, hN⟩
  refine ⟨C, hC, B, hB, N0, ?_⟩
  intro N hN0
  exact
    (liuMainPanCombinedInverseLogAverage_le_psiAbelAverage
      kappa N B u v).trans (hN N hN0)

end MathlibNt.SieveTheory.LiuWeight
