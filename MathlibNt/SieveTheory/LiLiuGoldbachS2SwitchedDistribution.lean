import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Nat
import MathlibNt.SieveTheory.LiLiuGoldbachS2SwitchedCarrier
import MathlibNt.SieveTheory.LiuPanWangDingSource
import MathlibNt.SieveTheory.LiuTrueLiPan
import MathlibNt.SieveTheory.LiLiuGoldbachS2SieveGate
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate

open scoped BigOperators

open Finset
open Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

set_option autoImplicit false

noncomputable local instance instDecidableGoldbachS2SwitchedDistribution (P : Prop) :
    Decidable P :=
  Classical.propDecidable P

/-- The bounded coefficient selecting the actual `S2` large-prime source. -/
noncomputable def goldbachS2SwitchedCoeff (N : ℕ) (T : ℝ) (r : ℕ) : ℝ :=
  if r ∈ goldbachS2Primes N T then 1 else 0

theorem goldbachS2SwitchedCoeff_eq_one_of_mem
    {N r : ℕ} {T : ℝ}
    (hr : r ∈ goldbachS2Primes N T) :
    goldbachS2SwitchedCoeff N T r = 1 := by
  simp [goldbachS2SwitchedCoeff, hr]

theorem goldbachS2SwitchedCoeff_eq_zero_of_not_mem
    {N r : ℕ} {T : ℝ}
    (hr : r ∉ goldbachS2Primes N T) :
    goldbachS2SwitchedCoeff N T r = 0 := by
  simp [goldbachS2SwitchedCoeff, hr]

theorem abs_goldbachS2SwitchedCoeff_le_one
    (N : ℕ) (T : ℝ) (r : ℕ) :
    |goldbachS2SwitchedCoeff N T r| ≤ 1 := by
  by_cases hr : r ∈ goldbachS2Primes N T
  · simp [goldbachS2SwitchedCoeff, hr]
  · simp [goldbachS2SwitchedCoeff, hr]

/-- The gated switched mass at modulus `d`. -/
noncomputable def goldbachS2SwitchedGatedMainMass
    (N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  ∑ r ∈ goldbachS2Primes N T,
    if Nat.Coprime r d then
      liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / r)
    else 0

/-- The actual switched remainder at modulus `d`, with the coprimality gate
retained in the main term. -/
noncomputable def goldbachS2SwitchedRemainder
    (N : ℕ) (T : ℝ) (d : ℕ) : ℝ :=
  (goldbachS2SwitchedDivCount N T d : ℝ) -
    goldbachS2SwitchedGatedMainMass N T d / Nat.totient d

/-- The Pan counting prefix attached to the bounded large-prime coefficient. -/
noncomputable def goldbachS2SwitchedPanAPPrefixCount
    (N Y A₁ A₂ d l : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ Ioc A₁ A₂,
    if Nat.Coprime r d then
      goldbachS2SwitchedCoeff N T r * (primesInAPBelow Y r d l : ℝ)
    else 0

/-- The corresponding Pan main prefix. -/
noncomputable def goldbachS2SwitchedPanMainPrefix
    (N Y A₁ A₂ d : ℕ) (T : ℝ) : ℝ :=
  ∑ r ∈ Ioc A₁ A₂,
    if Nat.Coprime r d then
      goldbachS2SwitchedCoeff N T r *
        (liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / r) / Nat.totient d)
    else 0

private theorem S2Switched_prod_eq_N_impossible
    {N r q : ℕ} {T : ℝ}
    (hr : r ∈ goldbachS2Primes N T) :
    r * q ≠ N := by
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, hrCop, _, _⟩
  intro hEq
  have hrN : r ∣ N := ⟨q, hEq.symm⟩
  exact (hrPrime.coprime_iff_not_dvd.mp hrCop) hrN

private noncomputable def S2SwitchedAPPrefix
    (N Y r d l : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun q => q.Prime ∧ r * q ≤ Y ∧ Nat.ModEq d (r * q) l

private theorem S2Switched_primesInAPBelow_eq_card
    {N Y r d l : ℕ}
    (hr1 : 1 ≤ r) (hY : Y ≤ N) :
    primesInAPBelow Y r d l = (S2SwitchedAPPrefix N Y r d l).card := by
  unfold primesInAPBelow S2SwitchedAPPrefix
  apply congrArg Finset.card
  ext q
  simp only [mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hqY, hqPrime, hrqY, hmod⟩
    exact ⟨hqY.trans hY, hqPrime, hrqY, hmod⟩
  · rintro ⟨hqN, hqPrime, hrqY, hmod⟩
    have hqY : q ≤ Y := by
      calc
        q ≤ r * q := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hr1
        _ ≤ Y := hrqY
    exact ⟨hqY, hqPrime, hrqY, hmod⟩

private theorem S2Switched_residue_eq_iff_modEq
    {N d r q : ℕ}
    (hrd : Nat.Coprime r d) :
    (q : ZMod d) = (N : ZMod d) * (r : ZMod d)⁻¹ ↔ Nat.ModEq d (r * q) N := by
  constructor
  · intro hq
    have hzmul :
        ((r : ZMod d) * (q : ZMod d)) = (N : ZMod d) := by
      calc
        ((r : ZMod d) * (q : ZMod d))
            = (r : ZMod d) * ((N : ZMod d) * (r : ZMod d)⁻¹) := by rw [hq]
        _ = (N : ZMod d) * ((r : ZMod d) * (r : ZMod d)⁻¹) := by ac_rfl
        _ = (N : ZMod d) * 1 := by rw [ZMod.coe_mul_inv_eq_one r hrd]
        _ = (N : ZMod d) := by simp
    have hzprod : (((r * q : ℕ) : ZMod d)) = (N : ZMod d) := by
      simpa using hzmul
    exact (ZMod.natCast_eq_natCast_iff (r * q) N d).1 hzprod
  · intro hrq
    have hzprod : (((r * q : ℕ) : ZMod d)) = (N : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff (r * q) N d).2 hrq
    have hzmul : ((r : ZMod d) * (q : ZMod d)) = (N : ZMod d) := by
      simpa using hzprod
    calc
      (q : ZMod d) = (1 : ZMod d) * (q : ZMod d) := by simp
      _ = (((r : ZMod d) * (r : ZMod d)⁻¹) * (q : ZMod d)) := by
            rw [← ZMod.coe_mul_inv_eq_one r hrd]
      _ = (r : ZMod d)⁻¹ * ((r : ZMod d) * (q : ZMod d)) := by ac_rfl
      _ = (r : ZMod d)⁻¹ * (N : ZMod d) := by rw [hzmul]
      _ = (N : ZMod d) * (r : ZMod d)⁻¹ := by simp [mul_comm]

private theorem S2Switched_residue_eq_iff_modEq_residue
    {N d r q : ℕ}
    (hrd : Nat.Coprime r d) :
    (q : ZMod d) = (N : ZMod d) * (r : ZMod d)⁻¹ ↔ Nat.ModEq d (r * q) (N % d) := by
  rw [S2Switched_residue_eq_iff_modEq hrd]
  constructor
  · intro hq
    exact hq.trans (Nat.mod_modEq N d).symm
  · intro hq
    exact hq.trans (Nat.mod_modEq N d)

private noncomputable def S2SwitchedDivisorQFiber
    (N d r : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun q => q.Prime ∧ r * q < N ∧ d ∣ N - r * q

private theorem S2SwitchedDivisorQFiber_eq_prefix
    {N d r : ℕ} {T : ℝ}
    (hd : 1 ≤ d)
    (hr : r ∈ goldbachS2Primes N T) :
    S2SwitchedDivisorQFiber N d r =
      S2SwitchedAPPrefix N N r d (N % d) := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime, hrqLt, hdiv⟩
    have hx : (Sigma.mk r q : Sigma fun _r : ℕ => ℕ) ∈ goldbachS2SwitchedLabels N T :=
      mem_goldbachS2SwitchedLabels_iff.mpr ⟨hr, hqPrime, hrqLt⟩
    have hmod : Nat.ModEq d (r * q) N :=
      (goldbachS2SwitchedAtom_output_dvd_iff_modEq (d := d) (x := Sigma.mk r q)
        hd hx).mp hdiv
    exact Finset.mem_filter.mpr
      ⟨hqRange, hqPrime, hrqLt.le, hmod.trans (Nat.mod_modEq N d).symm⟩
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime, hrqLe, hmod⟩
    have hrqLt : r * q < N :=
      lt_of_le_of_ne hrqLe (S2Switched_prod_eq_N_impossible (q := q) hr)
    have hx : (Sigma.mk r q : Sigma fun _r : ℕ => ℕ) ∈ goldbachS2SwitchedLabels N T :=
      mem_goldbachS2SwitchedLabels_iff.mpr ⟨hr, hqPrime, hrqLt⟩
    have hmodN : Nat.ModEq d (r * q) N := hmod.trans (Nat.mod_modEq N d)
    exact Finset.mem_filter.mpr
      ⟨hqRange, hqPrime, hrqLt,
        (goldbachS2SwitchedAtom_output_dvd_iff_modEq (d := d) (x := Sigma.mk r q)
          hd hx).mpr hmodN⟩

private theorem S2SwitchedDivisorQFiber_card_eq
    {N d r : ℕ} {T : ℝ}
    (hd : 1 ≤ d)
    (hr : r ∈ goldbachS2Primes N T)
    (_hdN : Nat.Coprime d N) :
    ((S2SwitchedDivisorQFiber N d r).card : ℝ) =
      if Nat.Coprime r d then (primesInAPBelow N r d (N % d) : ℝ) else 0 := by
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, hrCopN, _, _⟩
  by_cases hrd : Nat.Coprime r d
  · rw [if_pos hrd, S2SwitchedDivisorQFiber_eq_prefix hd hr]
    norm_num
    rw [← S2Switched_primesInAPBelow_eq_card hrPrime.one_le le_rfl]
  · have hempty : S2SwitchedDivisorQFiber N d r = ∅ := by
      ext q
      constructor
      · intro hq
        rcases Finset.mem_filter.mp hq with ⟨_, _, hlt, hdiv⟩
        have hrdvd : r ∣ d := by
          by_contra hnot
          exact hrd ((hrPrime.coprime_iff_not_dvd).2 hnot)
        have hrdout : r ∣ N - r * q := dvd_trans hrdvd hdiv
        have hrN : r ∣ N := by
          have hrProd : r ∣ r * q := dvd_mul_of_dvd_left (dvd_refl r) q
          have hsum : r ∣ r * q + (N - r * q) := Nat.dvd_add hrProd hrdout
          simpa [Nat.add_sub_of_le hlt.le] using hsum
        exact False.elim ((hrPrime.coprime_iff_not_dvd.mp hrCopN) hrN)
      · intro hq
        cases hq
    rw [if_neg hrd, hempty]
    simp

private theorem S2Switched_panAPPrefixCount_eq_support_sum
    {N Y A₁ A₂ d l : ℕ} {T : ℝ}
    (hsupp : ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂) :
    goldbachS2SwitchedPanAPPrefixCount N Y A₁ A₂ d l T =
      ∑ r ∈ goldbachS2Primes N T,
        if Nat.Coprime r d then (primesInAPBelow Y r d l : ℝ) else 0 := by
  unfold goldbachS2SwitchedPanAPPrefixCount
  have hsub : goldbachS2Primes N T ⊆ Ioc A₁ A₂ := fun _ hr => hsupp hr
  calc
    _ = ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then
            goldbachS2SwitchedCoeff N T r * (primesInAPBelow Y r d l : ℝ)
          else 0 := by
            symm
            apply Finset.sum_subset hsub
            intro r hrIoc hrNot
            have hcoeff0 : goldbachS2SwitchedCoeff N T r = 0 := by
              by_cases hr : r ∈ goldbachS2Primes N T
              · exact False.elim (hrNot hr)
              · simp [goldbachS2SwitchedCoeff, hr]
            simp [hcoeff0]
    _ = ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then (primesInAPBelow Y r d l : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : Nat.Coprime r d
            · rw [if_pos hrd, if_pos hrd]
              simp [goldbachS2SwitchedCoeff_eq_one_of_mem hr]
            · simp [hrd]

private theorem S2Switched_panMainPrefix_eq_support_sum
    {N Y A₁ A₂ d : ℕ} {T : ℝ}
    (hsupp : ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂) :
    goldbachS2SwitchedPanMainPrefix N Y A₁ A₂ d T =
      ∑ r ∈ goldbachS2Primes N T,
        if Nat.Coprime r d then
          liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / r) / Nat.totient d
        else 0 := by
  unfold goldbachS2SwitchedPanMainPrefix
  have hsub : goldbachS2Primes N T ⊆ Ioc A₁ A₂ := fun _ hr => hsupp hr
  calc
    _ = ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then
            goldbachS2SwitchedCoeff N T r *
              (liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / r) / Nat.totient d)
          else 0 := by
            symm
            apply Finset.sum_subset hsub
            intro r hrIoc hrNot
            have hcoeff0 : goldbachS2SwitchedCoeff N T r = 0 := by
              by_cases hr : r ∈ goldbachS2Primes N T
              · exact False.elim (hrNot hr)
              · simp [goldbachS2SwitchedCoeff, hr]
            simp [hcoeff0]
    _ = ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then
            liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / r) / Nat.totient d
          else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : Nat.Coprime r d
            · rw [if_pos hrd, if_pos hrd]
              simp [goldbachS2SwitchedCoeff_eq_one_of_mem hr]
            · simp [hrd]

theorem goldbachS2SwitchedDivCount_eq_panAPPrefixCount
    {N d A₁ A₂ : ℕ} {T : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hsupp : ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂) :
    (goldbachS2SwitchedDivCount N T d : ℝ) =
      goldbachS2SwitchedPanAPPrefixCount N N A₁ A₂ d (N % d) T := by
  have hsigma :
      goldbachS2SwitchedDivisorLabels N T d =
        (goldbachS2Primes N T).sigma fun r => S2SwitchedDivisorQFiber N d r := by
    ext x
    constructor
    · intro hx
      rcases mem_goldbachS2SwitchedDivisorLabels_iff.mp hx with ⟨hxS, hdiv⟩
      rcases mem_goldbachS2SwitchedLabels_iff.mp hxS with ⟨hr, hqPrime, hlt⟩
      rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _, _, _⟩
      have hqRange : x.2 ∈ range (N + 1) := by
        refine Finset.mem_range.mpr ?_
        apply Nat.lt_succ_of_le
        calc
          x.2 ≤ x.1 * x.2 := Nat.le_mul_of_pos_left _ hrPrime.pos
          _ ≤ N := hlt.le
      exact Finset.mem_sigma.mpr ⟨hr, by
        exact Finset.mem_filter.mpr ⟨hqRange, hqPrime, hlt, hdiv⟩⟩
    · intro hx
      rcases Finset.mem_sigma.mp hx with ⟨hr, hxq⟩
      rcases Finset.mem_filter.mp hxq with ⟨_, hqPrime, hlt, hdiv⟩
      exact mem_goldbachS2SwitchedDivisorLabels_iff.mpr
        ⟨mem_goldbachS2SwitchedLabels_iff.mpr ⟨hr, hqPrime, hlt⟩, hdiv⟩
  have hcount :
      goldbachS2SwitchedDivCount N T d =
        ∑ r ∈ goldbachS2Primes N T, (S2SwitchedDivisorQFiber N d r).card := by
    rw [goldbachS2SwitchedDivCount, hsigma, Finset.card_sigma]
  calc
    (goldbachS2SwitchedDivCount N T d : ℝ)
        = ∑ r ∈ goldbachS2Primes N T, ((S2SwitchedDivisorQFiber N d r).card : ℝ) := by
            exact_mod_cast hcount
    _ = ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then (primesInAPBelow N r d (N % d) : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            exact S2SwitchedDivisorQFiber_card_eq hd hr hdN
    _ = goldbachS2SwitchedPanAPPrefixCount N N A₁ A₂ d (N % d) T := by
          symm
          exact S2Switched_panAPPrefixCount_eq_support_sum hsupp

theorem goldbachS2SwitchedPanMainPrefix_eq_div_gatedMainMass
    {N A₁ A₂ d : ℕ} {T : ℝ}
    (hsupp : ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂) :
    goldbachS2SwitchedPanMainPrefix N N A₁ A₂ d T =
      goldbachS2SwitchedGatedMainMass N T d / Nat.totient d := by
  calc
    goldbachS2SwitchedPanMainPrefix N N A₁ A₂ d T =
        ∑ r ∈ goldbachS2Primes N T,
          if Nat.Coprime r d then
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / r) / Nat.totient d
          else 0 := S2Switched_panMainPrefix_eq_support_sum hsupp
    _ = ∑ r ∈ goldbachS2Primes N T,
          (if Nat.Coprime r d then
            liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / r)
          else 0) / Nat.totient d := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : Nat.Coprime r d
            · rw [if_pos hrd, if_pos hrd]
            · rw [if_neg hrd, if_neg hrd]
              simp
    _ = goldbachS2SwitchedGatedMainMass N T d / Nat.totient d := by
          rw [← Finset.sum_div, goldbachS2SwitchedGatedMainMass]

theorem liuMainPanCoprimeIntervalSum_eq_goldbachS2SwitchedPrefixCount_sub_mainPrefix
    (N Y A₁ A₂ d l : ℕ) (T : ℝ) :
    liuMainPanCoprimeIntervalSum
        (liuLogarithmicIntegral (2 / Real.log 2)) Y A₁ A₂ d l
        (goldbachS2SwitchedCoeff N T) =
      goldbachS2SwitchedPanAPPrefixCount N Y A₁ A₂ d l T -
        goldbachS2SwitchedPanMainPrefix N Y A₁ A₂ d T := by
  unfold liuMainPanCoprimeIntervalSum liuScaledAPError
    goldbachS2SwitchedPanAPPrefixCount goldbachS2SwitchedPanMainPrefix
  calc
    _ = ∑ r ∈ Ioc A₁ A₂,
          ((if Nat.Coprime r d then
              goldbachS2SwitchedCoeff N T r * (primesInAPBelow Y r d l : ℝ)
            else 0) -
            (if Nat.Coprime r d then
              goldbachS2SwitchedCoeff N T r *
                (liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / r) / Nat.totient d)
            else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro r hr
            by_cases hrd : Nat.Coprime r d
            · rw [if_pos hrd, if_pos hrd, if_pos hrd]
              ring
            · rw [if_neg hrd, if_neg hrd, if_neg hrd]
              ring
    _ = _ := by rw [Finset.sum_sub_distrib]

theorem goldbachS2SwitchedRemainder_eq_panError
    {N d A₁ A₂ : ℕ} {T : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hsupp : ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂) :
    goldbachS2SwitchedRemainder N T d =
      liuMainPanCoprimeIntervalSum
        (liuLogarithmicIntegral (2 / Real.log 2)) N A₁ A₂ d (N % d)
        (goldbachS2SwitchedCoeff N T) := by
  rw [liuMainPanCoprimeIntervalSum_eq_goldbachS2SwitchedPrefixCount_sub_mainPrefix]
  unfold goldbachS2SwitchedRemainder
  rw [goldbachS2SwitchedDivCount_eq_panAPPrefixCount hd hdN hsupp,
    goldbachS2SwitchedPanMainPrefix_eq_div_gatedMainMass hsupp]

private theorem S2Switched_intervalMaxL_nonneg
    (main : ℝ → ℝ) (Y A₁ A₂ d : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  by_cases hS : (unitResidues d).Nonempty
  · rw [dif_pos hS]
    have hmem :
        ((unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|)).max'
            (Finset.image_nonempty.mpr hS) ∈
          (unitResidues d).image
            (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|) :=
      Finset.max'_mem _ _
    rcases Finset.mem_image.mp hmem with ⟨l, _, hl⟩
    rw [← hl]
    exact abs_nonneg _
  · rw [dif_neg hS]

private theorem S2Switched_residue_mem_unitResidues
    {N d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    N % d ∈ unitResidues d := by
  rw [unitResidues]
  refine Finset.mem_filter.mpr ?_
  constructor
  · exact Finset.mem_range.mpr (Nat.mod_lt N (lt_of_lt_of_le Nat.zero_lt_one hd))
  · exact (ZMod.coprime_mod_iff_coprime N d).2 hdN.symm

private theorem S2Switched_abs_intervalSum_le_maxL
    {N Y A₁ A₂ d : ℕ} {main : ℝ → ℝ} {f : ℕ → ℝ}
    (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d (N % d) f| ≤
      liuMainPanCoprimeIntervalMaxL main Y A₁ A₂ d f := by
  have hl : N % d ∈ unitResidues d := S2Switched_residue_mem_unitResidues hd hdN
  have hS : (unitResidues d).Nonempty := ⟨N % d, hl⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  exact Finset.le_max'
    ((unitResidues d).image
      (fun l => |liuMainPanCoprimeIntervalSum main Y A₁ A₂ d l f|))
    _
    (Finset.mem_image.mpr ⟨N % d, hl, rfl⟩)

private theorem S2Switched_prime_support_mem_panInterval
    {N : ℕ} {B ε : ℝ}
    (hN : 2 ≤ N)
    (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N)
    (hεu : ε < (2 : ℝ) / 15)
    {r : ℕ}
    (hr : r ∈ goldbachS2Primes N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε))) :
    r ∈ Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  rcases Finset.mem_filter.mp hr with ⟨_, hrPrime, _hrCop, hrT, hrSqN⟩
  have hβ : (1 / 10 : ℝ) < (9 : ℝ) / 19 - ε := by
    nlinarith
  have hN1 : (1 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hN)
  have hpow : (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ ((9 : ℝ) / 19 - ε) := by
    exact Real.rpow_lt_rpow_of_exponent_lt hN1 hβ
  have hlowT : (liuPanSourceIntervalLower N B : ℝ) < (N : ℝ) ^ ((9 : ℝ) / 19 - ε) := by
    calc
      (liuPanSourceIntervalLower N B : ℝ) < liuSourceZ10 N := by exact_mod_cast hlow
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
            unfold liuSourceZ10
            exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ < (N : ℝ) ^ ((9 : ℝ) / 19 - ε) := hpow
  have hleft : liuPanSourceIntervalLower N B < r := by
    exact_mod_cast hlowT.trans_le hrT
  have hrSqR : (r : ℝ) ^ 2 ≤ N := by exact_mod_cast hrSqN
  have hrLeSqrt : (r : ℝ) ≤ Real.sqrt N := by
    by_contra hlt
    have hsqrtLt : Real.sqrt N < r := lt_of_not_ge hlt
    have hsqLt : N < (r : ℝ) ^ 2 := by
      have hNnonneg : (0 : ℝ) ≤ N := by positivity
      nlinarith [Real.sq_sqrt hNnonneg, Real.sqrt_nonneg (N : ℝ), hsqrtLt]
    exact not_lt_of_ge hrSqR hsqLt
  have hNbase : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hsqrtBound : Real.sqrt N ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hNbase (by norm_num : (1 / 2 : ℝ) ≤ 2 / 3)
  have hright : r ≤ liuPanSourceIntervalUpper N := by
    unfold liuPanSourceIntervalUpper
    apply Nat.le_floor
    exact hrLeSqrt.trans hsqrtBound
  exact Finset.mem_Ioc.mpr ⟨hleft, hright⟩

theorem goldbachS2SwitchedRemainder_log_saving
    (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < (2 : ℝ) / 15 →
      ∀ N : ℕ, N₀ ≤ N →
        let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachS2SwitchedRemainder N T d| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Nagg, hagg⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  obtain ⟨Nlow, hlow⟩ := eventually_atTop.mp
    (eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B)
  refine ⟨C, hC, B, hB, max 4 (max Nagg Nlow), le_max_left _ _, ?_⟩
  intro ε hε hεu N hN
  let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
  let A₁ := liuPanSourceIntervalLower N B
  let A₂ := liuPanSourceIntervalUpper N
  let S := (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N)
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hNagg : Nagg ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNlow : Nlow ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hsupp :
      ∀ ⦃r : ℕ⦄, r ∈ goldbachS2Primes N T → r ∈ Ioc A₁ A₂ := by
    intro r hr
    simpa [T, A₁, A₂] using
      S2Switched_prime_support_mem_panInterval (B := B) (ε := ε) hN2 (hlow N hNlow) hεu hr
  have hA₂ :
      (A₂ : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
    unfold A₂ liuPanSourceIntervalUpper
    exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  have hA₁ :
      Real.log (N : ℝ) ^ (2 * B) ≤ A₁ := by
    exact le_of_lt (log_rpow_lt_liuPanSourceIntervalLower N B)
  have haggN :
      ∑ d ∈ Icc 1 (panModulusCutoff N B),
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N A₁ A₂ d (goldbachS2SwitchedCoeff N T) ≤
        C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
    simpa [A₁, A₂, T] using
      hagg N hNagg A₁ A₂ (goldbachS2SwitchedCoeff N T) hA₂ hA₁
        (abs_goldbachS2SwitchedCoeff_le_one N T)
  have hpoint :
      ∀ d ∈ S,
        |goldbachS2SwitchedRemainder N T d| ≤
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d (goldbachS2SwitchedCoeff N T) := by
    intro d hdS
    rcases Finset.mem_filter.mp hdS with ⟨hdIcc, hdN⟩
    have hd : 1 ≤ d := (Finset.mem_Icc.mp hdIcc).1
    rw [goldbachS2SwitchedRemainder_eq_panError (T := T) hd hdN hsupp]
    exact S2Switched_abs_intervalSum_le_maxL hd hdN
  have hsubset : S ⊆ Icc 1 (panModulusCutoff N B) := by
    intro d hd
    exact (Finset.mem_filter.mp hd).1
  have hsum :
      ∑ d ∈ S,
        liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
          N A₁ A₂ d (goldbachS2SwitchedCoeff N T) ≤
        ∑ d ∈ Icc 1 (panModulusCutoff N B),
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d (goldbachS2SwitchedCoeff N T) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro d _ hdNot
    exact S2Switched_intervalMaxL_nonneg
      (liuLogarithmicIntegral (2 / Real.log 2)) N A₁ A₂ d
      (goldbachS2SwitchedCoeff N T)
  calc
    ∑ d ∈ S, |goldbachS2SwitchedRemainder N T d|
      ≤ ∑ d ∈ S,
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d (goldbachS2SwitchedCoeff N T) := by
              exact Finset.sum_le_sum hpoint
    _ ≤ ∑ d ∈ Icc 1 (panModulusCutoff N B),
          liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
            N A₁ A₂ d (goldbachS2SwitchedCoeff N T) := hsum
    _ ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U := haggN

theorem goldbachS2SwitchedGatedMainMass_eq_mainMass_of_dvd_prodPrimes
    (N : ℕ) {ε Z : ℝ} (hN : 1 ≤ N) (hεu : ε < (2 : ℝ) / 15)
    {d : ℕ}
    (hZ : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
    (hd : d ∣ goldbachS1ProdPrimes N Z) :
    goldbachS2SwitchedGatedMainMass N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) d =
      goldbachS2SwitchedMainMass N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) := by
  simpa [goldbachS2SwitchedGatedMainMass, goldbachS2SwitchedMainMass] using
    (goldbachS2_gated_sum_eq_sum (N := N) (ε := ε) (d := d) hN hεu hZ hd
      (fun r => liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / r)))

theorem goldbachS2SwitchedBoundingSieve_rem_eq_remainder_of_dvd_prodPrimes
    {N : ℕ} (hEven : Even N) {ε Z : ℝ} {d : ℕ}
    (hN : 1 ≤ N) (hεu : ε < (2 : ℝ) / 15)
    (hZ : Z ≤ (N : ℝ) ^ ((1 : ℝ) / 4))
    (hd : d ∣ goldbachS1ProdPrimes N Z) :
    let T : ℝ := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)
    (goldbachS2SwitchedBoundingSieve N hEven T Z).rem d =
      goldbachS2SwitchedRemainder N T d := by
  dsimp
  change
    (goldbachS2SwitchedBoundingSieve N hEven ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) Z).rem d =
      goldbachS2SwitchedRemainder N ((N : ℝ) ^ ((9 : ℝ) / 19 - ε)) d
  rw [goldbachS2SwitchedBoundingSieve_rem_eq_divCount_sub (N := N) (hEven := hEven)
    (T := (N : ℝ) ^ ((9 : ℝ) / 19 - ε)) (Z := Z) hd, goldbachS2SwitchedRemainder]
  rw [goldbachS2SwitchedGatedMainMass_eq_mainMass_of_dvd_prodPrimes N hN hεu hZ hd]

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig