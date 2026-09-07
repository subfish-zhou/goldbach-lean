import MathlibNt.SieveTheory.LiLiuGoldbachB10ProductCount
import MathlibNt.SieveTheory.LiuTrueLiPan
import MathlibNt.SieveTheory.LiuPanActualCountCharacters
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.ModEq
import Mathlib.Order.Interval.Finset.Nat

open scoped BigOperators

open Finset
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB10PanPrefixes (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The literal real-valued `C10` coefficient used by the finite Pan bridge. -/
noncomputable def goldbachC10CoeffReal (N : ℕ) (b c : ℝ) (m : ℕ) : ℝ :=
  goldbachC10Coeff N b c m

theorem goldbachC10CoeffReal_eq_one_of_mem_productSupport
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c) :
    goldbachC10CoeffReal N b c m = 1 := by
  simp [goldbachC10CoeffReal, goldbachC10Coeff_eq_one_of_mem_productSupport hm]

private theorem B10PanPrefixes_goldbachC10Coeff_eq_zero_of_not_mem_productSupport
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm : m ∉ goldbachC10ProductSupport N b c) :
    goldbachC10Coeff N b c m = 0 := by
  by_contra hcoeff
  have hpos : 0 < goldbachC10Coeff N b c m := Nat.pos_of_ne_zero hcoeff
  rcases Finset.card_pos.mp (by simpa [goldbachC10Coeff] using hpos) with ⟨rs, hrs⟩
  exact hm <| mem_goldbachC10ProductSupport_iff.mpr
    ⟨rs, (mem_goldbachC10ProductFiber_iff.mp hrs).1, (mem_goldbachC10ProductFiber_iff.mp hrs).2⟩

theorem abs_goldbachC10CoeffReal_le_one
    (N : ℕ) (b c : ℝ) (m : ℕ) :
    |goldbachC10CoeffReal N b c m| ≤ 1 := by
  have hnonneg : 0 ≤ goldbachC10CoeffReal N b c m := by
    simp [goldbachC10CoeffReal]
  rw [abs_of_nonneg hnonneg, goldbachC10CoeffReal]
  exact_mod_cast goldbachC10Coeff_le_one (N := N) (b := b) (c := c) (m := m)

theorem goldbachC10CoeffReal_ne_zero_iff
    {N : ℕ} {b c : ℝ} {m : ℕ} :
    goldbachC10CoeffReal N b c m ≠ 0 ↔ m ∈ goldbachC10ProductSupport N b c := by
  constructor
  · intro hm0
    by_contra hm
    have hcoeff0 : goldbachC10Coeff N b c m = 0 :=
      B10PanPrefixes_goldbachC10Coeff_eq_zero_of_not_mem_productSupport hm
    exact hm0 <| by simp [goldbachC10CoeffReal, hcoeff0]
  · intro hm
    rw [goldbachC10CoeffReal_eq_one_of_mem_productSupport hm]
    norm_num

theorem goldbachC10CoeffReal_ne_zero_imp_one_lt
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm0 : goldbachC10CoeffReal N b c m ≠ 0) :
    1 < m := by
  rcases mem_goldbachC10ProductSupport_iff.mp
      ((goldbachC10CoeffReal_ne_zero_iff).mp hm0) with ⟨rs, hrs, hprod⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨hrPrime, hsPrime, _, _, _, _, _⟩
  rw [← hprod]
  have hr2 : 2 ≤ rs.1 := hrPrime.two_le
  have hs2 : 2 ≤ rs.2 := hsPrime.two_le
  have hmul : 4 ≤ rs.1 * rs.2 := by
    simpa using Nat.mul_le_mul hr2 hs2
  exact lt_of_lt_of_le (by decide : 1 < 4) hmul

theorem goldbachC10CoeffReal_ne_zero_imp_coprime
    {N : ℕ} {b c : ℝ} {m : ℕ}
    (hm0 : goldbachC10CoeffReal N b c m ≠ 0) :
    Nat.Coprime m N := by
  rcases mem_goldbachC10ProductSupport_iff.mp
      ((goldbachC10CoeffReal_ne_zero_iff).mp hm0) with ⟨rs, hrs, hprod⟩
  rcases mem_goldbachC10Pairs_iff.mp hrs with ⟨_, _, hcop, _, _, _, _⟩
  rw [← hprod]
  exact hcop

private theorem B10PanPrefixes_prod_eq_N_impossible
    {N : ℕ} {b c : ℝ} {m q : ℕ}
    (hm0 : goldbachC10CoeffReal N b c m ≠ 0) :
    m * q ≠ N := by
  intro hEq
  have hcop : Nat.Coprime m N := goldbachC10CoeffReal_ne_zero_imp_coprime hm0
  have hm_dvd_N : m ∣ N := ⟨q, hEq.symm⟩
  have hm_eq_one : m = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hm_dvd_N
  exact (ne_of_gt <| goldbachC10CoeffReal_ne_zero_imp_one_lt hm0) hm_eq_one

private theorem B10PanPrefixes_upper_lt_iff_mul_le
    {N : ℕ} {b c : ℝ} {m q : ℕ}
    (hm0 : goldbachC10CoeffReal N b c m ≠ 0) :
    (q : ℝ) < (N : ℝ) / (m : ℝ) ↔ m * q ≤ N := by
  have hm1 : 1 < m := goldbachC10CoeffReal_ne_zero_imp_one_lt hm0
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (lt_trans Nat.zero_lt_one hm1)
  constructor
  · intro hq
    have hmul : (m * q : ℕ) < N := by
      have hreal : (q : ℝ) * (m : ℝ) < N := by
        rw [lt_div_iff₀ hmpos] at hq
        simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hq
      simpa [Nat.mul_comm] using (show (q * m : ℕ) < N by exact_mod_cast hreal)
    exact hmul.le
  · intro hmq
    have hlt : m * q < N :=
      lt_of_le_of_ne hmq (B10PanPrefixes_prod_eq_N_impossible (q := q) hm0)
    rw [lt_div_iff₀ hmpos]
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
      (show ((m * q : ℕ) : ℝ) < N by exact_mod_cast hlt)

private theorem B10PanPrefixes_lower_lt_iff_floor_lt_mul
    {N m q : ℕ} {ε : ℝ}
    (hmpos : 0 < m) (hε0 : 0 ≤ ε) :
    ε * (N : ℝ) / (m : ℝ) < (q : ℝ) ↔ ⌊ε * (N : ℝ)⌋₊ < m * q := by
  have hmposR : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hnonneg : 0 ≤ ε * (N : ℝ) := by positivity
  constructor
  · intro hq
    have hreal : ε * (N : ℝ) < (m * q : ℕ) := by
      rw [div_lt_iff₀ hmposR] at hq
      simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hq
    exact (Nat.floor_lt hnonneg).2 hreal
  · intro hmq
    have hreal : ε * (N : ℝ) < (m * q : ℕ) := (Nat.floor_lt hnonneg).1 hmq
    rw [div_lt_iff₀ hmposR]
    simpa [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using hreal

private noncomputable def B10PanPrefixesAPPrefix
    (N Y m d l : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun q => q.Prime ∧ m * q ≤ Y ∧ m * q ≡ l [MOD d]

private theorem B10PanPrefixes_primesInAPBelow_eq_card
    {N Y m d l : ℕ}
    (hm1 : 1 ≤ m) (hY : Y ≤ N) :
    primesInAPBelow Y m d l = (B10PanPrefixesAPPrefix N Y m d l).card := by
  unfold primesInAPBelow B10PanPrefixesAPPrefix
  apply congrArg Finset.card
  ext q
  simp only [mem_filter, mem_range, Nat.lt_succ_iff]
  constructor
  · rintro ⟨hqY, hqPrime, hmq, hmod⟩
    exact ⟨hqY.trans hY, hqPrime, hmq, hmod⟩
  · rintro ⟨hqN, hqPrime, hmq, hmod⟩
    have hqle : q ≤ Y := by
      calc
        q ≤ m * q := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right q hm1
        _ ≤ Y := hmq
    exact ⟨hqle, hqPrime, hmq, hmod⟩

private theorem B10PanPrefixesAPPrefix_mono
    {N Y₁ Y₂ m d l : ℕ}
    (hY : Y₁ ≤ Y₂) :
    B10PanPrefixesAPPrefix N Y₁ m d l ⊆ B10PanPrefixesAPPrefix N Y₂ m d l := by
  intro q hq
  rcases Finset.mem_filter.mp hq with ⟨hqRange, hqPrime, hqY₁, hmod⟩
  exact Finset.mem_filter.mpr ⟨hqRange, hqPrime, hqY₁.trans hY, hmod⟩

private theorem B10PanPrefixes_floor_mul_le_self
    {N : ℕ} {ε : ℝ}
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    ⌊ε * (N : ℝ)⌋₊ ≤ N := by
  have hεnonneg : 0 ≤ ε := le_of_lt hε0
  have hεle : ε ≤ 1 := le_of_lt hε1
  have hbound : ε * (N : ℝ) ≤ N := by
    nlinarith
  exact Nat.floor_le_of_le hbound

private theorem B10PanPrefixes_residue_eq_iff_modEq
    {N d m q : ℕ}
    (hmd : Nat.Coprime m d) :
    (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹ ↔ Nat.ModEq d (m * q) N := by
  constructor
  · intro hq
    have hzmul :
        ((m : ZMod d) * (q : ZMod d)) = (N : ZMod d) := by
      calc
        ((m : ZMod d) * (q : ZMod d))
            = (m : ZMod d) * ((N : ZMod d) * (m : ZMod d)⁻¹) := by rw [hq]
        _ = (N : ZMod d) * ((m : ZMod d) * (m : ZMod d)⁻¹) := by ac_rfl
        _ = (N : ZMod d) * 1 := by rw [ZMod.coe_mul_inv_eq_one m hmd]
        _ = (N : ZMod d) := by simp
    have hzprod : (((m * q : ℕ) : ZMod d)) = (N : ZMod d) := by
      simpa using hzmul
    exact (ZMod.natCast_eq_natCast_iff (m * q) N d).1 hzprod
  · intro hmq
    have hzprod : (((m * q : ℕ) : ZMod d)) = (N : ZMod d) :=
      (ZMod.natCast_eq_natCast_iff (m * q) N d).2 hmq
    have hzmul : ((m : ZMod d) * (q : ZMod d)) = (N : ZMod d) := by
      simpa using hzprod
    calc
      (q : ZMod d) = (1 : ZMod d) * (q : ZMod d) := by simp
      _ = (((m : ZMod d) * (m : ZMod d)⁻¹) * (q : ZMod d)) := by
            rw [← ZMod.coe_mul_inv_eq_one m hmd]
      _ = (m : ZMod d)⁻¹ * ((m : ZMod d) * (q : ZMod d)) := by ac_rfl
      _ = (m : ZMod d)⁻¹ * (N : ZMod d) := by rw [hzmul]
      _ = (N : ZMod d) * (m : ZMod d)⁻¹ := by simp [mul_comm]

private theorem B10PanPrefixes_residue_eq_iff_modEq_residue
    {N d m q : ℕ}
    (hmd : Nat.Coprime m d) :
    (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹ ↔ Nat.ModEq d (m * q) (N % d) := by
  rw [B10PanPrefixes_residue_eq_iff_modEq hmd]
  constructor
  · intro hmq
    exact hmq.trans (Nat.mod_modEq N d).symm
  · intro hmq
    exact hmq.trans (Nat.mod_modEq N d)

private theorem goldbachB10ProductQFiber_eq_primePrefixSdiff
    {N : ℕ} {ε b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c)
    (hε0 : 0 < ε) :
    goldbachB10ProductQFiber N ε m =
      B10PanPrefixesAPPrefix N N m 1 0 \
        B10PanPrefixesAPPrefix N ⌊ε * (N : ℝ)⌋₊ m 1 0 := by
  let Y₀ : ℕ := ⌊ε * (N : ℝ)⌋₊
  have hm0 : goldbachC10CoeffReal N b c m ≠ 0 :=
    (goldbachC10CoeffReal_ne_zero_iff).2 hm
  have hmpos : 0 < m := lt_trans Nat.zero_lt_one (goldbachC10CoeffReal_ne_zero_imp_one_lt hm0)
  ext q
  constructor
  · intro hq
    rcases mem_goldbachB10ProductQFiber_iff.mp hq with ⟨hqRange, hqPrime, hqLower, hqUpper⟩
    have hupperLe : m * q ≤ N := (B10PanPrefixes_upper_lt_iff_mul_le hm0).mp hqUpper
    have hlowerNot : ¬ m * q ≤ Y₀ := by
      intro hmq
      have hfloor : Y₀ < m * q := (B10PanPrefixes_lower_lt_iff_floor_lt_mul hmpos (le_of_lt hε0)).mp hqLower
      exact (not_lt_of_ge hmq) hfloor
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · exact Finset.mem_filter.mpr
        ⟨hqRange, hqPrime, hupperLe, (by simpa using (Nat.modEq_one : m * q ≡ 0 [MOD 1]))⟩
    · intro hLower
      exact hlowerNot (by
        rcases Finset.mem_filter.mp hLower with ⟨_, _, hmq, _⟩
        exact hmq)
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hUpper, hNotLower⟩
    rcases Finset.mem_filter.mp hUpper with ⟨hqRange, hqPrime, hupperLe, _⟩
    have hqUpper : (q : ℝ) < (N : ℝ) / (m : ℝ) :=
      (B10PanPrefixes_upper_lt_iff_mul_le hm0).2 hupperLe
    have hfloor : Y₀ < m * q := lt_of_not_ge fun hmq =>
      hNotLower <| by
        exact Finset.mem_filter.mpr
          ⟨hqRange, hqPrime, hmq, (by simpa using (Nat.modEq_one : m * q ≡ 0 [MOD 1]))⟩
    have hqLower : ε * (N : ℝ) / (m : ℝ) < (q : ℝ) :=
      (B10PanPrefixes_lower_lt_iff_floor_lt_mul hmpos (le_of_lt hε0)).2 hfloor
    exact mem_goldbachB10ProductQFiber_iff.mpr ⟨hqRange, hqPrime, hqLower, hqUpper⟩

theorem goldbachB10ProductQFiber_card_eq_primePrefix_sub
    {N : ℕ} {ε b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (goldbachB10ProductQFiber N ε m).card =
      primesInAPBelow N m 1 0 - primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m 1 0 := by
  let Y₀ : ℕ := ⌊ε * (N : ℝ)⌋₊
  have hm0 : goldbachC10CoeffReal N b c m ≠ 0 :=
    (goldbachC10CoeffReal_ne_zero_iff).2 hm
  have hm1 : 1 ≤ m := (goldbachC10CoeffReal_ne_zero_imp_one_lt hm0).le
  have hY₀ : Y₀ ≤ N := B10PanPrefixes_floor_mul_le_self hε0 hε1
  rw [goldbachB10ProductQFiber_eq_primePrefixSdiff hm hε0]
  have hsubset :
      B10PanPrefixesAPPrefix N Y₀ m 1 0 ⊆ B10PanPrefixesAPPrefix N N m 1 0 :=
    B10PanPrefixesAPPrefix_mono hY₀
  rw [Finset.card_sdiff_of_subset hsubset,
    ← B10PanPrefixes_primesInAPBelow_eq_card hm1 le_rfl,
    ← B10PanPrefixes_primesInAPBelow_eq_card hm1 hY₀]

private theorem goldbachB10ProductResidueQFiber_eq_primePrefixSdiff
    {N d : ℕ} {ε b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c)
    (hmd : Nat.Coprime m d)
    (hε0 : 0 < ε) :
    goldbachB10ProductResidueQFiber N d ε m =
      B10PanPrefixesAPPrefix N N m d (N % d) \
        B10PanPrefixesAPPrefix N ⌊ε * (N : ℝ)⌋₊ m d (N % d) := by
  let Y₀ : ℕ := ⌊ε * (N : ℝ)⌋₊
  have hm0 : goldbachC10CoeffReal N b c m ≠ 0 :=
    (goldbachC10CoeffReal_ne_zero_iff).2 hm
  have hmpos : 0 < m := lt_trans Nat.zero_lt_one (goldbachC10CoeffReal_ne_zero_imp_one_lt hm0)
  ext q
  constructor
  · intro hq
    rcases mem_goldbachB10ProductResidueQFiber_iff.mp hq with ⟨hqProd, hqResidue⟩
    rcases mem_goldbachB10ProductQFiber_iff.mp hqProd with ⟨hqRange, hqPrime, hqLower, hqUpper⟩
    have hupperLe : m * q ≤ N := (B10PanPrefixes_upper_lt_iff_mul_le hm0).mp hqUpper
    have hmod : Nat.ModEq d (m * q) (N % d) :=
      (B10PanPrefixes_residue_eq_iff_modEq_residue hmd).1 hqResidue
    have hlowerNot : ¬ m * q ≤ Y₀ := by
      intro hmq
      have hfloor : Y₀ < m * q := (B10PanPrefixes_lower_lt_iff_floor_lt_mul hmpos (le_of_lt hε0)).mp hqLower
      exact (not_lt_of_ge hmq) hfloor
    refine Finset.mem_sdiff.mpr ?_
    constructor
    · simp [B10PanPrefixesAPPrefix, hqRange, hqPrime, hupperLe, hmod]
    · intro hLower
      exact hlowerNot (by
        rcases Finset.mem_filter.mp hLower with ⟨_, _, hmq, _⟩
        exact hmq)
  · intro hq
    rcases Finset.mem_sdiff.mp hq with ⟨hUpper, hNotLower⟩
    rcases Finset.mem_filter.mp hUpper with ⟨hqRange, hqPrime, hupperLe, hmod⟩
    have hqUpper : (q : ℝ) < (N : ℝ) / (m : ℝ) :=
      (B10PanPrefixes_upper_lt_iff_mul_le hm0).2 hupperLe
    have hfloor : Y₀ < m * q := lt_of_not_ge fun hmq =>
      hNotLower <| by
        exact Finset.mem_filter.mpr ⟨hqRange, hqPrime, hmq, hmod⟩
    have hqLower : ε * (N : ℝ) / (m : ℝ) < (q : ℝ) :=
      (B10PanPrefixes_lower_lt_iff_floor_lt_mul hmpos (le_of_lt hε0)).2 hfloor
    have hqResidue : (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹ :=
      (B10PanPrefixes_residue_eq_iff_modEq_residue hmd).2 hmod
    exact mem_goldbachB10ProductResidueQFiber_iff.mpr
      ⟨mem_goldbachB10ProductQFiber_iff.mpr ⟨hqRange, hqPrime, hqLower, hqUpper⟩, hqResidue⟩

theorem goldbachB10ProductResidueQFiber_card_eq_primePrefix_sub
    {N d : ℕ} {ε b c : ℝ} {m : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N b c)
    (hmd : Nat.Coprime m d)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (goldbachB10ProductResidueQFiber N d ε m).card =
      primesInAPBelow N m d (N % d) -
        primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m d (N % d) := by
  let Y₀ : ℕ := ⌊ε * (N : ℝ)⌋₊
  have hm0 : goldbachC10CoeffReal N b c m ≠ 0 :=
    (goldbachC10CoeffReal_ne_zero_iff).2 hm
  have hm1 : 1 ≤ m := (goldbachC10CoeffReal_ne_zero_imp_one_lt hm0).le
  have hY₀ : Y₀ ≤ N := B10PanPrefixes_floor_mul_le_self hε0 hε1
  rw [goldbachB10ProductResidueQFiber_eq_primePrefixSdiff hm hmd hε0]
  have hsubset :
      B10PanPrefixesAPPrefix N Y₀ m d (N % d) ⊆
        B10PanPrefixesAPPrefix N N m d (N % d) :=
    B10PanPrefixesAPPrefix_mono hY₀
  rw [Finset.card_sdiff_of_subset hsubset,
    ← B10PanPrefixes_primesInAPBelow_eq_card hm1 le_rfl,
    ← B10PanPrefixes_primesInAPBelow_eq_card hm1 hY₀]

/-- The fixed-source Pan AP prefix count with the actual real coefficient
`goldbachC10CoeffReal N b c`. -/
noncomputable def goldbachB10PanAPPrefixCount
    (N Y A₁ A₂ d l : ℕ) (b c : ℝ) : ℝ :=
  ∑ m ∈ Ioc A₁ A₂,
    if Nat.Coprime m d then
      goldbachC10CoeffReal N b c m * (primesInAPBelow Y m d l : ℝ)
    else 0

private theorem B10PanPrefixes_panAPPrefixCount_eq_support_sum
    {N Y A₁ A₂ d l : ℕ} {b c : ℝ}
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) :
    goldbachB10PanAPPrefixCount N Y A₁ A₂ d l b c =
      ∑ m ∈ goldbachC10ProductSupport N b c,
        if Nat.Coprime m d then (primesInAPBelow Y m d l : ℝ) else 0 := by
  unfold goldbachB10PanAPPrefixCount
  classical
  have hsub : goldbachC10ProductSupport N b c ⊆ Ioc A₁ A₂ := fun _ hm => hsupp hm
  calc
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          if Nat.Coprime m d then
            goldbachC10CoeffReal N b c m * (primesInAPBelow Y m d l : ℝ)
          else 0 := by
            symm
            apply Finset.sum_subset hsub
            intro m hmIoc hmNot
            have hcoeff0 : goldbachC10CoeffReal N b c m = 0 := by
              by_cases hm : m ∈ goldbachC10ProductSupport N b c
              · exact False.elim (hmNot hm)
              · simp [goldbachC10CoeffReal, B10PanPrefixes_goldbachC10Coeff_eq_zero_of_not_mem_productSupport hm]
            simp [hcoeff0]
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
          if Nat.Coprime m d then (primesInAPBelow Y m d l : ℝ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hmd : Nat.Coprime m d
            · rw [if_pos hmd, if_pos hmd]
              simp [goldbachC10CoeffReal_eq_one_of_mem_productSupport hm]
            · simp [hmd]

theorem goldbachB10DivisorAtoms_card_eq_panAPPrefixCount_sub
    {N d A₁ A₂ : ℕ} {ε b c : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) :
    ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) =
      goldbachB10PanAPPrefixCount N N A₁ A₂ d (N % d) b c -
        goldbachB10PanAPPrefixCount N ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d (N % d) b c := by
  have hcount :
      ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) =
        ∑ m ∈ goldbachC10ProductSupport N b c,
          if Nat.Coprime m d then
            ((goldbachB10ProductResidueQFiber N d ε m).card : ℝ)
          else 0 := by
    calc
      ((goldbachB10DivisorAtoms N d ε b c).card : ℝ)
          = ∑ m ∈ goldbachC10ProductSupport N b c,
              (((goldbachC10Coeff N b c m *
                (if Nat.Coprime m d then (goldbachB10ProductResidueQFiber N d ε m).card else 0)) : ℕ) : ℝ) := by
                  exact_mod_cast
                    (goldbachB10DivisorAtoms_card_eq_sum_productSupport
                      (ε := ε) (b := b) (c := c) hd hdN)
      _ = ∑ m ∈ goldbachC10ProductSupport N b c,
            if Nat.Coprime m d then ((goldbachB10ProductResidueQFiber N d ε m).card : ℝ) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              by_cases hmd : Nat.Coprime m d
              · rw [if_pos hmd, if_pos hmd]
                simp [goldbachC10Coeff_eq_one_of_mem_productSupport hm]
              · simp [hmd]
  calc
    ((goldbachB10DivisorAtoms N d ε b c).card : ℝ)
        = ∑ m ∈ goldbachC10ProductSupport N b c,
            if Nat.Coprime m d then
              ((primesInAPBelow N m d (N % d) : ℝ) -
                (primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m d (N % d) : ℝ))
            else 0 := by
              rw [hcount]
              refine Finset.sum_congr rfl ?_
              intro m hm
              by_cases hmd : Nat.Coprime m d
              · rw [if_pos hmd]
                have hm0 : goldbachC10CoeffReal N b c m ≠ 0 :=
                  (goldbachC10CoeffReal_ne_zero_iff).2 hm
                have hm1 : 1 ≤ m := (goldbachC10CoeffReal_ne_zero_imp_one_lt hm0).le
                have hY₀ : ⌊ε * (N : ℝ)⌋₊ ≤ N := B10PanPrefixes_floor_mul_le_self hε0 hε1
                have hprefix_le :
                    primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m d (N % d) ≤
                      primesInAPBelow N m d (N % d) := by
                  rw [B10PanPrefixes_primesInAPBelow_eq_card hm1 hY₀,
                    B10PanPrefixes_primesInAPBelow_eq_card hm1 le_rfl]
                  exact Finset.card_le_card (B10PanPrefixesAPPrefix_mono hY₀)
                rw [goldbachB10ProductResidueQFiber_card_eq_primePrefix_sub hm hmd hε0 hε1]
                rw [Nat.cast_sub]
                · simp [hmd]
                · exact hprefix_le
              · simp [hmd]
    _ = ∑ m ∈ goldbachC10ProductSupport N b c,
            ((if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0) -
              (if Nat.Coprime m d then (primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m d (N % d) : ℝ) else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro m hm
              by_cases hmd : Nat.Coprime m d
              · rw [if_pos hmd, if_pos hmd, if_pos hmd]
              · rw [if_neg hmd, if_neg hmd, if_neg hmd]
                ring
    _ = (∑ m ∈ goldbachC10ProductSupport N b c,
            if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0) -
          ∑ m ∈ goldbachC10ProductSupport N b c,
            if Nat.Coprime m d then (primesInAPBelow ⌊ε * (N : ℝ)⌋₊ m d (N % d) : ℝ) else 0 := by
              rw [Finset.sum_sub_distrib]
    _ = goldbachB10PanAPPrefixCount N N A₁ A₂ d (N % d) b c -
          goldbachB10PanAPPrefixCount N ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d (N % d) b c := by
            rw [← B10PanPrefixes_panAPPrefixCount_eq_support_sum (Y := N) (d := d) (l := N % d) hsupp,
              ← B10PanPrefixes_panAPPrefixCount_eq_support_sum
                (Y := ⌊ε * (N : ℝ)⌋₊) (d := d) (l := N % d) hsupp]

/-- The Pan main-term normalization used for the exact B10 remainder bridge. -/
noncomputable def goldbachB10PanKappa0 : ℝ := 2 / Real.log 2

/-- The interval main-term prefix built from the literal coefficient
`goldbachC10CoeffReal N b c`. -/
noncomputable def goldbachB10PanMainPrefix
    (N Y A₁ A₂ d : ℕ) (b c : ℝ) : ℝ :=
  ∑ m ∈ Ioc A₁ A₂,
    if Nat.Coprime m d then
      goldbachC10CoeffReal N b c m *
        (liuLogarithmicIntegral goldbachB10PanKappa0 ((Y : ℝ) / m) / Nat.totient d)
    else 0

/-- The actual finite B10 remainder written with the same source coefficient
`goldbachC10CoeffReal N b c` and the same lower residue `N % d`. -/
noncomputable def goldbachB10PanPrefixRemainder
    (N d A₁ A₂ : ℕ) (ε b c : ℝ) : ℝ :=
  ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) -
    (goldbachB10PanMainPrefix N N A₁ A₂ d b c -
      goldbachB10PanMainPrefix N ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d b c)

theorem liuMainPanCoprimeIntervalSum_eq_prefixCount_sub_mainPrefix
    (N Y A₁ A₂ d l : ℕ) (b c : ℝ) :
    liuMainPanCoprimeIntervalSum
        (liuLogarithmicIntegral goldbachB10PanKappa0) Y A₁ A₂ d l
        (goldbachC10CoeffReal N b c) =
      goldbachB10PanAPPrefixCount N Y A₁ A₂ d l b c -
        goldbachB10PanMainPrefix N Y A₁ A₂ d b c := by
  unfold liuMainPanCoprimeIntervalSum liuScaledAPError
    goldbachB10PanAPPrefixCount goldbachB10PanMainPrefix goldbachB10PanKappa0
  calc
    _ = ∑ m ∈ Ioc A₁ A₂,
          ((if Nat.Coprime m d then goldbachC10CoeffReal N b c m * (primesInAPBelow Y m d l : ℝ) else 0) -
            (if Nat.Coprime m d then
              goldbachC10CoeffReal N b c m *
                (liuLogarithmicIntegral (2 / Real.log 2) ((Y : ℝ) / m) / Nat.totient d)
              else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro m hm
            by_cases hmd : Nat.Coprime m d
            · rw [if_pos hmd, if_pos hmd, if_pos hmd]
              ring
            · rw [if_neg hmd, if_neg hmd, if_neg hmd]
              ring
    _ = _ := by rw [Finset.sum_sub_distrib]

theorem goldbachB10PanPrefixRemainder_eq_panErrors_sub
    {N d A₁ A₂ : ℕ} {ε b c : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) :
    goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c =
      liuMainPanCoprimeIntervalSum
          (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d (N % d)
          (goldbachC10CoeffReal N b c) -
        liuMainPanCoprimeIntervalSum
          (liuLogarithmicIntegral goldbachB10PanKappa0) ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d (N % d)
          (goldbachC10CoeffReal N b c) := by
  rw [liuMainPanCoprimeIntervalSum_eq_prefixCount_sub_mainPrefix,
    liuMainPanCoprimeIntervalSum_eq_prefixCount_sub_mainPrefix]
  unfold goldbachB10PanPrefixRemainder
  rw [goldbachB10DivisorAtoms_card_eq_panAPPrefixCount_sub hd hdN hε0 hε1 hsupp]
  ring

theorem abs_goldbachB10PanPrefixRemainder_le
    {N d A₁ A₂ : ℕ} {ε b c : ℝ}
    (hd : 1 ≤ d)
    (hdN : Nat.Coprime d N)
    (hε0 : 0 < ε) (hε1 : ε < 1)
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Ioc A₁ A₂) :
    |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c| ≤
      |liuMainPanCoprimeIntervalSum
          (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d (N % d)
          (goldbachC10CoeffReal N b c)| +
        |liuMainPanCoprimeIntervalSum
          (liuLogarithmicIntegral goldbachB10PanKappa0) ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d (N % d)
          (goldbachC10CoeffReal N b c)| := by
  rw [goldbachB10PanPrefixRemainder_eq_panErrors_sub hd hdN hε0 hε1 hsupp]
  simpa [sub_eq_add_neg, abs_neg] using
    (abs_add_le (liuMainPanCoprimeIntervalSum
      (liuLogarithmicIntegral goldbachB10PanKappa0) N A₁ A₂ d (N % d)
      (goldbachC10CoeffReal N b c))
      (-liuMainPanCoprimeIntervalSum
        (liuLogarithmicIntegral goldbachB10PanKappa0) ⌊ε * (N : ℝ)⌋₊ A₁ A₂ d (N % d)
        (goldbachC10CoeffReal N b c)))

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig