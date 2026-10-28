import MathlibNt.SieveTheory.LiLiuGoldbachB9C10Bridge
import MathlibNt.SieveTheory.LiLiuGoldbachB9MainGate
import MathlibNt.SieveTheory.LiLiuGoldbachB10PanPrefixes
import MathlibNt.SieveTheory.LiuPanWangDingSource
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate
import MathlibNt.SieveTheory.LiuPanActualErrorEnvelope

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig


theorem goldbachB9Product_mul_ne_self {N m q : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) : m * q ≠ N := by
  intro heq
  have hm0 := goldbachC10CoeffReal_ne_zero_iff.mpr hm
  have hc := goldbachC10CoeffReal_ne_zero_imp_coprime hm0
  have hm1 := goldbachC10CoeffReal_ne_zero_imp_one_lt hm0
  exact (ne_of_gt hm1) (Nat.eq_one_of_dvd_coprimes hc dvd_rfl ⟨q, heq.symm⟩)

theorem goldbachB9Product_mul_lt_iff_le {N m q : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) : m * q < N ↔ m * q ≤ N :=
  ⟨le_of_lt, fun h => lt_of_le_of_ne h (goldbachB9Product_mul_ne_self hm)⟩


private theorem B9Pan_residue_iff_modEq {N m q d : ℕ} (hc : Nat.Coprime m d) :
    (q : ZMod d) = (N : ZMod d) * (m : ZMod d)⁻¹ ↔
      Nat.ModEq d (m * q) (N % d) := by
  have hmod : Nat.ModEq d (m * q) N ↔ Nat.ModEq d (m * q) (N % d) :=
    ⟨fun h => h.trans (Nat.mod_modEq N d).symm,
      fun h => h.trans (Nat.mod_modEq N d)⟩
  rw [← hmod]
  constructor
  · intro hq
    apply (ZMod.natCast_eq_natCast_iff _ _ d).mp
    push_cast
    rw [hq]
    calc
      (m : ZMod d) * ((N : ZMod d) * (m : ZMod d)⁻¹) =
          (N : ZMod d) * ((m : ZMod d) * (m : ZMod d)⁻¹) := by ac_rfl
      _ = _ := by rw [ZMod.coe_mul_inv_eq_one _ hc, mul_one]
  · intro h
    have hz : (m : ZMod d) * (q : ZMod d) = (N : ZMod d) := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ d).mpr h
    calc
      (q : ZMod d) = ((m : ZMod d) * (m : ZMod d)⁻¹) * q := by
        rw [ZMod.coe_mul_inv_eq_one _ hc, one_mul]
      _ = ((m : ZMod d) * q) * (m : ZMod d)⁻¹ := by ac_rfl
      _ = _ := by rw [hz]

theorem goldbachB9PlusProductResidueQFiber_card_eq_prefix
    {N m d : ℕ}
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) (hc : Nat.Coprime m d) :
    (goldbachB10ProductResidueQFiber N d 0 m).card = primesInAPBelow N m d (N % d) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast goldbachC10ProductSupport_pos hm
  unfold goldbachB10ProductResidueQFiber goldbachB10ProductQFiber primesInAPBelow
  congr 1
  ext q
  simp only [mem_filter, zero_mul, zero_div]
  constructor
  · rintro ⟨⟨hq, hp, _hpos, hupper⟩, hres⟩
    have hlt : m * q < N := by
      have h := (lt_div_iff₀ hmpos).mp hupper
      exact_mod_cast (by simpa [mul_comm] using h : (m : ℝ) * q < N)
    exact ⟨hq, hp, hlt.le, (B9Pan_residue_iff_modEq hc).mp hres⟩
  · rintro ⟨hq, hp, hle, hmod⟩
    have hlt := (goldbachB9Product_mul_lt_iff_le hm).mpr hle
    refine ⟨⟨hq, hp, by exact_mod_cast hp.pos, ?_⟩,
      (B9Pan_residue_iff_modEq hc).mpr hmod⟩
    apply (lt_div_iff₀ hmpos).mpr
    exact_mod_cast (by simpa [mul_comm] using hlt : q * m < N)


theorem goldbachB9ProductSupport_pan_bounds {N m : ℕ} (hN : 2 ≤ N)
    (hm : m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    (N : ℝ) ^ (65 / 159 : ℝ) ≤ m ∧ (m : ℝ) ≤ (N : ℝ) ^ (2 / 3 : ℝ) := by
  exact goldbachC9ProductSupport_bounds hN
    ((goldbachC9ProductSupport_eq_C10ProductSupport N).symm ▸ hm)

theorem goldbachB9ProductSupport_mem_panInterval {N : ℕ} {B : ℝ}
    (hN : 2 ≤ N) (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N) :
    goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆
        Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  intro m hm
  obtain ⟨hml, hmu⟩ := goldbachB9ProductSupport_pan_bounds hN hm
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hleft : (liuPanSourceIntervalLower N B : ℝ) < m := by
    calc
      (liuPanSourceIntervalLower N B : ℝ) < liuSourceZ10 N := by exact_mod_cast hlow
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ < (N : ℝ) ^ (65 / 159 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
      _ ≤ m := hml
  exact mem_Ioc.mpr ⟨by exact_mod_cast hleft, Nat.le_floor hmu⟩

theorem goldbachB9ProductSupport_eventually_panInterval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆
          Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  filter_upwards [eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B,
    eventually_ge_atTop (2 : ℕ)] with N hl hN
  exact goldbachB9ProductSupport_mem_panInterval hN hl


end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig