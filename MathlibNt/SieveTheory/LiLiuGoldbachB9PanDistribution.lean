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

noncomputable local instance instDecidableGoldbachB9PanDistribution (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual labelled zero-prefix divisor count, with output multiplicities. -/
noncomputable def goldbachB9PlusDivCount (N d : ℕ) : ℕ :=
  (goldbachB10DivisorAtoms N d 0 ((N : ℝ) ^ (4 / 53 : ℝ))
    ((N : ℝ) ^ (1 / 3 : ℝ))).card

noncomputable def goldbachB9PlusGatedMainMass (N d : ℕ) : ℝ :=
  ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)),
    if Nat.Coprime m d then goldbachB9PlusLiWeight N m else 0

noncomputable def goldbachB9PlusGatedRemainder (N d : ℕ) : ℝ :=
  (goldbachB9PlusDivCount N d : ℝ) - goldbachB9PlusGatedMainMass N d / d.totient

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

/-- The inverse class uses the original N, including its residue zero modulo one. -/
theorem goldbachB9PlusAtom_output_dvd_iff_residue
    {N d : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hx : x ∈ goldbachB10Atoms N 0 ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ))) :
    d ∣ goldbachPi10Output N x ↔
      Nat.Coprime (goldbachC10Prod x.1) d ∧
        (x.2 : ZMod d) = ((N % d : ℕ) : ZMod d) * (goldbachC10Prod x.1 : ZMod d)⁻¹ := by
  simpa only [goldbachB10DivisorResidueCondition, ZMod.natCast_mod] using
    goldbachB10Atom_output_dvd_iff_residueCondition hd hdN hx

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

theorem goldbachB9PlusDivCount_eq_product_sum
    {N d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N) :
    (goldbachB9PlusDivCount N d : ℝ) =
      ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)),
        if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0 := by
  rw [goldbachB9PlusDivCount, goldbachB10DivisorAtoms_card_eq_sum_productSupport _ _ _ hd hdN,
    Nat.cast_sum]
  apply sum_congr rfl
  intro m hm
  rw [goldbachC10Coeff_eq_one_of_mem_productSupport hm, one_mul]
  by_cases hc : Nat.Coprime m d
  · rw [if_pos hc, if_pos hc, goldbachB9PlusProductResidueQFiber_card_eq_prefix hm hc]
  · simp only [if_neg hc, Nat.cast_zero]

private theorem B9Pan_coeff_sum_eq_support {N A₁ A₂ : ℕ} (f : ℕ → ℝ)
    (hsupp : goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆ Ioc A₁ A₂) :
    ∑ m ∈ Ioc A₁ A₂,
      goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) m * f m =
      ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)), f m := by
  calc
    _ = ∑ m ∈ goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
        ((N : ℝ) ^ (1 / 3 : ℝ)),
        goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) m * f m := by
      symm
      apply sum_subset hsupp
      intro m _ hm
      have hz : goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ))
          ((N : ℝ) ^ (1 / 3 : ℝ)) m = 0 :=
        not_not.mp (fun h => hm (goldbachC10CoeffReal_ne_zero_iff.mp h))
      rw [hz, zero_mul]
    _ = _ := sum_congr rfl (fun _ hm => by
      rw [goldbachC10CoeffReal_eq_one_of_mem_productSupport hm, one_mul])

noncomputable def goldbachB9PlusPanAPPrefixCount (N A₁ A₂ d : ℕ) : ℝ :=
  ∑ m ∈ Ioc A₁ A₂,
    goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)) m *
      (if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0)

theorem goldbachB9PlusDivCount_eq_panAPPrefixCount
    {N A₁ A₂ d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hsupp : goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆ Ioc A₁ A₂) :
    (goldbachB9PlusDivCount N d : ℝ) = goldbachB9PlusPanAPPrefixCount N A₁ A₂ d := by
  rw [goldbachB9PlusDivCount_eq_product_sum hd hdN, goldbachB9PlusPanAPPrefixCount,
    B9Pan_coeff_sum_eq_support _ hsupp]

/-- One absolute value will be taken only after this entire m-sum. -/
theorem goldbachB9PlusGatedRemainder_eq_panError
    {N A₁ A₂ d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hsupp : goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆ Ioc A₁ A₂) :
    goldbachB9PlusGatedRemainder N d =
      liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d (N % d)
        (goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  unfold liuMainPanCoprimeIntervalSum
  have heq := B9Pan_coeff_sum_eq_support
    (fun m => if Nat.Coprime m d then
      liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N m d (N % d) else 0) hsupp
  simp only [mul_ite, mul_zero] at heq
  rw [heq, goldbachB9PlusGatedRemainder, goldbachB9PlusDivCount_eq_product_sum hd hdN,
    goldbachB9PlusGatedMainMass, sum_div, ← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  by_cases hc : Nat.Coprime m d
  · simp only [if_pos hc, liuScaledAPError, goldbachB9PlusLiWeight]
  · simp only [if_neg hc, zero_div, sub_self]

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

theorem goldbachB9PlusGatedRemainder_eventually_eq_panError (B : ℝ) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ d : ℕ,
      1 ≤ d → Nat.Coprime d N →
      goldbachB9PlusGatedRemainder N d =
        liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
          N (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) d (N % d)
          (goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp (goldbachB9ProductSupport_eventually_panInterval B)
  refine ⟨max 4 Ns, le_max_left _ _, ?_⟩
  intro N hN d hd hdN
  exact goldbachB9PlusGatedRemainder_eq_panError hd hdN (hs N ((le_max_right _ _).trans hN))

theorem goldbachB9PlusGatedRemainder_abs_le_maxL
    {N A₁ A₂ d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hsupp : goldbachC10ProductSupport N ((N : ℝ) ^ (4 / 53 : ℝ))
      ((N : ℝ) ^ (1 / 3 : ℝ)) ⊆ Ioc A₁ A₂) :
    |goldbachB9PlusGatedRemainder N d| ≤
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d
        (goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))) := by
  rw [goldbachB9PlusGatedRemainder_eq_panError hd hdN hsupp]
  have hl : N % d ∈ unitResidues d :=
    mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt N (by omega)),
      (ZMod.coprime_mod_iff_coprime N d).mpr hdN.symm⟩
  have hS : (unitResidues d).Nonempty := ⟨N % d, hl⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  exact le_max'
    ((unitResidues d).image (fun l =>
      |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d l
        (goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ)))|))
    _ (mem_image.mpr ⟨N % d, hl, rfl⟩)

theorem goldbachB9PlusGatedRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachB9PlusGatedRemainder N d| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Na, ha⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp (goldbachB9ProductSupport_eventually_panInterval B)
  refine ⟨C, hC, B, hB, max 4 (max Na Ns), le_max_left _ _, ?_⟩
  intro N hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let A₁ := liuPanSourceIntervalLower N B
  let A₂ := liuPanSourceIntervalUpper N
  let f := goldbachC10CoeffReal N ((N : ℝ) ^ (4 / 53 : ℝ)) ((N : ℝ) ^ (1 / 3 : ℝ))
  let F := fun d => liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
    N A₁ A₂ d f
  calc
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N), F d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hdI, hdc⟩ := mem_filter.mp hd
      exact goldbachB9PlusGatedRemainder_abs_le_maxL (mem_Icc.mp hdI).1 hdc (hs N hNs)
    _ ≤ ∑ d ∈ Icc 1 (panModulusCutoff N B), F d :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        (fun _ _ _ => liuMainPanCoprimeIntervalMaxL_nonneg _ _ _ _ _ _)
    _ ≤ _ := ha N hNa A₁ A₂ f
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (le_of_lt (log_rpow_lt_liuPanSourceIntervalLower N B))
      (abs_goldbachC10CoeffReal_le_one N _ _)

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig