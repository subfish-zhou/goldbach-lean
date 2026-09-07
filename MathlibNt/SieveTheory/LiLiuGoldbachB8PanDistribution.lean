import MathlibNt.SieveTheory.LiLiuGoldbachB8FibreSieve
import MathlibNt.SieveTheory.LiuPanWangDingSource
import MathlibNt.SieveTheory.LiuTrueLiPan
import MathlibNt.SieveTheory.LiLiuPanBoundedAggregate

open scoped BigOperators
open Finset Filter
open AnalyticNumberTheory.Sieve
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableGoldbachB8PanDistribution (P : Prop) : Decidable P :=
  Classical.propDecidable P

noncomputable def goldbachC8CoeffReal (N m : ℕ) : ℝ := goldbachC8Coeff N m

theorem goldbachC8CoeffReal_eq_one_of_mem {N m : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) : goldbachC8CoeffReal N m = 1 := by
  have hp := goldbachC8Coeff_pos_iff.mpr hm
  have hu := goldbachC8Coeff_le_one N m
  have heq : goldbachC8Coeff N m = 1 := by omega
  simp [goldbachC8CoeffReal, heq]

theorem goldbachC8CoeffReal_eq_zero_of_not_mem {N m : ℕ}
    (hm : m ∉ goldbachC8ProductSupport N) : goldbachC8CoeffReal N m = 0 := by
  have hzero : goldbachC8Coeff N m = 0 := by
    apply Nat.eq_zero_of_not_pos
    exact fun hp => hm (goldbachC8Coeff_pos_iff.mp hp)
  simp [goldbachC8CoeffReal, hzero]

theorem abs_goldbachC8CoeffReal_le_one (N m : ℕ) :
    |goldbachC8CoeffReal N m| ≤ 1 := by
  rw [goldbachC8CoeffReal, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast goldbachC8Coeff_le_one N m

/-- The gate is retained for every modulus, not only for sieve divisors. -/
noncomputable def goldbachB8PlusGatedMainMass (N d : ℕ) : ℝ :=
  ∑ m ∈ goldbachC8ProductSupport N,
    if Nat.Coprime m d then liuLogarithmicIntegral (2 / Real.log 2) ((N : ℝ) / m)
    else 0

noncomputable def goldbachB8PlusRemainder (N d : ℕ) : ℝ :=
  (goldbachB8PlusDivCount N d : ℝ) - goldbachB8PlusGatedMainMass N d / Nat.totient d

theorem goldbachC8Product_mul_ne_self {N m q : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) : m * q ≠ N := by
  intro heq
  obtain ⟨hm1, hcop⟩ := goldbachC8ProductSupport_one_lt_and_coprime hm
  have hdvd : m ∣ N := ⟨q, heq.symm⟩
  exact (ne_of_gt hm1) (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvd)

theorem goldbachC8Product_mul_lt_iff_le {N m q : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) : m * q < N ↔ m * q ≤ N :=
  ⟨le_of_lt, fun h => lt_of_le_of_ne h (goldbachC8Product_mul_ne_self hm)⟩

theorem goldbachC8Product_coprime_of_dvd_output {N m q d : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) (hle : m * q ≤ N)
    (hd : d ∣ N - m * q) : Nat.Coprime m d := by
  apply Nat.coprime_of_dvd'
  intro p hp hpm hpd
  have hpN : p ∣ N := by
    have hadd := Nat.dvd_add (dvd_mul_of_dvd_left hpm q) (hpd.trans hd)
    simpa [Nat.add_sub_of_le hle] using hadd
  exact (prime_not_dvd_of_coprime
    (goldbachC8ProductSupport_one_lt_and_coprime hm).2 hp hpm hpN).elim

/-- The inverse residue is coupled to the product label, including modulus one. -/
theorem goldbachB8PlusAtom_output_dvd_iff_residue
    {N d : ℕ} {x : Σ _rs : ℕ × ℕ, ℕ}
    (hx : x ∈ goldbachB8PlusAtoms N) :
    d ∣ goldbachB8PlusOutput N x ↔
      Nat.Coprime (goldbachC8Prod x.1) d ∧
        (x.2 : ZMod d) = (N : ZMod d) * (goldbachC8Prod x.1 : ZMod d)⁻¹ := by
  obtain ⟨hrs, _, hlt⟩ := mem_goldbachB8PlusAtoms_iff.mp hx
  have hm : goldbachC8Prod x.1 ∈ goldbachC8ProductSupport N :=
    Finset.mem_image.mpr ⟨x.1, hrs, rfl⟩
  have hmod : d ∣ goldbachB8PlusOutput N x ↔ Nat.ModEq d (goldbachC8Prod x.1 * x.2) N := by
    rw [goldbachB8PlusOutput, Nat.modEq_iff_dvd' hlt.le]
  constructor
  · intro hd
    have hc := goldbachC8Product_coprime_of_dvd_output hm hlt.le hd
    have hz : (goldbachC8Prod x.1 : ZMod d) * (x.2 : ZMod d) = (N : ZMod d) := by
      simpa using (ZMod.natCast_eq_natCast_iff _ _ d).2 (hmod.mp hd)
    refine ⟨hc, ?_⟩
    calc
      (x.2 : ZMod d) =
          ((goldbachC8Prod x.1 : ZMod d) * (goldbachC8Prod x.1 : ZMod d)⁻¹) * x.2 := by
            rw [ZMod.coe_mul_inv_eq_one _ hc, one_mul]
      _ = ((goldbachC8Prod x.1 : ZMod d) * x.2) *
          (goldbachC8Prod x.1 : ZMod d)⁻¹ := by ac_rfl
      _ = _ := by rw [hz]
  · rintro ⟨hc, hq⟩
    apply hmod.mpr
    apply (ZMod.natCast_eq_natCast_iff _ _ d).1
    push_cast
    rw [hq]
    calc
      (goldbachC8Prod x.1 : ZMod d) * ((N : ZMod d) * (goldbachC8Prod x.1 : ZMod d)⁻¹)
          = (N : ZMod d) * ((goldbachC8Prod x.1 : ZMod d) *
              (goldbachC8Prod x.1 : ZMod d)⁻¹) := by ac_rfl
      _ = _ := by rw [ZMod.coe_mul_inv_eq_one _ hc, mul_one]

private noncomputable def B8PanDivisorQFiber (N d m : ℕ) : Finset ℕ :=
  (range (N + 1)).filter fun q => q.Prime ∧ m * q < N ∧ d ∣ N - m * q

private theorem B8PanDivisorQFiber_card {N d m : ℕ}
    (hm : m ∈ goldbachC8ProductSupport N) :
    ((B8PanDivisorQFiber N d m).card : ℝ) =
      if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0 := by
  by_cases hc : Nat.Coprime m d
  · rw [if_pos hc]
    congr 1
    unfold B8PanDivisorQFiber primesInAPBelow
    congr 1
    ext q
    simp only [mem_filter]
    constructor
    · rintro ⟨hq, hp, hlt, hd⟩
      have hmod := (Nat.modEq_iff_dvd' hlt.le).mpr hd
      exact ⟨hq, hp, hlt.le, hmod.trans (Nat.mod_modEq N d).symm⟩
    · rintro ⟨hq, hp, hle, hmod⟩
      exact ⟨hq, hp, (goldbachC8Product_mul_lt_iff_le hm).mpr hle,
        (Nat.modEq_iff_dvd' hle).mp (hmod.trans (Nat.mod_modEq N d))⟩
  · rw [if_neg hc]
    have he : B8PanDivisorQFiber N d m = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      obtain ⟨_, _, hlt, hd⟩ := Finset.mem_filter.mp hq
      exact hc (goldbachC8Product_coprime_of_dvd_output hm hlt.le hd)
    simp [he]

theorem goldbachB8PlusDivCount_eq_product_sum (N d : ℕ) :
    (goldbachB8PlusDivCount N d : ℝ) =
      ∑ m ∈ goldbachC8ProductSupport N,
        if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0 := by
  have hsigma : (goldbachB8PlusAtoms N).filter (fun x => d ∣ goldbachB8PlusOutput N x) =
      (goldbachS4Pairs N ((N : ℝ) ^ ((3 : ℝ) / 11))).sigma
        (fun rs => B8PanDivisorQFiber N d (goldbachC8Prod rs)) := by
    ext x
    constructor
    · intro hx
      obtain ⟨ha, hdout⟩ := Finset.mem_filter.mp hx
      obtain ⟨hrs, hq⟩ := Finset.mem_sigma.mp ha
      obtain ⟨hqrange, hp, hlt⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_sigma.mpr ⟨hrs, Finset.mem_filter.mpr ⟨hqrange, hp, hlt, hdout⟩⟩
    · intro hx
      obtain ⟨hrs, hq⟩ := Finset.mem_sigma.mp hx
      obtain ⟨hqrange, hp, hlt, hdout⟩ := Finset.mem_filter.mp hq
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_sigma.mpr ⟨hrs, Finset.mem_filter.mpr ⟨hqrange, hp, hlt⟩⟩, hdout⟩
  unfold goldbachB8PlusDivCount
  rw [hsigma, Finset.card_sigma, Nat.cast_sum]
  calc
    _ = ∑ m ∈ goldbachC8ProductSupport N, ((B8PanDivisorQFiber N d m).card : ℝ) := by
      symm
      apply Finset.sum_image
      intro rs hrs tu htu heq
      exact goldbachC8Prod_injOn hrs htu heq
    _ = _ := Finset.sum_congr rfl (fun _ hm => B8PanDivisorQFiber_card hm)

theorem goldbachC8CoeffReal_sum_eq_support
    {N A₁ A₂ : ℕ} (f : ℕ → ℝ)
    (hsupp : goldbachC8ProductSupport N ⊆ Ioc A₁ A₂) :
    ∑ m ∈ Ioc A₁ A₂, goldbachC8CoeffReal N m * f m =
      ∑ m ∈ goldbachC8ProductSupport N, f m := by
  calc
    _ = ∑ m ∈ goldbachC8ProductSupport N, goldbachC8CoeffReal N m * f m := by
      symm
      apply Finset.sum_subset hsupp
      intro m _ hm
      rw [goldbachC8CoeffReal_eq_zero_of_not_mem hm, zero_mul]
    _ = _ := Finset.sum_congr rfl (fun _ hm => by
      rw [goldbachC8CoeffReal_eq_one_of_mem hm, one_mul])

noncomputable def goldbachB8PlusPanAPPrefixCount (N A₁ A₂ d : ℕ) : ℝ :=
  ∑ m ∈ Ioc A₁ A₂, goldbachC8CoeffReal N m *
    (if Nat.Coprime m d then (primesInAPBelow N m d (N % d) : ℝ) else 0)

theorem goldbachB8PlusDivCount_eq_panAPPrefixCount
    {N A₁ A₂ d : ℕ} (_hd : 1 ≤ d) (_hdN : Nat.Coprime d N)
    (hsupp : goldbachC8ProductSupport N ⊆ Ioc A₁ A₂) :
    (goldbachB8PlusDivCount N d : ℝ) = goldbachB8PlusPanAPPrefixCount N A₁ A₂ d := by
  rw [goldbachB8PlusDivCount_eq_product_sum, goldbachB8PlusPanAPPrefixCount,
    goldbachC8CoeffReal_sum_eq_support _ hsupp]

theorem goldbachB8PlusRemainder_eq_panError
    {N A₁ A₂ d : ℕ} (_hd : 1 ≤ d) (_hdN : Nat.Coprime d N)
    (hsupp : goldbachC8ProductSupport N ⊆ Ioc A₁ A₂) :
    goldbachB8PlusRemainder N d =
      liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d (N % d) (goldbachC8CoeffReal N) := by
  unfold liuMainPanCoprimeIntervalSum
  have heq :
      (∑ m ∈ Ioc A₁ A₂,
        if Nat.Coprime m d then goldbachC8CoeffReal N m *
          liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N m d (N % d) else 0) =
      ∑ m ∈ goldbachC8ProductSupport N,
        if Nat.Coprime m d then
          liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N m d (N % d) else 0 := by
    simpa only [mul_ite, mul_zero] using
      goldbachC8CoeffReal_sum_eq_support
        (fun m => if Nat.Coprime m d then
          liuScaledAPError (liuLogarithmicIntegral (2 / Real.log 2)) N m d (N % d) else 0) hsupp
  rw [heq, goldbachB8PlusRemainder, goldbachB8PlusDivCount_eq_product_sum,
    goldbachB8PlusGatedMainMass, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hc : Nat.Coprime m d
  · simp only [if_pos hc, liuScaledAPError]
  · simp only [if_neg hc, zero_div, sub_self]

theorem goldbachC8ProductSupport_mem_panInterval {N : ℕ} {B : ℝ}
    (hN : 2 ≤ N) (hlow : liuPanSourceIntervalLower N B < liuSourceZ10 N) :
    goldbachC8ProductSupport N ⊆
      Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  intro m hm
  obtain ⟨hml, hmu⟩ := goldbachC8ProductSupport_bounds hN hm
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hleft : (liuPanSourceIntervalLower N B : ℝ) < m := by
    calc
      (liuPanSourceIntervalLower N B : ℝ) < liuSourceZ10 N := by exact_mod_cast hlow
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      _ < (N : ℝ) ^ (6 / 11 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt hN1 (by norm_num)
      _ ≤ m := hml
  exact Finset.mem_Ioc.mpr ⟨by exact_mod_cast hleft, Nat.le_floor hmu⟩

theorem goldbachC8ProductSupport_eventually_panInterval (B : ℝ) :
    ∀ᶠ N : ℕ in atTop, goldbachC8ProductSupport N ⊆
      Ioc (liuPanSourceIntervalLower N B) (liuPanSourceIntervalUpper N) := by
  filter_upwards [eventually_liuPanSourceIntervalLower_lt_liuSourceZ10 B,
    eventually_ge_atTop (2 : ℕ)] with N hl hN
  exact goldbachC8ProductSupport_mem_panInterval hN hl

private theorem B8Pan_maxL_nonneg
    (N A₁ A₂ d : ℕ) (f : ℕ → ℝ) :
    0 ≤ liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
      N A₁ A₂ d f := by
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  split_ifs with h
  · have hmem := Finset.max'_mem
      ((unitResidues d).image (fun l =>
        |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
          N A₁ A₂ d l f|)) (Finset.image_nonempty.mpr h)
    obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hmem
    rw [← hl]
    exact abs_nonneg _
  · exact le_rfl

theorem goldbachB8PlusRemainder_abs_le_maxL
    {N A₁ A₂ d : ℕ} (hd : 1 ≤ d) (hdN : Nat.Coprime d N)
    (hsupp : goldbachC8ProductSupport N ⊆ Ioc A₁ A₂) :
    |goldbachB8PlusRemainder N d| ≤
      liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d (goldbachC8CoeffReal N) := by
  rw [goldbachB8PlusRemainder_eq_panError hd hdN hsupp]
  have hl : N % d ∈ unitResidues d := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt N (by omega)),
      (ZMod.coprime_mod_iff_coprime N d).2 hdN.symm⟩
  have hS : (unitResidues d).Nonempty := ⟨N % d, hl⟩
  unfold liuMainPanCoprimeIntervalMaxL
  dsimp only
  rw [dif_pos hS]
  exact Finset.le_max'
    ((unitResidues d).image (fun l =>
      |liuMainPanCoprimeIntervalSum (liuLogarithmicIntegral (2 / Real.log 2))
        N A₁ A₂ d l (goldbachC8CoeffReal N)|))
    _ (Finset.mem_image.mpr ⟨N % d, hl, rfl⟩)

theorem goldbachB8PlusRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
          |goldbachB8PlusRemainder N d| ≤ C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, Na, ha⟩ :=
    liuMainPanCoprimeIntervalMaxL_boundedAggregate_log_saving U hU
  obtain ⟨Ns, hs⟩ := eventually_atTop.mp (goldbachC8ProductSupport_eventually_panInterval B)
  refine ⟨C, hC, B, hB, max 4 (max Na Ns), le_max_left _ _, ?_⟩
  intro N hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNs : Ns ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let A₁ := liuPanSourceIntervalLower N B
  let A₂ := liuPanSourceIntervalUpper N
  let F := fun d => liuMainPanCoprimeIntervalMaxL (liuLogarithmicIntegral (2 / Real.log 2))
    N A₁ A₂ d (goldbachC8CoeffReal N)
  calc
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N), F d := by
      apply Finset.sum_le_sum
      intro d hd
      obtain ⟨hdI, hdc⟩ := Finset.mem_filter.mp hd
      exact goldbachB8PlusRemainder_abs_le_maxL (Finset.mem_Icc.mp hdI).1 hdc (hs N hNs)
    _ ≤ ∑ d ∈ Icc 1 (panModulusCutoff N B), F d :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun d _ _ => B8Pan_maxL_nonneg N A₁ A₂ d _)
    _ ≤ _ := ha N hNa A₁ A₂ (goldbachC8CoeffReal N)
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg N) _))
      (le_of_lt (log_rpow_lt_liuPanSourceIntervalLower N B))
      (abs_goldbachC8CoeffReal_le_one N)

theorem goldbachC8ProductSupport_coprime_of_dvd_prodPrimes
    {N m d : ℕ} {Z : ℝ} (hm : m ∈ goldbachC8ProductSupport N)
    (hZ : Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11)) (hd : d ∣ goldbachB10ProdPrimes N Z) :
    Nat.Coprime m d := by
  obtain ⟨rs, hrs, rfl⟩ := Finset.mem_image.mp hm
  have h := mem_goldbachS4Pairs_iff.mp hrs
  apply Nat.coprime_of_dvd'
  intro p hp hpm hpd
  have hpZ := prime_dvd_goldbachB10ProdPrimes_lt hp (hpd.trans hd)
  have hps : (N : ℝ) ^ ((3 : ℝ) / 11) ≤ (rs.2 : ℝ) :=
    h.2.2.2.1.trans (by exact_mod_cast h.2.2.2.2.1)
  rcases hp.dvd_mul.mp hpm with hpr | hps'
  · have heq := (Nat.prime_dvd_prime_iff_eq hp h.1).mp hpr
    subst p
    exact ((not_lt_of_ge (hZ.trans h.2.2.2.1)) hpZ).elim
  · have heq := (Nat.prime_dvd_prime_iff_eq hp h.2.1).mp hps'
    subst p
    exact ((not_lt_of_ge (hZ.trans hps)) hpZ).elim

theorem goldbachB8PlusGatedMainMass_eq_mainMass_of_dvd_prodPrimes
    {N d : ℕ} {Z : ℝ} (hZ : Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11))
    (hd : d ∣ goldbachB10ProdPrimes N Z) :
    goldbachB8PlusGatedMainMass N d = goldbachB8PlusMainMass N := by
  apply Finset.sum_congr rfl
  intro m hm
  rw [if_pos (goldbachC8ProductSupport_coprime_of_dvd_prodPrimes hm hZ hd)]

theorem goldbachB8PlusBoundingSieve_rem_eq_remainder
    {N d : ℕ} (hEven : Even N) {Z : ℝ}
    (hZ : Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11)) (hd : d ∣ goldbachB10ProdPrimes N Z) :
    (goldbachB8PlusBoundingSieve N hEven Z).rem d = goldbachB8PlusRemainder N d := by
  rw [goldbachB8PlusBoundingSieve_rem_eq_divCount_sub, goldbachB8PlusRemainder,
    goldbachB8PlusGatedMainMass_eq_mainMass_of_dvd_prodPrimes hZ hd]

/-- The actual sieve remainder contract for the next upper-sieve step. -/
theorem goldbachB8PlusBoundingSieve_remainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, 4 ≤ N₀ ∧
      ∀ N : ℕ, N₀ ≤ N → ∀ hEven : Even N, ∀ Z : ℝ,
        Z ≤ (N : ℝ) ^ ((3 : ℝ) / 11) →
        ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter
          (fun d => d ∣ goldbachB10ProdPrimes N Z),
          |(goldbachB8PlusBoundingSieve N hEven Z).rem d| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨C, hC, B, hB, N₀, hN₀, hrem⟩ := goldbachB8PlusRemainder_log_saving U hU
  refine ⟨C, hC, B, hB, N₀, hN₀, ?_⟩
  intro N hN hEven Z hZ
  calc
    _ = ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter
        (fun d => d ∣ goldbachB10ProdPrimes N Z), |goldbachB8PlusRemainder N d| := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [goldbachB8PlusBoundingSieve_rem_eq_remainder hEven hZ (Finset.mem_filter.mp hd).2]
    _ ≤ ∑ d ∈ (Icc 1 (panModulusCutoff N B)).filter (fun d => Nat.Coprime d N),
        |goldbachB8PlusRemainder N d| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro d hd
        obtain ⟨hdI, hdP⟩ := Finset.mem_filter.mp hd
        exact Finset.mem_filter.mpr ⟨hdI, goldbachB10_dvd_prodPrimes_coprime_N hdP⟩
      · intro d _ _
        exact abs_nonneg _
    _ ≤ _ := hrem N hN

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig