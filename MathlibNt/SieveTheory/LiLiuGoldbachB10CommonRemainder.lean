import MathlibNt.SieveTheory.LiLiuGoldbachB10MainWeight
import MathlibNt.SieveTheory.LiLiuGoldbachB10MainGateBudget
import MathlibNt.SieveTheory.LiLiuGoldbachB10PanDistribution
import MathlibNt.SieveTheory.LiuPanPrimitiveLedgerAssembly
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

noncomputable section

open scoped BigOperators
open Classical Finset Filter
open MathlibNt.SieveTheory.LiuWeight

namespace MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig

noncomputable local instance instDecidableB10CommonRemainder (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The actual common main-term remainder, with the divisor gate removed from the main mass. -/
noncomputable def goldbachB10CommonRemainder
    (N d : ℕ) (ε b c : ℝ) : ℝ :=
  ((goldbachB10DivisorAtoms N d ε b c).card : ℝ) -
    goldbachB10MainMass N ε b c / d.totient

/-- Instantiation of the generic gate-loss budget to the actual floor-endpoint B10 main weight. -/
theorem goldbachB10MainWeight_sum_gateLoss_le_logCube
    (ε γ : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
      (1 : ℝ) / 18 < β → ∀ Q : ℕ, Q ≤ N →
        ∑ d ∈ Finset.Icc 1 Q,
          gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d ≤
            (4 * ((N : ℝ) / Real.log 2) / ((N : ℝ) ^ β)) *
              (1 + Real.log (N : ℝ)) ^ 3 := by
  obtain ⟨N₀, hN₀, hweight⟩ := goldbachB10MainWeight_bounds_eventually ε γ hε hεlt hγ
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN β hβ Q hQ
  have hN2 : 2 ≤ N := hN₀.trans hN
  have hb : 0 < (N : ℝ) ^ β := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact Real.rpow_pos_of_pos hNpos β
  have hT : 0 ≤ (N : ℝ) / Real.log 2 := by
    positivity
  simpa using
    (sum_gateLoss_le_logCube (Q := Q) (b := (N : ℝ) ^ β) (c := (N : ℝ) ^ γ)
      (T := (N : ℝ) / Real.log 2) (w := goldbachB10MainWeight N ε)
      hQ hN2 hb hT (fun _ hm => (hweight N hN β hβ _ hm).2))

private theorem B10CommonRemainder_one_add_log_cube_le
    {N : ℕ} (hlog : 1 ≤ Real.log (N : ℝ)) :
    (1 + Real.log (N : ℝ)) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 := by
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hstep : 1 + Real.log (N : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    linarith
  calc
    (1 + Real.log (N : ℝ)) ^ 3 ≤ (2 * Real.log (N : ℝ)) ^ 3 := by
      exact pow_le_pow_left₀ (by linarith) hstep 3
    _ = 8 * Real.log (N : ℝ) ^ 3 := by
      ring

private theorem B10CommonRemainder_log_payment_eventually (U : ℝ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      1 ≤ Real.log (N : ℝ) ∧
        (32 / Real.log 2) * Real.log (N : ℝ) ^ (U + 3) ≤
          (N : ℝ) ^ ((1 : ℝ) / 18) := by
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (U + 3) (show 0 < (1 : ℝ) / 18 by norm_num)).bound
      (show 0 < Real.log 2 / 32 by
        have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        positivity)
  have hsmall' : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (U + 3) ≤
        (Real.log 2 / 32) * x ^ ((1 : ℝ) / 18) := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hx0 : 0 ≤ x := by linarith
    simpa only [Real.norm_of_nonneg (Real.rpow_nonneg hlogx _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] using hx
  have hlog :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (1 : ℝ))
  have hnat : ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log (N : ℝ) ∧
        (32 / Real.log 2) * Real.log (N : ℝ) ^ (U + 3) ≤
          (N : ℝ) ^ ((1 : ℝ) / 18) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hsmall', hlog] with N hsmallN hlogN
    have hmul :
        (32 / Real.log 2) * Real.log (N : ℝ) ^ (U + 3) ≤
          (32 / Real.log 2) * ((Real.log 2 / 32) * (N : ℝ) ^ ((1 : ℝ) / 18)) := by
      exact mul_le_mul_of_nonneg_left hsmallN (by positivity)
    have hrewrite :
        (32 / Real.log 2) * ((Real.log 2 / 32) * (N : ℝ) ^ ((1 : ℝ) / 18)) =
          (N : ℝ) ^ ((1 : ℝ) / 18) := by
      have hlog2 : Real.log 2 ≠ 0 := by
        exact ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      field_simp [hlog2]
    exact ⟨hlogN, hrewrite ▸ hmul⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hnat
  refine ⟨max 2 N₀, le_max_left _ _, ?_⟩
  intro N hN
  exact hN₀ N ((le_max_right _ _).trans hN)

/-- The actual main-weight gate loss is uniformly absorbed by any prescribed log-saving,
without requiring beta to stay a fixed distance away from `1 / 18`. -/
theorem goldbachB10MainWeight_sum_gateLoss_log_saving
    (ε γ U : ℝ) (hε : 0 < ε) (hεlt : ε < 1) (hγ : γ < (1 : ℝ) / 3) (_hU : 0 < U) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
      (1 : ℝ) / 18 < β → ∀ Q : ℕ, Q ≤ N →
        ∑ d ∈ Finset.Icc 1 Q,
          gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d ≤
            (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨N₁, hN₁, hcube⟩ :=
    goldbachB10MainWeight_sum_gateLoss_le_logCube ε γ hε hεlt hγ
  obtain ⟨N₂, hN₂, hpay⟩ := B10CommonRemainder_log_payment_eventually U
  refine ⟨max N₁ N₂, le_trans hN₁ (le_max_left _ _), ?_⟩
  intro N hN β hβ Q hQ
  have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
  have hbase : 1 ≤ (N : ℝ) := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hpow_beta :
      (N : ℝ) ^ ((1 : ℝ) / 18) ≤ (N : ℝ) ^ β := by
    exact Real.rpow_le_rpow_of_exponent_le hbase hβ.le
  have hcube_bound := hcube N hN₁' β hβ Q hQ
  rcases hpay N hN₂' with ⟨hlogN, hpayN⟩
  have hlog0 : 0 ≤ Real.log (N : ℝ) := by linarith
  have hlogpos : 0 < Real.log (N : ℝ) := by linarith
  have hpowUpos : 0 < Real.log (N : ℝ) ^ U := Real.rpow_pos_of_pos hlogpos U
  have hpowBetapos : 0 < (N : ℝ) ^ β := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    exact Real.rpow_pos_of_pos hNpos β
  have hlog_cube :
      (1 + Real.log (N : ℝ)) ^ 3 ≤ 8 * Real.log (N : ℝ) ^ 3 :=
    B10CommonRemainder_one_add_log_cube_le hlogN
  have hpayBeta :
      (32 / Real.log 2) * Real.log (N : ℝ) ^ (U + 3) ≤ (N : ℝ) ^ β :=
    hpayN.trans hpow_beta
  have haux :
      (32 / Real.log 2) * Real.log (N : ℝ) ^ 3 ≤
        (N : ℝ) ^ β / Real.log (N : ℝ) ^ U := by
    apply (le_div_iff₀ hpowUpos).2
    calc
      (32 / Real.log 2) * Real.log (N : ℝ) ^ 3 * Real.log (N : ℝ) ^ U =
          (32 / Real.log 2) * (Real.log (N : ℝ) ^ (3 : ℝ) * Real.log (N : ℝ) ^ U) := by
            rw [← Real.rpow_natCast]
            ring_nf
      _ = (32 / Real.log 2) * Real.log (N : ℝ) ^ (3 + U) := by
            conv_rhs => rw [Real.rpow_add hlogpos]
      _ = (32 / Real.log 2) * Real.log (N : ℝ) ^ (U + 3) := by
            rw [add_comm]
      _ ≤ (N : ℝ) ^ β := hpayBeta
  have hfrac :
      ((32 / Real.log 2) * Real.log (N : ℝ) ^ 3) / (N : ℝ) ^ β ≤
        1 / Real.log (N : ℝ) ^ U := by
    exact (div_le_iff₀ hpowBetapos).2 (by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using haux)
  have hmul :
      (N : ℝ) * (((32 / Real.log 2) * Real.log (N : ℝ) ^ 3) / (N : ℝ) ^ β) ≤
        (N : ℝ) * (1 / Real.log (N : ℝ) ^ U) := by
    exact mul_le_mul_of_nonneg_left hfrac (by positivity)
  calc
    ∑ d ∈ Finset.Icc 1 Q,
        gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d
      ≤ (4 * ((N : ℝ) / Real.log 2) / ((N : ℝ) ^ β)) * (1 + Real.log (N : ℝ)) ^ 3 :=
        hcube_bound
    _ ≤ (4 * ((N : ℝ) / Real.log 2) / ((N : ℝ) ^ β)) *
        (8 * Real.log (N : ℝ) ^ 3) := by
          exact mul_le_mul_of_nonneg_left hlog_cube (by positivity)
    _ = (N : ℝ) * (((32 / Real.log 2) * Real.log (N : ℝ) ^ 3) / (N : ℝ) ^ β) := by
      ring
    _ ≤ (N : ℝ) * (1 / Real.log (N : ℝ) ^ U) := hmul
    _ = (N : ℝ) / Real.log (N : ℝ) ^ U := by
      ring

/-- Exact bridge from the production Pan remainder to the common remainder, retaining
the signed deleted main-term contribution. -/
theorem goldbachB10CommonRemainder_eq_panPrefixRemainder_sub_deletedMain
    {N A₁ A₂ d : ℕ} {ε b c : ℝ}
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Finset.Ioc A₁ A₂) :
    goldbachB10CommonRemainder N d ε b c =
      goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c -
        (∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d,
          goldbachB10MainWeight N ε m) / d.totient := by
  classical
  have hsplit₀ :
      (∑ m ∈ (goldbachC10ProductSupport N b c).filter (fun m : ℕ => Nat.Coprime m d),
          goldbachB10MainWeight N ε m) +
        ∑ m ∈ (goldbachC10ProductSupport N b c).filter (fun m : ℕ => ¬Nat.Coprime m d),
          goldbachB10MainWeight N ε m =
        ∑ m ∈ goldbachC10ProductSupport N b c, goldbachB10MainWeight N ε m := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not
        (goldbachC10ProductSupport N b c)
        (fun m : ℕ => Nat.Coprime m d)
        (fun m => goldbachB10MainWeight N ε m))
  have hgood :
      ∑ m ∈ (goldbachC10ProductSupport N b c).filter (fun m : ℕ => Nat.Coprime m d),
          goldbachB10MainWeight N ε m =
        ∑ m ∈ goldbachC10ProductSupport N b c,
          if Nat.Coprime m d then goldbachB10MainWeight N ε m else 0 := by
    rw [← Finset.sum_filter]
  have hsplit :
      ∑ m ∈ goldbachC10ProductSupport N b c, goldbachB10MainWeight N ε m =
        (∑ m ∈ goldbachC10ProductSupport N b c,
            if Nat.Coprime m d then goldbachB10MainWeight N ε m else 0) +
          ∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d,
            goldbachB10MainWeight N ε m := by
    rw [← hsplit₀, hgood]
  unfold goldbachB10CommonRemainder goldbachB10PanPrefixRemainder goldbachB10MainMass
  rw [goldbachB10PanMainPrefix_sub_eq_gatedMainWeight hsupp, hsplit]
  ring

/-- Triangle-inequality comparison between the common remainder and the production
Pan-prefix remainder plus the explicit gate-loss term. -/
theorem abs_goldbachB10CommonRemainder_le
    {N A₁ A₂ d : ℕ} {ε b c : ℝ}
    (hsupp : ∀ ⦃m : ℕ⦄, m ∈ goldbachC10ProductSupport N b c → m ∈ Finset.Ioc A₁ A₂) :
    |goldbachB10CommonRemainder N d ε b c| ≤
      |goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c| +
        gateLoss N b c (goldbachB10MainWeight N ε) d := by
  rw [goldbachB10CommonRemainder_eq_panPrefixRemainder_sub_deletedMain hsupp, sub_eq_add_neg]
  simpa [gateLoss_eq, div_eq_mul_inv, abs_neg, mul_comm, mul_left_comm, mul_assoc] using
    (abs_add_le
      (goldbachB10PanPrefixRemainder N d A₁ A₂ ε b c)
      (-((∑ m ∈ goldbachC10ProductSupport N b c with ¬Nat.Coprime m d,
          goldbachB10MainWeight N ε m) / d.totient)))

/-- Final actual common-remainder bound, obtained by combining the production Pan
remainder estimate with the finite gate-loss budget for the removed non-coprime main mass. -/
theorem goldbachB10CommonRemainder_log_saving (U : ℝ) (hU : 0 < U) :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℝ, 0 ≤ B ∧ ∀ ε γ : ℝ,
      0 < ε → ε < 1 → γ < (1 : ℝ) / 3 →
      ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
        (1 : ℝ) / 18 < β →
        ∑ d ∈ (Finset.Icc 1 (panModulusCutoff N (B + 1))).filter (fun d => Nat.Coprime d N),
          |goldbachB10CommonRemainder N d ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)| ≤
            C * (N : ℝ) / Real.log (N : ℝ) ^ U := by
  obtain ⟨Cpan, hCpan, B, hB, hpan⟩ := goldbachB10PanPrefixRemainder_log_saving U hU
  refine ⟨Cpan + 1, by linarith, B, hB, ?_⟩
  intro ε γ hε hεlt hγ
  obtain ⟨Npan, hNpan, hpanN⟩ := hpan ε γ hε hεlt hγ
  obtain ⟨Ngate, hNgate, hgate⟩ :=
    goldbachB10MainWeight_sum_gateLoss_log_saving ε γ U hε hεlt hγ hU
  obtain ⟨Ngeo, hNgeo, hgeo⟩ :=
    B10PanGeometry_consumer_threshold ε γ B U 2 hε hεlt hγ hB hU.le
  have hB1 : 0 ≤ B + 1 := by linarith
  obtain ⟨Ncond, hcond⟩ := eventually_atTop.mp (eventually_pan_conductor_bounds (B + 1) hB1)
  refine ⟨max Npan (max Ngate (max Ngeo Ncond)), le_trans hNpan (le_max_left _ _), ?_⟩
  intro N hN β hβ
  have hNpan' : Npan ≤ N := (le_max_left _ _).trans hN
  have hNrest : max Ngate (max Ngeo Ncond) ≤ N := (le_max_right _ _).trans hN
  have hNgate' : Ngate ≤ N := (le_max_left _ _).trans hNrest
  have hNrest' : max Ngeo Ncond ≤ N := (le_max_right _ _).trans hNrest
  have hNgeo' : Ngeo ≤ N := (le_max_left _ _).trans hNrest'
  have hNcond' : Ncond ≤ N := (le_max_right _ _).trans hNrest'
  rcases hgeo N hNgeo' with ⟨_, _, _, _, _, _, _, _, _, _, hsupp⟩
  rcases hcond N hNcond' with ⟨_, _, _, _, hDN⟩
  let D := panModulusCutoff N (B + 1)
  let T := (Finset.Icc 1 D).filter (fun d => Nat.Coprime d N)
  have hpanBound := hpanN N hNpan' β hβ
  have hgateBound :
      ∑ d ∈ Finset.Icc 1 D,
        gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d ≤
          (N : ℝ) / Real.log (N : ℝ) ^ U := by
    simpa [D] using hgate N hNgate' β hβ D hDN
  have hgateFiltered :
      ∑ d ∈ T,
        gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d ≤
          (N : ℝ) / Real.log (N : ℝ) ^ U := by
    calc
      ∑ d ∈ T,
          gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d
        ≤ ∑ d ∈ Finset.Icc 1 D,
            gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d := by
              refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
              · intro d hd
                exact (Finset.mem_filter.mp hd).1
              · intro d hd hdt
                exact abs_nonneg _
      _ ≤ (N : ℝ) / Real.log (N : ℝ) ^ U := hgateBound
  calc
    ∑ d ∈ T, |goldbachB10CommonRemainder N d ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)|
      ≤ ∑ d ∈ T,
          (|goldbachB10PanPrefixRemainder N d (liuPanSourceIntervalLower N B)
            (B10PanGeometryUpperWindow N γ) ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)| +
            gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d) := by
              apply Finset.sum_le_sum
              intro d hd
              exact abs_goldbachB10CommonRemainder_le (hsupp β hβ)
    _ = (∑ d ∈ T,
          |goldbachB10PanPrefixRemainder N d (liuPanSourceIntervalLower N B)
            (B10PanGeometryUpperWindow N γ) ε ((N : ℝ) ^ β) ((N : ℝ) ^ γ)|) +
        ∑ d ∈ T,
          gateLoss N ((N : ℝ) ^ β) ((N : ℝ) ^ γ) (goldbachB10MainWeight N ε) d := by
            rw [Finset.sum_add_distrib]
    _ ≤ Cpan * (N : ℝ) / Real.log (N : ℝ) ^ U + (N : ℝ) / Real.log (N : ℝ) ^ U := by
      exact add_le_add hpanBound hgateFiltered
    _ = (Cpan + 1) * (N : ℝ) / Real.log (N : ℝ) ^ U := by
      ring

end MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig