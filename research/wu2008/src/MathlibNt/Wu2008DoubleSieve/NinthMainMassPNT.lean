import MathlibNt.Wu2008DoubleSieve.NinthMainMassQuadrature

/-!
# Sharp PNT transfer for the actual ninth prime-profile mass

The accepted prime error envelope tends to zero. Balanced support puts
every prefix endpoint above N^k2, so one threshold gives an arbitrary
relative 1+tau bound simultaneously for every support product.
-/

namespace Wu2008DoubleSieve

open Finset Set Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem P9_card_le_primePi {N m : ℕ} (hm : m ∈ ninthProductSupport N) :
    ((P9 N m).card : ℝ) ≤ primePi ((N : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast ninthProductSupport_pos hm
  have hsub : P9 N m ⊆ (Finset.Icc 0 ⌊(N : ℝ) / m⌋₊).filter Nat.Prime := by
    intro c hc
    have hs : (m : ℝ) * c ≤ N := by exact_mod_cast (P9_size hm hc).le
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor
      ((le_div_iff₀ hm0).mpr (by simpa only [mul_comm] using hs))⟩, P9_prime hc⟩
  calc
    _ ≤ (((Finset.Icc 0 ⌊(N : ℝ) / m⌋₊).filter Nat.Prime).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ = _ := by
      rw [primePi_eq_sum_indicator]
      simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem ninthMain_prefix_lower {N m : ℕ} (hN : 512 ≤ N)
    (hm : m ∈ ninthProductSupport N) :
    ninthProfileW N ≤ (N : ℝ) / m := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast ninthProductSupport_pos hm
  apply (le_div_iff₀ hm0).mpr
  have hprod : ninthProfileW N * (N : ℝ) ^ (1 - ninthProfileK2) = N := by
    unfold ninthProfileW
    rw [← rpow_add hN0, add_sub_cancel, rpow_one]
  calc
    ninthProfileW N * m ≤ ninthProfileW N * (N : ℝ) ^ (1 - ninthProfileK2) :=
      mul_le_mul_of_nonneg_left (ninthProductSupport_balanced hN hm).2 (by
        exact rpow_nonneg hN0.le _)
    _ = N := hprod

theorem P9_sharp_prefix_uniform {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop, ∀ m ∈ ninthProductSupport N,
      ((P9 N m).card : ℝ) ≤ (1 + τ) * ((N : ℝ) / m / log ((N : ℝ) / m)) := by
  have hk : 0 < ninthProfileK2 := by norm_num [ninthProfileK2]
  have hwTop : Tendsto ninthProfileW atTop atTop :=
    (tendsto_rpow_atTop hk).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (512 : ℕ),
    hwTop.eventually (eventually_ge_atTop primeErrorStart),
    (tendsto_primeErrorEnvelope.comp hwTop).eventually (gt_mem_nhds hτ)]
    with N hN hstart henv
  intro m hm
  have hx := ninthMain_prefix_lower hN hm
  have hx2 := (ninth_fixed_cutoffs_ge hN).1.trans hx
  have hx0 : 0 < (N : ℝ) / m := by linarith
  have hlog : 0 < log ((N : ℝ) / m) := log_pos (by linarith)
  have hpnt := primePi_error_le hstart hx
  have he := (le_abs_self _).trans hpnt
  have herr := mul_le_mul_of_nonneg_right henv.le (div_nonneg hx0.le hlog.le)
  have hprefix := P9_card_le_primePi hm
  dsimp only [Function.comp_apply] at herr
  nlinarith

theorem X9_eq_pair_profiles (N : ℕ) :
    X9 N = ∑ t ∈ ninthPairs N (ninthProfileW N) (ninthProfileU N),
      ((P9 N (ninthPairProduct t)).card : ℝ) := by
  unfold X9 ninthProductSupport M9
  rw [sum_image (ninthPairProduct_injOn N (ninthProfileW N) (ninthProfileU N))]

theorem ninthMain_pair_prefix_normalization {N : ℕ} (hN : 512 ≤ N) {t : ℕ × ℕ}
    (ht : t ∈ ninthPairs N (ninthProfileW N) (ninthProfileU N)) :
    (N : ℝ) / ninthPairProduct t / log ((N : ℝ) / ninthPairProduct t) =
      ((N : ℝ) / log N) *
        (ninthMainKernel (ninthMainCoordinate N t.1) (ninthMainCoordinate N t.2) /
          ((t.1 : ℝ) * t.2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  obtain ⟨ha, hb, _⟩ := mem_lowerPairs_source.mp (mem_filter.mp ht).1
  have ha0 : (0 : ℝ) < t.1 := by exact_mod_cast ha.pos
  have hb0 : (0 : ℝ) < t.2 := by exact_mod_cast hb.pos
  obtain ⟨hpa, hpb⟩ := ninthMain_pair_mem (by omega) ht
  have hca := ninthMain_coordinate_mem (by omega) hpa
  have hp := ninthMain_parameters
  have hca' : ninthMainCoordinate N t.1 ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
    constructor <;> linarith [hca.1, hca.2]
  have hcb := ninthMain_coordinate_mem (by omega) hpb
  have htop := ninthMainTop_bounds hca'
  have hcb' : ninthMainCoordinate N t.2 ∈ Set.Icc (1 / 10 : ℝ) (1 / 2) := by
    constructor <;> linarith [hcb.1, hcb.2, htop.2.2]
  have hd := ninthMainKernel_den_pos hca' hcb'
  rw [ninthMainClip, min_eq_left hca.2] at hd
  have hd0 : 0 < 1 - ninthMainCoordinate N t.1 - ninthMainCoordinate N t.2 := by linarith
  have he : log ((N : ℝ) / ninthPairProduct t) =
      log N * (1 - ninthMainCoordinate N t.1 - ninthMainCoordinate N t.2) := by
    simp only [ninthPairProduct, Nat.cast_mul]
    rw [log_div hN0.ne' (mul_pos ha0 hb0).ne', log_mul ha0.ne' hb0.ne']
    unfold ninthMainCoordinate
    field_simp
    ring
  rw [he, ninthMainKernel, ninthMainClip, min_eq_left hca.2]
  simp only [ninthPairProduct, Nat.cast_mul]
  field_simp

/-- The sharp finite-sum predecessor, with the actual profile mass on the
left and no PNT or multiplicity hypothesis supplied by the caller. -/
theorem X9_sharp_pair_bound {τ : ℝ} (hτ : 0 < τ) :
    ∀ᶠ N : ℕ in atTop,
      X9 N ≤ (1 + τ) * ((N : ℝ) / log N) * ninthMainPairSum N := by
  filter_upwards [P9_sharp_prefix_uniform hτ, eventually_ge_atTop (512 : ℕ)]
    with N hpnt hN
  rw [X9_eq_pair_profiles]
  calc
    _ ≤ ∑ t ∈ ninthPairs N (ninthProfileW N) (ninthProfileU N),
        (1 + τ) * ((N : ℝ) / log N) *
          (ninthMainKernel (ninthMainCoordinate N t.1) (ninthMainCoordinate N t.2) /
            ((t.1 : ℝ) * t.2)) := by
      apply sum_le_sum
      intro t ht
      have h := hpnt (ninthPairProduct t) (mem_image.mpr ⟨t, ht, rfl⟩)
      rw [ninthMain_pair_prefix_normalization hN ht] at h
      simpa only [mul_assoc] using h
    _ = _ := by rw [← mul_sum]; rfl

end Wu2008DoubleSieve
