import MathlibNt.Wu2004MeanValue.SmallBV

/-!
# Small-coefficient Wu errors with fully independent real endpoints

For a logarithmically small coefficient carrier it suffices to use the same
ordinary AP prefix maximum for each coefficient. We deliberately pay the
whole cardinality, rather than rescaling BV separately at every coefficient.
Extra logarithmic saving pays this loss. Endpoints, coefficients and supports
can all be selected independently for each modulus.
-/

namespace Wu2004MeanValue

open Classical Finset Filter
open scoped BigOperators Topology
open AnalyticNumberTheory.Sieve
open AnalyticNumberTheory.LargeSieve
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418
open MathlibNt.SieveTheory.LiuWeight

noncomputable section

/-- The inverse residue is retained. Richert's frozen normalization is
already Wu's, so only rounding the prime endpoint costs `1/(log 2 * phi d)`. -/
theorem small_ebar_le_prime_prefix (N d b m : ℕ) (r : ℝ)
    (hd : 0 < d) (hm : 0 < m) (hmd : m.Coprime d) (hb : b.Coprime d)
    (hr : 2 ≤ r) (hrN : r ≤ N) :
    |ebar ((m : ℝ) * r) d b m| ≤
      primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d := by
  have hr0 : 0 ≤ r := by linarith
  have hlo : 2 ≤ ⌊r⌋₊ := Nat.le_floor hr
  have hhi : ⌊r⌋₊ ≤ N := by exact_mod_cast (Nat.floor_le hr0).trans hrN
  have hres : natInvMod d m * b % d ∈ unitResidues d := by
    exact mem_filter.mpr ⟨mem_range.mpr (Nat.mod_lt _ hd),
      (ZMod.isUnit_iff_coprime _ _).mp (isUnit_natInvMod_mul_residue hd hmd hb)⟩
  have hprefix := (abs_primeAPError_le_residueMax (x := ⌊r⌋₊) hres).trans
    (primeAPResidueMaxError_le_prefixMax (mem_Icc.mpr ⟨hlo, hhi⟩))
  have hshort := PanPrincipal.abs_li_sub_le_short 0
    (show (2 : ℝ) ≤ ⌊r⌋₊ by exact_mod_cast hlo)
    (Nat.floor_le hr0) (Nat.lt_floor_add_one r).le
  have heq : ebar ((m : ℝ) * r) d b m =
      primeAPError ⌊r⌋₊ d (natInvMod d m * b % d) +
        (wuLi ⌊r⌋₊ - wuLi r) / Nat.totient d := by
    rw [ebar_moving_inverse r d b m hr0 hm hmd]
    unfold primeAPError Bombieri1965Richert418.logarithmicIntegral wuLi
    unfold primesInAP MathlibNt.SieveTheory.BombieriVinogradov.primesInAP
    ring
  rw [heq]
  calc
    _ ≤ |primeAPError ⌊r⌋₊ d (natInvMod d m * b % d)| +
        |(wuLi ⌊r⌋₊ - wuLi r) / Nat.totient d| := abs_add_le _ _
    _ ≤ primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d := by
      apply add_le_add hprefix
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Nat.totient d)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      simpa only [wuLi, abs_sub_comm] using hshort

theorem small_ebar_sum_le_prefix (N d b : ℕ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (F : ℝ) (hd : 0 < d) (hb : b.Coprime d)
    (hF : 0 ≤ F) (hS : ∀ m ∈ S, 1 ≤ m)
    (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ r m ≤ N) :
    |∑ m ∈ S.filter (fun m => m.Coprime d),
        f m * ebar ((m : ℝ) * r m) d b m| ≤
      F * S.card * (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d) := by
  have hp : 0 ≤ primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d :=
    add_nonneg (primeAPPrefixMaxError_nonneg N d) (by positivity)
  calc
    _ ≤ ∑ m ∈ S.filter (fun m => m.Coprime d),
        |f m * ebar ((m : ℝ) * r m) d b m| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ S.filter (fun m => m.Coprime d),
        F * (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d) := by
      apply sum_le_sum
      intro m hm
      obtain ⟨hmS, hmd⟩ := mem_filter.mp hm
      rw [abs_mul]
      exact mul_le_mul (hf m hmS)
        (small_ebar_le_prime_prefix N d b m (r m) hd (hS m hmS) hmd hb
          (hr m hmS).1 (hr m hmS).2) (abs_nonneg _) hF
    _ ≤ (S.card : ℝ) *
        (F * (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d)) := by
      simp only [sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast card_filter_le S (fun m => m.Coprime d)) (mul_nonneg hF hp)
    _ = _ := by ring

/-- The genuine moduluswise supremum includes independent coefficient
supports and weights, reduced residues and real prime endpoints. -/
def smallModulusSup (N : ℕ) (J F : ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ),
    (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log N ^ J) ∧
    (∀ m ∈ S, |f m| ≤ F) ∧
    (∀ m ∈ S, 2 ≤ r m ∧ r m ≤ N) ∧ b.Coprime d ∧
    v = |∑ m ∈ S.filter (fun m => m.Coprime d),
      f m * ebar ((m : ℝ) * r m) d b m|})

theorem small_support_card_le (S : Finset ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ M) :
    (S.card : ℝ) ≤ M := by
  have hsub : S ⊆ Icc 1 ⌊M⌋₊ := fun m hm =>
    mem_Icc.mpr ⟨(hS m hm).1, Nat.le_floor (hS m hm).2⟩
  have hc := card_le_card hsub
  simp only [Nat.card_Icc, Nat.add_sub_cancel] at hc
  exact (by exact_mod_cast hc : (S.card : ℝ) ≤ ⌊M⌋₊).trans (Nat.floor_le hM)

theorem smallModulusSup_le_prefix (N d : ℕ) (J F : ℝ)
    (hN : 2 ≤ N) (hd : 0 < d) (hF : 0 ≤ F) :
    smallModulusSup N J F d ≤ F * Real.log N ^ J *
      (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d) := by
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hp : 0 ≤ primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d :=
    add_nonneg (primeAPPrefixMaxError_nonneg N d) (by positivity)
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · positivity
  · obtain ⟨S, f, r, b, hS, hf, hr, hb, rfl⟩ := hv
    exact (small_ebar_sum_le_prefix N d b S f r F hd hb hF
      (fun m hm => (hS m hm).1) hf hr).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (small_support_card_le S _ (Real.rpow_nonneg hlog J) hS) hF) hp)

/-- Full weighted small-coefficient W1/W3 source norm at a natural ambient
endpoint. The real endpoints can vary independently with both `d` and `m`;
indeed they are only required to lie in `[2,N]`, a larger domain than `N/m`.
All constants precede all choices, and the supremum stays inside the sum. -/
theorem small_weighted_sup_log_saving (A J F : ℝ)
    (hA : 0 < A) (hJ : 0 ≤ J) (hF : 0 ≤ F) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ∀ Q : ℕ, Q ≤ panModulusCutoff N B →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * smallModulusSup N J F d) ≤
        C * N / Real.log N ^ A := by
  obtain ⟨B, C, hB, hC, N₁, hBV⟩ :=
    small_weighted_prime_prefix_log_saving (A + J) (by linarith)
  obtain ⟨L, hL, hphi⟩ := wu_reciprocal_totient_sum_bound
  refine ⟨B, F * (C + L / Real.log 2) + 1, hB, by positivity, ?_⟩
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop (max 3 N₁),
    PanPrincipal.eventually_log_rpow_le_rpow (A + J + 6) 1 (by norm_num)]
    with N hN hpay
  intro Q hQ
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN₁ : N₁ ≤ N := (le_max_right _ _).trans hN
  have hQN := hQ.trans
    (MathlibNt.SieveTheory.Richert1969.panModulusCutoff_le_endpoint N B hN3 hB.le)
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hpay' : Real.log N ^ (J + 6) ≤ (N : ℝ) / Real.log N ^ A := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hlog A)).mpr
    rw [← Real.rpow_add hlog]
    simpa only [Real.rpow_one, show J + 6 + A = A + J + 6 by ring] using hpay
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d *
        (F * Real.log N ^ J *
          (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d)) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (smallModulusSup_le_prefix N d J F hN2 (mem_Icc.mp hd).1 hF)
        (wuModulusWeight_nonneg d)
    _ = F * Real.log N ^ J *
        ((∑ d ∈ Icc 1 Q, wuModulusWeight d * primeAPPrefixMaxError N d) +
          (1 / Real.log 2) * ∑ d ∈ Icc 1 Q, wuModulusWeight d / Nat.totient d) := by
      simp only [mul_add, mul_sum]
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro d _
      ring
    _ ≤ F * Real.log N ^ J *
        (C * N / Real.log N ^ (A + J) +
          (1 / Real.log 2) * (L * Real.log N ^ (6 : ℝ))) := by
      gcongr
      · exact hBV N hN₁ Q hQ
      · exact hphi N (by exact_mod_cast hN2) Q (by exact_mod_cast hQN)
    _ = F * C * ((N : ℝ) / Real.log N ^ A) +
        (F * L / Real.log 2) * Real.log N ^ (J + 6) := by
      rw [Real.rpow_add hlog, Real.rpow_add hlog]
      field_simp
    _ ≤ F * C * ((N : ℝ) / Real.log N ^ A) +
        (F * L / Real.log 2) * ((N : ℝ) / Real.log N ^ A) := by
      gcongr
    _ ≤ (F * (C + L / Real.log 2) + 1) * N / Real.log N ^ A := by
      calc
        _ = (F * (C + L / Real.log 2)) * ((N : ℝ) / Real.log N ^ A) := by ring
        _ ≤ (F * (C + L / Real.log 2) + 1) * ((N : ℝ) / Real.log N ^ A) :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

end
end Wu2004MeanValue