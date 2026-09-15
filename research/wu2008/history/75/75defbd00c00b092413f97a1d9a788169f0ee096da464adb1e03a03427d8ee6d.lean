import MathlibNt.Wu2004MeanValue.SmallSource

/-!
# Real ambient endpoint and arbitrary fixed endpoint ratio

A common natural prefix `ceil(max(1,K) * x)` contains every admissible real
prime endpoint. The small carrier is paid by its logarithmic cardinality.
This avoids coefficient-dependent BV thresholds altogether.
-/

namespace Wu2004MeanValue

open Classical Finset
open scoped BigOperators
open MathlibNt.SieveTheory.LiuWeight
open AnalyticNumberTheory.LargeSieve.Bombieri1965Richert418

noncomputable section

theorem small_sum_le_sup (N d b : ℕ) (J F : ℝ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (hN : 2 ≤ N) (hd : 0 < d) (hF : 0 ≤ F)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log N ^ J)
    (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ r m ≤ N) (hb : b.Coprime d) :
    |∑ m ∈ S.filter (fun m => m.Coprime d),
      f m * ebar ((m : ℝ) * r m) d b m| ≤ smallModulusSup N J F d := by
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hp : 0 ≤ primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d :=
    add_nonneg (primeAPPrefixMaxError_nonneg N d) (by positivity)
  unfold smallModulusSup
  apply le_csSup
  · refine ⟨F * Real.log N ^ J *
      (primeAPPrefixMaxError N d + (1 / Real.log 2) / Nat.totient d), ?_⟩
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · positivity
    · obtain ⟨T, g, t, a, hT, hg, ht, ha, rfl⟩ := hv
      exact (small_ebar_sum_le_prefix N d a T g t F hd ha hF
        (fun m hm => (hT m hm).1) hg ht).trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (small_support_card_le T _ (Real.rpow_nonneg hlog J) hT) hF) hp)
  · exact Set.mem_insert_of_mem _ ⟨S, f, r, b, hS, hf, hr, hb, rfl⟩

def smallRealModulusSup (x J F K : ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ (S : Finset ℕ) (f r : ℕ → ℝ) (b : ℕ),
    (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log x ^ J) ∧
    (∀ m ∈ S, |f m| ≤ F) ∧
    (∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) ∧ b.Coprime d ∧
    v = |∑ m ∈ S.filter (fun m => m.Coprime d),
      f m * ebar ((m : ℝ) * r m) d b m|})

theorem small_real_domain_to_natural (x J K : ℝ) (N : ℕ)
    (hx : 1 ≤ x) (hJ : 0 ≤ J) (hxN : x ≤ N) (hKN : K * x ≤ N)
    (S : Finset ℕ) (r : ℕ → ℝ)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log x ^ J)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) :
    (∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log N ^ J) ∧
      (∀ m ∈ S, 2 ≤ r m ∧ r m ≤ N) := by
  have hlog : Real.log x ≤ Real.log N := Real.log_le_log (by linarith) hxN
  constructor
  · intro m hm
    exact ⟨(hS m hm).1, (hS m hm).2.trans
      (Real.rpow_le_rpow (Real.log_nonneg hx) hlog hJ)⟩
  · intro m hm
    refine ⟨(hr m hm).1, ?_⟩
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (hS m hm).1
    have hrr : r m ≤ (m : ℝ) * r m := by
      nlinarith [(hr m hm).1]
    exact hrr.trans ((hr m hm).2.trans hKN)

theorem small_real_sup_le_natural (x J F K : ℝ) (N d : ℕ)
    (hx : 1 ≤ x) (hJ : 0 ≤ J) (hF : 0 ≤ F)
    (hN : 2 ≤ N) (hd : 0 < d) (hxN : x ≤ N) (hKN : K * x ≤ N) :
    smallRealModulusSup x J F K d ≤ smallModulusSup N J F d := by
  apply csSup_le ⟨0, Set.mem_insert _ _⟩
  intro v hv
  rcases Set.mem_insert_iff.mp hv with rfl | hv
  · simpa using small_sum_le_sup N d 1 J F ∅ 0 0 hN hd hF
      (by simp) (by simp) (by simp) (Nat.coprime_one_left d)
  · obtain ⟨S, f, r, b, hS, hf, hr, hb, rfl⟩ := hv
    obtain ⟨hSN, hrN⟩ :=
      small_real_domain_to_natural x J K N hx hJ hxN hKN S r hS hr
    exact small_sum_le_sup N d b J F S f r hN hd hF hSN hf hrN hb

/-- The complete logarithmically small coefficient segment in the exact Wu
norm, with real ambient `x` and every fixed positive endpoint ratio `K`.
All parameters `B,C,x₀` precede every support, coefficient, residue and
independent modulus/coefficient-dependent endpoint selection. -/
theorem small_real_weighted_sup_log_saving (A J F K : ℝ)
    (hA : 0 < A) (hJ : 0 ≤ J) (hF : 0 ≤ F) (_hK : 0 < K) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d * smallRealModulusSup x J F K d) ≤
        C * x / Real.log x ^ A := by
  obtain ⟨B, C, hB, hC, N₀, hsource⟩ := small_weighted_sup_log_saving A J F hA hJ hF
  let L := max 1 K
  have hL : 1 ≤ L := le_max_left _ _
  have hKL : K ≤ L := le_max_right _ _
  refine ⟨B + 1, C * (L + 1), by linarith, by positivity,
    max (max 3 N₀) (max (L + 1) (Real.exp (2 ^ B))), ?_⟩
  intro x hx Q hQ
  have hx3 : 3 ≤ x := (le_max_left 3 _).trans ((le_max_left _ _).trans hx)
  have hxN₀ : (N₀ : ℝ) ≤ x :=
    (le_max_right 3 _).trans ((le_max_left _ _).trans hx)
  have hxL : L + 1 ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxexp : Real.exp (2 ^ B) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hlogB : (2 : ℝ) ^ B ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  let N := ⌈L * x⌉₊
  have hLN : L * x ≤ (N : ℝ) := Nat.le_ceil _
  have hxN : x ≤ (N : ℝ) := by nlinarith
  have hKN : K * x ≤ (N : ℝ) := (mul_le_mul_of_nonneg_right hKL hx0.le).trans hLN
  have hN2 : 2 ≤ N := by
    have : (2 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN₀ : N₀ ≤ N := by exact_mod_cast hxN₀.trans hxN
  have hNupper : (N : ℝ) ≤ (L + 1) * x := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ L * x by positivity)
    dsimp [N]
    linarith
  have hNxx : (N : ℝ) ≤ x ^ 2 := by nlinarith
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hloglo : Real.log x ≤ Real.log N := Real.log_le_log hx0 hxN
  have hloghi : Real.log (N : ℝ) ≤ 2 * Real.log x := by
    calc
      _ ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hNxx
      _ = _ := by rw [Real.log_pow]; norm_num
  have hpow : Real.log (N : ℝ) ^ B ≤ Real.log x ^ (B + 1) := by
    calc
      _ ≤ (2 * Real.log x) ^ B := Real.rpow_le_rpow hlogN.le hloghi hB.le
      _ = (2 : ℝ) ^ B * Real.log x ^ B := Real.mul_rpow (by norm_num) hlog0.le
      _ ≤ Real.log x * Real.log x ^ B :=
        mul_le_mul_of_nonneg_right hlogB (Real.rpow_nonneg hlog0.le _)
      _ = _ := by rw [Real.rpow_add hlog0, Real.rpow_one]; ring
  have hcut : Q ≤ panModulusCutoff N B := by
    apply Nat.le_floor
    change (Q : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) / Real.log N ^ B
    calc
      _ ≤ Real.sqrt x / Real.log x ^ (B + 1) := hQ
      _ ≤ Real.sqrt N / Real.log N ^ B := by
        apply div_le_div₀ (Real.sqrt_nonneg (N : ℝ))
          (Real.sqrt_le_sqrt hxN) (Real.rpow_pos_of_pos hlogN B) hpow
      _ = _ := by rw [Real.sqrt_eq_rpow]
  calc
    _ ≤ ∑ d ∈ Icc 1 Q, wuModulusWeight d * smallModulusSup N J F d := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left
        (small_real_sup_le_natural x J F K N d (by linarith) hJ hF hN2
          (mem_Icc.mp hd).1 hxN hKN) (wuModulusWeight_nonneg d)
    _ ≤ C * N / Real.log N ^ A := hsource N hN₀ Q hcut
    _ ≤ C * ((L + 1) * x) / Real.log x ^ A := by
      apply div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hNupper hC.le)
        (Real.rpow_pos_of_pos hlog0 A)
        (Real.rpow_le_rpow hlog0.le hloglo hA.le)
    _ = _ := by ring

theorem small_real_sum_le_sup (x J F K : ℝ) (d b : ℕ) (S : Finset ℕ)
    (f r : ℕ → ℝ) (hx : 2 ≤ x) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hd : 0 < d)
    (hS : ∀ m ∈ S, 1 ≤ m ∧ (m : ℝ) ≤ Real.log x ^ J)
    (hf : ∀ m ∈ S, |f m| ≤ F)
    (hr : ∀ m ∈ S, 2 ≤ r m ∧ (m : ℝ) * r m ≤ K * x) (hb : b.Coprime d) :
    |∑ m ∈ S.filter (fun m => m.Coprime d),
      f m * ebar ((m : ℝ) * r m) d b m| ≤ smallRealModulusSup x J F K d := by
  let N := ⌈max 1 K * x⌉₊
  have hx0 : 0 ≤ x := by linarith
  have hLN : max 1 K * x ≤ (N : ℝ) := Nat.le_ceil _
  have hxN : x ≤ (N : ℝ) := by
    have := mul_le_mul_of_nonneg_right (le_max_left 1 K) hx0
    linarith
  have hKN : K * x ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_max_right 1 K) hx0).trans hLN
  have hN : 2 ≤ N := by exact_mod_cast hx.trans hxN
  unfold smallRealModulusSup
  apply le_csSup
  · refine ⟨smallModulusSup N J F d, ?_⟩
    intro v hv
    rcases Set.mem_insert_iff.mp hv with rfl | hv
    · simpa using small_sum_le_sup N d 1 J F ∅ 0 0 hN hd hF
        (by simp) (by simp) (by simp) (Nat.coprime_one_left d)
    · obtain ⟨T, g, t, a, hT, hg, ht, ha, rfl⟩ := hv
      obtain ⟨hTN, htN⟩ :=
        small_real_domain_to_natural x J K N (by linarith) hJ hxN hKN T t hT ht
      exact small_sum_le_sup N d a J F T g t hN hd hF hTN hg htN ha
  · exact Set.mem_insert_of_mem _ ⟨S, f, r, b, hS, hf, hr, hb, rfl⟩

/-- Selected-family form. Even the support and coefficient sequence may vary
with `d`; in particular this includes a common Wu sequence `f(m)` and
arbitrary independent `r(d,m)`. The coefficient sum is inside the absolute
value, and the actual coprimality and inverse-residue coupling are retained. -/
theorem small_real_selected_ebar_log_saving (A J F K : ℝ)
    (hA : 0 < A) (hJ : 0 ≤ J) (hF : 0 ≤ F) (hK : 0 < K) :
    ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∃ x₀ : ℝ, ∀ x ≥ x₀,
      ∀ Q : ℕ, (Q : ℝ) ≤ Real.sqrt x / Real.log x ^ B →
      ∀ (S : ℕ → Finset ℕ) (f r : ℕ → ℕ → ℝ) (b : ℕ → ℕ),
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 1 ≤ m ∧ (m : ℝ) ≤ Real.log x ^ J) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, |f d m| ≤ F) →
      (∀ d ∈ Icc 1 Q, ∀ m ∈ S d, 2 ≤ r d m ∧ (m : ℝ) * r d m ≤ K * x) →
      (∀ d ∈ Icc 1 Q, (b d).Coprime d) →
      (∑ d ∈ Icc 1 Q, wuModulusWeight d *
        |∑ m ∈ (S d).filter (fun m => m.Coprime d),
          f d m * ebar ((m : ℝ) * r d m) d (b d) m|) ≤ C * x / Real.log x ^ A := by
  obtain ⟨B, C, hB, hC, x₁, hbound⟩ := small_real_weighted_sup_log_saving A J F K hA hJ hF hK
  refine ⟨B, C, hB, hC, max 2 x₁, ?_⟩
  intro x hx Q hQ S f r b hS hf hr hb
  have hx2 : 2 ≤ x := (le_max_left _ _).trans hx
  have hxx₁ : x₁ ≤ x := (le_max_right _ _).trans hx
  refine (sum_le_sum ?_).trans (hbound x hxx₁ Q hQ)
  intro d hd
  exact mul_le_mul_of_nonneg_left
    (small_real_sum_le_sup x J F K d (b d) (S d) (f d) (r d) hx2 hJ hF
      (mem_Icc.mp hd).1 (hS d hd) (hf d hd) (hr d hd) (hb d hd))
    (wuModulusWeight_nonneg d)

end
end Wu2004MeanValue
