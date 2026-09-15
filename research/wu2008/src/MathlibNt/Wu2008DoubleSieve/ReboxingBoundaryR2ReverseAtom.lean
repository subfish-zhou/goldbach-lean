import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryR2Atom

/-!
# The reverse s2 cutoff error

Wu04 source lines 1046--1065 and 1128--1149, with the reverse inequality
announced at lines 979--982. The lower cutoff is treated directly: its
prime window is `[cutoff(s2),p)`, not the already paid s1 window.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology

/-- The reverse window has polynomial height and the same logarithmic
span control. This uses only the actual parameter bracket, not continuity
of any finite-threshold improvement coefficient. -/
theorem reboxing_reverse_replacement_window_bounds {D p a b : ℝ}
    (hD : 0 < D) (hp : 1 < p) (ha : 1 ≤ a)
    (hau : a ≤ log D / log p - 1) (hub : log D / log p - 1 ≤ b)
    (hb : b ≤ 10) :
    (D / p) ^ (1 / b) ≤ p ∧
      p ^ (1 / 10 : ℝ) ≤ (D / p) ^ (1 / b) ∧
      log (p / ((D / p) ^ (1 / b))) ≤ (b - a) * log p := by
  have hp0 : 0 < p := by linarith
  have hLp : 0 < log p := log_pos hp
  have hb1 : 1 ≤ b := ha.trans (hau.trans hub)
  have hb0 : 0 < b := by linarith
  have hZ0 : 0 < (D / p) ^ (1 / b) := rpow_pos_of_pos (div_pos hD hp0) _
  have he : log ((D / p) ^ (1 / b)) =
      ((log D / log p - 1) / b) * log p := by
    rw [log_rpow (div_pos hD hp0), log_div hD.ne' hp0.ne']
    field_simp
  have hratio : (log D / log p - 1) / b ≤ 1 := (div_le_one hb0).2 hub
  have hratiolo : (1 / 10 : ℝ) ≤ (log D / log p - 1) / b := by
    apply (le_div_iff₀ hb0).2
    linarith
  have hle : (D / p) ^ (1 / b) ≤ p := by
    apply (log_le_log_iff hZ0 hp0).1
    rw [he]
    nlinarith
  have hlo : p ^ (1 / 10 : ℝ) ≤ (D / p) ^ (1 / b) := by
    apply (log_le_log_iff (rpow_pos_of_pos hp0 _) hZ0).1
    rw [log_rpow hp0, he]
    nlinarith
  refine ⟨hle, hlo, ?_⟩
  rw [log_div hp0.ne' hZ0.ne', he]
  have hdiv := div_le_self (sub_nonneg.mpr hub) hb1
  have hid : 1 - (log D / log p - 1) / b =
      (b - (log D / log p - 1)) / b := by field_simp
  have hquot : 1 - (log D / log p - 1) / b ≤ b - a := by
    rw [hid]
    linarith
  nlinarith

/-- One threshold bounds every actual reverse cutoff atom in every
source box and every geometric block. The carrier remains `P(dpN)`,
including the repeated-prime lane. -/
theorem reboxingR2Reverse_atom_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ B : ℝ, 0 < B ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ r →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t ((j : ℝ) - 1))
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j),
      let b := reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i j
      0 ≤ (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) b) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ) ∧
        (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) b) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ) ≤
        ((N : ℝ) / ((d : ℝ) * p)) * (B / log (N : ℝ) ^ (5 : ℕ)) := by
  let α := δ ^ (k + 2) / 10
  let K := (200 + 20 * (k : ℝ)) / δ ^ (k + 1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T1, hT1⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T2, _, hT2⟩ := reboxing_parameter_mesh_eventually k hδ hδhi
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp (hlogt.eventually (eventually_ge_atTop 1))
  refine ⟨2 * K / α + 2, by positivity, max 4 (max T1 (max T2 T3)), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht r hr j hj hjr d hd p hp
  dsimp only
  have hN4 : 4 ≤ N := (le_max_left _ _).trans hN
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN3 : T3 ≤ N := by omega
  have hL1 := hT3 N hN3
  have hL : 0 < log (N : ℝ) := by linarith
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let D := Q / d
  let a := reboxingS1 q Δ t j
  let b := reboxingS2 q Δ t i j
  obtain ⟨hΔ, hq, hmesh⟩ := hT2 N hN2 i Δ V hb
  have hq0 : 0 < q := by dsimp [q, Q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hQ0 : 0 < Q := rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 l)
  have hD := reboxing_support_level_bounds hQ0.le hΔ0 hV hd
  have hD0 : 0 < D := hq0.trans_le hD.1
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hαhi : reboxingAlpha q Δ t j ≤ q ^ (1 / s) :=
    (hm (by exact_mod_cast hjr)).trans hr
  have hdom := reboxing_parameter_domain hq hΔ hs hst ht hj1 hαhi hmesh
  have hprev0 : q ^ (1 / t) ≤ reboxingAlpha q Δ t ((j : ℝ) - 1) := by
    simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j - 1 by linarith)
  have ht0 : 0 < t := by linarith
  have hprev1 : 1 < reboxingAlpha q Δ t ((j : ℝ) - 1) :=
    (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hprev0
  have hp' := mem_primeWindow.mp hp
  have hpar := reboxing_parameter_bounds hq hΔ hD.1 hD.2 hprev1 hp'.2.2.1 hp'.2.2.2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hwindow := reboxing_reverse_replacement_window_bounds hD0 hp1 hdom.1
    hpar.1 hpar.2 hdom.2.2.2
  have hwidth := reboxing_source_parameter_width (show 2 ≤ N by omega) hδ hδhi hL1 hb
    ht0 ht hj1
  have hheightp : (N : ℝ) ^ (δ ^ (k + 2)) ≤ p :=
    (reboxing_endpoint_lower (show 2 ≤ N by omega) hδ hδhi hb
      ht0 ht hprev0).trans hp'.2.2.1
  have hheight : (N : ℝ) ^ α ≤ (D / p) ^ (1 / b) := by
    calc
      _ = ((N : ℝ) ^ (δ ^ (k + 2))) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul (by linarith : (0 : ℝ) ≤ N)]
        congr 1
        dsimp [α]
        ring
      _ ≤ (p : ℝ) ^ (1 / 10 : ℝ) :=
        rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hheightp (by norm_num)
      _ ≤ _ := hwindow.2.1
  have hpN : (p : ℝ) ≤ N := by
    have hDcut := reboxing_support_cutoff_bounds hQ0.le hΔ0 hV (show 0 < s by linarith) hd
    have hQN : Q ≤ N := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNreal.le
        (show 1 / 2 - δ ≤ 1 by linarith)
    have hd0 := (reboxing_support_product_bounds hΔ0 (fun l => (hV l).le) hd).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have hDN : D ≤ N := (div_le_self hQ0.le hd1).trans hQN
    have hD1 : 1 ≤ D := hq.le.trans hD.1
    calc
      _ ≤ reboxingAlpha q Δ t j := hp'.2.2.2.le
      _ ≤ q ^ (1 / s) := hαhi
      _ ≤ D ^ (1 / s) := hDcut.1
      _ ≤ D ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hD1
          ((one_div_le_one_div_of_le (by norm_num) (by linarith : 1 ≤ s)).trans_eq (by norm_num))
      _ = D := rpow_one D
      _ ≤ N := hDN
  have hlogp : log (p : ℝ) ≤ log (N : ℝ) :=
    log_le_log (by linarith : (0 : ℝ) < p) hpN
  have hlogwidth : log (p / ((D / p) ^ (1 / b))) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    calc
      _ ≤ (b - a) * log (p : ℝ) := hwindow.2.2
      _ ≤ (K / log (N : ℝ) ^ (5 : ℕ)) * log (N : ℝ) :=
        mul_le_mul hwidth.2 hlogp (log_pos hp1).le (by positivity)
      _ = _ := by field_simp
  have hmass := hT1 N hN1 ((D / p) ^ (1 / b)) (p : ℝ) hheight hwindow.1 hlogwidth
  have hcut : wuLocalCutoff N δ (d * p) b = (D / p) ^ (1 / b) := by
    simp only [wuLocalCutoff, Nat.cast_mul, div_div, D, Q]
  have hd0 := (reboxing_support_product_bounds hΔ0 (fun l => (hV l).le) hd).1
  have hf := reboxing_source_difference_le_prime_mass hN4 he
    (Nat.mul_pos hd0 hp'.1.pos) hwindow.1
  rw [hcut]
  refine ⟨hf.1, hf.2.trans ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (N : ℝ) / (d * p : ℕ) by positivity)

end Wu2008DoubleSieve
