import MathlibNt.Wu2008DoubleSieve.ReboxingBoundaryCount
import MathlibNt.Wu2008DoubleSieve.ReboxingParameterWidth

/-!
# Uniform actual R2 atom producer

Wu04 (3.19), source lines 1128--1149. The threshold precedes every legal
source box and every moving prime block. The final summation of these
atom estimates over the geometric blocks is not claimed here.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology

theorem reboxing_replacement_window_bounds {D p a b : ℝ}
    (hD : 0 < D) (hp : 1 < p) (ha : 1 ≤ a)
    (hau : a ≤ log D / log p - 1) (hub : log D / log p - 1 ≤ b) :
    p ≤ (D / p) ^ (1 / a) ∧
      log (((D / p) ^ (1 / a)) / p) ≤ (b - a) * log p := by
  have hp0 : 0 < p := by linarith
  have hLp : 0 < log p := log_pos hp
  have ha0 : 0 < a := by linarith
  have hZ0 : 0 < (D / p) ^ (1 / a) := rpow_pos_of_pos (div_pos hD hp0) _
  have he : log ((D / p) ^ (1 / a)) =
      ((log D / log p - 1) / a) * log p := by
    rw [log_rpow (div_pos hD hp0), log_div hD.ne' hp0.ne']
    field_simp
  have hratio : 1 ≤ (log D / log p - 1) / a := (one_le_div ha0).2 hau
  have hloglo : log p ≤ log ((D / p) ^ (1 / a)) := by rw [he]; nlinarith
  have hle : p ≤ (D / p) ^ (1 / a) := (log_le_log_iff hp0 hZ0).1 hloglo
  refine ⟨hle, ?_⟩
  rw [log_div hZ0.ne' hp0.ne', he]
  have hdiv := div_le_self (sub_nonneg.mpr hau) ha
  have hid : (log D / log p - 1) / a - 1 = ((log D / log p - 1) - a) / a := by
    field_simp
  have hquot : (log D / log p - 1) / a - 1 ≤ b - a := by
    rw [hid]
    linarith
  nlinarith

/-- The actual selected-modulus Buchstab identity and positive-complement
counting give the ordinary N/(m*q) majorant, with no coprimality of the
already selected prime and the original convolution assumed. -/
theorem reboxing_source_difference_le_prime_mass {N m : ℕ} {z w : ℝ}
    (hN : 4 ≤ N) (he : Even N) (hm : 0 < m) (hzw : z ≤ w) :
    0 ≤ (sourceSieveCount N m (m * N) z : ℝ) -
        (sourceSieveCount N m (m * N) w : ℝ) ∧
      (sourceSieveCount N m (m * N) z : ℝ) -
        (sourceSieveCount N m (m * N) w : ℝ) ≤
      ((N : ℝ) / m) * ∑ q ∈ primeWindow N z w, (1 : ℝ) / q := by
  have hid := source_buchstab_selected_modulus N m hzw
  have hdiff :
      (sourceSieveCount N m (m * N) z : ℝ) -
        (sourceSieveCount N m (m * N) w : ℝ) =
        ∑ q ∈ primeWindow (m * N) z w,
          (sourceSieveCount N (m * q) ((m * q) * N) (q : ℝ) : ℝ) := by linarith
  rw [hdiff]
  refine ⟨sum_nonneg (fun q _ => by simp only [sourceSieveCount, Int.cast_natCast]; positivity), ?_⟩
  have hsub : primeWindow (m * N) z w ⊆ primeWindow N z w := by
    intro q hq
    obtain ⟨hp, hc, hlo, hhi⟩ := mem_primeWindow.mp hq
    exact mem_primeWindow.mpr ⟨hp, (Nat.coprime_mul_iff_right.mp hc).2, hlo, hhi⟩
  calc
    _ ≤ ∑ q ∈ primeWindow (m * N) z w, (N : ℝ) / ((m : ℝ) * q) := by
      apply sum_le_sum
      intro q hq
      simpa only [Nat.cast_mul] using reboxing_source_count_le_divisor ((m * q) * N) (q : ℝ)
        hN he (Nat.mul_pos hm (mem_primeWindow.mp hq).1.pos)
    _ ≤ ∑ q ∈ primeWindow N z w, (N : ℝ) / ((m : ℝ) * q) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => by positivity)
    _ = _ := by
      rw [mul_sum]
      apply sum_congr rfl
      intro q _
      ring

/-- Uniform PNT and literal carrier bound for every actual replacement
atom, with its actual `s1` cutoff. No atom-dependent eventual threshold
is introduced. This is a predecessor, not an aggregate R2 payment. -/
theorem reboxingR2_atom_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ B : ℝ, 0 < B ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 → ∀ r : ℕ,
      (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) Δ t r ≤
          ((N : ℝ) ^ (1 / 2 - δ) / (∏ j, V j)) ^ (1 / s)) →
      ∀ j : ℕ, 1 ≤ j → j ≤ r →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t ((j : ℝ) - 1))
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j),
      let a := reboxingS1 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j
      0 ≤ (sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) a) : ℝ) ∧
        (sourceSieveCount N (d * p) ((d * p) * N) (p : ℝ) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) a) : ℝ) ≤
        ((N : ℝ) / ((d : ℝ) * p)) * (B / log (N : ℝ) ^ (5 : ℕ)) := by
  let α := δ ^ (k + 2)
  let K := (200 + 20 * (k : ℝ)) / δ ^ (k + 1)
  have hα : 0 < α := pow_pos hδ _
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
  have hwindow := reboxing_replacement_window_bounds hD0 hp1 hdom.1 hpar.1 hpar.2
  have hwidth := reboxing_source_parameter_width (show 2 ≤ N by omega) hδ hδhi hL1 hb
    (show 0 < t by linarith) ht hj1
  have hheight : (N : ℝ) ^ α ≤ p :=
    (reboxing_endpoint_lower (show 2 ≤ N by omega) hδ hδhi hb
      (show 0 < t by linarith) ht hprev0).trans hp'.2.2.1
  have hpN : (p : ℝ) ≤ N := by
    have hDcut := reboxing_support_cutoff_bounds hQ0.le hΔ0 hV (show 0 < s by linarith) hd
    have hQN : Q ≤ N := by
      simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNreal.le
        (show 1 / 2 - δ ≤ 1 by linarith)
    have hd0 := (reboxing_support_product_bounds hΔ0 (fun l => (hV l).le) hd).1
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd0
    have hDN : D ≤ N := by
      calc
        _ ≤ Q := div_le_self hQ0.le hd1
        _ ≤ N := hQN
    have hD1 : 1 ≤ D := hq.le.trans hD.1
    calc
      _ ≤ reboxingAlpha q Δ t j := hp'.2.2.2.le
      _ ≤ q ^ (1 / s) := hαhi
      _ ≤ D ^ (1 / s) := hDcut.1
      _ ≤ D ^ (1 : ℝ) :=
        rpow_le_rpow_of_exponent_le hD1 ((one_div_le_one_div_of_le (by norm_num) (by linarith : 1 ≤ s)).trans_eq (by norm_num))
      _ = D := rpow_one D
      _ ≤ N := hDN
  have hlogp : log (p : ℝ) ≤ log (N : ℝ) :=
    log_le_log (by linarith : (0 : ℝ) < p) hpN
  have hlogwidth : log (((D / p) ^ (1 / a)) / p) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    calc
      _ ≤ (b - a) * log (p : ℝ) := hwindow.2
      _ ≤ (K / log (N : ℝ) ^ (5 : ℕ)) * log (N : ℝ) :=
        mul_le_mul hwidth.2 hlogp (log_pos hp1).le (by positivity)
      _ = _ := by field_simp
  have hmass := hT1 N hN1 (p : ℝ) ((D / p) ^ (1 / a)) hheight hwindow.1 hlogwidth
  have hcut : wuLocalCutoff N δ (d * p) a = (D / p) ^ (1 / a) := by
    simp only [wuLocalCutoff, Nat.cast_mul, div_div, D, Q]
  have hd0 := (reboxing_support_product_bounds hΔ0 (fun l => (hV l).le) hd).1
  have hf := reboxing_source_difference_le_prime_mass hN4 he (Nat.mul_pos hd0 hp'.1.pos) hwindow.1
  rw [hcut]
  refine ⟨hf.1, hf.2.trans ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (N : ℝ) / (d * p : ℕ) by positivity)

end Wu2008DoubleSieve
