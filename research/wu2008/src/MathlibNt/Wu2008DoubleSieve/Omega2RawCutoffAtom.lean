import MathlibNt.Wu2008DoubleSieve.Omega2Parameter

/-!
# Actual fixed-cutoff reverse error for Omega2

The short window is between the inserted-box cutoff and `(Q/d)^(1/t)`.
Both sifting counts retain the modulus `(d*p)*N`. The positive-multiple
and reciprocal-prime estimates are the already accepted generic ones.
-/

namespace Wu2008DoubleSieve

open Finset Filter Real
open scoped Classical Topology

theorem omega2_fixed_cutoff_atom_bound (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ ≤ 1 / 10) :
    ∃ B : ℝ, 0 < B ∧ ∃ T : ℕ, ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), wuSourceBox k δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → 3 ≤ t → t ≤ 5 → ∀ r : ℕ,
      reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t r ≤
        ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) ^ (1 / s) →
      ∀ j : ℕ, 1 ≤ j → j ≤ r →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ p ∈ primeWindow N
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t ((j : ℝ) - 1))
        (reboxingAlpha ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t j),
      let b := omega2ParameterTransform t
        (reboxingS2 ((N : ℝ) ^ (1 / 2 - δ) / (∏ l, V l)) Δ t i j)
      0 ≤ (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) b) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ) ∧
        (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ (d * p) b) : ℝ) -
          (sourceSieveCount N (d * p) ((d * p) * N) (wuLocalCutoff N δ d t) : ℝ) ≤
        ((N : ℝ) / ((d : ℝ) * p)) * (B / log (N : ℝ) ^ (5 : ℕ)) := by
  let α := δ ^ (k + 2) / 10
  let K := 5 * ((200 + 20 * (k : ℝ)) / δ ^ (k + 1))
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T1, hT1⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T2, _, hT2⟩ := reboxing_parameter_mesh_eventually k hδ hδhi
  have hlogt : Tendsto (fun N : ℕ => log (N : ℝ)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨T3, hT3⟩ := eventually_atTop.mp (hlogt.eventually (eventually_ge_atTop 1))
  refine ⟨2 * K / α + 2, by positivity, max 4 (max T1 (max T2 T3)), ?_⟩
  intro N hN he i Δ V hb s t hs hst ht3 ht5 r hr j hj hjr d hd p hp
  dsimp only
  have hN4 : 4 ≤ N := by omega
  have hN1 : T1 ≤ N := by omega
  have hN2 : T2 ≤ N := by omega
  have hN3 : T3 ≤ N := by omega
  have hL1 := hT3 N hN3
  have hNreal : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let D := Q / d
  let a := reboxingS1 q Δ t j
  let b := reboxingS2 q Δ t i j
  let v := omega2ParameterTransform t b
  let w := D ^ (1 / t)
  obtain ⟨hΔ, hq, hmesh⟩ := hT2 N hN2 i Δ V hb
  have hq0 : 0 < q := by dsimp [q, Q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hQ0 : 0 < Q := rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _
  have hV : ∀ l, 0 < V l := fun l =>
    (rpow_pos_of_pos (by linarith : (0 : ℝ) < N) _).trans_le (hb.2.2.2.2.1 l)
  have hD := reboxing_support_level_bounds hQ0.le hΔ0 hV hd
  have hD1 : 1 < D := hq.trans_le hD.1
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hαhi : reboxingAlpha q Δ t j ≤ q ^ (1 / s) :=
    (hm (by exact_mod_cast hjr)).trans hr
  have hdom := reboxing_parameter_domain hq hΔ hs hst (show t ≤ 10 by linarith)
    hj1 hαhi hmesh
  have hprev0 : q ^ (1 / t) ≤ reboxingAlpha q Δ t ((j : ℝ) - 1) := by
    simpa only [reboxingAlpha_zero] using hm (show (0 : ℝ) ≤ j - 1 by linarith)
  have ht0 : 0 < t := by linarith
  have hprev1 : 1 < reboxingAlpha q Δ t ((j : ℝ) - 1) :=
    (one_lt_rpow hq (by positivity : 0 < 1 / t)).trans_le hprev0
  have hp' := mem_primeWindow.mp hp
  have hpar := reboxing_parameter_bounds hq hΔ hD.1 hD.2 hprev1 hp'.2.2.1 hp'.2.2.2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hwindow := omega2_fixed_replacement_window_bounds hD1 hp1 ht3 ht5
    hdom.1 hpar.1 hpar.2
  have hwidth := reboxing_source_parameter_width (show 2 ≤ N by omega) hδ hδhi hL1 hb
    ht0 (show t ≤ 10 by linarith) hj1
  have hheightw : (N : ℝ) ^ (δ ^ (k + 2)) ≤ w :=
    (reboxing_endpoint_lower (show 2 ≤ N by omega) hδ hδhi hb
      ht0 (show t ≤ 10 by linarith) (le_refl (q ^ (1 / t)))).trans
      (reboxing_support_cutoff_bounds hQ0.le hΔ0 hV ht0 hd).1
  have hheight : (N : ℝ) ^ α ≤ (D / p) ^ (1 / v) := by
    calc
      _ = ((N : ℝ) ^ (δ ^ (k + 2))) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul (by linarith : (0 : ℝ) ≤ N)]
        congr 1
        dsimp [α]
        ring
      _ ≤ w ^ (1 / 10 : ℝ) :=
        rpow_le_rpow (rpow_nonneg (Nat.cast_nonneg _) _) hheightw (by norm_num)
      _ ≤ _ := hwindow.2.1
  have hsupport := reboxing_support_product_bounds hΔ0 (fun l => (hV l).le) hd
  have hQN : Q ≤ N := by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hNreal.le
      (show 1 / 2 - δ ≤ 1 by linarith)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hsupport.1
  have hDN : D ≤ N := (div_le_self hQ0.le hd1).trans hQN
  have hwN : w ≤ N := by
    calc
      _ ≤ D ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hD1.le
        ((one_div_le_one_div_of_le (by norm_num) (by linarith : 1 ≤ t)).trans_eq
          (by norm_num))
      _ = D := rpow_one D
      _ ≤ N := hDN
  have hw1 : 1 < w := one_lt_rpow hD1 (by positivity)
  have hlogw : log w ≤ log (N : ℝ) := log_le_log (by linarith : 0 < w) hwN
  have hlogwidth : log (w / ((D / p) ^ (1 / v))) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    calc
      _ ≤ 5 * (b - a) * log w := hwindow.2.2
      _ ≤ (5 * (((200 + 20 * (k : ℝ)) / δ ^ (k + 1)) /
          log (N : ℝ) ^ (5 : ℕ))) * log (N : ℝ) := by
        apply mul_le_mul _ hlogw (log_pos hw1).le (by positivity)
        nlinarith [hwidth.2]
      _ = _ := by dsimp [K]; field_simp
  have hmass := hT1 N hN1 ((D / p) ^ (1 / v)) w hheight hwindow.1 hlogwidth
  have hcut : wuLocalCutoff N δ (d * p) v = (D / p) ^ (1 / v) := by
    simp only [wuLocalCutoff, Nat.cast_mul, div_div, D, Q]
  have hf := reboxing_source_difference_le_prime_mass hN4 he
    (Nat.mul_pos hsupport.1 hp'.1.pos) hwindow.1
  rw [hcut]
  refine ⟨hf.1, hf.2.trans ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (N : ℝ) / (d * p : ℕ) by positivity)

end Wu2008DoubleSieve
