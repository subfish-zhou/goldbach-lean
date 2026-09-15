import Wu18938Campaign.M1.Confirmed.ReboxingChildren
import MathlibNt.Wu2008DoubleSieve.Omega2RawCutoffAtom

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Rebox

open Wu2008DoubleSieve Finset Real Filter
open scoped Classical Topology

theorem cutoff_atom (m : ℕ) {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 < B ∧ ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → Even N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
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
  let α := η / 100
  let K := 5 * ((400 + 40 * (m : ℝ)) / η)
  have hα : 0 < α := by dsimp [α]; positivity
  have hK : 0 < K := by dsimp [K]; positivity
  obtain ⟨T0,hT0⟩ := reboxing_short_prime_mass hα hK
  obtain ⟨T1,hT14,hT1⟩ := scale m hη hδ
  refine ⟨2 * K / α + 2,by positivity,max T0 T1,hT14.trans (le_max_right _ _),?_⟩
  intro N hN heven i Δ V hb s t hs hst ht ht5 r hr j hj hjr d hd p hp
  dsimp only
  obtain ⟨hΔ,hL,hqlo,hq,_,hmesh⟩ := hT1 N (by omega) i Δ V hb
  have hN4 : 4 ≤ N := by omega
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hN0 : (0 : ℝ) < N := by linarith
  let Q := (N : ℝ) ^ (1 / 2 - δ)
  let q := Q / (∏ l, V l)
  let D := Q / d
  let a := reboxingS1 q Δ t j
  let b := reboxingS2 q Δ t i j
  let v := omega2ParameterTransform t b
  let w := D ^ (1 / t)
  have hq0 : 0 < q := by dsimp [q,Q]; linarith
  have hΔ0 : 0 < Δ := by linarith
  have hQ0 : 0 < Q := rpow_pos_of_pos hN0 _
  have hV : ∀ l, 0 < V l := fun l => (rpow_pos_of_pos hN0 η).trans_le (hb.endpoint_lower l)
  have hD := reboxing_support_level_bounds hQ0.le hΔ0 hV hd
  have hD1 : 1 < D := hq.trans_le hD.1
  have hm := (reboxingAlpha_strictMono (t := t) hq0 hΔ).monotone
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have htop := (hm (show (j : ℝ) ≤ r by exact_mod_cast hjr)).trans hr
  have hdom := reboxing_parameter_domain hq hΔ hs hst (by linarith : t ≤ 10) hj1 htop hmesh
  have hprev : 1 < reboxingAlpha q Δ t ((j : ℝ) - 1) := by
    have hbase : 1 < reboxingAlpha q Δ t 0 := by
      rw [reboxingAlpha_zero]
      exact one_lt_rpow hq (by positivity)
    exact hbase.trans_le (hm (by linarith))
  have hp' := mem_primeWindow.mp hp
  have hpar := reboxing_parameter_bounds hq hΔ hD.1 hD.2 hprev hp'.2.2.1 hp'.2.2.2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp'.1.one_lt
  have hwindow := omega2_fixed_replacement_window_bounds hD1 hp1 ht ht5
    hdom.1 hpar.1 hpar.2
  have hwidth := parameter_width hb (by omega) hη hL hqlo (by linarith : 0 < t)
    (by linarith : t ≤ 10) hj1
  have hheightw : (N : ℝ) ^ (η / 10) ≤ w := by
    calc
      _ = ((N : ℝ) ^ η) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        ring
      _ ≤ D ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) (hb.remaining d hd) (by norm_num)
      _ ≤ _ := rpow_le_rpow_of_exponent_le hD1.le
        (one_div_le_one_div_of_le (by linarith) (by linarith : t ≤ 10))
  have hheight : (N : ℝ) ^ α ≤ (D / p) ^ (1 / v) := by
    calc
      _ = ((N : ℝ) ^ (η / 10)) ^ (1 / 10 : ℝ) := by
        rw [← rpow_mul hN0.le]
        congr 1
        dsimp [α]
        ring
      _ ≤ w ^ (1 / 10 : ℝ) := rpow_le_rpow (by positivity) hheightw (by norm_num)
      _ ≤ _ := hwindow.2.1
  have hgeom := hb.support_geometry (by omega) hη hδ hd
  have hwN : w ≤ N := (show D ^ (1 / t) ≤ D by
    simpa only [rpow_one] using rpow_le_rpow_of_exponent_le hD1.le
      ((div_le_iff₀ (by linarith : 0 < t)).mpr (by linarith) : 1 / t ≤ 1)).trans hgeom.2.2.2
  have hw1 : 1 < w := one_lt_rpow hD1 (by positivity)
  have hlogw : log w ≤ log (N : ℝ) := log_le_log (by linarith : 0 < w) hwN
  have hlogwidth : log (w / ((D / p) ^ (1 / v))) ≤ K / log (N : ℝ) ^ (4 : ℕ) := by
    calc
      _ ≤ 5 * (b - a) * log w := hwindow.2.2
      _ ≤ (5 * (((400 + 40 * (m : ℝ)) / η) / log (N : ℝ) ^ (5 : ℕ))) *
          log (N : ℝ) := by
        apply mul_le_mul _ hlogw (log_pos hw1).le (by positivity)
        nlinarith [hwidth.2]
      _ = _ := by dsimp [K]; field_simp
  have hmass := hT0 N (by omega) ((D / p) ^ (1 / v)) w hheight hwindow.1 hlogwidth
  have hcut : wuLocalCutoff N δ (d * p) v = (D / p) ^ (1 / v) := by
    simp only [wuLocalCutoff,Nat.cast_mul,div_div,D,Q]
  have hf := reboxing_source_difference_le_prime_mass hN4 heven
    (Nat.mul_pos hgeom.1 hp'.1.pos) hwindow.1
  rw [hcut]
  refine ⟨hf.1,hf.2.trans ?_⟩
  simpa only [Nat.cast_mul] using mul_le_mul_of_nonneg_left hmass
    (show 0 ≤ (N : ℝ) / (d * p : ℕ) by positivity)

end Wu18938Campaign.M1.Confirmed.Rebox
