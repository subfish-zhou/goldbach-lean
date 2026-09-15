import MathlibNt.Wu2008DoubleSieve.Gamma5ClassicalUpper

/-!
# Exact two-insertion arithmetic transport

The multipliers retain primes dividing the old convolution product. All
comparisons are bilateral, before any prime quadrature is performed.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Classical Topology

noncomputable def gamma5MassAtom (d p : ℕ) : ℝ :=
  if p ∣ d then 1 / (p : ℝ) else 1 / ((p : ℝ) - 2)

noncomputable def gamma5MassCoordinate (R : ℝ) (p : ℕ) : ℝ := log p / log R

noncomputable def gamma5MassOldWeight (N d : ℕ) (Q : ℝ) : ℝ :=
  wuSingularSeries (d * N) / ((Nat.totient d : ℝ) * log (Q / d))

theorem gamma5Mass_two_insertions {N d p q : ℕ} {Q : ℝ}
    (hN : 0 < N) (hd : 0 < d) (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hpN : p.Coprime N) (hqN : q.Coprime N)
    (hR : 1 < Q / d) :
    wuSingularSeries ((d * p * q) * N) /
        ((Nat.totient (d * p * q) : ℝ) * log (Q / (d * p * q))) =
      gamma5MassOldWeight N d Q * gamma5MassAtom d p * gamma5MassAtom (d * p) q /
        (1 - gamma5MassCoordinate (Q / d) p - gamma5MassCoordinate (Q / d) q) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hR0 : 0 < Q / d := by linarith
  have hl : log (Q / d) ≠ 0 := (log_pos hR).ne'
  have hlog : log (Q / ((d : ℝ) * p * q)) =
      log (Q / d) * (1 - gamma5MassCoordinate (Q / d) p -
        gamma5MassCoordinate (Q / d) q) := by
    rw [show Q / ((d : ℝ) * p * q) = (Q / d) / ((p : ℝ) * q) by ring,
      log_div hR0.ne' (mul_pos hp0 hq0).ne', log_mul hp0.ne' hq0.ne']
    dsimp [gamma5MassCoordinate]
    field_simp
    ring
  rw [← div_div, wu_inserted_arithmetic_weight hN (Nat.mul_pos hd hp.pos) hq hq2 hqN,
    wu_inserted_arithmetic_weight hN hd hp hp2 hpN]
  rw [hlog]
  simp only [gamma5MassOldWeight, gamma5MassAtom, div_eq_mul_inv, mul_inv]
  ring

theorem gamma5Mass_atom_bilateral {Z : ℝ} {d p : ℕ}
    (hZ : 4 ≤ Z) (hpZ : Z ≤ (p : ℝ)) :
    1 / (p : ℝ) ≤ gamma5MassAtom d p ∧
      gamma5MassAtom d p ≤ (1 + 4 / Z) / p := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hp2 : 0 < (p : ℝ) - 2 := by linarith
  have hZ0 : 0 < Z := by linarith
  have hupper : 1 / ((p : ℝ) - 2) ≤ (1 + 4 / Z) / p := by
    apply (div_le_div_iff₀ hp2 hp0).mpr
    apply (le_of_mul_le_mul_right ?_ hZ0)
    field_simp
    nlinarith
  have hlower := one_div_le_one_div_of_le hp2
    (show (p : ℝ) - 2 ≤ p by linarith)
  unfold gamma5MassAtom
  split_ifs
  · exact ⟨le_rfl, hlower.trans hupper⟩
  · exact ⟨hlower, hupper⟩

theorem gamma5Mass_atoms_bilateral {Z : ℝ} {d p q : ℕ}
    (hZ : 4 ≤ Z) (hpZ : Z ≤ (p : ℝ)) (hqZ : Z ≤ (q : ℝ)) :
    1 / ((p : ℝ) * q) ≤ gamma5MassAtom d p * gamma5MassAtom (d * p) q ∧
      gamma5MassAtom d p * gamma5MassAtom (d * p) q ≤
        (1 + 4 / Z) ^ 2 / ((p : ℝ) * q) := by
  have hp := gamma5Mass_atom_bilateral (d := d) hZ hpZ
  have hq := gamma5Mass_atom_bilateral (d := d * p) hZ hqZ
  have hp0 : 0 ≤ gamma5MassAtom d p := (by positivity : (0 : ℝ) ≤ 1 / p).trans hp.1
  have hq0 : 0 ≤ gamma5MassAtom (d * p) q := (by positivity : (0 : ℝ) ≤ 1 / q).trans hq.1
  constructor
  · simpa only [one_div_mul_one_div] using
      mul_le_mul hp.1 hq.1 (by positivity) hp0
  · have hh := mul_le_mul hp.2 hq.2 hq0 (by positivity : 0 ≤ (1 + 4 / Z) / p)
    exact hh.trans_eq (by ring)

theorem gamma5Mass_label_eventually (k : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδhi : δ < 1 / 2) :
    ∀ᶠ N : ℕ in atTop, ∀ i : ℕ, ∀ Δ : ℝ, ∀ V : Fin i → ℝ,
      wuSourceBox k δ N i Δ V →
      ∀ x ∈ gamma5ClassicalLabels N δ (convolutionWuWindows N Δ V),
        2 < x.2.1 ∧ 2 < x.2.2 ∧
        0 < gamma5MassOldWeight N x.1 ((N : ℝ) ^ (1 / 2 - δ)) ∧
        0 < 1 - gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.1 -
          gamma5MassCoordinate ((N : ℝ) ^ (1 / 2 - δ) / x.1) x.2.2 := by
  have hα := (gamma5Classical_exponents_pos k hδ hδhi).1
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (4 : ℝ))] with N hN hfour
  intro i Δ V hb x hx
  have hg := gamma5Classical_label_geometry hN hδ hδhi hb hx
  obtain ⟨ha, hp, hq, _hpN, _hqN, _hz, hpq, _hu⟩ := mem_filter.mp hx
  have hd := (mem_product.mp ha).1
  have hbase := wuLocal_support_bounds (by omega) hδ hδhi hb.2.2.2.2.1
    ((boxSquaredPrefixes_iff _ _).mp hb.2.2.2.2.2) hd
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hR : 1 < (N : ℝ) ^ (1 / 2 - δ) / x.1 :=
    (one_lt_rpow hN1 (wuLocalExponent_pos k hδ hδhi)).trans_le hbase.2.2
  have hp4 : (4 : ℝ) ≤ x.2.1 := hfour.trans hg.prime_lower
  have hp2 : 2 < x.2.1 := by exact_mod_cast (show (2 : ℝ) < x.2.1 by linarith)
  have hq2 : 2 < x.2.2 := by omega
  have hweight : 0 < gamma5MassOldWeight N x.1 ((N : ℝ) ^ (1 / 2 - δ)) := by
    unfold gamma5MassOldWeight
    exact div_pos (wuSingularSeries_pos _ (Nat.mul_pos hbase.1 (by omega)))
      (mul_pos (by exact_mod_cast Nat.totient_pos.mpr hbase.1) (log_pos hR))
  refine ⟨hp2, hq2, hweight, ?_⟩
  have hr := gamma5Classical_ratio_coordinates (p := (x.2.1 : ℝ)) (q := (x.2.2 : ℝ)) hR
    (by exact_mod_cast hp.pos) (by exact_mod_cast hq.pos)
  have he : ((N : ℝ) ^ (1 / 2 - δ) / x.1) / ((x.2.1 : ℝ) * x.2.2) =
      gamma5ClassicalLevel N δ x := by
    simp only [gamma5ClassicalLevel, gamma5ClassicalProduct, Nat.cast_mul]
    ring
  rw [he] at hr
  have hl : 0 < log (gamma5ClassicalLevel N δ x) /
      log (((N : ℝ) ^ (1 / 2 - δ) / x.1) ^ (1 / gamma5ClassicalS)) :=
    div_pos (log_pos hg.level_gt_one)
      (log_pos (one_lt_rpow hR (by norm_num [gamma5ClassicalS])))
  rw [hr] at hl
  change 0 < 1 - log (x.2.1 : ℝ) / log _ - log (x.2.2 : ℝ) / log _
  exact pos_of_mul_pos_left hl (by norm_num [gamma5ClassicalS])

end Wu2008DoubleSieve
