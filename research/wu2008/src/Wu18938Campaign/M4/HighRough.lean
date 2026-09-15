import Wu18938Campaign.M4.HighProduct
import MathlibNt.Wu2008DoubleSieve.InclusiveRoughProduct

noncomputable section
namespace Wu18938Campaign.M4
open Wu2008DoubleSieve LiLiuPrereqBuchstab Finset Real Filter
open scoped Classical Topology

theorem six_label_rough_uniform {ε : ℝ} (heps : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N → ∀ d q : ℕ, 0 < d →
      ∀ l : List ℕ, l.length ≤ 6 →
      (d : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) →
      (∀ p ∈ l, 0 < p ∧ (p : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ)) →
      (N : ℝ) ^ (1 / 40 : ℝ) ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (100 / 1327 : ℝ) →
      ((roughNumbers ((N : ℝ) / (d * l.prod : ℕ)) q).card : ℝ) ≤
        (buchstab (log ((N : ℝ) / (d * l.prod : ℕ)) / log q) + ε) *
          ((N : ℝ) / (d * l.prod : ℕ)) / log q := by
  obtain ⟨T0, hT04, hscalar⟩ := InclusiveRoughUniform.uniform_product_upper
    (show (0 : ℝ) < 1 / 40 by norm_num) (half_pos heps)
  have ht : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 / 40 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 40)).comp
      tendsto_natCast_atTop_atTop
  obtain ⟨T1, hlarge⟩ := eventually_atTop.mp
    (ht.eventually_ge_atTop (1 / (ε / 2)))
  refine ⟨max T0 T1, hT04.trans (le_max_left _ _), ?_⟩
  intro N hN d q hd0 l hlen hd hl hqlo hqhi
  have hN2 : 2 ≤ N := by omega
  let D := d * l.prod
  have hD : 0 < D := Nat.mul_pos hd0 (List.prod_pos (fun p hp => (hl p hp).1))
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hq1 : (1 : ℝ) < q :=
    (one_lt_rpow (by exact_mod_cast hN2) (by norm_num : (0 : ℝ) < 1 / 40)).trans_le hqlo
  have hgap := (six_label_square_gap hN2 l hlen hd
    (fun p hp => (hl p hp).2) hqhi).2
  have hx : (q : ℝ) ^ 2 ≤ (N : ℝ) / D := by
    apply (le_div_iff₀ hDR).mpr
    simpa only [D, mul_comm] using hgap.le
  have hqX : (q : ℝ) ≤ (N : ℝ) / D :=
    (by nlinarith only [hq1] : (q : ℝ) ≤ (q : ℝ) ^ 2).trans hx
  have hDX : D ≤ N :=
    (InclusiveRoughUniform.unit_gate_iff N D hD).mp (hq1.le.trans hqX)
  have hDq : D * q ≤ N := (InclusiveRoughUniform.nonunit_gate_iff N D q hD).mp hqX
  have hu := rough_unit_absorbed hq1 (half_pos heps)
    ((hlarge N (by omega)).trans hqlo) hx
  have h := hscalar N (by omega) D q hD hqlo
  rw [if_pos hDX, if_pos hDq] at h
  change ((roughNumbers ((N : ℝ) / D) q).card : ℝ) ≤
    (buchstab (log ((N : ℝ) / D) / log q) + ε) * ((N : ℝ) / D) / log q
  calc
    _ ≤ 1 + (buchstab (log ((N : ℝ) / D) / log q) + ε / 2) *
        ((N : ℝ) / D) / log q := h
    _ ≤ (ε / 2) * ((N : ℝ) / D) / log q +
        (buchstab (log ((N : ℝ) / D) / log q) + ε / 2) *
          ((N : ℝ) / D) / log q := add_le_add hu le_rfl
    _ = _ := by ring

end Wu18938Campaign.M4
