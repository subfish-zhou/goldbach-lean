import U8SingleLineageJoin
import OriginalPayment

noncomputable section
open Finset
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
namespace U8Literal.Mesh

/-- The sieve is chosen at the unique original physical cell, not globally. -/
def familyGood (N : ℕ) (e ρ : ℝ) (P : Key → Finset ℕ) : Finset Label := by
  classical
  exact (physicalPrefix N e).filter fun x =>
    (output N x.1.1 (x.1.2*x.2)).Coprime ((P (gridKey ρ x)).prod id)
def familyBad (N : ℕ) (e ρ : ℝ) (P : Key → Finset ℕ) : Finset Label := by
  classical
  exact (physicalPrefix N e).filter fun x =>
    ¬(output N x.1.1 (x.1.2*x.2)).Coprime ((P (gridKey ρ x)).prod id)

theorem family_partition (N : ℕ) (e ρ : ℝ) (P : Key → Finset ℕ) :
    (physicalPrefix N e).card = (familyGood N e ρ P).card + (familyBad N e ρ P).card := by
  classical
  exact (card_filter_add_card_filter_not (s := physicalPrefix N e)
    (fun x => (output N x.1.1 (x.1.2*x.2)).Coprime ((P (gridKey ρ x)).prod id))).symm

theorem familyGood_partition (N : ℕ) (e ρ : ℝ) (P : Key → Finset ℕ) :
    (∑ k ∈ occupied N e ρ,
      (((familyGood N e ρ P).filter fun x => gridKey ρ x=k).card : ℝ)) =
      ((familyGood N e ρ P).card : ℝ) := by
  classical
  have h := sum_fiberwise_of_maps_to (s := familyGood N e ρ P)
    (t := occupied N e ρ) (g := gridKey ρ)
    (fun x hx => mem_image_of_mem (gridKey ρ) (mem_filter.mp hx).1) (fun _ => (1 : ℝ))
  simpa only [sum_const, nsmul_eq_mul, mul_one] using h

/-- Exact bad-cell partition: no atom is lost or counted in two cells. -/
theorem familyBad_partition (N : ℕ) (e ρ : ℝ) (P : Key → Finset ℕ) :
    (∑ k ∈ occupied N e ρ,
      (((familyBad N e ρ P).filter fun x => gridKey ρ x=k).card : ℝ)) =
      ((familyBad N e ρ P).card : ℝ) := by
  classical
  have h := sum_fiberwise_of_maps_to (s := familyBad N e ρ P)
    (t := occupied N e ρ) (g := gridKey ρ)
    (fun x hx => mem_image_of_mem (gridKey ρ) (mem_filter.mp hx).1) (fun _ => (1 : ℝ))
  simpa only [sum_const, nsmul_eq_mul, mul_one] using h

theorem physicalSmall_family {N : ℕ} (hN : 1 ≤ N) (e : ℝ) {ρ : ℝ}
    (hρ : 1 < ρ) (P : Key → Finset ℕ) :
    ((physicalSmall N).card : ℝ) ≤
      (∑ k ∈ occupied N e ρ, OriginalU8.sifted N ρ k (P k)) +
        (familyBad N e ρ P).card + (smallPrefix N e).card := by
  classical
  have hs : ((familyGood N e ρ P).card : ℝ) ≤
      ∑ k ∈ occupied N e ρ, OriginalU8.sifted N ρ k (P k) := by
    rw [← familyGood_partition N e ρ P]
    apply sum_le_sum
    intro k _
    rw [← Join.sifted_eq]
    apply labels_le_rectangle
    intro x hx
    obtain ⟨hx,hkey⟩ := mem_filter.mp hx
    obtain ⟨hpre,hcop⟩ := mem_filter.mp hx
    have hc : x ∈ cell N e ρ k := mem_filter.mpr ⟨hpre,hkey⟩
    obtain ⟨hn,hl⟩ := cell_rectangle hN hρ hc
    have hd := physicalSmall_data (mem_filter.mp hpre).1
    rw [hkey] at hcop
    exact ⟨hn,hl,hd.1,hd.2.2.2.1,hcop⟩
  rw [physicalSmall_card_split N e, family_partition N e ρ P, Nat.cast_add, Nat.cast_add]
  exact add_le_add (add_le_add hs le_rfl) le_rfl

theorem familyBad_constant (N : ℕ) (e ρ : ℝ) (P : Finset ℕ) :
    familyBad N e ρ (fun _ => P) = outputBad N e P := rfl

/-- Bound the original grid directly; no identification with the modern alpha carrier. -/
theorem occupied_card_nat {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ) :
    (occupied N e ρ).card ≤ (gridIndex ρ N+1)^3 := by
  classical
  let I := range (gridIndex ρ N+1)
  have hi : ∀ {t : ℕ}, 0 < t → t ≤ N → gridIndex ρ t ∈ I := by
    intro t ht htN
    apply mem_range.mpr
    apply Nat.lt_succ_of_le
    exact Nat.floor_mono (div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast ht) (by exact_mod_cast htN))
      (Real.log_pos hρ).le)
  have hsub : occupied N e ρ ⊆ I ×ˢ (I ×ˢ I) := by
    intro k hk
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hk
    obtain ⟨ha,hb,hr,_,_,_,_,_,hab,_,hbN,hrN,_,_⟩ :=
      physicalSmall_data (mem_filter.mp hx).1
    exact mem_product.mpr ⟨hi ha.pos (by omega),
      mem_product.mpr ⟨hi hb.pos (by omega), hi hr.pos (by omega)⟩⟩
  calc
    _ ≤ (I ×ˢ (I ×ˢ I)).card := card_le_card hsub
    _ = _ := by simp only [card_product, card_range, I]; ring

theorem occupied_card_log {N : ℕ} {e ρ : ℝ} (hρ : 1 < ρ)
    (hlog : 1 ≤ Real.log (N : ℝ)) :
    ((occupied N e ρ).card : ℝ) ≤
      (1/Real.log ρ+1)^3 * Real.log (N : ℝ)^3 := by
  have hf : (gridIndex ρ N : ℝ) ≤ Real.log (N : ℝ)/Real.log ρ :=
    Nat.floor_le (div_nonneg (by linarith) (Real.log_pos hρ).le)
  have hb : (gridIndex ρ N : ℝ)+1 ≤ (1/Real.log ρ+1)*Real.log (N : ℝ) := by
    calc
      _ ≤ Real.log (N : ℝ)/Real.log ρ+Real.log (N : ℝ) := add_le_add hf hlog
      _ = _ := by ring
  have hc : ((occupied N e ρ).card : ℝ) ≤ ((gridIndex ρ N : ℝ)+1)^3 := by
    exact_mod_cast (occupied_card_nat (N := N) (e := e) hρ)
  exact hc.trans ((pow_le_pow_left₀ (by positivity) hb 3).trans_eq (by ring))

/-- Fixed rho and constants precede the cutoff; A+4 pays the actual cubic grid. -/
theorem mesh_log_payment (A : ℕ) {ρ C σ : ℝ} (hρ : 1 < ρ)
    (hC : 0 ≤ C) (hσ : 0 < σ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ e : ℝ, ∀ E : Key → ℝ,
      (∀ k ∈ occupied N e ρ, E k ≤ C*(N : ℝ)/Real.log (N : ℝ)^(A+4)) →
      (∑ k ∈ occupied N e ρ, E k) ≤ σ*(N : ℝ)/Real.log (N : ℝ)^A := by
  let D := (1/Real.log ρ+1)^3
  let L := max 1 (D*(C/σ))
  refine ⟨Real.exp L, ?_⟩
  intro N hN e E hE
  have hn : 0 < (N : ℝ) := (Real.exp_pos L).trans_le hN
  have hL : L ≤ Real.log (N : ℝ) := (Real.le_log_iff_exp_le hn).mpr hN
  have hl : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hL
  have hDC : D*(C/σ) ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hL
  calc
    _ ≤ ∑ _k ∈ occupied N e ρ, C*(N : ℝ)/Real.log (N : ℝ)^(A+4) := sum_le_sum hE
    _ = ((occupied N e ρ).card : ℝ)*(C*(N : ℝ)/Real.log (N : ℝ)^(A+4)) := by simp
    _ ≤ (D*Real.log (N : ℝ)^3)*(C*(N : ℝ)/Real.log (N : ℝ)^(A+4)) :=
      mul_le_mul_of_nonneg_right (occupied_card_log hρ hl) (by positivity)
    _ = σ*((D*Real.log (N : ℝ)^3)*((C/σ)*(N : ℝ)/Real.log (N : ℝ)^(A+4))) := by
      field_simp [hσ.ne']
    _ ≤ σ*((N : ℝ)/Real.log (N : ℝ)^A) :=
      mul_le_mul_of_nonneg_left (fouvryG9GridCost_scalar A hn.le (by linarith) hDC) hσ.le
    _ = _ := by ring

end U8Literal.Mesh
