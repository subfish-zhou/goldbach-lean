import MathlibNt.SieveTheory.LiLiuGoldbachG12SafeGridBudget
import MathlibNt.SieveTheory.LiLiuGoldbachG12GridAdmission

noncomputable section
open Classical Finset Filter
open scoped BigOperators Topology
open MathlibNt.SieveTheory.LiLiuOnePlusOneNine.GoldbachBig
open MathlibNt.SieveTheory.LiLiuPrereqWF
namespace G12SafeGridBudget

theorem absorb_constant (C : ℝ) (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, C*(N/Real.log (N : ℝ)^(B+1)) ≤ N/Real.log (N : ℝ)^B := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 C))] with N hN
  have hl1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hN
  have hC : C ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hN
  have hl : 0 < Real.log (N : ℝ) := by linarith
  calc
    _ ≤ Real.log (N : ℝ)*(N/Real.log (N : ℝ)^(B+1)) :=
      mul_le_mul_of_nonneg_right hC (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

theorem fixed_prefix_log {e : ℝ} (he : 0 < e) :
    ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) ∧ ∀ x : ℝ,
      e*N ≤ x → Real.log (N : ℝ)/2 ≤ Real.log x := by
  filter_upwards [(Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (eventually_ge_atTop (max 1 (-2*Real.log e))), eventually_ge_atTop 1] with N hl hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine ⟨(le_max_left _ _).trans hl,?_⟩
  intro x hx
  have hh := Real.log_le_log (mul_pos he hn) hx
  rw [Real.log_mul he.ne' hn.ne'] at hh
  have hh' : -2*Real.log e ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hl
  linarith

theorem scaled_discrepancy (A : ℕ) {n x : ℝ} (hn : 0 ≤ n)
    (hl : 0 < Real.log n) (hx : x ≤ 4*n) (hxl : Real.log n/2 ≤ Real.log x) :
    x/Real.log x^A ≤ (4*2^A)*(n/Real.log n^A) := by
  have hxl0 : 0 < Real.log x := by linarith
  have hp : (Real.log n/2)^A ≤ Real.log x^A :=
    pow_le_pow_left₀ (by positivity) hxl A
  calc
    _ ≤ (4*n)/Real.log x^A := div_le_div_of_nonneg_right hx (by positivity)
    _ ≤ (4*n)/(Real.log n/2)^A :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hp
    _ = _ := by rw [div_pow]; field_simp

theorem small_numerical (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ Q : ℝ, Q ≤ N →
      8000*(Nat.ceil (Real.sqrt Q) : ℝ) ≤ 16000*(N/Real.log (N : ℝ)^B) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (G12OutsideBudget.scalar_log_saving B (by norm_num : (0 : ℝ) < 1/2))] with N hN
  have hn : (0 : ℝ) < N := by linarith [hN.1]
  have hl : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by linarith [hN.1])
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hn
  have hs1 : 1 ≤ Real.sqrt (N : ℝ) := (Real.le_sqrt (by norm_num) hn.le).mpr (by nlinarith [hN.1])
  have hb := hN.2
  rw [← Real.sqrt_eq_rpow] at hb
  have hcoef : 1/Real.sqrt (N : ℝ) ≤ 1/Real.log (N : ℝ)^B := by
    apply le_trans _ hb
    apply div_le_div_of_nonneg_right _ hs.le
    nlinarith [sq_nonneg (Real.log (N : ℝ))]
  have hm := mul_le_mul_of_nonneg_left hcoef hn.le
  have hroot : Real.sqrt (N : ℝ) ≤ N/Real.log (N : ℝ)^B := by
    calc
      _ = (N : ℝ)*(1/Real.sqrt (N : ℝ)) := by
        have he := Real.sq_sqrt hn.le
        rw [mul_one_div]
        apply (eq_div_iff hs.ne').mpr
        nlinarith
      _ ≤ _ := by simpa only [mul_one_div] using hm
  intro Q hQ
  have hc := (Nat.ceil_lt_add_one (Real.sqrt_nonneg Q)).le
  have hmono := Real.sqrt_le_sqrt hQ
  nlinarith

/-- The literal production index set, including repeated and empty endpoint cells. -/
theorem indices_card_log {ρ : ℝ} (hρ : 1 < ρ) {N : ℕ}
    (hl : 1 ≤ Real.log (N : ℝ)) :
    ((G12FineGrid.indices ρ N).card : ℝ) ≤
      (1/Real.log ρ+2)^2 * Real.log (N : ℝ)^2 := by
  have hr := Real.log_pos hρ
  have hh := (Nat.ceil_lt_add_one
    (div_nonneg (by linarith : 0 ≤ Real.log (N : ℝ)) hr.le)).le
  have hc : (G12FineGrid.count ρ N : ℝ) ≤ (1/Real.log ρ+2)*Real.log (N : ℝ) := by
    unfold G12FineGrid.count
    push_cast
    calc
      _ ≤ Real.log (N : ℝ)/Real.log ρ+2 := by linarith
      _ ≤ _ := by
        have he : (1/Real.log ρ+2)*Real.log (N : ℝ) =
            Real.log (N : ℝ)/Real.log ρ+2*Real.log (N : ℝ) := by ring
        rw [he]
        linarith
  have hc0 : 0 ≤ (G12FineGrid.count ρ N : ℝ) := Nat.cast_nonneg _
  have hs := mul_self_le_mul_self hc0 hc
  simpa [G12FineGrid.indices, card_product, pow_two, mul_assoc, mul_left_comm, mul_comm] using hs

end G12SafeGridBudget
