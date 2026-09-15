import HighBoxRecoveryRemainders

namespace HighBoxRecovery
open Finset Real Wu2008DoubleSieve Filter
open scoped Classical Topology
noncomputable section

/-- Fixed auxiliary exponent; the original alpha remains 100/1327. -/
def highEta : ℝ := 1/1327

/-- The two literal Wu08 1635--1643 rectangles imply a total-product gap.
This includes the high-prime part and uses no squared prefix. -/
theorem original_rectangles_product {N : ℕ} {V : Fin 2 → ℝ} (hN : 2 ≤ N)
    (hV : ∀ j, 0 ≤ V j)
    (hrect : (V 0 ≤ (N : ℝ)^(25/206 : ℝ) ∧
        V 1 ≤ (N : ℝ)^(1/2-2*(25/206 : ℝ))) ∨
      (V 0 ≤ (N : ℝ)^(3*(100/1327 : ℝ)/2) ∧
        V 1 ≤ (N : ℝ)^(1/2-3*(100/1327 : ℝ)))) :
    (∏ j, V j) ≤ (N : ℝ)^(1/2-100*highEta) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  rw [Fin.prod_univ_two]
  rcases hrect with h | h
  · calc
      _ ≤ (N : ℝ)^(25/206 : ℝ) * (N : ℝ)^(1/2-2*(25/206 : ℝ)) :=
        mul_le_mul h.1 h.2 (hV 1) (by positivity)
      _ = (N : ℝ)^((25/206 : ℝ)+(1/2-2*(25/206 : ℝ))) := (rpow_add hNr _ _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hN1 (by norm_num [highEta])
  · calc
      _ ≤ (N : ℝ)^(3*(100/1327 : ℝ)/2) * (N : ℝ)^(1/2-3*(100/1327 : ℝ)) :=
        mul_le_mul h.1 h.2 (hV 1) (by positivity)
      _ = (N : ℝ)^((3*(100/1327 : ℝ)/2)+(1/2-3*(100/1327 : ℝ))) :=
        (rpow_add hNr _ _).symm
      _ ≤ _ := rpow_le_rpow_of_exponent_le hN1 (by norm_num [highEta])

/-- The shrink factor is controlled before the moving box is chosen. -/
theorem delta_eventually_small : ∀ᶠ N : ℕ in atTop, ∀ Δ : ℝ,
    1+log (N : ℝ)^(-4 : ℝ) ≤ Δ →
    Δ < 1+2*log (N : ℝ)^(-4 : ℝ) →
    1 ≤ Δ ∧ Δ ≤ (N : ℝ)^highEta := by
  have hpow : ∀ᶠ N : ℕ in atTop, (3 : ℝ) ≤ (N : ℝ)^highEta :=
    ((tendsto_rpow_atTop (show 0 < highEta by norm_num [highEta])).comp
      tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 3)
  have hlog : ∀ᶠ N : ℕ in atTop, 1 ≤ log (N : ℝ) :=
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1)
  filter_upwards [hpow,hlog] with N hp hl
  intro Δ hlo hhi
  have hn : 0 ≤ log (N : ℝ)^(-4 : ℝ) := rpow_nonneg (by linarith) _
  have hle : log (N : ℝ)^(-4 : ℝ) ≤ 1 := rpow_le_one_of_one_le_of_nonpos hl (by norm_num)
  constructor <;> linarith

/-- Occupied insertion, scalar form. The witness retains the actual d and p;
Delta losses are paid explicitly, rather than assuming a balanced new box. -/
theorem occupied_insertion_product {N : ℕ} {δ D U Δ d p : ℝ}
    (hN : 2 ≤ N) (hδhi : δ ≤ 50*highEta)
    (hD : 0 < D) (hU : 0 ≤ U) (hΔ : 1 ≤ Δ) (hΔhi : Δ ≤ (N : ℝ)^highEta)

    (hbase : D ≤ (N : ℝ)^(1/2-100*highEta))
    (hlabel : D ≤ Δ^2*d) (hinsert : d*p^2 ≤ (N : ℝ)^(1/2-δ))
    (hbox : U ≤ Δ*p) :
    D*U ≤ (N : ℝ)^(1/2-δ-10*highEta) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hQ : 0 ≤ (N : ℝ)^(1/2-δ) := by positivity
  have hΔ0 : 0 ≤ Δ := by linarith
  have hU2 : U^2 ≤ Δ^2*p^2 := by nlinarith
  have hstep : D*U^2 ≤ Δ^4*(N : ℝ)^(1/2-δ) := by
    calc
      _ ≤ D*(Δ^2*p^2) := mul_le_mul_of_nonneg_left hU2 hD.le
      _ ≤ (Δ^2*d)*(Δ^2*p^2) := mul_le_mul_of_nonneg_right hlabel (by positivity)
      _ = Δ^4*(d*p^2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hinsert (by positivity)
  have hsquare : (D*U)^2 ≤ D*Δ^4*(N : ℝ)^(1/2-δ) := by nlinarith
  have hΔ4 : Δ^4 ≤ (N : ℝ)^(4*highEta) := by
    calc
      _ ≤ ((N : ℝ)^highEta)^4 := pow_le_pow_left₀ hΔ0 hΔhi 4
      _ = (N : ℝ)^(4*highEta) := by rw [← rpow_natCast, ← rpow_mul hNr.le]; congr 1; ring
  have hbound : D*Δ^4*(N : ℝ)^(1/2-δ) ≤
      (N : ℝ)^((1/2-δ-10*highEta)*2) := by
    calc
      _ ≤ ((N : ℝ)^(1/2-100*highEta)*(N : ℝ)^(4*highEta)) * (N : ℝ)^(1/2-δ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul hbase hΔ4 (by positivity) (by positivity)) hQ
      _ = (N : ℝ)^((1/2-100*highEta)+4*highEta+(1/2-δ)) := by
        rw [← rpow_add hNr, ← rpow_add hNr]
      _ ≤ _ := rpow_le_rpow_of_exponent_le hN1 (by
        have hηpos : 0 < highEta := by norm_num [highEta]
        linarith)
  have heq : ((N : ℝ)^(1/2-δ-10*highEta))^2 =
      (N : ℝ)^((1/2-δ-10*highEta)*2) := by rw [← rpow_two, ← rpow_mul hNr.le]
  have hout := hsquare.trans hbound
  rw [← heq] at hout
  have ht : 0 ≤ (N : ℝ)^(1/2-δ-10*highEta) := by positivity
  nlinarith

/-- A prime below the actual cutoff with s>=2 has the exact quadratic bound. -/
theorem inserted_prime_square {N d p : ℕ} {δ s : ℝ} (hd : 0 < d)
    (hR : 1 ≤ (N : ℝ)^(1/2-δ)/d) (hs : 2 ≤ s)
    (hp : (p : ℝ) ≤ wuLocalCutoff N δ d s) :
    (d : ℝ)*(p : ℝ)^2 ≤ (N : ℝ)^(1/2-δ) := by
  have hR0 : 0 ≤ (N : ℝ)^(1/2-δ)/d := by positivity
  have hcap : (p : ℝ) ≤ ((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ) := by
    apply hp.trans
    apply rpow_le_rpow_of_exponent_le hR
    exact one_div_le_one_div_of_le (show (0 : ℝ) < 2 by norm_num) hs
  have hsquare : (p : ℝ)^2 ≤ (N : ℝ)^(1/2-δ)/d := by
    have heq : (((N : ℝ)^(1/2-δ)/d)^(1/2 : ℝ))^2 = (N : ℝ)^(1/2-δ)/d := by
      rw [← rpow_two, ← rpow_mul hR0]; norm_num
    have hnonneg := rpow_nonneg hR0 (1/2 : ℝ)
    nlinarith [show (0 : ℝ) ≤ p from Nat.cast_nonneg p]
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  have h := (le_div_iff₀ hdr).mp hsquare
  simpa only [mul_comm] using h

end
end HighBoxRecovery
