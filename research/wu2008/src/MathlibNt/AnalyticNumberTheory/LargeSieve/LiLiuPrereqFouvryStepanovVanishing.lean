import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovConstraints
import MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvryStepanovNonzero

/-!
# Vanishing of the actual Stepanov auxiliary polynomial

This is the passage from (20) to (22) on printed page 11 of Harcos,
*Weil's bound for Kloosterman sums*
(`pages/harcos-stepanov-11.png`). Frobenius kills the positive Hasse
derivatives of `X^(jq)` below order `q`. Factoring out `f^(ell-k)`
additionally requires `k ≤ ell`; the vanishing application uses `k < ell ≤ q`.
-/

noncomputable section

namespace MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- Frobenius forces every positive Hasse derivative of `X^(jq)` below
order `q` to vanish as a polynomial, not just as a function on the field.
The Frobenius residue of `((X + 1)^j)^q` determines its low Taylor
coefficients; evaluating a Hasse monomial at `1` recovers its sole coefficient. -/
theorem stepanov_hasseDeriv_X_card_mul (j k : ℕ)
    (hk : 0 < k) (hkq : k < Fintype.card F) :
    hasseDeriv k ((X : F[X]) ^ (j * Fintype.card F)) = 0 := by
  have hd := stepanov_X_card_dvd_pow_sub_const (((X : F[X]) + C 1) ^ j)
  have hc := (X_pow_dvd_iff.mp hd) k hkq
  have ht : (taylor (1 : F) (X ^ (j * Fintype.card F))).coeff k = 0 := by
    simpa [taylor_X_pow, pow_mul, coeff_sub, coeff_C, coeff_one, Nat.ne_of_gt hk]
      using hc
  have hchoose : ((j * Fintype.card F).choose k : F) = 0 := by
    rw [taylor_coeff, X_pow_eq_monomial, hasseDeriv_monomial] at ht
    simpa using ht
  rw [X_pow_eq_monomial, hasseDeriv_monomial, hchoose, zero_mul, monomial_zero_right]

/-- Below order `q`, a factor `X^(jq)` is constant for Hasse differentiation. -/
theorem stepanov_hasseDeriv_mul_X_card_mul (g : F[X]) (j k : ℕ)
    (hkq : k < Fintype.card F) :
    hasseDeriv k (g * X ^ (j * Fintype.card F)) =
      hasseDeriv k g * X ^ (j * Fintype.card F) := by
  classical
  rw [hasseDeriv_mul, Finset.sum_eq_single (k, 0)]
  · simp
  · intro ij hij hne
    have hij' := Finset.mem_antidiagonal.mp hij
    have hj : 0 < ij.2 := by
      by_contra hn
      have hz : ij.2 = 0 := by omega
      apply hne
      apply Prod.ext <;> simp_all
    rw [stepanov_hasseDeriv_X_card_mul j ij.2 hj (by omega), mul_zero]
  · simp

/-- Equation (20), with the necessary extraction range `k ≤ ell`. -/
theorem stepanov_hasseDeriv_pow_mul_ansatz
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (hk : k ≤ ell) (hkq : k < Fintype.card F) :
    hasseDeriv k (f ^ ell * stepanovAnsatz f r s) =
      f ^ (ell - k) *
        ∑ j : Fin J,
          (stepanovHasseOperator f hf ell k (r j) +
            stepanovHasseOperator f hf (ell + (Fintype.card F - 1) / 2) k (s j) *
              f ^ ((Fintype.card F - 1) / 2)) * X ^ (j.val * Fintype.card F) := by
  classical
  have he : ell + (Fintype.card F - 1) / 2 - k =
      ell - k + (Fintype.card F - 1) / 2 := by omega
  simp only [stepanovAnsatz, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hblock :
      f ^ ell * ((r j + s j * f ^ ((Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F)) =
      (r j * f ^ ell + s j * f ^ (ell + (Fintype.card F - 1) / 2)) *
        X ^ (j.val * Fintype.card F) := by
    rw [pow_add]
    ring
  rw [hblock, stepanov_hasseDeriv_mul_X_card_mul _ _ _ hkq, map_add,
    stepanovHasseOperator_spec f hf ell k,
    stepanovHasseOperator_spec f hf (ell + (Fintype.card F - 1) / 2) k,
    he, pow_add]
  ring

/-- Evaluating (20) at `f(x)^((q-1)/2) = a` gives precisely (22). -/
theorem stepanov_hasseDeriv_pow_mul_ansatz_eval
    (f : F[X]) (hf : f ≠ 0) (ell k : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a x : F)
    (hk : k < ell) (hell : ell ≤ Fintype.card F)
    (hx : f.eval x ^ ((Fintype.card F - 1) / 2) = a) :
    (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x =
      f.eval x ^ (ell - k) *
        (stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s).eval x := by
  rw [stepanov_hasseDeriv_pow_mul_ansatz f hf ell k r s (Nat.le_of_lt hk)
    (lt_of_lt_of_le hk hell)]
  simp only [stepanovConstraint, eval_mul, eval_pow, eval_finsetSum, eval_add,
    eval_X, eval_smul, smul_eq_mul, hx]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [Nat.mul_comm j.val, pow_mul, FiniteField.pow_card]
  ring

omit [Fintype F] in
/-- At a zero of `f`, the multiplier `f^ell` itself supplies all required
Hasse vanishing, independently of the coefficient equations. -/
theorem stepanov_hasseDeriv_pow_mul_eval_zero
    (f g : F[X]) (ell k : ℕ) (x : F) (hk : k < ell) (hx : f.eval x = 0) :
    (hasseDeriv k (f ^ ell * g)).eval x = 0 := by
  obtain ⟨u, hu⟩ := stepanov_pow_dvd_hasseDeriv_mul_pow f g ell k
  rw [mul_comm (f ^ ell) g, hu, eval_mul, eval_pow, hx,
    zero_pow (by omega : ell - k ≠ 0), zero_mul]

/-- The actual equation system (22) forces Hasse vanishing of the actual
auxiliary polynomial at the union of the two specified loci. -/
theorem stepanov_constraints_imply_hasse_vanishing
    (f : F[X]) (hf : f ≠ 0) (ell : ℕ) {J : ℕ}
    (r s : Fin J → F[X]) (a : F) (hell : ell ≤ Fintype.card F)
    (hc : ∀ k < ell,
      stepanovConstraint f hf ell ((Fintype.card F - 1) / 2) a k r s = 0) :
    ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
      ∀ k < ell, (hasseDeriv k (f ^ ell * stepanovAnsatz f r s)).eval x = 0 := by
  intro x hx k hk
  rcases hx with hx | hx
  · exact stepanov_hasseDeriv_pow_mul_eval_zero f (stepanovAnsatz f r s) ell k x hk hx
  · rw [stepanov_hasseDeriv_pow_mul_ansatz_eval f hf ell k r s a x hk hell hx,
      hc k hk, eval_zero, mul_zero]

omit [Fintype F] in
private theorem stepanov_degree_mul_lt_add_natDegree
    (p g : F[X]) (B : ℕ) (hp : p.degree < (B : WithBot ℕ)) :
    (p * g).degree < ((B + g.natDegree : ℕ) : WithBot ℕ) := by
  calc
    (p * g).degree ≤ p.degree + g.degree := degree_mul_le p g
    _ ≤ p.degree + (g.natDegree : WithBot ℕ) :=
      add_le_add le_rfl degree_le_natDegree
    _ < (B : WithBot ℕ) + (g.natDegree : WithBot ℕ) :=
      WithBot.add_lt_add_right (by simp) hp
    _ = _ := by rw [Nat.cast_add]

/-- Degree of the block ansatz, including the empty family and zero
coefficients. The strict `degree` convention also covers `B = 0`. -/
theorem stepanovAnsatz_degree_lt
    (f : F[X]) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F : ℕ) : WithBot ℕ) := by
  apply mem_degreeLT.mp
  apply Submodule.sum_mem
  intro j _
  apply mem_degreeLT.mpr
  have hr' : (r j).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    apply (hr j).trans_le
    exact_mod_cast Nat.le_add_right B ((Fintype.card F - 1) / 2 * f.natDegree)
  have hs' : (s j * f ^ ((Fintype.card F - 1) / 2)).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) := by
    simpa only [natDegree_pow] using
      stepanov_degree_mul_lt_add_natDegree (s j)
        (f ^ ((Fintype.card F - 1) / 2)) B (hs j)
  have hd := (degree_add_le _ _).trans_lt (max_lt hr' hs')
  rw [degree_mul_X_pow]
  calc
    _ < ((B + (Fintype.card F - 1) / 2 * f.natDegree : ℕ) : WithBot ℕ) +
        ((j.val * Fintype.card F : ℕ) : WithBot ℕ) :=
      WithBot.add_lt_add_right WithBot.coe_ne_bot hd
    _ ≤ _ := by
      rw [← Nat.cast_add]
      exact_mod_cast Nat.add_le_add_left
        (Nat.mul_le_mul_right (Fintype.card F) (show j.val ≤ J - 1 by omega)) _

/-- Degree budget for the actual auxiliary polynomial used in point counting. -/
theorem stepanov_pow_mul_ansatz_degree_lt
    (f : F[X]) (ell : ℕ) {J B : ℕ} (r s : Fin J → F[X])
    (hr : ∀ j, (r j).degree < (B : WithBot ℕ))
    (hs : ∀ j, (s j).degree < (B : WithBot ℕ)) :
    (f ^ ell * stepanovAnsatz f r s).degree <
      ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) := by
  rw [mul_comm]
  simpa only [natDegree_pow] using
    stepanov_degree_mul_lt_add_natDegree (stepanovAnsatz f r s) (f ^ ell)
      (B + (Fintype.card F - 1) / 2 * f.natDegree + (J - 1) * Fintype.card F)
      (stepanovAnsatz_degree_lt f r s hr hs)

/-- Harcos's auxiliary polynomial exists from the actual dimension
inequality, with nonvanishing, degree control, and genuine Hasse vanishing. -/
theorem stepanov_exists_auxiliary_polynomial
    (f : F[X]) (ell B J : ℕ) (a : F)
    (hq : Odd (Fintype.card F)) (hf0 : f.eval 0 ≠ 0)
    (hf : ¬ IsSquare (f.map (algebraMap F (AlgebraicClosure F))))
    (hm : 1 ≤ f.natDegree) (hJ : 0 < J) (hell : ell ≤ Fintype.card F)
    (hB : 2 * (B - 1) + f.natDegree < Fintype.card F)
    (hcount : (∑ k : Fin ell, (B + k.val * (f.natDegree - 1) + (J - 1))) <
      2 * J * B) :
    ∃ h : F[X], h ≠ 0 ∧
      h.degree < ((B + (Fintype.card F - 1) / 2 * f.natDegree +
        (J - 1) * Fintype.card F + ell * f.natDegree : ℕ) : WithBot ℕ) ∧
      ∀ x : F, f.eval x = 0 ∨ f.eval x ^ ((Fintype.card F - 1) / 2) = a →
        ∀ k < ell, (hasseDeriv k h).eval x = 0 := by
  have hfne : f ≠ 0 := by
    intro hz
    apply hf0
    simp [hz]
  obtain ⟨r, s, hr, hs, hne, hc⟩ :=
    stepanov_exists_coefficients f hfne ell ((Fintype.card F - 1) / 2) B J a hm hJ hcount
  exact ⟨f ^ ell * stepanovAnsatz f r s,
    stepanov_pow_mul_ansatz_ne_zero f ell r s hq hf0 hf hr hs hB hne,
    stepanov_pow_mul_ansatz_degree_lt f ell r s hr hs,
    stepanov_constraints_imply_hasse_vanishing f hfne ell r s a hell hc⟩

end MathlibNt.AnalyticNumberTheory.LargeSieve.LiLiuPrereqFouvry
