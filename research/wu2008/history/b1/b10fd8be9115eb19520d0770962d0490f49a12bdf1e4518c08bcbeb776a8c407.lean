import MathlibNt.Wu2008DoubleSieve.LocalProductReal
import MathlibNt.Wu2008DoubleSieve.ConvolutionWuBoxes

/-!
# Uniform local normalization on Wu's actual convolution support

Source: Wu04 §3, (3.1), (3.10). The last squared-prefix inequality controls
the quotient `Q/d`; the zero-depth convolution is the unit at `d = 1`.
All thresholds below precede the windows, their depth, their support integers,
and `s ∈ [1,10]`. Nothing here estimates the sieve remainder or box mass.
-/

namespace Wu2008DoubleSieve

open Finset Real Filter
open scoped Topology Classical

/-- A positive exponent also valid at depth zero. -/
noncomputable def wuLocalExponent (k : ℕ) (δ : ℝ) : ℝ :=
  min (δ ^ (k + 1)) (1 / 2 - δ)

theorem wuLocalExponent_pos (k : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    0 < wuLocalExponent k δ :=
  lt_min (pow_pos hδ _) (sub_pos.mpr hδ')

/-- The literal moving cutoff `underline d ^ (1/s)` in (3.10). -/
noncomputable def wuLocalCutoff (N : ℕ) (δ : ℝ) (d : ℕ) (s : ℝ) : ℝ :=
  ((N : ℝ) ^ (1 / 2 - δ) / d) ^ (1 / s)

private theorem box_product_mul_lower_le {i : ℕ} (V : Fin i → ℝ)
    {W Q : ℝ} (hW : 0 < W) (hWQ : W ≤ Q)
    (hV : ∀ j, W ≤ V j)
    (hsq : ∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤ Q) :
    (∏ j, V j) * W ≤ Q := by
  cases i with
  | zero => simpa using hWQ
  | succ n =>
    have hlast := hsq (Fin.last n)
    rw [Fin.prod_univ_castSucc] at hlast
    simp only [Fin.castSucc_lt_last, if_true, lt_self_iff_false, if_false, mul_one] at hlast
    rw [Fin.prod_univ_castSucc]
    have hp : 0 ≤ ∏ j : Fin n, V j.castSucc :=
      prod_nonneg fun j _ => (hW.trans_le (hV j.castSucc)).le
    have hl := hV (Fin.last n)
    nlinarith [mul_le_mul_of_nonneg_left hl
      (mul_nonneg hp (hW.trans_le hl).le)]

/-- The support and the squared-prefix conditions themselves produce the
polynomially large quotient. This includes empty support and depth zero. -/
theorem wuLocal_support_bounds {i k N d : ℕ} {Δ δ : ℝ} {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hV : ∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j)
    (hsq : ∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤
      (N : ℝ) ^ (1 / 2 - δ))
    (hd : d ∈ (Fintype.piFinset (convolutionWuWindows N Δ V)).image
      (fun t => ∏ j, t j)) :
    0 < d ∧ d ≤ N ∧
      (N : ℝ) ^ (wuLocalExponent k δ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d := by
  obtain ⟨t, ht, rfl⟩ := mem_image.mp hd
  have ht' := Fintype.mem_piFinset.mp ht
  have hd0 : 0 < ∏ j, t j :=
    prod_pos fun j _ => (mem_convolutionWuWindows.mp (ht' j)).1.pos
  have hd0' : (0 : ℝ) < (∏ j, t j : ℕ) := by exact_mod_cast hd0
  have hdV : ((∏ j, t j : ℕ) : ℝ) ≤ ∏ j, V j := by
    rw [Nat.cast_prod]
    exact prod_le_prod (fun j _ => Nat.cast_nonneg (t j))
      (fun j _ => (mem_convolutionWuWindows.mp (ht' j)).2.2.2.le)
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη := wuLocalExponent_pos k hδ hδ'
  have hlow : ∀ j, (N : ℝ) ^ (wuLocalExponent k δ) ≤ V j := by
    intro j
    exact (rpow_le_rpow_of_exponent_le hN' (min_le_left _ _)).trans (hV j)
  have hWQ : (N : ℝ) ^ (wuLocalExponent k δ) ≤ (N : ℝ) ^ (1 / 2 - δ) :=
    rpow_le_rpow_of_exponent_le hN' (min_le_right _ _)
  have hW : 0 < (N : ℝ) ^ (wuLocalExponent k δ) := rpow_pos_of_pos (by linarith) _
  have hprod := box_product_mul_lower_le V hW hWQ hlow hsq
  have hdW :
      ((∏ j, t j : ℕ) : ℝ) * (N : ℝ) ^ (wuLocalExponent k δ) ≤
        (N : ℝ) ^ (1 / 2 - δ) :=
    (mul_le_mul_of_nonneg_right hdV hW.le).trans hprod
  have hW1 : 1 ≤ (N : ℝ) ^ (wuLocalExponent k δ) := one_le_rpow hN' hη.le
  have hQN : (N : ℝ) ^ (1 / 2 - δ) ≤ N := by
    simpa only [rpow_one] using
      rpow_le_rpow_of_exponent_le hN' (show 1 / 2 - δ ≤ 1 by linarith)
  refine ⟨hd0, ?_, (le_div_iff₀ hd0').mpr (by simpa [mul_comm] using hdW)⟩
  exact_mod_cast (show ((∏ j, t j : ℕ) : ℝ) ≤ N by nlinarith)

/-- The source support yields a cutoff growing by a *fixed* positive power,
uniformly for all `s ∈ [1,10]`. -/
theorem wuLocalCutoff_lower {k N d : ℕ} {δ s : ℝ}
    (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hs : 1 ≤ s) (hs' : s ≤ 10)
    (hquot : (N : ℝ) ^ (wuLocalExponent k δ) ≤ (N : ℝ) ^ (1 / 2 - δ) / d) :
    (N : ℝ) ^ (wuLocalExponent k δ / 10) ≤ wuLocalCutoff N δ d s := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hη := wuLocalExponent_pos k hδ hδ'
  have hsp : 0 < s := by linarith
  have hexp : wuLocalExponent k δ / 10 ≤ wuLocalExponent k δ * (1 / s) := by
    have := one_div_le_one_div_of_le hsp hs'
    nlinarith
  calc
    _ ≤ (N : ℝ) ^ (wuLocalExponent k δ * (1 / s)) :=
      rpow_le_rpow_of_exponent_le hN' hexp
    _ = ((N : ℝ) ^ (wuLocalExponent k δ)) ^ (1 / s) :=
      rpow_mul (by positivity) _ _
    _ ≤ _ := rpow_le_rpow (by positivity) hquot (by positivity)

/-- An explicit uniform decay bound for the omitted divisor correction at
the actual moving cutoff. Unlike the final epsilon theorem, this states the
rate, including the rounding loss. Neither squarefreeness nor evenness is
needed for this finite divisor-product estimate. -/
theorem wuLocal_divisorTail_bound {i k N d : ℕ} {Δ δ s : ℝ} {V : Fin i → ℝ}
    (hN : 1 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hV : ∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j)
    (hsq : ∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤
      (N : ℝ) ^ (1 / 2 - δ))
    (hd : convolutionCoeff (convolutionWuWindows N Δ V) d ≠ 0)
    (hs : 1 ≤ s) (hs' : s ≤ 10)
    (hsize : 3 ≤ (N : ℝ) ^ (wuLocalExponent k δ / 10)) :
    1 - localDivisorTail (d * N) (localClosedCutoff (wuLocalCutoff N δ d s)) ≤
      4 * log N / (log 2 * (N : ℝ) ^ (wuLocalExponent k δ / 10)) := by
  obtain ⟨t, ht, htd⟩ := convolutionCoeff_pos_iff.mp (Nat.pos_of_ne_zero hd)
  have hdmem := mem_image.mpr ⟨t, Fintype.mem_piFinset.mpr ht, htd⟩
  obtain ⟨hd0, hdN, hquot⟩ := wuLocal_support_bounds hN hδ hδ' hV hsq hdmem
  have hcut := wuLocalCutoff_lower hN hδ hδ' hs hs' hquot
  have hy := localClosedCutoff_bounds (wuLocalCutoff N δ d s) (hsize.trans hcut)
  have hround :
      (N : ℝ) ^ (wuLocalExponent k δ / 10) / 2 ≤
        (localClosedCutoff (wuLocalCutoff N δ d s) : ℝ) := by
    have hy2 : (2 : ℝ) ≤ localClosedCutoff (wuLocalCutoff N δ d s) := by
      exact_mod_cast hy.1
    linarith [hy.2.2]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : 0 < d * N := Nat.mul_pos hd0 (by omega)
  have hlogM : log (d * N : ℕ) ≤ 2 * log N := by
    have hMN : ((d * N : ℕ) : ℝ) ≤ (N : ℝ) * N := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdN) hN0.le
    have hl := log_le_log (by exact_mod_cast hM0) hMN
    rw [log_mul hN0.ne' hN0.ne'] at hl
    linarith
  have hlogN : 0 ≤ log (N : ℝ) := log_nonneg (by exact_mod_cast hN)
  calc
    _ ≤ log (d * N : ℕ) /
        (log 2 * (localClosedCutoff (wuLocalCutoff N δ d s) : ℝ)) :=
      one_sub_localDivisorTail_le_log (d * N) _ hM0 hy.1
    _ ≤ (2 * log N) /
        (log 2 * (localClosedCutoff (wuLocalCutoff N δ d s) : ℝ)) :=
      div_le_div_of_nonneg_right hlogM (by positivity)
    _ ≤ (2 * log N) / (log 2 * ((N : ℝ) ^ (wuLocalExponent k δ / 10) / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (mul_le_mul_of_nonneg_left hround (by positivity))
    _ = _ := by ring

/-- The source support forces a strictly positive main term already for
`N ≥ 2`. This independently rules out a zero-denominator interpretation of
the relative normalization and is available to subsequent consumers. -/
theorem wuLocal_main_pos {i k N d : ℕ} {Δ δ s : ℝ} {V : Fin i → ℝ}
    (hN : 2 ≤ N) (hδ : 0 < δ) (hδ' : δ < 1 / 2)
    (hV : ∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j)
    (hsq : ∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤
      (N : ℝ) ^ (1 / 2 - δ))
    (hd : convolutionCoeff (convolutionWuWindows N Δ V) d ≠ 0) (hs : 0 < s) :
    0 < 2 * s * wuSingularSeries (d * N) /
      (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
  obtain ⟨t, ht, htd⟩ := convolutionCoeff_pos_iff.mp (Nat.pos_of_ne_zero hd)
  have hdmem := mem_image.mpr ⟨t, Fintype.mem_piFinset.mpr ht, htd⟩
  obtain ⟨hd0, _, hquot⟩ := wuLocal_support_bounds (by omega) hδ hδ' hV hsq hdmem
  have hq1 : 1 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    (one_lt_rpow (by exact_mod_cast (by omega : 1 < N))
      (wuLocalExponent_pos k hδ hδ')).trans_le hquot
  exact div_pos (mul_pos (mul_pos (by norm_num) hs)
    (wuSingularSeries_pos _ (Nat.mul_pos hd0 (by omega))))
      (mul_pos (exp_pos _) (log_pos hq1))

/-- Wu04 (3.10), with an explicit relative-error quantifier and the actual
coefficient support. The strict prime product, `C(d*N)`, factor two, real
moving cutoff, and evenness are all literal. No normalization input is
assumed. Fixed `k,δ,ε` choose `N₀` before every box and every `s`.

The depth bound, ordering, and Δ bounds are retained to display the source
family. This particular normalization needs only its lower window bounds
and squared-prefix inequalities. -/
theorem wu04_310_local_normalization (k : ℕ) (_hk : 1 ≤ k)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 / 2) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∀ i : ℕ, i ≤ k → ∀ Δ : ℝ,
        1 + log (N : ℝ) ^ (-4 : ℝ) ≤ Δ →
        Δ < 1 + 2 * log (N : ℝ) ^ (-4 : ℝ) →
        ∀ V : Fin i → ℝ, Antitone V →
          (∀ j, (N : ℝ) ^ (δ ^ (k + 1)) ≤ V j) →
          (∀ j, (∏ l, if l < j then V l else 1) * V j ^ 2 ≤
            (N : ℝ) ^ (1 / 2 - δ)) →
          ∀ d : ℕ, convolutionCoeff (convolutionWuWindows N Δ V) d ≠ 0 →
            ∀ s : ℝ, 1 ≤ s → s ≤ 10 →
              |localSieveProduct (d * N) (wuLocalCutoff N δ d s) /
                (2 * s * wuSingularSeries (d * N) /
                  (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d))) - 1| ≤ ε := by
  let α := wuLocalExponent k δ / 10
  have hα : 0 < α := div_pos (wuLocalExponent_pos k hδ hδ') (by norm_num)
  obtain ⟨Z, hZ⟩ := eventually_atTop.mp
    (eventually_localSieveProduct_relative (2 / α) ε (by positivity) hε)
  have hpows : ∀ᶠ N : ℕ in atTop, max Z 3 ≤ (N : ℝ) ^ α :=
    ((tendsto_rpow_atTop hα).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop (max Z 3))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hpows.and (eventually_ge_atTop 2))
  refine ⟨N₀, ?_⟩
  intro N hN hEven i _hik Δ _hΔlo _hΔhi V _horder hV hsq d hd s hs hs'
  have hlarge := hN₀ N hN
  have hN1 : 1 ≤ N := by omega
  have hdmem : d ∈ (Fintype.piFinset (convolutionWuWindows N Δ V)).image
      (fun t => ∏ j, t j) := by
    obtain ⟨t, ht, htd⟩ := convolutionCoeff_pos_iff.mp (Nat.pos_of_ne_zero hd)
    exact mem_image.mpr ⟨t, Fintype.mem_piFinset.mpr ht, htd⟩
  obtain ⟨hd0, hdN, hquot⟩ := wuLocal_support_bounds hN1 hδ hδ' hV hsq hdmem
  have hcut : (N : ℝ) ^ α ≤ wuLocalCutoff N δ d s :=
    wuLocalCutoff_lower hN1 hδ hδ' hs hs' hquot
  have hz : 3 ≤ wuLocalCutoff N δ d s :=
    ((le_max_right _ _).trans hlarge.1).trans hcut
  have hZcut : Z ≤ wuLocalCutoff N δ d s :=
    ((le_max_left _ _).trans hlarge.1).trans hcut
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hM0 : 0 < d * N := Nat.mul_pos hd0 (by omega)
  have hpoly : ((d * N : ℕ) : ℝ) ≤ (wuLocalCutoff N δ d s) ^ (2 / α) := by
    calc
      _ ≤ (N : ℝ) ^ (2 : ℝ) := by
        rw [Nat.cast_mul, Real.rpow_two, pow_two]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hdN) hN0.le
      _ = ((N : ℝ) ^ α) ^ (2 / α) := by
        rw [← rpow_mul hN0.le]
        congr 1
        field_simp
      _ ≤ _ := rpow_le_rpow (by positivity) hcut (by positivity)
  have hrel := hZ (wuLocalCutoff N δ d s) hZcut (d * N) hM0
    (hEven.mul_left d) hpoly
  have hs0 : s ≠ 0 := by linarith
  have hq0 : 0 < (N : ℝ) ^ (1 / 2 - δ) / d :=
    div_pos (rpow_pos_of_pos hN0 _) (by exact_mod_cast hd0)
  have hlog : log (wuLocalCutoff N δ d s) =
      (1 / s) * log ((N : ℝ) ^ (1 / 2 - δ) / d) :=
    log_rpow hq0 _
  have hlz : log (wuLocalCutoff N δ d s) ≠ 0 :=
    ne_of_gt (log_pos (by linarith))
  have hlq : log ((N : ℝ) ^ (1 / 2 - δ) / d) ≠ 0 := by
    intro he
    simp only [he, mul_zero] at hlog
    exact hlz hlog
  have hmain :
      2 * exp (-eulerMascheroniConstant) * wuSingularSeries (d * N) /
          log (wuLocalCutoff N δ d s) =
        2 * s * wuSingularSeries (d * N) /
          (exp eulerMascheroniConstant * log ((N : ℝ) ^ (1 / 2 - δ) / d)) := by
    rw [hlog, exp_neg]
    field_simp
  rwa [hmain] at hrel

end Wu2008DoubleSieve
