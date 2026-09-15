import MathlibNt.SieveTheory.LiLiuPrereqBuchstabUniform
import MathlibNt.SieveTheory.LiLiuPrereqBuchstabPNT

open Finset Real Filter LiLiuPrereqBuchstab

namespace Wu2008DoubleSieve.NonunitRoughUniform

/-- The actual rough carrier with the unit removed. -/
noncomputable def count (x y : ℝ) : ℕ := ((roughNumbers x y).erase 1).card

theorem nonunit_eq_primes {x y : ℝ} (hy : 0 ≤ y) (hxy : x < y ^ 2) :
    (roughNumbers x y).erase 1 = primeNumbers x y := by
  classical
  ext n
  rw [mem_erase, rough_below_sq_iff hy hxy, mem_primeNumbers]
  constructor
  · rintro ⟨hn1, h | h⟩
    · exact False.elim (hn1 h.1)
    · exact h
  · intro h
    exact ⟨h.1.ne_one, Or.inr h⟩

theorem nonunit_empty {x y : ℝ} (hy : 1 ≤ y) (hxy : x < y) :
    (roughNumbers x y).erase 1 = ∅ := by
  rw [nonunit_eq_primes (by linarith) (by nlinarith)]
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨_, hlo, hhi⟩ := mem_primeNumbers.mp hn
  linarith

theorem count_eq_zero {x y : ℝ} (hy : 1 ≤ y) (hxy : x < y) :
    count x y = 0 := by
  simp [count, nonunit_empty hy hxy]

theorem count_le_roughCount (x y : ℝ) : count x y ≤ roughCount x y := by
  exact card_le_card (erase_subset _ _)

theorem count_le_primePi {x y : ℝ} (hy : 0 ≤ y) (hxy : x < y ^ 2) :
    (count x y : ℝ) ≤ primePi x := by
  classical
  have hsub : primeNumbers x y ⊆ (Nat.floor x).primesLE := by
    intro n hn
    obtain ⟨hp, _, hnx⟩ := mem_primeNumbers.mp hn
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor hnx, hp⟩
  have hc := card_le_card hsub
  rw [Nat.primesLE_card_eq_primeCounting] at hc
  simpa [count, nonunit_eq_primes hy hxy, primePi] using (Nat.cast_le (α := ℝ)).mpr hc

/-- A genuine PNT consequence, not a supplied prime-count hypothesis. -/
theorem exists_primePi_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ Z : ℝ, 1 < Z ∧ ∀ x ≥ Z, primePi x ≤ (1 + ε) * x / log x := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp
    (tendsto_primeErrorEnvelope.eventually (gt_mem_nhds hε))
  let Z := max 2 (max primeErrorStart a)
  have hZ : 1 < Z := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨Z, hZ, ?_⟩
  intro x hx
  have hx1 : 1 < x := hZ.trans_le hx
  have he := primePi_error_le (le_trans (le_max_left _ _) (le_max_right 2 _)) hx
  have heps : primeErrorEnvelope Z < ε := ha Z (le_trans (le_max_right _ _) (le_max_right 2 _))
  have hp : 0 ≤ x / log x := le_of_lt (div_pos (lt_trans zero_lt_one hx1) (log_pos hx1))
  have hb := (le_abs_self (primePi x - x / log x)).trans he
  have hh := mul_le_mul_of_nonneg_right heps.le hp
  calc
    primePi x ≤ x / log x + ε * (x / log x) := by linarith
    _ = (1 + ε) * x / log x := by ring

theorem log_ratio_ge_one {x y : ℝ} (hy : 1 < y) (hxy : y ≤ x) :
    1 ≤ log x / log y := by
  exact (one_le_div (log_pos hy)).mpr (log_le_log (by linarith) hxy)

theorem rpow_inv_log_ratio {x y : ℝ} (hy : 1 < y) (hxy : y ≤ x) :
    x ^ (1 / (log x / log y)) = y := by
  have hx : 1 < x := hy.trans_le hxy
  rw [rpow_def_of_pos (by linarith)]
  have he : log x * (1 / (log x / log y)) = log y := by
    field_simp [(log_pos hx).ne', (log_pos hy).ne']
  rw [he, exp_log (by linarith)]

theorem below_square {x y : ℝ} (hy : 1 < y) (hxy : y ≤ x)
    (hu : log x / log y ≤ (3 : ℝ) / 2) : x < y ^ 2 := by
  have hx : 0 < x := lt_of_lt_of_le (by linarith : 0 < y) hxy
  have hlog : log x ≤ (3 : ℝ) / 2 * log y := (div_le_iff₀ (log_pos hy)).mp hu
  apply (log_lt_log_iff hx (sq_pos_of_pos (by linarith))).mp
  rw [log_pow]
  norm_num
  nlinarith [log_pos hy]

theorem small_upper {ε x y : ℝ} (hε : 0 < ε) (hy : 1 < y) (hxy : y ≤ x)
    (hu : log x / log y ≤ (3 : ℝ) / 2)
    (hp : primePi x ≤ (1 + ε) * x / log x) :
    (count x y : ℝ) ≤ (buchstab (log x / log y) + ε) * x / log y := by
  have hx : 1 < x := hy.trans_le hxy
  have hly := log_pos hy
  have hlx := log_pos hx
  have hlxy := log_le_log (by linarith : 0 < y) hxy
  have hb := buchstab_eq_one_div (log_ratio_ge_one hy hxy) (by linarith : log x / log y ≤ 2)
  have hc := count_le_primePi (by linarith : 0 ≤ y) (below_square hy hxy hu)
  refine hc.trans (hp.trans ?_)
  rw [hb]
  have hid : (1 / (log x / log y) + ε) * x / log y =
      x / log x + ε * (x / log y) := by
    field_simp
  rw [hid]
  have hd : x / log x ≤ x / log y :=
    div_le_div_of_nonneg_left (by linarith) hly hlxy
  have hm := mul_le_mul_of_nonneg_left hd hε.le
  calc
    (1 + ε) * x / log x = x / log x + ε * (x / log x) := by ring
    _ ≤ x / log x + ε * (x / log y) := add_le_add le_rfl hm

end Wu2008DoubleSieve.NonunitRoughUniform
