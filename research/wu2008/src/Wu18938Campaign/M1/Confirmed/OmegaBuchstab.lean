import Wu18938Campaign.M1.Confirmed.OmegaRemainders
import Wu18938Campaign.M1.Confirmed.SourceGeometry
import MathlibNt.Wu2008DoubleSieve.Omega3XBuchstabSource

noncomputable section

namespace Wu18938Campaign.M1.Confirmed.Omega

open Wu2008DoubleSieve Finset Real Filter LiLiuPrereqBuchstab
open scoped Classical Topology

theorem prime_interval {m i N d : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s t d) :
    p.1 ∈ primesIcc ((N : ℝ) ^ (η / 10)) N ∧
    p.2.1 ∈ primesIcc ((N : ℝ) ^ (η / 10)) N ∧
    p.2.2 ∈ primesIcc ((N : ℝ) ^ (η / 10)) N := by
  rcases p with ⟨p1,p2,p3⟩
  obtain ⟨hp2,hp1,hp3N,hp3,h23,_⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have h12 : p1 < p2 := by exact_mod_cast h1.2.2.2
  have hlow := roughBox_cutoff_lower hb hN hη hδ hd (by linarith : 1 ≤ t) ht
  refine ⟨(mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h1.1,hlow.trans h1.2.2.1,?_⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨h2.1,hlow.trans h2.2.2.1,?_⟩,
    (mem_primesIcc (Nat.cast_nonneg N)).mpr ⟨hp3,?_,?_⟩⟩
  · exact_mod_cast (h12.le.trans h23.le).trans hp3N
  · exact_mod_cast h23.le.trans hp3N
  · exact (hlow.trans h2.2.2.1).trans (by exact_mod_cast h23.le)
  · exact_mod_cast hp3N

theorem X_geometry {m i N d : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    {p : ℕ × ℕ × ℕ} (hp : p ∈ omega3XPrimes N δ s t d) :
    0 < omega3XScale N d p.1 p.2.1 p.2.2 ∧
    (N : ℝ) ^ (η / 10) ≤ p.2.1 ∧
    (p.2.1 : ℝ) < omega3XScale N d p.1 p.2.1 p.2.2 ∧
    4 ≤ log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1 ∧
    log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1 ≤ 1 / (η / 10) := by
  obtain ⟨hp2,hp1,_,hp3,h23,h3s⟩ := mem_omega3XPrimes.mp hp
  have h1 := mem_primeWindow.mp hp1
  have h2 := mem_primeWindow.mp hp2
  have hd0 := hb.support_pos hd
  have hNr : (0 : ℝ) < N := by positivity
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have h10 : (0 : ℝ) < p.1 := by exact_mod_cast h1.1.pos
  have h20 : (0 : ℝ) < p.2.1 := by exact_mod_cast h2.1.pos
  have h30 : (0 : ℝ) < p.2.2 := by exact_mod_cast hp3.pos
  have hx : 0 < omega3XScale N d p.1 p.2.1 p.2.2 := by unfold omega3XScale; positivity
  have hl2 : 0 < log (p.2.1 : ℝ) := log_pos (by exact_mod_cast h2.1.one_lt)
  have hR := (hb.support_geometry hN hη hδ hd).2.2.1
  have hg := roughBox_log_geometry hb hN hη hδ hd
  have hphi := (le_div_iff₀ (log_pos hR)).mp hg.2.2.1
  have h3 := h3s.trans (rpow_le_rpow_of_exponent_le hR.le
    (one_div_le_one_div_of_le (by norm_num) hs))
  have hlog3 := log_le_log h30 h3
  rw [log_rpow (lt_trans zero_lt_one hR)] at hlog3
  have hlog12 := log_lt_log h10 h1.2.2.2
  have hlog23 := log_lt_log h20 (by exact_mod_cast h23 : (p.2.1 : ℝ) < p.2.2)
  have hxlog : log (omega3XScale N d p.1 p.2.1 p.2.2) =
      log ((N : ℝ) / d) - log p.1 - log p.2.1 - log p.2.2 := by
    rw [omega3XScale,log_div hNr.ne' (by positivity),
      log_mul (by positivity) h30.ne',log_mul (by positivity) h20.ne',
      log_mul (by exact_mod_cast hd0.ne') h10.ne',
      log_div hNr.ne' (by exact_mod_cast hd0.ne')]
    ring
  have hu : 4 ≤ log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1 := by
    rw [le_div_iff₀ hl2,hxlog]
    change (7 / 2 : ℝ) * log ((N : ℝ) ^ (1 / 2 - δ) / d) ≤ log ((N : ℝ) / d) at hphi
    linarith
  have hxy : (p.2.1 : ℝ) < omega3XScale N d p.1 p.2.1 p.2.2 := by
    apply (log_lt_log_iff h20 hx).mp
    have hh := (le_div_iff₀ hl2).mp hu
    linarith
  have hy := ((mem_primesIcc (Nat.cast_nonneg N)).mp
    (prime_interval hb hN hη hδ hs hst ht hd hp).2.1).2.1
  have hxN : omega3XScale N d p.1 p.2.1 p.2.2 ≤ N :=
    div_le_self hNr.le (by
      exact_mod_cast (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hd0 h1.1.pos) h2.1.pos) hp3.pos))
  have hlow := log_le_log (rpow_pos_of_pos hNr _) hy
  rw [log_rpow hNr] at hlow
  refine ⟨hx,hy,hxy,hu,?_⟩
  apply (div_le_iff₀ hl2).mpr
  calc
    _ ≤ log N := log_le_log hx hxN
    _ ≤ log (p.2.1 : ℝ) / (η / 10) := (le_div_iff₀ (by positivity)).mpr (by linarith)
    _ = _ := by ring

theorem scale_mass {m i N d : ℕ} {η δ Δ s t : ℝ} {V : Fin i → ℝ}
    (hb : RoughBox m η δ N i Δ V) (hN : 2 ≤ N) (hη : 0 < η) (hδ : 0 < δ)
    (hs : 2 ≤ s) (hst : s ≤ t) (ht : t ≤ 10)
    (hd : d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V))
    (hstart : primeErrorStart ≤ (N : ℝ) ^ (η / 10)) :
    (∑ p ∈ omega3XPrimes N δ s t d,
      omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) ≤
      ((5 / (η / 10)) ^ 3 / (η / 10)) * ((N : ℝ) / d / log N) := by
  have hlogN : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hsum := omega3X_prime_triple_reciprocal_le hN (show 0 < η / 10 by positivity) hstart
    (omega3XPrimes N δ s t d) (fun p hp => prime_interval hb hN hη hδ hs hst ht hd hp)
  calc
    _ ≤ ∑ p ∈ omega3XPrimes N δ s t d,
        ((N : ℝ) / d / ((η / 10) * log N)) * (1 / ((p.1 : ℝ) * p.2.1 * p.2.2)) := by
      apply sum_le_sum
      intro p hp
      have hlow := ((mem_primesIcc (Nat.cast_nonneg N)).mp
        (prime_interval hb hN hη hδ hs hst ht hd hp).2.1).2.1
      have hl := log_le_log (rpow_pos_of_pos (by positivity : (0 : ℝ) < N) _) hlow
      rw [log_rpow (by positivity : (0 : ℝ) < N)] at hl
      calc
        _ ≤ omega3XScale N d p.1 p.2.1 p.2.2 / ((η / 10) * log N) :=
          div_le_div_of_nonneg_left (by unfold omega3XScale; positivity) (by positivity) hl
        _ = _ := by unfold omega3XScale; ring
    _ = ((N : ℝ) / d / ((η / 10) * log N)) *
        ∑ p ∈ omega3XPrimes N δ s t d, 1 / ((p.1 : ℝ) * p.2.1 * p.2.2) := (mul_sum ..).symm
    _ ≤ ((N : ℝ) / d / ((η / 10) * log N)) * (5 / (η / 10)) ^ 3 :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

theorem rough_scalar (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ d ∈ boxConvolutionSupport (convolutionWuWindows N Δ V),
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      ∀ p ∈ omega3XPrimes N δ s t d,
      (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) ≤
        omega3XScale N d p.1 p.2.1 p.2.2 *
          buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1 +
        ε * (omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) := by
  let M := ⌈1 / (η / 10)⌉₊ + 4
  obtain ⟨X,_,hX⟩ := roughCount_uniform_buchstab_fixed M (by omega)
    (by norm_num : (1 : ℝ) < 2) he
  obtain ⟨T,hT⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < η / 10 by positivity)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop X))
  refine ⟨max 4 T,le_max_left _ _,?_⟩
  intro N hN i Δ V hb d hd s t hs hst ht p hp
  have hg := X_geometry hb (by omega) hη hδ hs hst ht hd hp
  have hy1 : (1 : ℝ) < p.2.1 := by
    exact_mod_cast (mem_primeWindow.mp (mem_omega3XPrimes.mp hp).1).1.one_lt
  have hu : log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1 ∈ Set.Icc 2 (M : ℝ) := by
    refine ⟨by linarith [hg.2.2.2.1],hg.2.2.2.2.trans ?_⟩
    exact (Nat.le_ceil _).trans (by dsimp [M]; push_cast; linarith)
  have hxX := ((hT N (by omega)).trans hg.2.1).trans hg.2.2.1.le
  obtain ⟨_,_,_,hcoord,hnorm⟩ := omega3X_buchstab_coordinates hy1 hg.2.2.1.le
  obtain ⟨hpos,hrel⟩ := hX _ hxX _ hu
  rw [← hcoord,hnorm] at hrel
  rw [hnorm] at hpos
  let B := omega3XScale N d p.1 p.2.1 p.2.2 *
    buchstab (log (omega3XScale N d p.1 p.2.1 p.2.2) / log p.2.1) / log p.2.1
  have heq : (roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) / B - 1 =
      ((roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) - B) / B := by
    have : B ≠ 0 := hpos.ne'
    field_simp
  change |(roughCount (omega3XScale N d p.1 p.2.1 p.2.2) p.2.1 : ℝ) / B - 1| < ε at hrel
  rw [heq,abs_div,abs_of_pos hpos] at hrel
  have hbnd := ((div_lt_iff₀ hpos).mp hrel).le.trans
    (mul_le_mul_of_nonneg_left (omega3X_buchstab_main_term_bounds hy1 hg.2.2.1.le).2 he.le)
  have hh := (le_abs_self _).trans hbnd
  linarith only [hh]

theorem X_buchstab (m : ℕ) {η δ ε : ℝ}
    (hη : 0 < η) (hδ : 0 < δ) (he : 0 < ε) :
    ∃ T : ℕ, 4 ≤ T ∧ ∀ N : ℕ, T ≤ N →
      ∀ (i : ℕ) (Δ : ℝ) (V : Fin i → ℝ), RoughBox m η δ N i Δ V →
      ∀ s t : ℝ, 2 ≤ s → s ≤ t → t ≤ 10 →
      omega3SieveX N δ s t (convolutionWuWindows N Δ V) ≤
        omega3XBuchstabMain N δ s t (convolutionWuWindows N Δ V) +
        ε * ((N : ℝ) / log N) * boxConvolutionReciprocalMass (convolutionWuWindows N Δ V) := by
  let C : ℝ := (5 / (η / 10)) ^ 3 / (η / 10)
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨T0,hT04,h0⟩ := rough_scalar m hη hδ (show 0 < (ε / 2) / C by positivity)
  obtain ⟨T1,h1⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (show 0 < η / 10 by positivity)).comp tendsto_natCast_atTop_atTop).eventually
      (eventually_ge_atTop primeErrorStart))
  obtain ⟨T2,h2⟩ := eventually_atTop.mp
    (omega3_repeated_scalar_budget (show 0 < η / 10 by positivity) (half_pos he))
  refine ⟨max T0 (max T1 T2),hT04.trans (le_max_left _ _),?_⟩
  intro N hN i Δ V hb s t hs hst ht
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let W := convolutionWuWindows N Δ V
  have hrough : omega3XRoughMajorant N δ s t W ≤ omega3XBuchstabMain N δ s t W +
      ((ε / 2) / C) * (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
        ∑ p ∈ omega3XPrimes N δ s t d, omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) := by
    unfold omega3XRoughMajorant omega3XBuchstabMain
    simp only [mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro d hd
    apply sum_le_sum
    intro p hp
    have hh := mul_le_mul_of_nonneg_left (h0 N (by omega) i Δ V hb d hd s t hs hst ht p hp)
      (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _)
    nlinarith only [hh]
  have hmass : (∑ d ∈ boxConvolutionSupport W, (convolutionCoeff W d : ℝ) *
      ∑ p ∈ omega3XPrimes N δ s t d, omega3XScale N d p.1 p.2.1 p.2.2 / log p.2.1) ≤
      C * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by
    unfold boxConvolutionReciprocalMass
    rw [mul_sum]
    apply sum_le_sum
    intro d hd
    have hh := mul_le_mul_of_nonneg_left
      (scale_mass hb (by omega) hη hδ hs hst ht hd (h1 N (by omega)))
      (Nat.cast_nonneg (convolutionCoeff W d) : (0 : ℝ) ≤ _)
    convert hh using 1
    ring
  have hm := mul_le_mul_of_nonneg_left hmass (show 0 ≤ (ε / 2) / C by positivity)
  have hcancel : ((ε / 2) / C) * (C * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W) =
      (ε / 2) * ((N : ℝ) / log N) * boxConvolutionReciprocalMass W := by field_simp
  rw [hcancel] at hm
  have hrep : omega3XRepeatedMajorant N δ s t W ≤
      (((N : ℝ) / (N : ℝ) ^ (η / 10)) * (1 + log N) ^ 3) * boxConvolutionReciprocalMass W := by
    unfold omega3XRepeatedMajorant omega3XScale
    apply omega3_repeated_weighted_floor_le _ _ (rpow_pos_of_pos hNpos _)
    · intro d hd
      exact hb.support_pos hd
    · intro d _ a ha
      exact omega3XPrimes_mem_Icc ha
    · intro d hd a ha
      exact (roughBox_cutoff_lower hb (by omega) hη hδ hd (by linarith) ht).trans
        (mem_primeWindow.mp (mem_omega3XPrimes.mp ha).2.1).2.2.1
  have hr := hrep.trans (mul_le_mul_of_nonneg_right (h2 N (by omega))
    (show 0 ≤ boxConvolutionReciprocalMass W from sum_nonneg (fun _ _ => by positivity)))
  have hf := omega3SieveX_le_rough_add_repeated N δ s t W (fun _ hd => hb.support_pos hd)
  linarith only [hrough,hm,hr,hf]

end Wu18938Campaign.M1.Confirmed.Omega
