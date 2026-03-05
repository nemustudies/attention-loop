/-
  AttentionLoop/ProofOfMainTheorem.lean

  Proves `mainTheorem : StatementOfTheorem` by connecting the Mathlib-only
  inline definitions in MainTheorem.lean to the project's existing theorems.
-/
import AttentionLoop.MainTheorem
import AttentionLoop.Defs.SimplexMap
import AttentionLoop.Defs.BlendRate
import AttentionLoop.Defs.Consolidation
import AttentionLoop.Defs.DerivedQuantities
import AttentionLoop.Core.Convergence
import AttentionLoop.Rigidity.AccumulationRigidity
import AttentionLoop.CaptureInertness.SoftmaxLipschitz
import AttentionLoop.Core.FanEffect
import AttentionLoop.Core.RetrievalWeightBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

open Finset BigOperators Filter

/-! ## Glue: connecting inline definitions to project definitions -/

/-- Convert AdmissibleBlendRate to project BlendRate. -/
private def toBlendRate (br : AdmissibleBlendRate) : BlendRate :=
  ⟨br.fn, br.maps_to, br.at_zero, br.at_one, br.pos_interior, br.continuous_fn⟩

/-- consolidationStep' with AdmissibleBlendRate = consolidationStep with BlendRate. -/
private theorem consolidationStep'_eq {d n : ℕ}
    (φ : (Fin n → ℝ) → (Fin n → ℝ))
    (br : AdmissibleBlendRate) (w : Fin n → ℝ)
    (q : EuclideanSpace ℝ (Fin d))
    (M : Fin n → EuclideanSpace ℝ (Fin d))
    (hM : 0 < n) :
    consolidationStep' φ br w q M hM =
    consolidationStep φ (toBlendRate br) w q M hM := by
  simp only [consolidationStep', consolidationStep, consolidationBlendRates,
    consolidationTarget, toBlendRate]

/-! ## Part 1: Convergence -/

private theorem proof_convergence : Convergence := by
  intro d n hn psm br q v M w hv hv_unique hw_pos h_step h_bounded h_weight_gap
  -- Construct the project's PositiveSimplexMap instance
  haveI : PositiveSimplexMap psm.φ := {
    nonneg := psm.nonneg
    sum_one := psm.sum_one
    pos := psm.pos
    order_preserving := psm.order_preserving
    cont := psm.cont
  }
  let br' := toBlendRate br
  -- lyapunovV' and lyapunovV are definitionally equal after unfolding
  suffices h : Tendsto (fun t => lyapunovV (M t) v hn) atTop (nhds 0) by
    convert h using 1
  -- The step condition translates
  have h_step' : ∀ t, M (t + 1) = consolidationStep psm.φ br' (w t) q (M t) (by omega) := by
    intro t; rw [← consolidationStep'_eq]; exact h_step t
  exact convergence_under_consolidation psm.φ br' q hn v M w hv hv_unique hw_pos
    h_step' h_bounded h_weight_gap

/-! ## Part 2: Accumulation Rigidity -/

private theorem proof_accumulation_rigidity : AccumulationRigidity := by
  intro C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec hf_pos σ_lim hσ_pos hσ_conv
  exact accumulation_rigidity_aggregate C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec
    hf_pos σ_lim hσ_pos hσ_conv

/-! ## Part 3: Sublinear → σ → 0 -/

private theorem proof_sublinear_zero : SublinearZero := by
  intro C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec hf_pos hf_sub
  exact accum_sublinear_implies_sigma_zero C a f N₀ hN₀ δ hδ ha_lb ha_ub hC_pos hC_rec
    hf_pos hf_sub

/-! ## Part 4: Superlinear → σ → ∞ -/

private theorem proof_superlinear_unbounded : SuperlinearUnbounded := by
  intro C a f N₀ hN₀ δ hδ ha_lb hC_pos hC_rec hf_pos hf_superlinear
  exact accum_superlinear_implies_sigma_unbounded C a f N₀ hN₀ δ hδ ha_lb hC_pos hC_rec
    hf_pos hf_superlinear

/-! ## Part 5: Softmax Lipschitz -/

private theorem proof_softmax_lipschitz : SoftmaxLipschitz := by
  intro n _ x y
  -- Inline defs are definitionally equal to project defs
  change l1Norm' (fun i => softmax' x i - softmax' y i) ≤
    2 * linfNorm' (fun i => x i - y i)
  simp only [softmax', l1Norm', linfNorm']
  exact softmax_lipschitz x y

/-! ## Helpers for Fan Effect and Opposition -/

/-- Jensen's inequality for exp over a nonempty finite set:
    |S| * exp(avg(f)) ≤ Σ exp(f). -/
private lemma jensen_exp_sum {ι : Type*} (S : Finset ι) (hS : S.Nonempty) (f : ι → ℝ) :
    ↑S.card * Real.exp ((∑ i ∈ S, f i) / ↑S.card) ≤ ∑ i ∈ S, Real.exp (f i) := by
  have hc : (0 : ℝ) < ↑S.card := Nat.cast_pos.mpr hS.card_pos
  have hcne : (↑S.card : ℝ) ≠ 0 := hc.ne'
  have hw : ∀ i ∈ S, (0 : ℝ) ≤ (↑S.card)⁻¹ := fun _ _ => inv_nonneg.mpr hc.le
  have hw1 : ∑ i ∈ S, (↑S.card : ℝ)⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hcne]
  have := convexOn_exp.map_sum_le hw hw1 (fun i _ => Set.mem_univ (f i))
  simp only [smul_eq_mul] at this
  rw [← Finset.mul_sum, ← Finset.mul_sum] at this
  have h2 := mul_le_mul_of_nonneg_left this hc.le
  rw [← mul_assoc, mul_inv_cancel₀ hcne, one_mul] at h2
  rwa [div_eq_inv_mul]

/-- The core fan effect inequality: for any scores s,
    every softmax value is at most 1/(1 + (n-1)*exp(-g)). -/
private lemma softmax_le_bound {n : ℕ} [NeZero n] (s : Fin n → ℝ) (i : Fin n) :
    softmax' (fun j => s j) i ≤
      1 / (1 + (↑n - 1) * Real.exp (-(_root_.max' s -
        (_root_.sum' s - _root_.max' s) / (↑n - 1)))) := by
  set g := _root_.max' s - (_root_.sum' s - _root_.max' s) / (↑n - 1)
  set D := ∑ j : Fin n, Real.exp (s j)
  have hD_pos : 0 < D := Finset.sum_pos (fun j _ => Real.exp_pos (s j)) ⟨i, Finset.mem_univ i⟩
  have hn_pos : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  -- denominator positivity
  have hn1_nn : (0 : ℝ) ≤ ↑n - 1 := by
    have : (1 : ℝ) ≤ ↑n := by exact_mod_cast hn_pos
    linarith
  have h1x_pos : 0 < 1 + (↑n - 1) * Real.exp (-g) := by
    linarith [mul_nonneg hn1_nn (Real.exp_pos (-g)).le]
  -- Unfold softmax and reduce to exp(s i) * (1 + (n-1)*exp(-g)) ≤ D
  change softmax' (fun j => s j) i ≤ 1 / (1 + (↑n - 1) * Real.exp (-g))
  unfold softmax'
  simp only
  rw [div_le_div_iff₀ hD_pos h1x_pos]
  -- Goal: exp(s i) * (1 + (n-1)*exp(-g)) ≤ 1 * D
  rw [one_mul]
  -- Goal: exp(s i) * (1 + (n-1)*exp(-g)) ≤ D
  -- Get argmax
  obtain ⟨j_max, hj_mem, hj_max⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty s
  have hmax_eq : _root_.max' s = s j_max := by
    simp only [_root_.max']; exact hj_max
  -- exp(s i) ≤ exp(max' s)
  have hsi_le : s i ≤ _root_.max' s :=
    Finset.le_sup' s (Finset.mem_univ i)
  have hexp_le : Real.exp (s i) ≤ Real.exp (_root_.max' s) :=
    Real.exp_le_exp.mpr hsi_le
  -- Handle n = 1 case
  by_cases hn1 : n = 1
  · subst hn1
    simp only [Nat.cast_one, sub_self, zero_mul, add_zero, mul_one]
    -- Goal: exp(s i) ≤ D = ∑ j : Fin 1, exp(s j) = exp(s 0)
    -- Since Fin 1 is a singleton, D = exp(s ⟨0, ..⟩)
    change Real.exp (s i) ≤ ∑ j : Fin 1, Real.exp (s j)
    rw [Fin.sum_univ_one]
    exact le_of_eq (congrArg Real.exp (congrArg s (Subsingleton.elim i 0)))
  -- n ≥ 2 case
  have hn2 : 2 ≤ n := by omega
  have hn1_pos : (0 : ℝ) < ↑n - 1 := by
    have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn2
    linarith
  -- Decompose D
  have hD_split : D = Real.exp (s j_max) + ∑ j ∈ Finset.univ.erase j_max, Real.exp (s j) := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ j_max)).symm
  -- The erase set is nonempty
  have herase_ne : (Finset.univ.erase j_max : Finset (Fin n)).Nonempty := by
    haveI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn2
    exact (Finset.univ_nontrivial (α := Fin n)).erase_nonempty
  -- card of erase = n - 1
  have hcard : (Finset.univ.erase j_max : Finset (Fin n)).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j_max), Finset.card_fin]
  -- sum over erase = sum' s - max' s
  have hsum_erase : ∑ j ∈ Finset.univ.erase j_max, s j = _root_.sum' s - _root_.max' s := by
    have := (Finset.add_sum_erase Finset.univ s (Finset.mem_univ j_max)).symm
    simp only [_root_.sum', _root_.max', hj_max] at this ⊢
    linarith
  -- Jensen on erase: (n-1) * exp(avg_rest) ≤ Σ_{j ≠ j_max} exp(s j)
  have hjensen : (↑n - 1) * Real.exp ((_root_.sum' s - _root_.max' s) / (↑n - 1)) ≤
      ∑ j ∈ Finset.univ.erase j_max, Real.exp (s j) := by
    have hn_ge_1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
    have hcast : (↑(n - 1) : ℝ) = ↑n - 1 := by
      rw [Nat.cast_sub hn_ge_1]; simp
    have hj := jensen_exp_sum (Finset.univ.erase j_max) herase_ne s
    rw [hcard, hsum_erase, hcast] at hj
    exact hj
  -- exp(-g) * exp(max' s) = exp(avg_rest)
  have hexp_neg_g : Real.exp (-g) * Real.exp (_root_.max' s) =
      Real.exp ((_root_.sum' s - _root_.max' s) / (↑n - 1)) := by
    rw [← Real.exp_add]; congr 1; simp only [g]; ring
  -- Main bound
  calc Real.exp (s i) * (1 + (↑n - 1) * Real.exp (-g))
      = Real.exp (s i) + Real.exp (s i) * ((↑n - 1) * Real.exp (-g)) := by ring
    _ ≤ Real.exp (_root_.max' s) + Real.exp (_root_.max' s) * ((↑n - 1) * Real.exp (-g)) := by
        have h_nn : 0 ≤ (↑n - 1) * Real.exp (-g) := mul_nonneg hn1_pos.le (Real.exp_pos _).le
        linarith [mul_le_mul_of_nonneg_right hexp_le h_nn]
    _ = Real.exp (_root_.max' s) + (↑n - 1) * (Real.exp (-g) * Real.exp (_root_.max' s)) := by
        ring
    _ = Real.exp (_root_.max' s) +
        (↑n - 1) * Real.exp ((_root_.sum' s - _root_.max' s) / (↑n - 1)) := by
          rw [hexp_neg_g]
    _ = Real.exp (s j_max) + (↑n - 1) * Real.exp ((_root_.sum' s - _root_.max' s) / (↑n - 1)) := by
        rw [hmax_eq]
    _ ≤ Real.exp (s j_max) + ∑ j ∈ Finset.univ.erase j_max, Real.exp (s j) := by
        linarith [hjensen]
    _ = D := by rw [← hD_split]

/-! ## Part 6: Fan Effect -/

private theorem proof_fan_effect : FanEffect := by
  intro n hn s
  haveI : NeZero n := ⟨by omega⟩
  change _root_.max' (fun i => softmax' (fun j => s j) i) ≤
    1 / (1 + (↑n - 1) * Real.exp (-(_root_.max' s -
      (_root_.sum' s - _root_.max' s) / (↑n - 1))))
  simp only [_root_.max']
  apply Finset.sup'_le
  intro i _
  exact softmax_le_bound s i

/-! ## Part 7: Opposition -/

private theorem proof_opposition : Opposition := by
  intro n hn c hc s
  haveI : NeZero n := ⟨by omega⟩
  change _root_.max' (fun i => softmax' (fun j => s j) i) ≥ c →
    _root_.max' s - (_root_.sum' s - _root_.max' s) / (↑n - 1) ≥
      Real.log (c * (↑n - 1) / (1 - c))
  intro h_wmax
  set g := _root_.max' s - (_root_.sum' s - _root_.max' s) / (↑n - 1)
  have h_bound : _root_.max' (fun i => softmax' (fun j => s j) i) ≤
      1 / (1 + (↑n - 1) * Real.exp (-g)) := by
    simp only [_root_.max']
    apply Finset.sup'_le
    intro i _
    exact softmax_le_bound s i
  have hc_pos : 0 < c := hc.1
  have hc1 : c < 1 := hc.2
  have h1mc : 0 < 1 - c := by linarith
  have hn1_pos : (0 : ℝ) < ↑n - 1 := by
    have : (2 : ℝ) ≤ ↑n := by exact_mod_cast hn
    linarith
  have hx_pos : 0 < (↑n - 1) * Real.exp (-g) := mul_pos hn1_pos (Real.exp_pos _)
  have h1x_pos : 0 < 1 + (↑n - 1) * Real.exp (-g) := by linarith
  -- From c ≤ 1/(1+x): c*(1+x) ≤ 1, so x ≤ (1-c)/c
  have hcb : c ≤ 1 / (1 + (↑n - 1) * Real.exp (-g)) := le_trans h_wmax h_bound
  -- Algebra: derive g ≥ log(c*(n-1)/(1-c))
  -- Step 1: cross-multiply: c * (1 + (n-1)*exp(-g)) ≤ 1
  have h1 : c * (1 + (↑n - 1) * Real.exp (-g)) ≤ 1 := by
    rwa [le_div_iff₀ h1x_pos] at hcb
  -- Step 2: (n-1)*exp(-g) ≤ (1-c)/c
  have h2 : (↑n - 1) * Real.exp (-g) ≤ (1 - c) / c := by
    rw [le_div_iff₀ hc_pos]
    nlinarith
  -- Step 3: exp(-g) ≤ (1-c)/(c*(n-1))
  have h3 : Real.exp (-g) ≤ (1 - c) / (c * (↑n - 1)) := by
    rw [le_div_iff₀ (mul_pos hc_pos hn1_pos)]
    -- goal: exp(-g) * (c * (n-1)) ≤ 1 - c
    nlinarith [h1]
  -- Step 4: -g ≤ log((1-c)/(c*(n-1)))
  have h_quot_pos : 0 < (1 - c) / (c * (↑n - 1)) :=
    div_pos h1mc (mul_pos hc_pos hn1_pos)
  have h4 : -g ≤ Real.log ((1 - c) / (c * (↑n - 1))) := by
    rw [← Real.log_exp (-g)]
    exact Real.log_le_log (Real.exp_pos _) h3
  -- Step 5: g ≥ -log((1-c)/(c*(n-1))) = log(c*(n-1)/(1-c))
  have h_cn1_pos : 0 < c * (↑n - 1) := mul_pos hc_pos hn1_pos
  have h5 : -Real.log ((1 - c) / (c * (↑n - 1))) =
      Real.log (c * (↑n - 1) / (1 - c)) := by
    rw [← Real.log_inv, inv_div]
  linarith [h5]

/-! ## Main Theorem -/

/-- The main theorem of the AttentionLoop formalization for the rigidity paper. -/
theorem mainTheorem : StatementOfTheorem :=
  ⟨proof_convergence, proof_accumulation_rigidity, proof_sublinear_zero,
   proof_superlinear_unbounded, proof_softmax_lipschitz, proof_fan_effect,
   proof_opposition⟩
