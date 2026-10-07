/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt asymptotic bounds to the actual log-two minor and geometry.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Analysis.Counting

@[expose] public section
namespace LogTwo.Analysis
open OAI PiExponent MatrixTranslation
open LogTwo.Interpolation LogTwo.Arithmetic
open Filter Topology
noncomputable section

def fixedAnalyticError {m : ℕ} (w : Weights m) (ν F ws : ℝ) : ℝ :=
  translationBudget w (Real.log (w.K : ℝ)+ν) ν F ws + holomorphicBudget w ws

def collisionRate {m : ℕ} (w : Weights m) (A η H : ℝ) : ℝ :=
  (Real.log 2/4)*η^2*(rowCount w H : ℝ)/(H*lowCountReal w A H)

theorem combinedAnalyticBudget_eq {m : ℕ} {w : Weights m} {H : ℚ}
    {r : Fin m → ℚ} {T : Fin m → ℕ} (minor : FullRowMinor w H r T) (ν F ws A η : ℝ) :
    combinedAnalyticBudget minor (Real.log (w.K : ℝ)+ν) ν F ws A η +
      Real.log (rowChoiceCount w H : ℝ)/(H : ℝ) =
    fixedAnalyticError w ν F ws + analyticRemainder w (H : ℝ) +
      max (-collisionRate w A η (H : ℝ)) (-ν*(A*(1-η)-averageRowWeight minor)) := by
  unfold combinedAnalyticBudget fixedAnalyticError analyticRemainder collisionRate
  rw [← fullRowMinor_size_eq_rowCount minor]
  change _ = _ + (Collision.collisionRemainder minor.size (H : ℝ) +
    Real.log (rowChoiceCount w H : ℝ)/(H : ℝ)) +
    max (-((Real.log 2/4)*η^2*(minor.size : ℝ)/((H : ℝ)*lowIndexCount w H A))) _
  simp only [neg_mul, neg_div]
  ring

/-- The remainder and collision rate are uniform in the chosen columns. -/
theorem actual_minor_log_bound_with_remainder {m : ℕ} {w : Weights m} {H F : ℚ}
    (r : Fin m → ℚ) (q : Fin m → ℕ)
    (minor : FullRowMinor w H r (truncationOrders w F))
    (hK : 0 < w.K) (hH : 0 < H) (hF : 0 < F) {ν ws A η : ℝ}
    (hν : 0 ≤ ν) (hws : 0 < ws) (hA : 0 ≤ A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(r k : ℝ)| ≤ (q k : ℝ)^(-ν)) :
    Real.log |(minor.matrix.det : ℝ)|/((minor.size : ℝ)*(H : ℝ)) ≤
      fixedAnalyticError w ν (F : ℝ) ws + analyticRemainder w (H : ℝ) +
        max (-collisionRate w A η (H : ℝ)) (-ν*(A*(1-η)-averageRowWeight minor)) := by
  rw [← combinedAnalyticBudget_eq minor]
  exact actual_minor_log_bound_of_approximations r q minor hK hH hF hν hws hA hη hq hwq hw happrox

theorem eventual_analytic_errors {m : ℕ} (w : Weights m) (hK : 0 < w.K)
    {A : ℝ} (hA : 0 < A) (η : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℚ in atTop, 0 < H ∧ analyticRemainder w (H : ℝ) < ε ∧
      collisionLimit w A η - ε < collisionRate w A η (H : ℝ) := by
  have hr := ((tendsto_analyticRemainder w hK).eventually_lt_const hε).ratCast_atTop
  have hc := ((tendsto_collisionRate w hA η).eventually
    (Ioi_mem_nhds (show collisionLimit w A η-ε < collisionLimit w A η by linarith))).ratCast_atTop
  filter_upwards [eventually_gt_atTop (0 : ℚ), hr, hc] with H hH hR hC
  exact ⟨hH, hR, hC⟩

theorem eventual_actual_minor_log_bound {m : ℕ} (w : Weights m) {F : ℚ}
    (r : Fin m → ℚ) (q : Fin m → ℕ) (hK : 0 < w.K) (hF : 0 < F)
    {ν ws A η : ℝ} (hν : 0 ≤ ν) (hws : 0 < ws) (hA : 0 < A) (hη : 0 ≤ η)
    (hq : ∀ k, 2 ≤ q k) (hwq : ∀ k, w.w k = ceilLogWeight (q k))
    (hw : ∀ k, ws ≤ (w.w k : ℝ))
    (happrox : ∀ k, |Real.log 2-(r k : ℝ)| ≤ (q k : ℝ)^(-ν))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ H : ℚ in atTop, ∀ minor : FullRowMinor w H r (truncationOrders w F),
      Real.log |(minor.matrix.det : ℝ)|/((minor.size : ℝ)*(H : ℝ)) ≤
        fixedAnalyticError w ν (F : ℝ) ws + ε +
          max (-collisionLimit w A η+ε) (-ν*(A*(1-η)-averageRowWeight minor)) := by
  filter_upwards [eventual_analytic_errors w hK hA η hε] with H hH
  intro minor
  apply (actual_minor_log_bound_with_remainder r q minor hK hH.1 hF hν hws hA.le hη hq hwq hw happrox).trans
  exact add_le_add (add_le_add le_rfl hH.2.1.le) (max_le_max (by linarith [hH.2.2]) le_rfl)

end
end LogTwo.Analysis
