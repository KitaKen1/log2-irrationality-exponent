/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the auxiliary-jet proof to varying Y-centers and simultaneous derivative words.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedIndices

@[expose] public section

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/FormalAuxiliaryJet.lean (Apache-2.0). The same global polynomial now vanishes
at varying Y-centers. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent PiExponent.JetGeometry
open Filter Topology
noncomputable section

def formalEvaluationAtCenters {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    FramePolynomial m →ₗ[ℂ] ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJetAt (y ρ.1) (c ρ.1)).toLinearMap)

/-- Dimension counting supplies one nonzero polynomial, vanishing simultaneously
at every center. The volume inequality is an explicit hypothesis. -/
theorem eventually_exists_auxiliary_at_centers {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJetAt (y j) (c j) P) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨P, hP, hw, he⟩ :=
    hN (formalEvaluationAtCenters K (fun i => (V i : ℝ)) (a*N) y c)
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  simpa [formalEvaluationAtCenters, FormalMatrixBridge.exponentVector_coe] using hh

theorem eventually_exists_auxiliary_at_centers_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j, formalJetAt (y j) (c j) P ∈
        rationalWeightedIdeal V (fun i => (hV i).le) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliary_at_centers W V hW hV K (by exact_mod_cast ha) hvol y c)
  filter_upwards [h] with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

/-- A derivative word loses at most its total weight at all centers. -/
theorem eventually_exists_auxiliary_words_at_centers {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j (word : List (Fin (m+1))),
        formalJetAt (y j) (c j) (polynomialFrameWord m word P) ∈
          rationalWeightedIdeal V (fun i => (hV i).le) (a*N - (word.map V).sum) := by
  filter_upwards [eventually_exists_auxiliary_at_centers_nat W V hW hV K ha hvol y c]
    with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  exact ⟨P, hP, hw, fun j word =>
    formalJetAt_word_vanishing (y j) (c j) V (fun i => (hV i).le) (a*N) P (hv j) word⟩

end
end LogTwo.Geometry
