/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic weighted-section lemmas, change namespaces/imports and omit fixed-center wrappers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.WeightedSliceDegree
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCharts

@[expose] public section

/-! Generic weighted-section lemma extracted from the pinned openai/math source.
Fixed-center admissible wrappers are excluded; proof bodies are preserved.
See THIRD_PARTY_NOTICES.txt. -/


namespace LogTwo.Geometry.WeightedHomogeneousSubstitution
noncomputable section
open OAI PiExponent
open scoped BigOperators
open MvPolynomial
open WeightedSliceDegree
open PiExponentSeshadri.Projective


variable {σ ι K : Type*}

theorem supportBound_substitution [Field K] (ρ : ι → ℝ) (B : ℝ)
    (a : σ → ι →₀ ℕ) (ha : ∀ j, Finsupp.weight ρ (a j) ≤ B)
    (n : ℕ) (p : MvPolynomial.homogeneousSubmodule σ K n) :
    SupportBound ρ ((n : ℝ) * B)
      (MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p.val) := by
  classical
  refine supportBound_aeval (fun _ : σ => B) ρ
    (fun j => MvPolynomial.monomial (a j) (1 : K)) ?_ ((n : ℝ) * B) p.val ?_
  · intro j b hb
    have he : b = a j := Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hb)
    simpa only [he] using ha j
  · intro b hb
    have hd : b.degree = n := by
      exact (p.property.degree_eq_sum_deg_support hb).symm
    simp only [Finsupp.weight_apply, Finsupp.sum, nsmul_eq_mul,
      ← Finset.sum_mul, ← Nat.cast_sum, ← Finsupp.degree_apply, hd, le_refl]

theorem dehomogenize_substitution [CommRing K] (a : σ → ι →₀ ℕ)
    (z : σ) (hz : a z = 0) (p : MvPolynomial σ K) :
    MvPolynomial.aeval (fun j : ChartVariables z => MvPolynomial.monomial (a j.val) (1 : K))
      (dehomogenize z p) =
    MvPolynomial.aeval (fun j => MvPolynomial.monomial (a j) (1 : K)) p := by
  classical
  have he :
      (MvPolynomial.aeval (R := K) (fun j : ChartVariables z =>
        MvPolynomial.monomial (a j.val) (1 : K))).toRingHom.comp (dehomogenize (R := K) z) =
      (MvPolynomial.aeval (R := K) (fun j => MvPolynomial.monomial (a j) (1 : K))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [dehomogenize]
    · intro j
      by_cases hj : j = z
      · subst j
        simp [dehomogenize, hz]
      · simp [dehomogenize, hj]
  exact RingHom.congr_fun he p

end
end LogTwo.Geometry.WeightedHomogeneousSubstitution
