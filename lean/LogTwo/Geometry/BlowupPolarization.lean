/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the auxiliary ample-bundle construction to the project blowup.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedBlowup
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupAmpleTwist

@[expose] public section

/-! An actual auxiliary ample bundle A^a tensor J on the varying-center
blowup. This does not assert ampleness of the interpolation bundle A tensor J.
Adapted from openai/math Ampleness/AdmissibleBlowupPolarization.lean
(Apache-2.0), applying its scheme-generic construction. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open LogTwo.Interpolation
noncomputable section
variable {m K : ℕ} (w : Weights m) (y : Fin K → ℂ)
variable (hy0 : ∀ j, y j ≠ 0) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

include hy0 in
theorem exists_ampleExponent : ∃ k : ℕ, 1 < k ∧
    (((A w y a T).pow k).tensor (J w y a T)).IsAmple :=
  PiExponentSeshadri.BlowupGluing.exists_ample_exceptional_power_gt_one
    (MatrixCompactification.centerIdeal w y a T)
    (MatrixCompactification.centerIdeal_support_ne_top w y hy0 a T)
    (hyperplane w) (hyperplane_ample w)

def ampleExponent : ℕ := (exists_ampleExponent w y hy0 a T).choose

theorem ampleExponent_gt_one : 1 < ampleExponent w y hy0 a T :=
  (exists_ampleExponent w y hy0 a T).choose_spec.1

def H : LineBundle (space w y a T) :=
  ((A w y a T).pow (ampleExponent w y hy0 a T)).tensor (J w y a T)

theorem H_ample : (H w y hy0 a T).IsAmple :=
  (exists_ampleExponent w y hy0 a T).choose_spec.2

end
end LogTwo.Geometry.MatrixBlowup
