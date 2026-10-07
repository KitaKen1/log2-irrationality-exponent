/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveEmbeddingCohomologyBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer
public import OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleCoherent
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveSpaceBasics

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open PiExponent.ProjectiveO1

theorem projectiveSpace_cohomology_eq_zero (r : ℕ)
    (M : (projectiveSpace ℂ (Fin (r+1))).Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : r+1 ≤ q) (z : cohomology M q) : z = 0 := by
  exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover (r+1) (by omega)
    (coordinateOpen (R := ℂ) (σ := Fin (r+1)))
    (fun j => standardChart_isAffineOpen j) standardChart_cover M q hq z

theorem cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : r+1 ≤ q)
    (z : cohomology M q) : z = 0 := by
  let N := (Scheme.Modules.pushforward i).obj M
  let : N.IsFinitePresentation := PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation i M
  let : N.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData N).choose.isQuasicoherent
  let e := PiExponent.ClosedImmersionSerreTransfer.closedCohomologyEquiv i M q
  apply e.injective
  exact (projectiveSpace_cohomology_eq_zero r N q hq (e z)).trans e.map_zero.symm

theorem lineBundle_cohomology_eq_zero_of_projective_embedding {X : Scheme.{0}} (r : ℕ)
    (i : X ⟶ projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (L : LineBundle X) (q : ℕ) (hq : r+1 ≤ q) (z : cohomology L.sheaf q) : z = 0 := by
  let : L.sheaf.IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation L
  exact cohomology_eq_zero_of_projective_embedding r i L.sheaf q hq z

end
end PiExponent.NumericalAmpleness

end OAI
