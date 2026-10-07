/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectivePencilScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveLineProper
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap

@[expose] public section

namespace OAI

namespace PiExponent.ProjectivePencilScalars
noncomputable section
open AlgebraicGeometry CategoryTheory

theorem projection_eq_structureMap (F : Type) [CommRing F] :
    polynomialProjectiveProjection F Bool = ProjectiveLine.structureMap F := by
  have hc : (polynomialGradeZeroEquiv F Bool).toRingHom =
      ProjectiveLine.constantsInDegreeZero F := by
    ext r
    rfl
  rw [polynomialProjectiveProjection, ProjectiveLine.structureMap, hc]

theorem scalars_comp_eq_structureScalars {F : Type} [CommRing F] {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine F) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := F) (σ := Bool)) =
      (f ≫ ProjectiveLine.structureMap F).appTop.hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom := by
  rw [ProjectiveO1.scalars, Scheme.Hom.comp_appTop, ← projection_eq_structureMap F]
  rfl

theorem scalars_comp_eq_baseScalars {Y : Scheme.{0}}
    (f : Y ⟶ ProjectiveLine.projectiveLine ℂ) :
    f.appTop.hom.comp (ProjectiveO1.scalars (R := ℂ) (σ := Bool)) =
      PiExponentSeshadri.Geometry.baseScalars (f ≫ ProjectiveLine.structureMap ℂ) :=
  scalars_comp_eq_structureScalars f

end
end PiExponent.ProjectivePencilScalars

end OAI
