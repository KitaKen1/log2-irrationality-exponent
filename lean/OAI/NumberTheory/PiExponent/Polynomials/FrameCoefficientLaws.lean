/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficientLaws.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveFrameNaturality

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.ProjectiveChartSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque RestrictionCohomology Frames
variable {X : Scheme} (U : X.Opens) (M : X.Modules)

lemma framedCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (a : Γ(X,U)) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M e (a • s) =
      a * framedCoefficientsEquiv U M e s := by
  have hs : (restrictionSectionsIso U M).inv (a • s) =
      U.topIso.inv a • (restrictionSectionsIso U M).inv s := by
    change M.presheaf.map (eqToHom U.ι_image_top).op (a • s) =
      (U.ι.appIso ⊤).inv (U.topIso.inv a) •
        M.presheaf.map (eqToHom U.ι_image_top).op s
    rw [M.map_smul, U.ι_appIso]
    rfl
  change U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv (a • s))) =
    a * U.topIso.hom (e.hom.app ⊤ ((restrictionSectionsIso U M).inv s))
  rw [hs, e.hom.app_smul]
  change U.topIso.hom (U.topIso.inv a * _) = _
  erw [map_mul]
  erw [Iso.inv_hom_id_apply]

lemma framedCoefficientsEquiv_change
    (e f : M.restrict U.ι ≅ structureSheaf U.toScheme) (s : Γ(M,U)) :
    framedCoefficientsEquiv U M f s =
      U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) *
        framedCoefficientsEquiv U M e s := by
  let t := (restrictionSectionsIso U M).inv s
  have he : e.inv.app ⊤ (e.hom.app ⊤ t) = t := by
    exact congrArg (fun q => q.app ⊤ t) e.hom_inv_id
  have h := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ t)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ t)) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ t) *
      (frameChange e f : Γ(U.toScheme,⊤)) at h
  rw [he, mul_comm] at h
  change U.topIso.hom (f.hom.app ⊤ t) =
    U.topIso.hom (frameChange e f : Γ(U.toScheme,⊤)) * U.topIso.hom (e.hom.app ⊤ t)
  rw [h, map_mul]

end
end PiExponentSeshadri.ProjectiveChartSections

end OAI
