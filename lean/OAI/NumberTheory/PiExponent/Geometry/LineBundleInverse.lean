/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleInverse.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.CocycleTensorIso
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme}

def LineBundle.inverseCover (L : LineBundle X) (x : X) : X.Opens :=
  (L.locallyRankOne x).choose

lemma LineBundle.mem_inverseCover (L : LineBundle X) (x : X) :
    x ∈ L.inverseCover x := (L.locallyRankOne x).choose_spec.1

def LineBundle.inverseCoverFrame (L : LineBundle X) (x : X) :
    L.sheaf.restrict (L.inverseCover x).ι ≅ structureSheaf (L.inverseCover x).toScheme :=
  (L.locallyRankOne x).choose_spec.2.some

lemma LineBundle.inverseCover_covers (L : LineBundle X) :
    ⊤ ≤ ⨆ x, L.inverseCover x := by
  intro x _
  exact Opens.mem_iSup.mpr ⟨x, L.mem_inverseCover x⟩

def LineBundle.inverseCocycle (L : LineBundle X) :
    LineBundleGluing.Cocycle L.inverseCover :=
  LineBundleFrameCocycle.ofFrames L.sheaf L.inverseCover L.inverseCoverFrame

def LineBundle.inverse (L : LineBundle X) : LineBundle X :=
  LineBundleGluing.lineBundle L.inverseCocycle.inverse L.inverseCover_covers

def lineTensorInverseIso (L : LineBundle X) :
    moduleTensor X L.sheaf L.inverse.sheaf ≅ structureSheaf X :=
  moduleTensorIso
    (LineBundleFrameCocycle.isoSheaf L.sheaf L.inverseCover L.inverseCoverFrame
      L.inverseCover_covers) (Iso.refl _) ≪≫
    LineBundleGluing.tensorInverseIso L.inverseCocycle L.inverseCover_covers

def moduleTensorInverseCancelIso (M : X.Modules) (L : LineBundle X) :
    moduleTensor X (moduleTensor X M L.sheaf) L.inverse.sheaf ≅ M :=
  moduleLineTensorAssoc M L L.inverse ≪≫
    moduleTensorIso (Iso.refl M) (lineTensorInverseIso L) ≪≫ moduleTensorRightUnit M

def LineBundle.dualSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    L.inverse.sheaf ⟶ structureSheaf X :=
  (moduleTensorUnit L.inverse.sheaf).inv ≫ moduleTensorMap s (𝟙 _) ≫
    (lineTensorInverseIso L).hom

end
end PiExponentSeshadri.Geometry

end OAI
