/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinatePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.CoordinateFrameIdentification
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateChartMap
public import OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable {M : X.Modules} (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ M))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)

def coordinatePullbackModule : X.Modules :=
  (Scheme.Modules.pullback (sectionsMorphism k s hc)).obj
    (PiExponent.ProjectiveO1.lineBundle (R := K) (σ := σ)).sheaf

def coordinatePullbackSection (i : σ) : O X ⟶ coordinatePullbackModule k s hc :=
  pullbackSection (sectionsMorphism k s hc) (PiExponent.ProjectiveO1.coordinateSection i)

def coordinatePullbackFrame (i : σ) :
    (coordinatePullbackModule k s hc).restrict (SectionOpens.isoOpen (s i)).ι ≅
      O (SectionOpens.isoOpen (s i)).toScheme :=
  restrictedPullbackFrame (sectionsMorphism k s hc)
    (PiExponent.ProjectiveO1.coordinateOpen i) (SectionOpens.isoOpen (s i))
    (coordinateChartMap k s hc i) (coordinateChartMap_factor k s hc i).symm
    (LineBundleGluing.openFrame PiExponent.ProjectiveO1.coordinateCocycle i
      (PiExponent.ProjectiveO1.coordinateOpen i) le_rfl)

lemma coordinatePullbackFrame_coefficient (i j : σ) :
    coefficient (coordinatePullbackFrame k s hc i)
      (restrictSection (SectionOpens.isoOpen (s i)).ι (coordinatePullbackSection k s hc j)) =
    coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  have h := restrictedPullbackFrame_coefficient (sectionsMorphism k s hc)
    (PiExponent.ProjectiveO1.coordinateOpen i) (SectionOpens.isoOpen (s i))
    (coordinateChartMap k s hc i) (coordinateChartMap_factor k s hc i).symm
    (LineBundleGluing.openFrame PiExponent.ProjectiveO1.coordinateCocycle i
      (PiExponent.ProjectiveO1.coordinateOpen i) le_rfl)
    (PiExponent.ProjectiveO1.coordinateSection j)
  change coefficient (coordinatePullbackFrame k s hc i)
      (restrictSection (SectionOpens.isoOpen (s i)).ι (coordinatePullbackSection k s hc j)) = _ at h
  rw [PiExponent.ProjectiveO1.coordinateSection_coefficient_eq] at h
  exact h.trans (coordinateChartMap_ratio k s hc i j)

attribute [local irreducible] coordinatePullbackModule coordinatePullbackFrame coordinatePullbackSection

def coordinatePullbackIso : M ≅ coordinatePullbackModule k s hc :=
  LineBundleFrameCocycle.isoOfCoordinateCoefficients M (coordinatePullbackModule k s hc)
    (fun i => sectionFrame (s i)) (coordinatePullbackFrame k s hc)
    s (coordinatePullbackSection k s hc) (fun i => sectionFrame_normalized (s i))
    (coordinatePullbackFrame_coefficient k s hc) (by rw [hc])

def coordinateLineBundlePullbackIso (L : LineBundle X)
    (k : K →+* Γ(X,⊤)) (s : σ → (O X ⟶ L.sheaf))
    (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤) :
    L.sheaf ≅ ((PiExponent.ProjectiveO1.lineBundle (R := K) (σ := σ)).pullback
      (sectionsMorphism k s hc)).sheaf := by
  simpa only [coordinatePullbackModule, LineBundle.pullback] using coordinatePullbackIso k s hc

end
end PiExponentSeshadri.Projective

end OAI
