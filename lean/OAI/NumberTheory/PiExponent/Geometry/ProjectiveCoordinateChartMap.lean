/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateChartMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1ChartMap
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveO1Sections

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

def coordinateChartMap (i : σ) : (SectionOpens.isoOpen (s i)).toScheme ⟶
    (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).toScheme :=
  (X.isoOfEq (sectionsMorphism_preimage k s hc i).symm).hom ≫
    (sectionsMorphism k s hc ∣_ PiExponent.ProjectiveO1.coordinateOpen i)

lemma coordinateChartMap_factor (i : σ) :
    coordinateChartMap k s hc i ≫ (PiExponent.ProjectiveO1.coordinateOpen (R := K) i).ι =
      (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc := by
  simp only [coordinateChartMap, Category.assoc, morphismRestrict_ι,
    Scheme.isoOfEq_hom_ι_assoc]

lemma coordinateChartMap_ratio (i j : σ) :
    (coordinateChartMap k s hc i).appTop
      (PiExponent.ProjectiveO1.chartRatios (R := K) i j) =
    coefficient (sectionFrame (s i))
      (restrictSection (SectionOpens.isoOpen (s i)).ι (s j)) := by
  let g := coordinateChartMap k s hc i
  let a := Proj.basicOpenIsoSpec (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide)
  have hg : (SectionOpens.isoOpen (s i)).ι ≫ sectionsMorphism k s hc =
      (g ≫ a.hom) ≫ Proj.awayι (PolyGrade K σ) (MvPolynomial.X i) (poly_X_mem i) (by decide) := by
    simpa only [Proj.awayι, a, Category.assoc, Iso.hom_inv_id_assoc] using
      (coordinateChartMap_factor k s hc i).symm
  have h := sectionFrame_coordinate i k s hc (g ≫ a.hom) hg j
  rw [Scheme.Hom.comp_appTop, ← Category.assoc,
    PiExponent.ProjectiveO1.coordinateOpen_pullback] at h
  change _ = g.appTop ((PiExponent.ProjectiveO1.coordinateOpen (R := K) i).topIso.inv
    (Proj.awayToSection (PolyGrade K σ) (MvPolynomial.X i) (chartCoordinate (R := K) i j))) at h
  rw [PiExponent.ProjectiveO1.awayToSection_coordinate] at h
  exact h.symm

end
end PiExponentSeshadri.Projective

end OAI
