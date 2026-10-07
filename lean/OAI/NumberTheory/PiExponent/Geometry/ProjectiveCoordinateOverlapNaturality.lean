/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateOverlapNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateTransitions

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
open PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinatePowerOverlap_restrict (n : ℕ) (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : freeOpen X.ringCatSheaf (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) :
    coordinatePowerOverlap M s k hc f hf n j b
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      coordinatePowerOverlap M s k hc f hf n i a z := by
  let ci := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) (modulePow X M n)
    (restrictOpenFrame inf_le_left (coordinatePowerFrame (s i) n)) z
  let ri := coordinateFiniteRingEquiv M s k hc f hf i a
  let rj := coordinateFiniteRingEquiv M s k hc f hf j b
  let u := coordinateRatioOn (s j) (s i)
    (show coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) from inf_le_left)
  have ht : coordinateFiniteTransition M s k hc f hf i j a b h (ri ci) =
      rj (X.presheaf.map (homOfLE h).op ci) := by
    simp only [coordinateFiniteTransition, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ri, RingEquiv.symm_apply_apply, rj]
  change overlapLaurent j (n : ℤ) b
    (rj (framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) (modulePow X M n)
      (restrictOpenFrame inf_le_left (coordinatePowerFrame (s j) n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z))) =
    overlapLaurent i (n : ℤ) a (ri ci)
  have hcoef : framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) (modulePow X M n)
      (restrictOpenFrame inf_le_left (coordinatePowerFrame (s j) n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      u ^ n * X.presheaf.map (homOfLE h).op ci :=
    coordinatePowerFrame_hom_change_restrict (s i) (s j) n
      (U := coordinateFiniteOpen M s i a) (W := coordinateFiniteOpen M s j b)
      inf_le_left inf_le_left h z
  rw [hcoef, map_mul, map_pow]
  change overlapLaurent j (n : ℤ) b
    ((rj u) ^ n * rj (X.presheaf.map (homOfLE h).op ci)) = _
  rw [← ht]
  exact overlapLaurent_change_pivot_pow i j n a b
    (coordinateFiniteTransition M s k hc f hf i j a b h)
    (coordinateFiniteTransition_full M s k hc f hf i j a b h) (rj u)
    (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) (ri ci)

end
end PiExponentSeshadri.Projective

end OAI
