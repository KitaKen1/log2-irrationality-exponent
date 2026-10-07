/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurvePlaceSectionDivisor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.CurveNormalizationPolarization
public import OAI.NumberTheory.PiExponent.Geometry.CurveModelPlaces
public import OAI.NumberTheory.PiExponent.Geometry.SectionOrderDivisor

@[expose] public section

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.CurveNormalizationModel PiExponent.CurveModelPlaces
open PiExponent.CurveValuationCenter

namespace PiExponent.CurvePlaceSectionDivisor


variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

def divisor (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    NormalizedPlace ℂ E →₀ ℕ :=
  Finsupp.domCongr (placesEquivNongenericPoints f hf).symm
    (SectionOrderDivisor.divisor (parameterCurveStructureMap f hf)
      (parameterCurve_dimension_le_one f hf) (parameterCurve_stalkDVR f hf) L s hs)

@[simp] theorem divisor_apply (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (p : NormalizedPlace ℂ E) :
    divisor f hf L s hs p =
      SectionOrderDivisor.orderAt (parameterCurve_stalkDVR f hf) L s
        ⟨placePoint f hf p, placePoint_ne_genericPoint f hf p⟩ := by
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_apply]
  rfl

theorem degree_eq_euler_difference (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0)
    (hfiniteO : ∀ n ≤ 1,
      letI := Module.compHom (cohomology (structureSheaf (parameterCurve f hf)) n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology (structureSheaf (parameterCurve f hf)) n))
    (hfiniteL : ∀ n ≤ 1,
      letI := Module.compHom (cohomology L.sheaf n) (baseScalars (parameterCurveStructureMap f hf))
      FiniteDimensional ℂ (cohomology L.sheaf n)) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) := by
  let : Subsingleton (cohomology (structureSheaf (parameterCurve f hf)) 2) := by
    apply subsingleton_of_forall_eq 0
    intro x
    exact parameterCurve_lineBundle_ext_zero f hf (L.pow 0) 2 (by omega) x
  rw [divisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain,
    Finsupp.sum_mapDomain_index (by simp) (by intros; simp)]
  exact SectionOrderDivisor.divisor_degree_eq_euler_difference
    (parameterCurveStructureMap f hf) (parameterCurve_dimension_le_one f hf)
    (parameterCurve_stalkDVR f hf) L s hs hfiniteO hfiniteL

theorem degree_eq_euler_difference_full (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections (parameterCurve f hf) L.sheaf) (hs : s ≠ 0) :
    (divisor f hf L s hs).sum (fun _ n => (n : ℤ)) =
      eulerCharacteristic (parameterCurveStructureMap f hf) 1 L.sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) :=
  degree_eq_euler_difference f hf L s hs
    (parameterCurve_finiteLineCohomology f hf (L.pow 0))
    (parameterCurve_finiteLineCohomology f hf L)

end PiExponent.CurvePlaceSectionDivisor

end

end OAI
