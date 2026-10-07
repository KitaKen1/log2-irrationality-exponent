/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveRegularEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.AmpleCohomologyFinite
public import OAI.NumberTheory.PiExponent.Cohomology.LineCohomologyDimension
public import OAI.NumberTheory.PiExponent.Geometry.GeneralCartierDegreeLength

@[expose] public section

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_section_tensor_euler_eq_lengths {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1)
    (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    letI : Finite (SectionZeroIdeal.zeroIdeal L s).subscheme :=
      GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
    letI : Fintype (SectionZeroIdeal.zeroIdeal L s).subscheme := Fintype.ofFinite _
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      ∑ x : (SectionZeroIdeal.zeroIdeal L s).subscheme,
        ((Module.length
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)
          ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk x)).toNat : ℤ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation M
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (L.tensor M)
  let : Subsingleton (cohomology M.sheaf 2) := ⟨fun a b =>
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p H hH M hd
      2 (by omega) a).trans
    (NumericalAmpleness.lineBundle_cohomology_zero_of_dimension_le 1 p H hH M hd
      2 (by omega) b).symm⟩
  exact GeneralCartierDegreeLength.regular_section_tensor_euler_eq_sum_local_lengths
    p hd L M s
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH M.sheaf q)
    (fun q _ => AmpleCohomologyFinite.cohomology_finite_of_ample p H hH (L.tensor M).sheaf q)

end
end PiExponent.CurveCycle

end OAI
