/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.NakaiSectionLifting
public import OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian


variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem closed_line_unit_epi (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X) :
    Epi ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf) :=
  PiExponentSeshadri.LineClosedUnit.epi f M

theorem pullbackSection_surjective_of_kernel_cohomology_zero
    (f : Y ⟶ X) [IsClosedImmersion f] (M : LineBundle X)
    (hzero : ∀ z : cohomology
      (kernel ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf)) 1,
      z = 0) :
    Function.Surjective (fun s : GlobalSections X M.sheaf => pullbackSection f s) := by
  let u := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M.sheaf
  have : Epi u := closed_line_unit_epi f M
  let S := ShortComplex.mk (kernel.ι u) u (kernel.condition u)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel u }
  exact PiExponent.NumericalAmpleness.pullbackSection_surjective_of_unit_surjective f M
    (globalSections_surjective_of_ext_one_zero S hS hzero)

end PiExponentSeshadri.Geometry

end

end OAI
