/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPowerSectionLifting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.ClosedImmersionSerreTransfer
public import OAI.NumberTheory.PiExponent.Approximation.ClosedRestrictionTensor
public import OAI.NumberTheory.PiExponent.Approximation.ClosedThickeningSections

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}
local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem pullbackPowerSection_surjective_of_ideal_ext_zero (i : Y ⟶ X)
    [IsClosedImmersion i] (L : LineBundle X) (n : ℕ)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X)
      ((moduleTwistFunctor L n).obj (IdealModule.idealModule i)) 1, x = 0) :
    Function.Surjective (pullbackPowerSection L i n) := by
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hS := moduleTwistFunctor_shortExact L n S (IdealModule.closedSequence_exact i)
  have hsurj := globalSections_surjective_of_ext_one_zero (S.map (moduleTwistFunctor L n)) hS hzero
  intro σ
  let e := PiExponent.ClosedRestrictionTensor.powerProjectionIso i L n
  let b : GlobalSections X ((Scheme.Modules.pushforward i).obj ((L.pullback i).pow n).sheaf) :=
    IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map σ
  obtain ⟨a,ha⟩ := hsurj (b ≫ e.inv)
  let t : GlobalSections X (L.pow n).sheaf := a ≫ (moduleTwistUnitIso L n).hom
  refine ⟨t, ?_⟩
  apply (PiExponent.ClosedImmersionSerreTransfer.globalHom_push_bijective i
    ((L.pullback i).pow n).sheaf).injective
  have ht := PiExponent.ClosedRestrictionTensor.section_restriction_eq i L n t
  change t ≫ (moduleTwistUnitIso L n).inv ≫
    (moduleTwistFunctor L n).map (IdealModule.structureMap i) ≫ e.hom =
      IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
        (pullbackPowerSection L i n t) at ht
  change IdealModule.structureMap i ≫ (Scheme.Modules.pushforward i).map
    (pullbackPowerSection L i n t) = b
  rw [← ht]
  dsimp only [t]
  erw [Category.assoc a (moduleTwistUnitIso L n).hom,
    (moduleTwistUnitIso L n).hom_inv_id_assoc]
  change (a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i)) ≫ e.hom = b
  have ha' : a ≫ (moduleTwistFunctor L n).map (IdealModule.structureMap i) = b ≫ e.inv := ha
  exact (congrArg (fun z => z ≫ e.hom) ha').trans (by simp only [Category.assoc,
    Iso.inv_hom_id, Category.comp_id])

end
end PiExponentSeshadri.Geometry

end OAI
