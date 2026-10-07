/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedThickeningSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.AffineThickeningCriterion
public import OAI.NumberTheory.PiExponent.Approximation.FullSupportNilpotence
public import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}}
local instance (Z : Scheme.{0}) : HasExt.{1} Z.Modules := HasExt.standard _

theorem globalSections_surjective_of_ext_one_zero (S : ShortComplex X.Modules)
    (hS : S.ShortExact)
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) S.X₁ 1, x = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  intro s
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s)
    rfl (hzero _)
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem closed_appTop_surjective_of_ext_one_zero (i : Y ⟶ X) [IsClosedImmersion i]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.idealModule i) 1, x = 0) :
    Function.Surjective i.appTop := by
  let P := (Scheme.Modules.pushforward i).obj (IdealModule.unit Y)
  let S := ShortComplex.mk (IdealModule.inclusion i) (IdealModule.structureMap i)
    (kernel.condition _)
  have hlift := globalSections_surjective_of_ext_one_zero S
    (IdealModule.closedSequence_exact i) hzero
  intro y
  let t : GlobalSections X P := (moduleSectionEquiv P).symm y
  obtain ⟨s, hs⟩ := hlift t
  refine ⟨s.app ⊤ (1 : Γ(X,⊤)), ?_⟩
  have he := congrArg (fun t : GlobalSections X P => t.app ⊤ (1 : Γ(X,⊤))) hs
  exact he.trans ((moduleSectionEquiv P).apply_symm_apply y)

theorem subscheme_surjective_of_fullSupport (I : X.IdealSheafData)
    (hI : I.support = ⊤) : Function.Surjective I.subschemeι := by
  apply Set.range_eq_univ.mp
  rw [I.range_subschemeι, hI]
  rfl

theorem isAffine_of_fullSupport_of_ideal_ext_one_zero (I : X.IdealSheafData)
    (hI : I.support = ⊤) [IsAffine I.subscheme]
    (hzero : ∀ x : Abelian.Ext.{1} (structureSheaf X) (IdealModule.closedModule I) 1, x = 0) :
    IsAffine X :=
  isAffine_of_surjective_appTop I.subschemeι (subscheme_surjective_of_fullSupport I hI)
    (closed_appTop_surjective_of_ext_one_zero I.subschemeι hzero)

end
end PiExponentSeshadri.Geometry

end OAI
