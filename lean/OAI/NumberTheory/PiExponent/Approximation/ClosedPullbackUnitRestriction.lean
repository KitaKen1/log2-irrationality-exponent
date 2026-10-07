/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPullbackUnitRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.ClosedPullbackUnit
public import OAI.NumberTheory.PiExponent.Approximation.OpenPullbackUnit
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealModule

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.ClosedPullbackUnitRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
variable {X Y : Scheme.{0}} (f : Y ⟶ X)

lemma restrict_unit_isIso_iff (U : X.Opens) (M : X.Modules) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)) ↔
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      (M.restrict U.ι)) := by
  let g := (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
  let e := OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)
  let k := (Scheme.Modules.pushforward (f ∣_ U)).map
    ((OpenBaseChange.leftSquare f U).hom.app M)
  calc
    IsIso g ↔ IsIso (g ≫ e.hom) := (isIso_comp_right_iff g e.hom).symm
    _ ↔ IsIso (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        (M.restrict U.ι)) ≫ k) := by rw [OpenBaseChange.unit_compatibility]
    _ ↔ _ := isIso_comp_right_iff _ k

theorem unit_isIso_of_affine (M : X.Modules)
    (h : ∀ U : X.affineOpens,
      IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U.1)).unit.app
        (M.restrict U.1.ι))) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply IdealModule.isIso_of_affine_app
  intro U
  have hr := (restrict_unit_isIso_iff f U.1 M).mpr (h U)
  have ht := Scheme.Modules.Hom.isIso_iff_isIso_app.mp hr ⊤
  change IsIso (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app
    (U.1.ι ''ᵁ ⊤)) at ht
  have he : U.1.ι ''ᵁ ⊤ = U.1 :=
    (Scheme.Hom.image_top_eq_opensRange U.1.ι).trans (Scheme.Opens.opensRange_ι U.1)
  rw [he] at ht
  exact ht

lemma morphismRestrict_surjective (hf : Function.Surjective f) (U : X.Opens) :
    Function.Surjective (f ∣_ U) := by
  intro x
  obtain ⟨y, hy⟩ := hf x.1
  refine ⟨⟨y, ?_⟩, ?_⟩
  · change f y ∈ U
    simpa only [hy] using x.2
  · apply Subtype.ext
    exact (morphismRestrict_base_coe f U _).trans hy

theorem unit_isIso_of_affine_pushforward [IsClosedImmersion f]
    (hf : Function.Surjective f) (M : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ N : (f ⁻¹ᵁ U.1).toScheme.Modules,
      Nonempty (M.restrict U.1.ι ≅ (Scheme.Modules.pushforward (f ∣_ U.1)).obj N)) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) := by
  apply unit_isIso_of_affine f M
  intro U
  obtain ⟨N, ⟨e⟩⟩ := h U
  exact ClosedPullbackUnit.unit_isIso_of_pushforward (f ∣_ U.1)
    (morphismRestrict_surjective f hf U.1) e

end
end PiExponentSeshadri.ClosedPullbackUnitRestriction

end OAI
