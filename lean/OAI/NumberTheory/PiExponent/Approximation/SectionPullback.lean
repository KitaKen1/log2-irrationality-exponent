/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.FrameSections
public import OAI.NumberTheory.PiExponent.Approximation.PushforwardTensor

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

lemma pullback_endValue (f : Y ⟶ X) (a : O X ⟶ O X) :
    endValue ((pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom) = f.appTop (endValue a) := by
  let u := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  let b := (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map a ≫
      (pullbackUnitIso f).hom
  have he : a ≫ u = u ≫ (Scheme.Modules.pushforward f).map b := by
    have hn := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_left
      a (pullbackUnitIso f).hom
    have hr := (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv_naturality_right
      (pullbackUnitIso f).hom b
    rw [pullbackUnit_adjunction] at hn hr
    have hcomp : (pullbackUnitIso f).hom ≫ b =
        (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom := by simp [b]
    rw [hcomp] at hr
    exact hn.symm.trans hr
  have hev := congrArg (fun t : O X ⟶ (Scheme.Modules.pushforward f).obj (O Y) =>
      t.app ⊤ (1 : Γ(X,⊤))) he
  change f.app ⊤ (a.app ⊤ (1 : Γ(X,⊤))) = b.app (f ⁻¹ᵁ ⊤) (f.app ⊤ 1) at hev
  have hfOne : f.app ⊤ (1 : Γ(X,⊤)) = (1 : Γ(Y,f ⁻¹ᵁ ⊤)) := map_one (f.app ⊤).hom
  rw [hfOne] at hev
  exact hev.symm

lemma coefficient_pullback (f : Y ⟶ X) {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (pullbackFrame f e) (pullbackSection f s) =
      f.appTop (coefficient e s) := by
  unfold coefficient pullbackFrame pullbackSection
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [← Functor.map_comp_assoc]
  exact pullback_endValue f (s ≫ e.hom)

end
end PiExponentSeshadri.Geometry

end OAI
