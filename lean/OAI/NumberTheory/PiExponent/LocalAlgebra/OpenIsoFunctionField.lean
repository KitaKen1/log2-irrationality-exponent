/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/OpenIsoFunctionField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.CurveBlowupImageBase

@[expose] public section

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace PiExponent.CurveBlowupImage
variable {C X : Scheme.{0}} [IsIntegral C] [IsIntegral X]

def functionFieldMap (f : C ⟶ X) [IsDominant f] : X.functionField ⟶ C.functionField :=
  eqToHom (congrArg (fun x => X.presheaf.stalk x)
    (genericPoint_eq_of_isDominant f).symm) ≫ f.stalkMap (genericPoint C)

theorem functionFieldMap_isIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    IsIso (functionFieldMap f) := by
  have hx : f (genericPoint C) ∈ U := by
    apply ((genericPoint_spec C).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
    obtain ⟨q⟩ := hU
    exact ⟨q.1, trivial, q.2⟩
  let := stalkMap_isIso_of_restrict f U (genericPoint C) hx
  unfold functionFieldMap
  infer_instance

def functionFieldIso (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    X.functionField ≅ C.functionField :=
  letI := functionFieldMap_isIso f U hU
  asIso (functionFieldMap f)

private theorem eqToHom_fromSpecStalk (X : Scheme.{0}) {x y : X} (h : x = y) :
    Spec.map (eqToHom (congrArg (fun z => X.presheaf.stalk z) h)) ≫
      X.fromSpecStalk x = X.fromSpecStalk y := by
  subst y
  simp

theorem functionFieldMap_fromSpecStalk (f : C ⟶ X) [IsDominant f] :
    Spec.map (functionFieldMap f) ≫ X.fromSpecStalk (genericPoint X) =
      C.fromSpecStalk (genericPoint C) ≫ f := by
  unfold functionFieldMap
  rw [Spec.map_comp, Category.assoc,
    eqToHom_fromSpecStalk X (genericPoint_eq_of_isDominant f).symm]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk f

theorem functionFieldIso_fromSpecStalk (f : C ⟶ X) [IsDominant f]
    (U : X.Opens) [IsIso (f ∣_ U)] (hU : Nonempty (f ⁻¹ᵁ U)) :
    Spec.map (functionFieldIso f U hU).hom ≫ X.fromSpecStalk (genericPoint X) =
      C.fromSpecStalk (genericPoint C) ≫ f :=
  functionFieldMap_fromSpecStalk f

end PiExponent.CurveBlowupImage

end

end OAI
