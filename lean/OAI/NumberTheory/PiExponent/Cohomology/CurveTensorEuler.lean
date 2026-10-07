/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveTensorEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.CurveRegularEuler
public import OAI.NumberTheory.PiExponent.Cohomology.EulerRegularSections

@[expose] public section

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem regular_tensor_euler_add {X : Scheme.{0}} [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  have hM := regular_section_tensor_euler_eq_lengths p hd H hH L M s
  have hO := regular_section_tensor_euler_eq_lengths p hd H hH L (L.pow 0) s
  have he := eulerCharacteristic_iso p (moduleTensorRightUnit L.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor (L.pow 0)).sheaf =
    eulerCharacteristic p 1 L.sheaf at he
  rw [he] at hO
  exact hM.trans hO.symm

theorem tensor_euler_add {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      eulerCharacteristic p 1 L.sheaf - eulerCharacteristic p 1 (structureSheaf X) := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_tensor_euler_add p hd H hH (L.tensor B) M s
  have h₂ := regular_tensor_euler_add p hd H hH B L t
  have h₃ := regular_tensor_euler_add p hd H hH B (L.tensor M) t
  have hc := eulerCharacteristic_iso p (moduleTensorComm L.sheaf B.sheaf) 1
  change eulerCharacteristic p 1 (L.tensor B).sheaf =
    eulerCharacteristic p 1 (B.tensor L).sheaf at hc
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
