/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EulerZeroDimensional.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.AlgebraicGeometry.Artinian
public import OAI.NumberTheory.PiExponent.Cohomology.FiniteLineEuler

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem discreteTopology_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : DiscreteTopology X := by
  let : IsLocallyArtinian X := IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim
  infer_instance

theorem finite_of_dim_le_zero [IsNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) : Finite X := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact finite_of_compact_of_discrete

theorem lineBundle_trivial_of_dim_le_zero [IsLocallyNoetherian X]
    (hdim : topologicalKrullDim X ≤ 0) (L : LineBundle X) :
    Nonempty (L.sheaf ≅ structureSheaf X) := by
  let : DiscreteTopology X := discreteTopology_of_dim_le_zero hdim
  exact PiExponentSeshadri.FiniteSupport.lineBundle_trivial L

theorem eulerCharacteristic_tensor_pow_eq_of_dim_le_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (M : X.Modules) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) (n : ℕ) :
    eulerCharacteristic p d (moduleTensor X M (L.pow n).sheaf) =
      eulerCharacteristic p d M := by
  obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim (L.pow n)
  exact eulerCharacteristic_iso p
    (moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M) d

theorem eulerCharacteristic_pow_eq_of_dim_le_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) (n : ℕ) :
    eulerCharacteristic p d (L.pow n).sheaf =
      eulerCharacteristic p d (structureSheaf X) := by
  obtain ⟨e⟩ := lineBundle_trivial_of_dim_le_zero hdim (L.pow n)
  exact eulerCharacteristic_iso p e d

theorem fwdDiff_eulerCharacteristic_tensor_pow_eq_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (M : X.Modules) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) :
    fwdDiff (1 : ℕ) (fun n =>
      eulerCharacteristic p d (moduleTensor X M (L.pow n).sheaf)) = 0 := by
  funext n
  simp only [fwdDiff, eulerCharacteristic_tensor_pow_eq_of_dim_le_zero p L M d hdim,
    sub_self, Pi.zero_apply]

theorem fwdDiff_eulerCharacteristic_pow_eq_zero [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ 0) :
    fwdDiff (1 : ℕ) (fun n => eulerCharacteristic p d (L.pow n).sheaf) = 0 := by
  funext n
  simp only [fwdDiff, eulerCharacteristic_pow_eq_of_dim_le_zero p L d hdim,
    sub_self, Pi.zero_apply]

end
end PiExponent.NumericalAmpleness

end OAI
