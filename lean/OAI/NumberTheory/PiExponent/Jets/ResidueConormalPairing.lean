/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/ResidueConormalPairing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Jets.ConormalPairing

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSiegel.W58

variable {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
variable (I : Ideal R) (D : Derivation K R (R ⧸ I))

instance cotangentQuotientScalarTower : IsScalarTower R (R ⧸ I) I.Cotangent :=
  inferInstance

def residueConormalPairing : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  (conormalPairing I D).extendScalarsOfSurjective
    (show Function.Surjective (algebraMap R (R ⧸ I)) from Ideal.Quotient.mk_surjective)

@[simp] theorem residueConormalPairing_apply (x : I.Cotangent) :
    residueConormalPairing I D x = conormalPairing I D x := rfl

@[simp] theorem residueConormalPairing_toCotangent (x : I) :
    residueConormalPairing I D (I.toCotangent x) = D x := rfl

theorem residueConormalPairing_restrictScalars :
    (residueConormalPairing I D).restrictScalars R = conormalPairing I D := by
  ext x
  rfl

def reducedDerivation (D₀ : Derivation K R R) : Derivation K R (R ⧸ I) :=
  (Ideal.Quotient.mkₐ R I).toLinearMap.compDer D₀

@[simp] theorem reducedDerivation_apply (D₀ : Derivation K R R) (x : R) :
    reducedDerivation I D₀ x = Ideal.Quotient.mk I (D₀ x) := rfl

def derivationNormal (D₀ : Derivation K R R) : I.Cotangent →ₗ[R ⧸ I] R ⧸ I :=
  residueConormalPairing I (reducedDerivation I D₀)

@[simp] theorem derivationNormal_toCotangent (D₀ : Derivation K R R) (x : I) :
    derivationNormal I D₀ (I.toCotangent x) = Ideal.Quotient.mk I (D₀ x) := rfl

end PiExponentSiegel.W58

end

end OAI
