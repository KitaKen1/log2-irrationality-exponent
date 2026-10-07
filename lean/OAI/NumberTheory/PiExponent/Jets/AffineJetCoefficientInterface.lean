/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AffineJetCoefficientInterface.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Jets.AffineJetPolynomial

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.AffineJetCoefficientInterface
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry
open PiExponent.ExceptionalAffineChart
variable {X : Scheme} {R : Type} [CommRing R]
variable (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
variable (A : LineBundle X)

def Frame : Type := A.sheaf.restrict (chartOpen j).1.ι ≅ structureSheaf (chartOpen j).1.toScheme

def Sections (n : ℕ) : Type := GlobalSections X (modulePow X A.sheaf n)

def coefficient (n : ℕ) (e : Frame j A) : Sections A n → R :=
  AffineJetPolynomial.polynomialCoefficient j A n e

theorem coefficient_eq (n : ℕ) (e : Frame j A) (s : Sections A n) :
    coefficient j A n e s = AffineJetPolynomial.polynomialCoefficient j A n e s := rfl

end PiExponent.AffineJetCoefficientInterface
end

end OAI
