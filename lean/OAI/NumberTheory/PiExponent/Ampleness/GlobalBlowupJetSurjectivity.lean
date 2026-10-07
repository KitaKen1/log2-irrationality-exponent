/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupJetSurjectivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.BlowupJetSurjectivity
public import OAI.NumberTheory.PiExponent.Ampleness.BlowupProperIntegral
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleProduct

@[expose] public section

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

def blowupBundle (I : X.IdealSheafData) (A : LineBundle X) :
    LineBundle (PiExponentSeshadri.BlowupGluing.scheme I) :=
  (PiExponentSeshadri.BlowupGluing.exceptionalLineBundle I).tensor
    (A.pullback (PiExponentSeshadri.BlowupGluing.projection I))

theorem eventual_blowup_jetRestriction_surjective_of_section_comparison
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A))
    {J : Type} (U : J → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤)
    (hcomparison : ∃ N, ∀ n, N ≤ n → Nonempty
      (CechH1Transfer.SectionComparison U
        (fun i => PiExponentSeshadri.BlowupGluing.projection I ⁻¹ᵁ U i)
        (twistedIdeal I A n)
        (modulePow (PiExponentSeshadri.BlowupGluing.scheme I) (blowupBundle I A).sheaf n))) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact eventual_jetRestriction_surjective_of_ample_comparison
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.projection I ≫ p) I A (blowupBundle I A)
    hample U hU hcover hcomparison

end
end PiExponent.BlowupJetSurjectivity

end OAI
