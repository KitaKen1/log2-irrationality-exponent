/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoordinateFrameIdentification.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.LineBundleFrameCocycle

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.LineBundleFrameCocycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme} {ι : Type} {U : ι → X.Opens}

lemma cocycle_ext {c d : LineBundleGluing.Cocycle U}
    (h : c.transition = d.transition) : c = d := by
  cases c
  cases d
  cases h
  rfl

def isoOfCoordinateCoefficients (M N : X.Modules)
    (e : ∀ i, M.restrict (U i).ι ≅ O (U i).toScheme)
    (f : ∀ i, N.restrict (U i).ι ≅ O (U i).toScheme)
    (s : ι → (O X ⟶ M)) (t : ι → (O X ⟶ N))
    (hnorm : ∀ i, coefficient (e i) (restrictSection (U i).ι (s i)) = 1)
    (hcoeff : ∀ i j, coefficient (f i) (restrictSection (U i).ι (t j)) =
      coefficient (e i) (restrictSection (U i).ι (s j)))
    (hcover : ⊤ ≤ ⨆ i, U i) : M ≅ N := by
  have hnorm' (i : ι) : coefficient (f i) (restrictSection (U i).ι (t i)) = 1 :=
    (hcoeff i i).trans (hnorm i)
  have hc : ofFrames M U e = ofFrames N U f := by
    apply cocycle_ext
    funext i j W hi hj
    apply Units.ext
    change W.topIso.hom
      (frameChange (restrictOpenFrame hj (e j)) (restrictOpenFrame hi (e i)) : Γ(W.toScheme,⊤)) =
      W.topIso.hom
        (frameChange (restrictOpenFrame hj (f j)) (restrictOpenFrame hi (f i)) : Γ(W.toScheme,⊤))
    rw [frameChange_restrictOpenFrame hj hi (e j) (e i) (s j) (hnorm j),
      frameChange_restrictOpenFrame hj hi (f j) (f i) (t j) (hnorm' j), hcoeff i j]
  exact isoSheaf M U e hcover ≪≫ eqToIso (congrArg LineBundleGluing.sheaf hc) ≪≫
    (isoSheaf N U f hcover).symm

end
end PiExponentSeshadri.LineBundleFrameCocycle

end OAI
