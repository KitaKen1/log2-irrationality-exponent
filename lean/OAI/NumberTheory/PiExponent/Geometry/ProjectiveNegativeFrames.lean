/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Approximation.InverseFrameRestriction
public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveCoordinateRatios

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.InverseFrames
variable {X : Scheme} {M N : X.Modules}

def negativeCoordinateFrame (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si : O X ⟶ M) :
    N.restrict (SectionOpens.isoOpen si).ι ≅ O (SectionOpens.isoOpen si).toScheme :=
  inverseOpenFrame E _ (coordinatePowerFrame si n)

lemma negativeCoordinateFrame_frameChange (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    W.topIso.hom
      (frameChange (restrictOpenFrame hi (negativeCoordinateFrame n E si))
        (restrictOpenFrame hj (negativeCoordinateFrame n E sj)) : Γ(W.toScheme,⊤)) =
      coordinateRatioOn si sj hi ^ n := by
  have h := (congrArg₂
    (fun e f : N.restrict W.ι ≅ O W.toScheme => frameChange e f)
    (inverseOpenFrame_restrict E hi (coordinatePowerFrame si n))
    (inverseOpenFrame_restrict E hj (coordinatePowerFrame sj n))).trans
      (inverseOpenFrame_frameChange E W _ _)
  have hv := congrArg
    (fun z : Γ(W.toScheme,⊤)ˣ => W.topIso.hom (z : Γ(W.toScheme,⊤))) h
  refine hv.trans ?_
  erw [coordinatePowerFrame_frameChange, map_pow, topIso_hom_restrict]
  rfl

lemma negativeCoordinateFrame_hom_change_restrict (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {U W : X.Opens} (hi : U ≤ SectionOpens.isoOpen si)
    (hj : W ≤ SectionOpens.isoOpen sj) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ N) :
    framedHomCoefficientsEquiv W N (restrictOpenFrame hj (negativeCoordinateFrame n E sj))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      coordinateRatioOn si sj (h.trans hi) ^ n * X.presheaf.map (homOfLE h).op
        (framedHomCoefficientsEquiv U N (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b) := by
  erw [framedHomCoefficientsEquiv_change W N
    (restrictOpenFrame (h.trans hi) (negativeCoordinateFrame n E si)),
    negativeCoordinateFrame_frameChange]
  congr 1
  have hr := framedHomCoefficientsEquiv_restrict N h
    (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b
  rw [restrictOpenFrame_trans] at hr
  exact hr

end
end PiExponentSeshadri.Projective

end OAI
