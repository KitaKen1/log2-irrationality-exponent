/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveTwoAffineVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.CurveEuler
public import OAI.NumberTheory.PiExponent.Cohomology.SerreVanishing

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.CurveTwoAffineVanishing
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem cohomology_subsingleton (U V : X.Opens) (hU : IsAffineOpen U)
    (hV : IsAffineOpen V) (hcover : U ⊔ V = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) (hn : 2 ≤ n) :
    Subsingleton (cohomology M n) := by
  let D : Fin 2 → X.Opens := ![U,V]
  have hD : ∀ i, IsAffineOpen (D i) := by
    intro i
    fin_cases i
    · exact hU
    · exact hV
  have hc : (⨆ i, D i) = ⊤ := by
    calc
      (⨆ i, D i) = U ⊔ V := le_antisymm
        (iSup_le (fun i => by
          fin_cases i
          · exact le_sup_left
          · exact le_sup_right))
        (sup_le (le_iSup D 0) (le_iSup D 1))
      _ = ⊤ := hcover
  exact ⟨fun x y =>
    (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn x).trans
      (SerreVanishing.ext_eq_zero_of_affine_cover 2 (by decide) D hD hc M n hn y).symm⟩

end PiExponent.CurveTwoAffineVanishing

end

end OAI
