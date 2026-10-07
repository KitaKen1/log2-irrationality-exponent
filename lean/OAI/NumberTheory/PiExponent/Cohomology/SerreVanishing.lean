/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/SerreVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.FiniteCoverCohomology

@[expose] public section

namespace OAI

namespace PiExponent.SerreVanishing

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian

universe u

variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

abbrev schemeUnit (Y : Scheme.{u}) : Y.Modules :=
  SheafOfModules.unit Y.ringCatSheaf

theorem ext_eq_zero_of_affine_cover (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hcover : (⨆ i, U i) = ⊤) (M : X.Modules) [M.IsQuasicoherent]
    (q : ℕ) (hq : l ≤ q)
    (x : Abelian.Ext.{u+1} (C := X.Modules) (schemeUnit X) M q) : x = 0 := by
  cases l with
  | zero => exact False.elim (Nat.not_lt_zero 0 hl)
  | succ l =>
      have he : l + (q - (l + 1)) + 1 = q := by omega
      revert x
      clear hq
      rw [← he]
      exact PiExponentSeshadri.FiniteCoverCohomology.cover_ext_zero
        l U hU hcover M _

end

end PiExponent.SerreVanishing

end OAI
