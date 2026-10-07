/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFromClosedFibers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
universe u

theorem isFinite_of_proper_finite_closed_fibers {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (hfinite : ∀ y : Y, IsClosed ({y} : Set Y) → (f ⁻¹' {y}).Finite) : IsFinite f := by
  have htop : f.quasiFiniteLocus = ⊤ := by
    apply top_unique
    intro x _
    by_contra hx
    have hclosed : IsClosed (f '' ((f.quasiFiniteLocus : Set X)ᶜ)) :=
      f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl
    obtain ⟨y, ⟨z, hz, hzy⟩, hy⟩ :=
      nonempty_inter_closedPoints (Z := f '' ((f.quasiFiniteLocus : Set X)ᶜ))
        ⟨f x, x, hx, rfl⟩ hclosed.isLocallyClosed
    have hfin : (f ⁻¹' {f z}).Finite := by rw [hzy]; exact hfinite y hy
    let : Finite (f.fiber (f z)) := (f.fiberHomeo (f z)).finite_iff.mpr hfin
    have hq : f.QuasiFiniteAt z :=
      Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
    exact hz hq
  let : LocallyQuasiFinite f := (Scheme.Hom.quasiFiniteLocus_eq_top_iff f).mp htop
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

end PiExponent.NumericalAmpleness

end

end OAI
