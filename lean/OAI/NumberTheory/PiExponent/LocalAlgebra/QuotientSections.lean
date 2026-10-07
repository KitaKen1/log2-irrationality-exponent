/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import OAI.NumberTheory.PiExponent.Polynomials.HomogeneousSections

@[expose] public section

namespace OAI

namespace PiExponentJets.W64

variable {k σ : Type*} [Field k] [Finite σ]

noncomputable def quotientSection (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Submodule k (MvPolynomial σ k ⧸ I) :=
  (MvPolynomial.homogeneousSubmodule σ k n).map (Ideal.Quotient.mkₐ k I).toLinearMap

noncomputable instance quotientSection_finite (I : Ideal (MvPolynomial σ k)) (n : ℕ) :
    Module.Finite k (quotientSection I n) := by
  unfold quotientSection
  infer_instance

noncomputable def quotientSectionMultiply (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d) (n : ℕ) :
    quotientSection I n →ₗ[k] quotientSection I (n + d) where
  toFun x := ⟨x.1 * Ideal.Quotient.mk I f, by
    obtain ⟨p, hp, hpx⟩ := Submodule.mem_map.mp x.2
    apply Submodule.mem_map.mpr
    refine ⟨p * f, hp.mul hf, ?_⟩
    change Ideal.Quotient.mk I (p * f) = x.1 * Ideal.Quotient.mk I f
    rw [map_mul]
    exact congrArg (fun y => y * Ideal.Quotient.mk I f) hpx⟩
  map_add' x y := by apply Subtype.ext; exact add_mul _ _ _
  map_smul' c x := by apply Subtype.ext; exact smul_mul_assoc _ _ _

omit [Finite σ] in
theorem quotientSectionMultiply_injective (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Function.Injective (quotientSectionMultiply I f hf n) := by
  intro x y h
  apply Subtype.ext
  exact hreg (congrArg Subtype.val h)

theorem quotientSectionCokernel_finrank_add (I : Ideal (MvPolynomial σ k))
    {d : ℕ} (f : MvPolynomial σ k) (hf : f.IsHomogeneous d)
    (hreg : IsRightRegular (Ideal.Quotient.mk I f)) (n : ℕ) :
    Module.finrank k
        (quotientSection I (n + d) ⧸
          LinearMap.range (quotientSectionMultiply I f hf n)) +
      Module.finrank k (quotientSection I n) =
      Module.finrank k (quotientSection I (n + d)) := by
  have hi := quotientSectionMultiply_injective I f hf hreg n
  simpa only [LinearMap.finrank_range_of_inj hi] using
    (LinearMap.range (quotientSectionMultiply I f hf n)).finrank_quotient_add_finrank

end PiExponentJets.W64

end OAI
