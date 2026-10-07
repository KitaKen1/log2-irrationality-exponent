/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/EquidimensionalRetainedCut.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.LocalAlgebra.PrimeHypersurfaceEquidimension
public import OAI.NumberTheory.PiExponent.LocalAlgebra.RetainedMinimalPrimeFamily

@[expose] public section

namespace OAI

namespace PiExponentJets.W22.RetainedPrimeCycle

attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

theorem retainedChild_dimension
    (C : RetainedPrimeCycle.{u,u,u} k σ) (f : MvPolynomial σ k)
    (havoid : ∀ a, f ∉ (C.component a).val) (s : ℕ)
    (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (a : C.Index)
    (Q : RetainedMinimalPrime (Ideal.span {f} ⊔ (C.component a).val) T) :
    ringKrullDim (MvPolynomial σ k ⧸ Q.val) = (s+1 : ℕ) := by
  obtain ⟨N, hN⟩ := actualHP_eventually (C.component a).val (C.component a).homogeneous
  have hPdim := W24.prime_hilbert_natDegree_add_one_eq_krullDim (C.component a).val
    (C.component a).homogeneous (C.component a).coordinate (C.component a).coordinate_not_mem
    (actualHP (C.component a).val (C.component a).homogeneous) (N+1)
    (fun n hn => (hN n (by omega)).symm)
  have hdim : ringKrullDim (MvPolynomial σ k ⧸ (C.component a).val) = (s+2 : ℕ) := by
    calc
      _ = ((actualHP (C.component a).val (C.component a).homogeneous).natDegree + 1 :
          WithBot ℕ∞) := hPdim.symm
      _ = ((s+2 : ℕ) : WithBot ℕ∞) := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact congrArg (fun n : ℕ => (n : WithBot ℕ∞)) (by rw [hparent a])
  exact W24.minimal_prime_hypersurface_dimension k σ (C.component a).val Q.val f
    (havoid a) (by simpa only [sup_comm] using Q.property.1) s hdim

noncomputable def equidimensionalRetainedCut
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) : ProperCut C :=
  canonicalRetainedCut C f d hd hf havoid s hparent T v hv
    (retainedChild_dimension C f havoid s hparent T)

theorem equidimensionalRetainedCut_covers
    (C : RetainedPrimeCycle.{u,u,u} k σ)
    (f : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hf : f.IsHomogeneous d)
    (havoid : ∀ a, f ∉ (C.component a).val)
    (s : ℕ) (hparent : ∀ a,
      (actualHP (C.component a).val (C.component a).homogeneous).natDegree = s+1)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    (equidimensionalRetainedCut C f d hd hf havoid s hparent T v hv).CoversBelow T :=
  canonicalRetainedCut_covers C f d hd hf havoid s hparent T v hv
    (retainedChild_dimension C f havoid s hparent T)

end PiExponentJets.W22.RetainedPrimeCycle

end OAI
