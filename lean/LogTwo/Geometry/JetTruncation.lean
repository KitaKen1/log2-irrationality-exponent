/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the formal-log truncation proof to varying Y-centers and scaled polynomials.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.ScaledJet
public import OAI.NumberTheory.PiExponent.Analysis.FormalLogTruncation

@[expose] public section

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
FormalLogTruncation.formalLog_packets_surjective_iff_truncated (Apache-2.0).
Modified here to allow a family of different Y-centers; see THIRD_PARTY_NOTICES.txt.

Transfer interpolation surjectivity through a filtration-preserving change
of variables. The full and truncated coefficient packets need not be equal. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogTruncation PiExponent.JetGeometry
noncomputable section

def truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (truncatedFormalJet c T).comp (scaleY y)

theorem shiftMap_truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedJetAt y c T P) = formalJetAt y c P :=
  shiftMap_truncatedFormalJet c T (scaleY y P)

/-- For an entire family of different Y-centers, one common shift of jet variables
transfers surjectivity. No equality of the individual coefficient packets is used. -/
theorem formalJetAt_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (formalJetAt (y j) (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H
        (truncatedJetAt (y j) (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedJetAt (y j) (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedJetAt] using hh

end
end LogTwo.Geometry
