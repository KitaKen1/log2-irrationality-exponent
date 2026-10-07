/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the CRT packet proof using the project scaleYEquiv.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.JetIdealCRT

@[expose] public section

/-! Formal packets at distinct, nonzero Y centers. CRT is used before degree
bounds; the final quotient-lifting theorem can then receive bounded sections. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox JetGeometry
noncomputable section
variable {m : ℕ}

theorem formalJetAt_packet_surjective (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : FramePolynomial m =>
      rationalCoefficientPacket v H (formalJetAt y c P)) := by
  intro packet
  obtain ⟨P, hP⟩ := AlgebraicJetPackets.formalJet_packet_surjective c v hv H packet
  obtain ⟨Q, hQ⟩ := (scaleYEquiv y hy).surjective P
  refine ⟨Q, ?_⟩
  change rationalCoefficientPacket v H (FormalLogJet.formalJet c (scaleY y Q)) = packet
  change scaleY y Q = P at hQ
  rw [hQ]
  exact hP

theorem formalJetAt_packet_eq_of_sub_mem_pow (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : FramePolynomial m) (hPQ : P - Q ∈ jetIdealAt y c T e ^ n) :
    rationalCoefficientPacket v (n * R) (formalJetAt y c P) =
      rationalCoefficientPacket v (n * R) (formalJetAt y c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n * R) _ _).mpr
  simpa only [map_sub] using
    formalJetAt_mem_weighted_of_mem_pow y c T e v hv hT R he n (P - Q) hPQ

theorem formalJetAt_packets_surjective {J : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : FramePolynomial m => fun j =>
      rationalCoefficientPacket v (n * R) (formalJetAt (y j) (c j) P)) := by
  intro packets
  choose P hP using fun j => formalJetAt_packet_surjective (y j) (hy0 j) (c j) v hv
    (n * R) (packets j)
  obtain ⟨Q, hQ⟩ := jetIdealAt_residue_surjective y hy c T e hepos n
    (fun j => Ideal.Quotient.mk (jetIdealAt (y j) (c j) T e ^ n) (P j))
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (Ideal.Quotient.eq.mp (congrFun hQ j))).trans (hP j)

theorem formalJetAt_packets_surjective_of_quotient {J α : Type*} [Fintype J]
    (y : J → ℂ) (hy0 : ∀ j, y j ≠ 0) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → FramePolynomial m)
    (hf : Function.Surjective (fun a => Ideal.Quotient.mk (jetProductIdeal y c T e ^ n) (f a))) :
    Function.Surjective (fun a => fun j =>
      rationalCoefficientPacket v (n * R) (formalJetAt (y j) (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJetAt_packets_surjective y hy0 hy c T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  refine ⟨a, ?_⟩
  funext j
  exact (formalJetAt_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (jetProductIdeal_pow_le y c T e n j (Ideal.Quotient.eq.mp ha))).trans
      (congrFun hP j)

end
end LogTwo.Geometry
