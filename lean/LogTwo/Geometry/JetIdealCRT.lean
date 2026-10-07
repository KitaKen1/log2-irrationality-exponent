module

public import LogTwo.Geometry.JetIdealAt

@[expose] public section

/-! Chinese remainder interpolation at the distinct centers. There is no
weighted-degree bound here, so this does not imply FullRowMinor. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
noncomputable section

theorem jetIdealAt_pairwise_coprime {m : ℕ} {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun j k => IsCoprime (jetIdealAt (y j) (c j) T e)
      (jetIdealAt (y k) (c k) T e)) := by
  intro j k hjk
  have hne : WeightedBezout.pointIdeal (centerPoint (y j) (c j)) ≠
      WeightedBezout.pointIdeal (centerPoint (y k) (c k)) := by
    intro h
    apply hjk
    apply centerPrime_injective_of_Y y hy c
    exact PrimeSpectrum.ext h
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_jetIdealAt (y j) (c j) T e he,
    radical_jetIdealAt (y k) (c k) T e he,
    (Ideal.isCoprime_of_isMaximal hne).sup_eq, Ideal.radical_top]

/-- Every finite set of polynomial residue classes can be simultaneously
realized, with no bound asserted on the degree of the realizing polynomial. -/
theorem jetIdealAt_residue_surjective {m : ℕ} {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (n : ℕ) :
    Function.Surjective (fun P : FramePolynomial m =>
      fun j => Ideal.Quotient.mk (jetIdealAt (y j) (c j) T e ^ n) P) := by
  intro b
  have hpair : Pairwise (fun j k => IsCoprime (jetIdealAt (y j) (c j) T e ^ n)
      (jetIdealAt (y k) (c k) T e ^ n)) := by
    intro j k hjk
    exact (jetIdealAt_pairwise_coprime y hy c T e he hjk).pow
  obtain ⟨P, hP⟩ := Ideal.pi_quotient_surjective hpair b
  exact ⟨P, funext hP⟩

end
end LogTwo.Geometry
