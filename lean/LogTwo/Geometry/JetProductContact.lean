module

public import LogTwo.Geometry.JetIdealContact

@[expose] public section

/-! At a branch centered at one of the distinct Y-centers, all other factors
of the product jet ideal become the unit ideal. Thus the local colength of the
full product is the already verified logarithmic contact at this center. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox MvPolynomial
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section

variable {m : ℕ}

theorem isUnit_of_residueAugmentation_ne_zero {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (x : A) (hx : CurveLocalOrder.residueAugmentation ℂ A x ≠ 0) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro h
  apply hx
  change (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm
    (IsLocalRing.residue A x) = 0
  rw [h, map_zero]

/-- A different residue of the Y-coordinate makes the whole jet ideal a unit.
Only the radical is needed; explicit logarithmic generators are unnecessary. -/
theorem map_jetIdealAt_eq_top_of_residue_ne {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (he : ∀ i, 0 < e i) (u : Fin (m+1) → A)
    (hne : CurveLocalOrder.residueAugmentation ℂ A (u 0) ≠ y) :
    (jetIdealAt y c T e).map (MvPolynomial.aeval u).toRingHom = ⊤ := by
  have hg : X 0 - C y ∈ (jetIdealAt y c T e).radical := by
    rw [radical_jetIdealAt y c T e he]
    simp [centerPoint]
  obtain ⟨n, hn⟩ := hg
  have hu : IsUnit (MvPolynomial.aeval u (X 0 - C y)) := by
    apply isUnit_of_residueAugmentation_ne_zero
    simpa only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      CurveLocalOrder.residueAugmentation_algebraMap, sub_ne_zero] using hne
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (MvPolynomial.aeval u).toRingHom hn)
  change IsUnit (MvPolynomial.aeval u ((X 0 - C y) ^ n))
  rw [map_pow]
  exact hu.pow n

theorem map_jetProductIdeal_eq_factor {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    {J : Type*} [Fintype J] (y : J → ℂ) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (he : ∀ i, 0 < e i) (u : Fin (m+1) → A) (j : J)
    (hu : CurveLocalOrder.residueAugmentation ℂ A (u 0) = y j) :
    (jetProductIdeal y c T e).map (MvPolynomial.aeval u).toRingHom =
      (jetIdealAt (y j) (c j) T e).map (MvPolynomial.aeval u).toRingHom := by
  classical
  change Ideal.mapHom (MvPolynomial.aeval u).toRingHom
    (∏ k, jetIdealAt (y k) (c k) T e) = _
  rw [map_prod]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    have hne : CurveLocalOrder.residueAugmentation ℂ A (u 0) ≠ y k := by
      rw [hu]
      exact fun h => hkj (hy h).symm
    exact (map_jetIdealAt_eq_top_of_residue_ne (y k) (c k) T e he u hne).trans
      Ideal.one_eq_top.symm
  · simp

variable {E : Type*} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E)
variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def localJetProductIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (ring p) :=
  (jetProductIdeal y c T e).map
    (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom

theorem localJetProductIdeal_eq {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    localJetProductIdeal p y c z j hc T e = localJetIdealAt p (y j) z (c j) hc T e := by
  exact map_jetProductIdeal_eq_factor y hy c T e he
    (lift p z (centerPoint (y j) (c j)) hc) j
    (lift_residue p z (centerPoint (y j) (c j)) hc 0)

theorem localJetProductIdeal_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (hbalance : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ localJetProductIdeal p y c z j hc T e)).toNat : ℚ) =
      R * logContactAt p (y j) (hy0 j) z (c j) hc hnc v := by
  rw [localJetProductIdeal_eq p y hy c z j hc T e he]
  exact localJetIdealAt_colength_eq_contact p (y j) (hy0 j) z (c j) hc hnc
    v hv T hT R e hbalance

theorem localJetProductIdeal_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (hbalance : ∀ i, v i * (e i : ℚ) = R) :
    Module.length (ring p) ((ring p) ⧸ localJetProductIdeal p y c z j hc T e) ≠ ⊤ := by
  rw [localJetProductIdeal_eq p y hy c z j hc T e he]
  exact localJetIdealAt_colength_ne_top p (y j) (hy0 j) z (c j) hc hnc
    v hv T hT R e hbalance

end
end LogTwo.Geometry
