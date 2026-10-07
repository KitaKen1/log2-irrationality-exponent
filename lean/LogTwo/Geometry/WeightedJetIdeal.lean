/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt ideal-support arguments to rational matrix weights and varying Y-centers.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.WeightedCompactification
public import LogTwo.Geometry.CompactJetIdealAt
public import LogTwo.Geometry.JetProductContact
public import LogTwo.Geometry.StrictJetTruncation

@[expose] public section

/-! Varying-center jet ideals on the concrete weighted compactification.
The chart, proper structure morphism, Noetherian hypotheses, and balanced
integer powers are constructed from the matrix weights. This does not yet
identify the global normalization curve's stalk maps or its divisor degrees.
Support arguments adapt openai/math Ampleness/AdmissibleBlowupGeometry.lean
(Apache-2.0); see THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.MatrixCompactification
open OAI PiExponent AlgebraicGeometry CategoryTheory
open LogTwo.Interpolation LogTwo.Arithmetic
open CurveValuationCenter PlaceValuationRing PlaceCenteredBranch CurveCenters
noncomputable section
variable {m : ℕ} (w : Weights m)

def centerIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) : (space w).IdealSheafData :=
  CompactJetIdealAt.compactIdeal y c T (scale w).jetPowers (affineChart w)

theorem centerIdeal_restrict {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (affineChart w) =
      CompactJetIdealAt.affineIdeal y c T (scale w).jetPowers :=
  CompactJetIdealAt.restrict_compactIdeal _ _ _ _ _

theorem centerIdeal_support {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).support : Set (space w)) =
      ⋃ j, Set.range (CompactJetIdealAt.point (y j) (c j) ≫ affineChart w) :=
  CompactJetIdealAt.support_compactIdeal _ _ _ _ (scale w).jetPowers_pos _
    (structureMap w) (affineChart_over w)

theorem centerIdeal_support_finite {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).support : Set (space w)).Finite := by
  rw [centerIdeal_support]
  exact Set.finite_iUnion (fun _ => Set.finite_range _)

theorem centerIdeal_support_subset_chart {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    ((centerIdeal w y c T).support : Set (space w)) ⊆ (affineChart w).opensRange := by
  rw [centerIdeal_support]
  intro x hx
  obtain ⟨j,z,rfl⟩ := Set.mem_iUnion.mp hx
  exact ⟨CompactJetIdealAt.point (y j) (c j) z, rfl⟩

theorem centerIdeal_coherent {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    (PiExponentSeshadri.IdealModule.closedModule (centerIdeal w y c T)).IsFinitePresentation :=
  CompactJetIdealAt.compactIdeal_isFinitePresentation _ _ _ _ _

theorem centerIdeal_affine_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    {A : Type} [CommRing A] (f : MvPolynomial (Fin (m+1)) ℂ →+* A) :
    (centerIdeal w y c T).comap (Spec.map (CommRingCat.ofHom f) ≫ affineChart w) =
      PiExponentSeshadri.IdealPullback.specIdeal
        ((jetProductIdeal y c T (scale w).jetPowers).map f) :=
  CompactJetIdealAt.comap_compactIdeal_spec _ _ _ _ _ f

theorem center_points_injective {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ) :
    Function.Injective (fun j => affineChart w (centerPrime (y j) (c j))) :=
  (affineChart w).isOpenEmbedding.injective.comp (centerPrime_injective_of_Y y hy c)

theorem origin_ne_center (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ) :
    origin w ≠ centerPrime y c := by
  intro h
  have hx : MvPolynomial.X (0 : Fin (m+1)) ∈ (origin w).asIdeal := by
    change MvPolynomial.aeval (0 : Fin (m+1) → ℂ) (MvPolynomial.X 0) = 0
    simp
  rw [h] at hx
  change MvPolynomial.aeval (centerPoint y c) (MvPolynomial.X 0) = 0 at hx
  exact hy (by simpa [centerPoint] using hx)

theorem origin_avoids_centers {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    affineChart w (origin w) ∉ (centerIdeal w y c T).support := by
  change affineChart w (origin w) ∉ ((centerIdeal w y c T).support : Set (space w))
  rw [centerIdeal_support]
  intro h
  obtain ⟨j,hj⟩ := Set.mem_iUnion.mp h
  obtain ⟨z,hz⟩ := hj
  have he : CompactJetIdealAt.point (y j) (c j) z = origin w :=
    (affineChart w).isOpenEmbedding.injective hz
  have hc : CompactJetIdealAt.point (y j) (c j) z = centerPrime (y j) (c j) := by
    apply Set.mem_singleton_iff.mp
    erw [← CompactJetIdealAt.range_point]
    exact ⟨z,rfl⟩
  exact origin_ne_center w (y j) (hy j) (c j) (he.symm.trans hc)

theorem centerIdeal_support_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ) (T : Fin m → ℕ) :
    (centerIdeal w y c T).support ≠ ⊤ := by
  intro h
  exact origin_avoids_centers w y hy c T (by rw [h]; trivial)

theorem formalJet_packet_zero {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (F : ℚ) (hF : 1 / w.theta < F)
    (n : ℕ) (P : MvPolynomial (Fin (m+1)) ℂ)
    (hP : P ∈ jetProductIdeal y c (truncationOrders w F) (scale w).jetPowers ^ n)
    (j : J) :
    JetGeometry.rationalCoefficientPacket (jetWeight w) (n * (scale w).radius)
      (formalJetAt (y j) (c j) P) = (fun _ => (0 : ℂ)) := by
  apply formalJetAt_packet_zero_of_mem_product_pow y c _ _ (jetWeight w)
    (fun i => (jetWeight_pos w i).le) (fun i => (truncation_weight_strict w F hF i).le)
    (scale w).radius (fun i => ?_) n P hP j
  rw [mul_comm, jet_balance]

/-- The manuscript's actual centers; rational r_i are cast only at the geometry boundary. -/
def logTwoIdeal (r : Fin m → ℚ) (T : Fin m → ℕ) : (space w).IdealSheafData :=
  centerIdeal w (fun j : Fin w.K => (2 : ℂ) ^ j.val)
    (fun j i => (j.val : ℂ) * (r i : ℂ)) T

theorem logTwoIdeal_support_finite (r : Fin m → ℚ) (T : Fin m → ℕ) :
    ((logTwoIdeal w r T).support : Set (space w)).Finite :=
  centerIdeal_support_finite w _ _ T

theorem logTwoIdeal_support_ne_top (r : Fin m → ℚ) (T : Fin m → ℕ) :
    (logTwoIdeal w r T).support ≠ ⊤ :=
  centerIdeal_support_ne_top w _ (fun j => pow_ne_zero _ (by norm_num)) _ T

theorem logTwo_centers_injective (r : Fin m → ℚ) :
    Function.Injective (fun j : Fin w.K => affineChart w
      (centerPrime ((2 : ℂ) ^ j.val) (fun i => (j.val : ℂ) * (r i : ℂ)))) := by
  apply center_points_injective
  intro a b h
  apply Fin.ext
  exact complex_centerY_injective h

variable {E : Type} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E)

def branchMap {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    Spec (.of (ring p)) ⟶ space w :=
  Spec.map (CommRingCat.ofHom
    (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom) ≫ affineChart w

theorem branchMap_over {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    branchMap w p y c z j hc ≫ structureMap w =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (ring p))) := by
  rw [branchMap, Category.assoc, affineChart_over,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext a
  simp

theorem branchMap_generic {J : Type*} (y : J → ℂ) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) :
    Spec.map (CommRingCat.ofHom (algebraMap (ring p) E)) ≫ branchMap w p y c z j hc =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫ affineChart w := by
  have h : (algebraMap (ring p) E).comp
      (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom =
      (MvPolynomial.aeval z).toRingHom :=
    RingHom.ext (lift_aeval p z (centerPoint (y j) (c j)) hc)
  rw [branchMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h]

theorem centerIdeal_branch_pullback {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    (centerIdeal w y c T).comap (branchMap w p y c z j hc) =
      PiExponentSeshadri.IdealPullback.specIdeal
        (localJetProductIdeal p y c z j hc T (scale w).jetPowers) :=
  centerIdeal_affine_pullback w y c T _

/-- The actual pulled-back sheaf ideal, expressed in the DVR via its affine
section ring. The computation follows ExceptionalCurveDegree.localIdeal_specIdeal. -/
def branchIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) : Ideal (ring p) :=
  (((centerIdeal w y c T).comap (branchMap w p y c z j hc)).ideal
    ⟨⊤, isAffineOpen_top _⟩).map (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom

theorem branchIdeal_eq {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E)
    (j : J) (hc : Centered z (centerPoint (y j) (c j)) p) (T : Fin m → ℕ) :
    branchIdeal w p y c z j hc T = localJetProductIdeal p y c z j hc T (scale w).jetPowers := by
  rw [branchIdeal, centerIdeal_branch_pullback,
    PiExponentSeshadri.IdealPullback.specIdeal_top, Ideal.map_map]
  have he : (Scheme.ΓSpecIso (CommRingCat.of (ring p))).hom.hom.comp
      (Scheme.ΓSpecIso (CommRingCat.of (ring p))).inv.hom = RingHom.id (ring p) := by
    apply RingHom.ext
    intro a
    exact (Scheme.ΓSpecIso (CommRingCat.of (ring p))).inv_hom_id_apply a
  rw [he, Ideal.map_id]

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem branch_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    ((Module.length (ring p) ((ring p) ⧸
      branchIdeal w p y c z j hc (truncationOrders w F))).toNat : ℚ) =
      (scale w).radius * logContactAt p (y j) (hy0 j) z (c j) hc hnc (jetWeight w) := by
  rw [branchIdeal_eq]
  exact localJetProductIdeal_colength_eq_contact p y hy hy0 c z j hc hnc (jetWeight w)
    (jetWeight_pos w) _ (truncation_weight_strict w F hF) (scale w).radius
    (scale w).jetPowers (scale w).jetPowers_pos (jet_balance w)

theorem branch_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (F : ℚ) (hF : 1 / w.theta < F) :
    Module.length (ring p) ((ring p) ⧸
      branchIdeal w p y c z j hc (truncationOrders w F)) ≠ ⊤ := by
  rw [branchIdeal_eq]
  exact localJetProductIdeal_colength_ne_top p y hy hy0 c z j hc hnc (jetWeight w)
    (jetWeight_pos w) _ (truncation_weight_strict w F hF) (scale w).radius
    (scale w).jetPowers (scale w).jetPowers_pos (jet_balance w)

end
end LogTwo.Geometry.MatrixCompactification
