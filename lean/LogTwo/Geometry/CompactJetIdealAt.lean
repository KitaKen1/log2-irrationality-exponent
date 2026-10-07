/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt compact jet ideals to arbitrary Y-centers and add an affine pullback identity.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.JetIdealAt
public import OAI.NumberTheory.PiExponent.Jets.CompactLogJetIdeal

@[expose] public section

/-! Adapted from openai/math at adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/CompactLogJetIdeal.lean (Apache-2.0), to arbitrary Y-centers.
The finite-support ideal extends to an ambient scheme, restricts back to the
given affine chart, and has no support away from the actual centers.
Ampleness, curve-degree transport, and bounded-degree interpolation are separate.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.CompactJetIdealAt
open OAI PiExponent CategoryTheory AlgebraicGeometry
open CompactLogJetIdeal (affineSpace base structureMap support_specIdeal)
noncomputable section

variable {m : ℕ}

def point (y : ℂ) (c : Fin m → ℂ) : base ⟶ affineSpace m :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (centerPoint y c)).toRingHom)

theorem point_section (y : ℂ) (c : Fin m → ℂ) :
    point y c ≫ structureMap m = 𝟙 base := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (algebraMap ℂ (CompactLogJetIdeal.coordinateRing m)) ≫
      CommRingCat.ofHom (MvPolynomial.aeval (centerPoint y c)).toRingHom =
      𝟙 (CommRingCat.of ℂ) := by
    ext a
    simp
  rw [h, Spec.map_id]

theorem range_point (y : ℂ) (c : Fin m → ℂ) :
    Set.range (point y c) = {centerPrime y c} := by
  change Set.range (PrimeSpectrum.comap (MvPolynomial.aeval (centerPoint y c)).toRingHom) = _
  rw [range_comap_of_surjective _ _ (by
    intro a
    exact ⟨MvPolynomial.C a, by simp⟩)]
  exact PrimeSpectrum.zeroLocus_eq_singleton (WeightedBezout.pointIdeal (centerPoint y c))

def affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    (affineSpace m).IdealSheafData :=
  PiExponentSeshadri.IdealPullback.specIdeal (jetProductIdeal y c T e)

theorem support_affineIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    ((affineIdeal y c T e).support : Set (affineSpace m)) =
      ⋃ j, Set.range (point (y j) (c j)) := by
  rw [affineIdeal, support_specIdeal, zeroLocus_jetProductIdeal y c T e he]
  simp only [range_point]
  ext p
  constructor
  · rintro ⟨j, rfl⟩
    exact Set.mem_iUnion.mpr ⟨j, Set.mem_singleton _⟩
  · intro hp
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hp
    exact ⟨j, (Set.mem_singleton_iff.mp hj).symm⟩

def compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) : X.IdealSheafData :=
  CompactJetIdeal.extend (affineIdeal y c T e) j

theorem restrict_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j] :
    (compactIdeal y c T e j).comap j = affineIdeal y c T e :=
  CompactJetIdeal.restrict_extend _ j

/-- Pullback along any affine ring map agrees with the algebraic image of the
product ideal. Instantiating the ring map with branch evaluation is now exact. -/
theorem comap_compactIdeal_spec {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} (j : affineSpace m ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    {A : Type} [CommRing A] (f : CompactLogJetIdeal.coordinateRing m →+* A) :
    (compactIdeal y c T e j).comap (Spec.map (CommRingCat.ofHom f) ≫ j) =
      PiExponentSeshadri.IdealPullback.specIdeal ((jetProductIdeal y c T e).map f) := by
  rw [Scheme.IdealSheafData.comap_comp, restrict_compactIdeal]
  exact PiExponentSeshadri.IdealPullback.specIdeal_comap _ f

theorem support_compactIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m) :
    ((compactIdeal y c T e j).support : Set X) =
      ⋃ a, Set.range (point (y a) (c a) ≫ j) := by
  rw [compactIdeal, CompactJetIdeal.support_extend (affineIdeal y c T e) j π
    (fun a => point (y a) (c a)) (fun a => by
      rw [Category.assoc, hπ, point_section]) (support_affineIdeal y c T e he),
    support_affineIdeal y c T e he, Set.image_iUnion]
  congr 1
  funext a
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]

theorem compactIdeal_isFinitePresentation {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    {X : Scheme} [IsLocallyNoetherian X] (j : affineSpace m ⟶ X) :
    (PiExponentSeshadri.IdealModule.closedModule (compactIdeal y c T e j)).IsFinitePresentation :=
  CompactJetIdeal.extend_isFinitePresentation _ j

theorem comap_compactIdeal_eq_top_of_avoids_centers {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    {X V : Scheme} (j : affineSpace m ⟶ X) [QuasiCompact j]
    (π : X ⟶ base) [IsSeparated π] (hπ : j ≫ π = structureMap m)
    (f : V ⟶ X) (havoid : ∀ v a, f v ∉ Set.range (point (y a) (c a) ≫ j)) :
    (compactIdeal y c T e j).comap f = ⊤ := by
  apply CompactJetIdeal.restrict_eq_top_of_disjoint
  intro v
  change f v ∉ ((compactIdeal y c T e j).support : Set X)
  rw [support_compactIdeal y c T e he j π hπ]
  exact fun h => (Set.mem_iUnion.mp h).elim (fun a ha => havoid v a ha)

end
end LogTwo.Geometry.CompactJetIdealAt
