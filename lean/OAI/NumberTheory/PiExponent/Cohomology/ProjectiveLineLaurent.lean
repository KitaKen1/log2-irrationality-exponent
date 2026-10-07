/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLineLaurent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.AlgebraicGeometry.OpenImmersion

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponent.ProjectiveLine

open CategoryTheory AlgebraicGeometry
universe u
variable (F : Type u) [CommRing F]

def zeroPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.toLaurent

def infinityPolynomialMap : Polynomial F →+* LaurentPolynomial F :=
  Polynomial.eval₂RingHom LaurentPolynomial.C (LaurentPolynomial.T (-1))

@[simp] theorem zeroPolynomialMap_C (r : F) :
    zeroPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [zeroPolynomialMap]

@[simp] theorem zeroPolynomialMap_X :
    zeroPolynomialMap F Polynomial.X = LaurentPolynomial.T 1 := by
  simp [zeroPolynomialMap]

@[simp] theorem infinityPolynomialMap_C (r : F) :
    infinityPolynomialMap F (Polynomial.C r) = LaurentPolynomial.C r := by
  simp [infinityPolynomialMap]

@[simp] theorem infinityPolynomialMap_X :
    infinityPolynomialMap F Polynomial.X = LaurentPolynomial.T (-1) := by
  simp [infinityPolynomialMap]

theorem infinityPolynomialMap_eq_invert_comp :
    infinityPolynomialMap F =
      (LaurentPolynomial.invert (R := F)).toRingHom.comp (zeroPolynomialMap F) := by
  apply Polynomial.ringHom_ext
  · intro r
    simp
  · simp

def laurentInversion :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶
      Spec (CommRingCat.of (LaurentPolynomial F)) :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.invert (R := F)).toRingHom)

instance laurentInversion_isIso : IsIso (laurentInversion F) := by
  have : IsIso (CommRingCat.ofHom (LaurentPolynomial.invert (R := F)).toRingHom) :=
    (LaurentPolynomial.invert (R := F)).toRingEquiv.toCommRingCatIso.isIso_hom
  unfold laurentInversion
  infer_instance

def zeroChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (zeroPolynomialMap F))

def infinityChartOverlap :
    Spec (CommRingCat.of (LaurentPolynomial F)) ⟶ Spec (CommRingCat.of (Polynomial F)) :=
  Spec.map (CommRingCat.ofHom (infinityPolynomialMap F))

theorem infinityChartOverlap_eq :
    infinityChartOverlap F = laurentInversion F ≫ zeroChartOverlap F := by
  unfold infinityChartOverlap laurentInversion zeroChartOverlap
  rw [infinityPolynomialMap_eq_invert_comp, CommRingCat.ofHom_comp, Spec.map_comp]

instance zeroChartOverlap_isOpenImmersion : IsOpenImmersion (zeroChartOverlap F) :=
  IsOpenImmersion.of_isLocalization (S := LaurentPolynomial F) (Polynomial.X : Polynomial F)

instance infinityChartOverlap_isOpenImmersion : IsOpenImmersion (infinityChartOverlap F) := by
  rw [infinityChartOverlap_eq]
  infer_instance

theorem zeroChartOverlap_opensRange :
    (zeroChartOverlap F).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial F) := by
  exact TopologicalSpace.Opens.ext
    (PrimeSpectrum.localization_away_comap_range (LaurentPolynomial F) Polynomial.X)

theorem infinityChartOverlap_opensRange :
    (infinityChartOverlap F).opensRange = PrimeSpectrum.basicOpen (Polynomial.X : Polynomial F) := by
  simpa only [infinityChartOverlap_eq] using
    (Scheme.Hom.opensRange_comp_of_isIso (laurentInversion F) (zeroChartOverlap F)).trans
      (zeroChartOverlap_opensRange F)

end PiExponent.ProjectiveLine

end

end OAI
