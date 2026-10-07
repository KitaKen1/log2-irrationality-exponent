/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part029
public import LogTwoCheckpoints.Part030
public import LogTwoCheckpoints.Part031
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.ReesAlgebra
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesCechInjectivity.lean
section Source0800
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesCechInjectivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesCechInjectivity
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [IsNoetherianRing R]

theorem exists_ideal_power_annihilating (I : Ideal R) (a : J → R)
    (ha : Ideal.span (Set.range a) = I) (x : R)
    (hx : ∀ j, ∃ k : ℕ, a j ^ k * x = 0) :
    ∃ k : ℕ, ∀ b ∈ I ^ k, b * x = 0 := by
  let A : Ideal R := (Ideal.span {x}).annihilator
  have hIA : I ≤ A.radical := by
    rw [← ha]
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := hx j
    apply Ideal.mem_radical_iff.mpr
    refine ⟨k, ?_⟩
    change a j ^ k ∈ (Submodule.span R {x}).annihilator
    simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using hk
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIA (IsNoetherian.noetherian I)
  refine ⟨k, ?_⟩
  intro b hb
  have h := hk hb
  change b ∈ (Submodule.span R {x}).annihilator at h
  simpa only [Submodule.mem_annihilator_span_singleton, smul_eq_mul] using h

variable [Fintype J] [DecidableEq J] (I : Ideal R) (a : J → I)

theorem eventually_augmentation_injective
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Function.Injective
      (augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesPushdown.eventually_no_power_torsion I
  refine ⟨N, ?_⟩
  intro n hn z w hzw
  have hzero : augmentation (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n (z - w) = 0 := by
    rw [map_sub, hzw, sub_self]
  let m : reesAlgebra I := (z - w).val
  let x : R := ((m : reesAlgebra I) : Polynomial R).coeff n
  have hm : m ∈ piece I n := (z - w).property
  have heval : evaluation I m = x := evaluation_piece I ⟨m, hm⟩
  have hx : x ∈ I ^ n := m.property n
  have hloc (j : J) : ∃ k : ℕ, (a j).val ^ k * x = 0 := by
    have ht := congrArg Subtype.val (congrFun hzero (fun _ : Fin 1 => j))
    change fraction (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0 = 0 at ht
    have htuple : tupleSet (fun _ : Fin 1 => j) = {j} := by
      ext k
      simp [tupleSet, eq_comm]
    obtain ⟨k, hk⟩ := (fraction_eq_zero
      (coverProduct MvPolynomial.X (tupleSet (fun _ : Fin 1 => j))) m 0).mp ht
    have hprod : coverProduct (MvPolynomial.X : J → MvPolynomial J R)
        (tupleSet (fun _ : Fin 1 => j)) = MvPolynomial.X j := by
      rw [htuple, coverProduct, Finset.prod_singleton]
    rw [hprod] at hk
    refine ⟨k, ?_⟩
    have h := congrArg (evaluation I) hk
    change evaluation I (presentation I a (MvPolynomial.X j ^ k) * m) = evaluation I 0 at h
    simpa only [map_mul, map_pow, presentation_X, evaluation_generator, heval, map_zero] using h
  have hxzero : x = 0 := hN n hn x hx (exists_ideal_power_annihilating I
    (fun j => (a j).val) ha x hloc)
  apply Subtype.ext
  apply sub_eq_zero.mp
  change m = 0
  apply Subtype.ext
  rw [(mem_piece I n m).mp hm]
  change Polynomial.monomial n x = 0
  rw [hxzero, map_zero]

end
end PiExponent.ReesCechInjectivity

end OAI
end Source0800

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesCechRecovery.lean
section Source0801
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesCechRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesCechRecovery
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {R J : Type u} [CommRing R] [IsNoetherianRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem eventually_ordinary_power_recovery
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ q : ℕ, GradedSerreStep.HasPrimitive (J := J) (R := R) (integerPiece I) n q) ∧
      (∀ c : Cochain (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n 0,
        differential (grading (J := J) (R := R)) (integerPiece I)
          MvPolynomial.X variable_mem n c = 0 →
        ∃! z : ↥(I ^ n : Ideal R),
          augmentation (grading (J := J) (R := R)) (integerPiece I)
            MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n z) = c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  let : Module.Finite (MvPolynomial J R) (reesAlgebra I) := finite_presented_module I a ha
  obtain ⟨N₁, h₁⟩ := GradedSerreVanishing.eventually_all_positive (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₂, h₂⟩ := GradedSerreVanishing.eventually_augmentation_recovery (J := J) (R := R)
    (integerPiece I)
  obtain ⟨N₃, h₃⟩ := ReesCechInjectivity.eventually_augmentation_injective I a ha
  refine ⟨max N₁ (max N₂ N₃), ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := (le_max_left _ _).trans hn
  have hn₂ : N₂ ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn₃ : N₃ ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  refine ⟨h₁ n hn₁, ?_⟩
  intro c hc
  obtain ⟨m, hm⟩ := h₂ n hn₂ c hc
  refine ⟨(ordinaryPowerEquivIntegerPiece I n).symm m, ?_, ?_⟩
  · simpa only [AddEquiv.apply_symm_apply] using hm
  · intro z hz
    apply (ordinaryPowerEquivIntegerPiece I n).injective
    rw [AddEquiv.apply_symm_apply]
    exact h₃ n hn₃ (hz.trans hm.symm)

end
end PiExponent.ReesCechRecovery

end OAI
end Source0801

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesCohomologySetup.lean
section Source0802
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesCohomologySetup.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesCohomologySetup
noncomputable section
open AlgebraicGeometry PiExponentSeshadri.ReesGrading
variable {R : Type} [CommRing R] (I : Ideal R)

instance [IsNoetherianRing R] : IsNoetherian (affineBlowup I) := by
  let : CompactSpace (affineBlowup I) :=
    QuasiCompact.compactSpace_of_compactSpace (projection I)
  exact { __ := LocallyOfFiniteType.isLocallyNoetherian (projection I) }

theorem exceptionalPower_isQuasicoherent (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.IsQuasicoherent :=
  GeometrySupport.LineBundleCoherent.modulePow_isQuasicoherent (exceptionalLineBundle I) n

end
end PiExponent.ReesCohomologySetup

end OAI
end Source0802

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedRestriction.lean
section Source0803
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.IdealPullback
variable {R A B : Type} [CommRing R] [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (h : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

def restrictSections (L : LineBundle Y) (n : ℕ) :
    Sections j L n →+ Sections j' L n where
  toFun b := freeOpenMap Y.ringCatSheaf
    (homOfLE (ExceptionalAffineChart.opensRange_le j j' θ h)) ≫ b
  map_zero' := Limits.HasZeroMorphisms.comp_zero (C := Y.Modules) _ _
  map_add' b c := Preadditive.comp_add _ _ _ _ b c

variable (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R))
  (φ : R →+* A) (hf : j ≫ f = Spec.map (CommRingCat.ofHom φ))
  (L : LineBundle Y) (ι : L.sheaf ⟶ O Y)
  (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
  (e : Frame j L)
  (φ' : R →+* B) (hf' : j' ≫ f = Spec.map (CommRingCat.ofHom φ'))
  (e' : Frame j' L)

theorem representedSectionsTyped_restrict (n : ℕ) (b : Sections j L n) :
    (representedSectionsTyped I f j' φ' hf' L ι hL e' n
      (restrictSections j j' θ h L n b)).val =
      θ (representedSectionsTyped I f j φ hf L ι hL e n b).val := by
  rw [representedSectionsTyped_apply, representedSectionsTyped_apply]
  exact ExceptionalAffineChart.representedSectionsEquiv_restrict
    I f j φ hf L ι hL e j' θ h φ' hf' e' n b

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end Source0803

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransportNaturality.lean
section Source0804
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalTypedTransportNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ExceptionalRepresentedTypes
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {A B : Type} [CommRing A] [CommRing B] {Y : Scheme}
variable (j : Spec (CommRingCat.of A) ⟶ Y) [IsOpenImmersion j]
  (j' : Spec (CommRingCat.of B) ⟶ Y) [IsOpenImmersion j']
  (θ : A →+* B) (hchart : Spec.map (CommRingCat.ofHom θ) ≫ j = j')

theorem transportSections_restrict (L : LineBundle Y) (n : ℕ)
    {U V : Y.Opens} (hU : j.opensRange = U) (hV : j'.opensRange = V)
    (hVU : V ≤ U) (b : freeOpen Y.ringCatSheaf U ⟶ (L.pow n).sheaf) :
    transportSections j' L n hV (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b) =
      restrictSections j j' θ hchart L n (transportSections j L n hU b) := by
  subst U V
  simp [transportSections, restrictSections, freeOpenMap]
  change (𝟙 _ ≫ (freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ b)) =
    freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ (𝟙 _ ≫ b)
  exact (Category.id_comp _).trans
    (congrArg (fun c => freeOpenMap Y.ringCatSheaf (homOfLE hVU) ≫ c)
      (Category.id_comp b).symm)

end
end PiExponent.ExceptionalRepresentedTypes

end OAI
end Source0804

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductRestriction.lean
section Source0805
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesProductRestriction
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

omit [Fintype J] in
theorem productGenerator_factor {s t : Finset J} (hst : s ⊆ t) :
    productGenerator I a t = productGenerator I a s * productGenerator I a (t \ s) := by
  simp only [productGenerator_eq_prod]
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

omit [Fintype J] in
theorem coefficientProduct_factor {s t : Finset J} (hst : s ⊆ t) :
    coefficientProduct I a t = coefficientProduct I a s * coefficientProduct I a (t \ s) := by
  exact (Finset.prod_sdiff hst).symm.trans (mul_comm _ _)

def chartRestriction {s t : Finset J} (hst : s ⊆ t) : Chart I a s →+* Chart I a t :=
  HomogeneousLocalization.awayMap (piece I) (productGenerator_mem I a (t \ s))
    (productGenerator_factor I a hst)

theorem chartRestriction_base {s t : Finset J} (hst : s ⊆ t) (r : R) :
    chartRestriction I a hst (ReesProductChart.chartBase I a s r) =
      ReesProductChart.chartBase I a t r :=
  HomogeneousLocalization.awayMap_fromZeroRingHom _ _ _ _

omit [Fintype J] [DecidableEq J] in
theorem chartMap_mk_homogeneous (s : Finset J) {d : ℕ}
    (hgen : productGenerator I a s ∈ piece I d) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • d)) :
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I) hgen k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [ReesProductChart.chartMap, RingHom.comp_apply,
    HomogeneousLocalization.algebraMap_apply, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

omit [Fintype J] in
theorem coefficientRestriction_fraction {s t : Finset J} (hst : s ⊆ t) (r : R) (k : ℕ) :
    coefficientRestriction I a hst
      (IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) r
        (powerDenominator (coefficientProduct I a s) k)) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a t))
        (r * coefficientProduct I a (t \ s) ^ k)
        (powerDenominator (coefficientProduct I a t) k) := by
  have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
      (coefficientProduct I a s)) :=
    IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t)
      ⟨coefficientProduct I a (t \ s), coefficientProduct_factor I a hst⟩
  apply (hu.pow k).mul_right_injective
  calc
    _ = algebraMap R (Localization.Away (coefficientProduct I a t)) r := by
      have h := congrArg (coefficientRestriction I a hst)
        (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s)) r
          (powerDenominator (coefficientProduct I a s) k))
      simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow] using h
    _ = _ := by
      rw [← map_pow]
      dsimp only
      rw [IsLocalization.mul_mk'_eq_mk'_of_mul]
      symm
      apply IsLocalization.mk'_eq_iff_eq_mul.mpr
      rw [← map_mul]
      congr 1
      change coefficientProduct I a s ^ k * (r * coefficientProduct I a (t \ s) ^ k) =
        r * coefficientProduct I a t ^ k
      rw [coefficientProduct_factor I a hst, mul_pow]
      ring

theorem chartMap_restriction {s t : Finset J} (hst : s ⊆ t) (q : Chart I a s) :
    ReesProductChart.chartMap I a t (chartRestriction I a hst q) =
      coefficientRestriction I a hst (ReesProductChart.chartMap I a s q) := by
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) q
  rw [chartRestriction, HomogeneousLocalization.awayMap_mk, chartMap_mk_homogeneous,
    ReesProductChart.chartMap_mk, coefficientRestriction_fraction,
    map_mul, (evaluation I).map_pow, evaluation_productGenerator]

theorem chartRestriction_power_mem {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    chartRestriction I a hst q.val ∈ (I ^ n).map (ReesProductChart.chartBase I a t) := by
  have hmap : ((I ^ n).map (ReesProductChart.chartBase I a s)).map (chartRestriction I a hst) =
      (I ^ n).map (ReesProductChart.chartBase I a t) := by
    rw [Ideal.map_map]
    congr 1
    apply RingHom.ext
    intro r
    exact chartRestriction_base I a hst r
  rw [← hmap]
  exact Ideal.mem_map_of_mem _ q.property

def chartPowerRestriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ) :
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) →+
      ↥((I ^ n).map (ReesProductChart.chartBase I a t)) where
  toFun q := ⟨chartRestriction I a hst q.val, chartRestriction_power_mem I a hst n q⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

theorem chartPowerMap_restriction {s t : Finset J} {j k : J}
    (hj : j ∈ s) (hk : k ∈ t) (hst : s ⊆ t) (n : ℕ) (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartPowerMap I a hk n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      chartPowerRestriction I a hst n (chartPowerMap I a hj n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  apply ReesProductChart.chartMap_injective I a t
  change ReesProductChart.chartMap I a t _ =
    ReesProductChart.chartMap I a t (chartRestriction I a hst (chartPowerMap I a hj n z).val)
  rw [chartPowerMap_evaluation I a hk, chartMap_restriction, chartPowerMap_evaluation I a hj,
    pieceEvaluation_restriction]

end
end PiExponent.ReesProductRestriction

end OAI
end Source0805

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductSchemeRestriction.lean
section Source0806
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductSchemeRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesProductSchemeRestriction
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart PiExponent.ReesProductRestriction
open PiExponent.ReesProductPowerSections
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem chartRestriction_chartMorphism {s t : Finset J} (hs : s.Nonempty)
    (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (chartRestriction I a hst)) ≫ chartMorphism I a hs =
      chartMorphism I a ht := by
  have h := Proj.SpecMap_awayMap_awayι (piece I)
    (productGenerator_mem I a s) (Finset.card_pos.mpr hs)
    (productGenerator_mem I a (t \ s)) (productGenerator_factor I a hst)
  rw [chartMorphism_eq, chartMorphism_eq]
  unfold chartRestriction
  simpa only [Proj.awayι, Proj.basicOpenIsoSpec, affineBlowup] using h

end
end PiExponent.ReesProductSchemeRestriction

end OAI
end Source0806

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFixedRestriction.lean
section Source0807
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def restriction {s t : Finset J} (hst : s ⊆ t) : coordinateRing I a s →+* coordinateRing I a t :=
  (coordinateEquiv I a t).symm.toRingHom.comp
    ((ReesProductRestriction.chartRestriction I a hst).comp (coordinateEquiv I a s).toRingHom)

theorem restriction_chart {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty) (hst : s ⊆ t) :
    Spec.map (CommRingCat.ofHom (restriction I a hst)) ≫ chart I a hs = chart I a ht := by
  have he : (restriction I a hst).comp (coordinateEquiv I a s).symm.toRingHom =
      (coordinateEquiv I a t).symm.toRingHom.comp (ReesProductRestriction.chartRestriction I a hst) := by
    apply RingHom.ext
    intro z
    simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  have heCat :
      (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
        CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) ≫
        CommRingCat.ofHom (restriction I a hst) =
      (CommRingCat.ofHom (ReesProductRestriction.chartRestriction I a hst) :
        CommRingCat.of (Chart I a s) ⟶ CommRingCat.of (Chart I a t)) ≫
        CommRingCat.ofHom (coordinateEquiv I a t).symm.toRingHom :=
    congrArg (fun f : Chart I a s →+* coordinateRing I a t => CommRingCat.ofHom f) he
  rw [chart, ← Category.assoc, ← Spec.map_comp]
  erw [heCat]
  rw [Spec.map_comp, Category.assoc,
    ReesProductSchemeRestriction.chartRestriction_chartMorphism I a hs ht hst]
  rfl

end
end PiExponent.ReesFrozenChart

end OAI
end Source0807

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFixedPowerRestriction.lean
section Source0808
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedPowerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesFrozenPower
noncomputable section
open PiExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

theorem pieceEquiv_restriction {s t : Finset J} {p r : J} (hp : p ∈ s) (hr : r ∈ t)
    (hst : s ⊆ t) (n : ℕ) (z : ReesLocalizedIntersections.Piece I a s n) :
    letI := ReesPolynomialPresentation.presentationAlgebra I a
    letI := ReesGradedModule.gradedScalarAction I a
    (pieceEquiv I a hr n (GradedCech.setRestriction
      (GradedPolynomialLaurent.grading (J := J) (R := R)) (ReesGradedModule.integerPiece I)
      MvPolynomial.X GradedPolynomialLaurent.variable_mem hst n z)).val =
      restriction I a hst (pieceEquiv I a hp n z).val := by
  let := ReesPolynomialPresentation.presentationAlgebra I a
  let := ReesGradedModule.gradedScalarAction I a
  apply (coordinateEquiv I a t).injective
  rw [coordinate_pieceEquiv, ReesProductRestriction.chartPowerMap_restriction I a hp hr hst n]
  change ReesProductRestriction.chartRestriction I a hst
    (ReesProductPower.chartPowerMap I a hp n z).val = _
  simp only [restriction, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [coordinate_pieceEquiv]

end
end PiExponent.ReesFrozenPower

end OAI
end Source0808

-- Source: OAI/NumberTheory/PiExponent/Approximation/AddEquivSignedSum.lean
section Source0809
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/AddEquivSignedSum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.AddEquivSignedSum
open scoped BigOperators

theorem map_signed_sum {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • E (f k) := by
  simp only [map_sum, map_zsmul]

theorem map_signed_sum_eq {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (E : A ≃+ B) (q : ℕ) (f : Fin (q+2) → A) (g : Fin (q+2) → B)
    (h : ∀ k, E (f k) = g k) :
    E (∑ k, (-1 : ℤ)^k.val • f k) = ∑ k, (-1 : ℤ)^k.val • g k := by
  rw [map_signed_sum]
  exact Finset.sum_congr rfl (fun k _ => congrArg (fun z => (-1 : ℤ)^k.val • z) (h k))

end PiExponent.AddEquivSignedSum

end OAI
end Source0809

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechNaturality.lean
section Source0810
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesSheafCechNaturality
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
open PiExponent.ReesSheafCechBase PiExponent.ReesFrozenChart
open PiExponent.ReesFrozenPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections
  PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ExceptionalRepresentedTypes.restrictSections
  PiExponent.ExceptionalRepresentedTypes.transportSections
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (coordinateRing I a s)) ⟶ affineBlowup I :=
  chart I a hs

local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

theorem chartHomEquiv_restrict {s t : Finset J} (hs : s.Nonempty) (ht : t.Nonempty)
    {p r : J} (hp : p ∈ s) (hr : r ∈ t) (hst : s ⊆ t) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs) (exceptionalLineBundle I) n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    chartHomEquiv I a ht hr n
      (ExceptionalRepresentedTypes.restrictSections (chartMap I a hs) (chartMap I a ht)
        (restriction I a hst) (restriction_chart I a hs ht hst)
        (exceptionalLineBundle I) n b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem hst n (chartHomEquiv I a hs hp n b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (pieceEquiv I a hr n).injective
  apply Subtype.ext
  rw [chartHomEquiv_pieceEquiv, pieceEquiv_restriction I a hp hr hst n,
    chartHomEquiv_pieceEquiv]
  exact ExceptionalRepresentedTypes.representedSectionsTyped_restrict
    (chartMap I a hs) (chartMap I a ht) (restriction I a hst)
    (restriction_chart I a hs ht hst) I (projection I)
    (base I a s) (chart_projection I a hs) (exceptionalLineBundle I)
    (exceptionalInclusion I) (exceptional_presents I) (chartFrameTyped I a hs hp)
    (base I a t) (chart_projection I a ht) (chartFrameTyped I a ht hr) n b

theorem tupleHomEquiv_restrict (n q : ℕ) (t : Fin (q + 2) → J) (k : Fin (q + 2))
    (b : schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) (t ∘ k.succAbove)) ⟶ exceptionalPower I n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    tupleHomEquiv I a n (q+1) t
      (CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) b) =
      GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
        (tupleHomEquiv I a n q (t ∘ k.succAbove) b) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change chartHomEquiv I a _ _ n
    (ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty (q+1) t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a (q+1) t)
      (freeOpenMap _ (homOfLE (CechHigher.faceLE (opens I a) t k)) ≫ b)) = _
  rw [ExceptionalRepresentedTypes.transportSections_restrict
    (chartMap I a (tuple_nonempty q (t ∘ k.succAbove)))
    (chartMap I a (tuple_nonempty (q+1) t))
    (restriction I a (tupleSet_comp_subset t k.succAbove))
    (restriction_chart I a (tuple_nonempty q (t ∘ k.succAbove))
      (tuple_nonempty (q+1) t) (tupleSet_comp_subset t k.succAbove))
    (exceptionalLineBundle I) n
    (tupleOpen_eq I a q (t ∘ k.succAbove)) (tupleOpen_eq I a (q+1) t)
    (CechHigher.faceLE (opens I a) t k) b]
  exact chartHomEquiv_restrict I a (tuple_nonempty q (t ∘ k.succAbove))
    (tuple_nonempty (q+1) t) (tuple_mem q (t ∘ k.succAbove) 0)
    (tuple_mem (q+1) t 0) (tupleSet_comp_subset t k.succAbove) n _

theorem cochainEquiv_differential (n q : ℕ)
    (c : CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    cochainEquiv I a n (q+1) (CechHigher.differential _ (opens I a) (exceptionalPower I n) c) =
      GradedCech.differential (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (cochainEquiv I a n q c) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  funext t
  let : AddCommGroup (ReesLocalizedIntersections.Piece I a (tupleSet t) n) :=
    AddSubgroup.toAddCommGroup _
  let : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  change tupleHomEquiv I a n (q+1) t
    (∑ k : Fin (q+2), (-1 : ℤ)^k.val •
      CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k) (c (t ∘ k.succAbove))) = _
  exact AddEquivSignedSum.map_signed_sum_eq
    (A := (schemeFreeOpen (affineBlowup I)
      (CechHigher.intersection (opens I a) t) ⟶ exceptionalPower I n))
    (B := ReesLocalizedIntersections.Piece I a (tupleSet t) n)
    (tupleHomEquiv I a n (q+1) t) q
    (fun k => CechOne.restrictHom _ (CechHigher.faceLE (opens I a) t k)
      (c (t ∘ k.succAbove)))
    (fun k => GradedCech.setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) n
      (tupleHomEquiv I a n q (t ∘ k.succAbove) (c (t ∘ k.succAbove))))
    (fun k => tupleHomEquiv_restrict I a n q t k (c (t ∘ k.succAbove)))

end
end PiExponent.ReesSheafCechNaturality

end OAI
end Source0810

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechRecovery.lean
section Source0811
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase PiExponent.ReesSheafCechNaturality
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance 1001] AddCommGroup.toAddCommMonoid
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def gradedCycles (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    AddSubgroup (GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n q).ker

instance gradedCyclesGroup (n q : ℕ) : AddCommGroup (gradedCycles I a n q) :=
  AddSubgroup.toAddCommGroup _

@[instance_reducible] def groupAddZero {A : Type*} (G : AddCommGroup A) : AddZero A := by
  letI := G
  infer_instance

@[instance_reducible] def groupAddZeroClass {A : Type*} (G : AddCommGroup A) : AddZeroClass A := by
  letI := G
  infer_instance

instance (priority := 2000) gradedCyclesAddZero (n q : ℕ) : AddZero (gradedCycles I a n q) :=
  groupAddZero (gradedCyclesGroup I a n q)

instance (priority := 2000) gradedCyclesAddZeroClass (n q : ℕ) :
    AddZeroClass (gradedCycles I a n q) :=
  groupAddZeroClass (gradedCyclesGroup I a n q)

def cyclesEquiv (n q : ℕ) :
    CechZeroAdditive.cycles (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      gradedCycles I a n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact AdditiveKernelTransport.kernelEquiv
    (cochainEquiv I a n q) (cochainEquiv I a n (q+1))
    (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
      (opens I a) (exceptionalPower I n) q)
    (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem n q)
    (fun c => cochainEquiv_differential I a n q c)

def ordinaryAugmentation (n : ℕ) : ↥(I^n : Ideal R) →+ gradedCycles I a n 0 := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ((GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n).comp (ordinaryPowerEquivIntegerPiece I n).toAddMonoidHom).codRestrict
    (gradedCycles I a n 0) (fun b =>
      GradedCech.differential_augmentation _ _ _ _ _ _)

def globalCyclesEquiv (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) ≃+
      gradedCycles I a n 0 := by
  letI : AddCommGroup (freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact (CechZeroAdditive.sectionsEquiv (affineBlowup I).ringCatSheaf (opens I a)
    (exceptionalPower I n) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])).trans
      (cyclesEquiv I a n 0)

def ordinarySectionHom (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ (schemeFreeOpen (affineBlowup I) ⊤ ⟶ exceptionalPower I n) :=
  (globalCyclesEquiv I a ha n).symm.toAddMonoidHom.comp (ordinaryAugmentation I a n)

def ordinaryGlobalSection (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ) :
    ↥(I^n : Ideal R) →+ Γ(exceptionalPower I n, ⊤) :=
  (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).toAddMonoidHom.comp
    (ordinarySectionHom I a ha n)

theorem ordinarySectionHom_restriction
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    tupleHomEquiv I a n 0 t
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) (ordinarySectionHom I a ha n b) t) =
      ReesProductAugmentation.ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have h := (globalCyclesEquiv I a ha n).apply_symm_apply (ordinaryAugmentation I a n b)
  have hv := congrFun (congrArg Subtype.val h) t
  change _ = GradedCech.augmentation (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem n (ordinaryPowerEquivIntegerPiece I n b) t at hv
  exact hv.trans (ReesProductAugmentation.augmentation_eq_ordinaryFraction I a n b t)

theorem ordinarySectionHom_chartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesProductPower.chartPowerMap I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesProductChart.chartBase I a (tupleSet t) b.val := by
  rw [ordinarySectionHom_restriction]
  exact ReesProductAugmentation.chartPowerMap_ordinaryFraction I a (tuple_mem 0 t 0) n b

theorem ordinarySectionHom_frozenChartValue
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) (t : Fin 1 → J) :
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (ordinarySectionHom I a ha n b) t))).val =
      ReesFrozenChart.base I a (tupleSet t) b.val := by
  apply (ReesFrozenChart.coordinateEquiv I a (tupleSet t)).injective
  rw [ReesFrozenPower.coordinate_pieceEquiv, ordinarySectionHom_chartValue]
  exact ((ReesFrozenChart.coordinateEquiv I a (tupleSet t)).apply_symm_apply _).symm

variable [IsNoetherianRing R]

theorem eventually_recovery_and_primitives
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ q : ℕ, CechHigher.HasPrimitives (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨N, hN⟩ := ReesCechRecovery.eventually_ordinary_power_recovery I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hpositive, hrecovery⟩ := hN n hn
  have hb : Function.Bijective (ordinaryAugmentation I a n) := by
    apply (Function.bijective_iff_existsUnique _).mpr
    intro c
    obtain ⟨b, hb, hu⟩ := hrecovery c.val c.property
    refine ⟨b, Subtype.ext hb, ?_⟩
    intro z hz
    exact hu z (congrArg Subtype.val hz)
  constructor
  · exact (freeOpenSectionsEquiv ⊤ (exceptionalPower I n)).bijective.comp
      ((globalCyclesEquiv I a ha n).symm.bijective.comp hb)
  · intro q
    exact AdditiveKernelTransport.transport_primitives
      (cochainEquiv I a n q) (cochainEquiv I a n (q+1)) (cochainEquiv I a n (q+2))
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) q)
      (CechZeroAdditive.differentialHom (affineBlowup I).ringCatSheaf
        (opens I a) (exceptionalPower I n) (q+1))
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q)
      (GradedCech.differentialHom (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n (q+1))
      (fun c => cochainEquiv_differential I a n q c)
      (fun c => cochainEquiv_differential I a n (q+1) c) (hpositive q)

theorem eventually_recovery_and_cohomology
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Function.Bijective (ordinaryGlobalSection I a ha n) ∧
      ∀ (q : ℕ) (x : CategoryTheory.Abelian.Ext.{1} (C := (affineBlowup I).Modules)
        (schemeFreeOpen (affineBlowup I) ⊤) (exceptionalPower I n) (q+1)), x = 0 := by
  obtain ⟨N, hN⟩ := eventually_recovery_and_primitives I a ha
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hb, hp⟩ := hN n hn
  refine ⟨hb, ?_⟩
  intro q x
  let : (exceptionalPower I n).IsQuasicoherent :=
    ReesCohomologySetup.exceptionalPower_isQuasicoherent I n
  exact FreeCechSections.affine_ext_succ_eq_zero (affineBlowup I) (exceptionalPower I n)
    (opens I a) ⊤ (fun _ => le_top) (by rw [iSup_opens I a ha])
    (tuple_isAffine I a) q (hp q) x

end
end PiExponent.ReesSheafCechRecovery

end OAI
end Source0811

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesSheafCanonicalValue.lean
section Source0812
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesSheafCanonicalValue.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesSheafCechRecovery
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance chartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

theorem ordinaryGlobalSection_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (b : ↥(I^n : Ideal R)) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (ordinaryGlobalSection I a ha n b) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv b.val) :=
  ReesSectionInclusion.section_inclusion I a ha n
    (ordinarySectionHom I a ha n b) b.val
    (fun t => ordinarySectionHom_frozenChartValue I a ha n b t)

end
end PiExponent.ReesSheafCechRecovery

end OAI
end Source0812

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealSectionRestriction.lean
section Source0813
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealSectionRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}}

def sectionsEquiv (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) :
    Γ(closedModule I, f ''ᵁ U) ≃+ Γ(closedModule (I.comap f), U) :=
  ((closedModule I).restrictAppIso f U).symm.addCommGroupIsoToAddEquiv.trans
    (asIso ((closedModuleRestrictIso I f).hom.app U)).addCommGroupIsoToAddEquiv

theorem sectionsEquiv_inclusion (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ(closedModule I, f ''ᵁ U)) :
    (closedInclusion (I.comap f)).app U (sectionsEquiv I f U s) =
      (f.appIso U).hom ((closedInclusion I).app (f ''ᵁ U) s) := by
  have h := congrArg (fun g => g.app U s) (restrictedToClosed_inclusion I f)
  exact h

theorem inclusion_injective (I : Y.IdealSheafData) (U : Y.Opens) :
    Function.Injective ((closedInclusion I).app U) := by
  let : Mono (closedInclusion I).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules Y).map (closedInclusion I)))
  exact PresheafOfModules.injective_of_mono (closedInclusion I).val (op U)

def pullback (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    Γ(closedModule I,U) →+ Γ(closedModule (I.comap f),V) :=
  ((closedModule (I.comap f)).presheaf.map (homOfLE h).op).hom.comp
    ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom

theorem pullback_inclusion (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) (V : X.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (s : Γ(closedModule I,U)) :
    (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
      f.appLE U V h ((closedInclusion I).app U s) := by
  have hn := PresheafOfModules.naturality_apply (closedInclusion (I.comap f)).val
    (homOfLE h).op ((GeometrySupport.IdealPullbackMap.comap f I).app U s)
  change (closedInclusion (I.comap f)).app V (pullback f I U V h s) =
    X.presheaf.map (homOfLE h).op
      ((closedInclusion (I.comap f)).app (f ⁻¹ᵁ U)
        ((GeometrySupport.IdealPullbackMap.comap f I).app U s)) at hn
  have he := congrArg (fun g => g.app U s)
    (GeometrySupport.IdealPullbackMap.comap_inclusion f I)
  exact hn.trans (congrArg (X.presheaf.map (homOfLE h).op) he)

def idealCongr {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens) :
    Γ(closedModule I,U) ≃+ Γ(closedModule J,U) := by
  subst J
  exact AddEquiv.refl _

theorem idealCongr_inclusion {I J : Y.IdealSheafData} (h : I = J) (U : Y.Opens)
    (s : Γ(closedModule I,U)) :
    (closedInclusion J).app U (idealCongr h U s) = (closedInclusion I).app U s := by
  subst J
  rfl

theorem pullback_self (f : X ⟶ Y) [QuasiCompact f] (I : Y.IdealSheafData)
    (U : Y.Opens) :
    pullback f I U (f ⁻¹ᵁ U) le_rfl =
      ((GeometrySupport.IdealPullbackMap.comap f I).app U).hom := by
  ext s
  exact congrArg (fun a => a ((GeometrySupport.IdealPullbackMap.comap f I).app U s))
    ((closedModule (I.comap f)).presheaf.map_id (op (f ⁻¹ᵁ U)))

theorem pullback_bijective_iff_comap (f : X ⟶ Y) [QuasiCompact f]
    (I : Y.IdealSheafData) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) (he : V = f ⁻¹ᵁ U) :
    Function.Bijective (pullback f I U V h) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) := by
  subst V
  rw [pullback_self]
  rfl

end PiExponent.IdealSectionRestriction

end

end OAI
end Source0813

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPullbackOpenSquare.lean
section Source0814
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPullbackOpenSquare.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.IdealSectionRestriction
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.IdealModule

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

private theorem appLE_congr {X Y : Scheme.{0}} {f g : X ⟶ Y} (h : f = g)
    (U : Y.Opens) (V : X.Opens) (hf : V ≤ f ⁻¹ᵁ U) (hg : V ≤ g ⁻¹ᵁ U) :
    f.appLE U V hf = g.appLE U V hg := by
  subst g
  rfl

theorem squareIdeal {X Y X' Y' : Scheme.{0}} (f : Y ⟶ X)
    (j : X' ⟶ X) (k : Y' ⟶ Y) (f' : Y' ⟶ X') (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) :
    (I.comap f).comap k = (I.comap j).comap f' := by
  rw [← I.comap_comp k f, ← I.comap_comp f' j, h]

theorem pullback_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U)
    (s : Γ(closedModule I, j ''ᵁ U)) :
    idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V
        (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)) =
      pullback f' (I.comap j) U V hV' (sectionsEquiv I j U s) := by
  apply inclusion_injective ((I.comap j).comap f') V
  rw [idealCongr_inclusion]
  have h₁ := sectionsEquiv_inclusion (I.comap f) k V
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV s)
  have h₂ := pullback_inclusion f I (j ''ᵁ U) (k ''ᵁ V) hV s
  have h₃ := pullback_inclusion f' (I.comap j) U V hV' (sectionsEquiv I j U s)
  have h₄ := sectionsEquiv_inclusion I j U s
  rw [Scheme.Hom.appIso_hom'] at h₁ h₄
  have hh : f.appLE (j ''ᵁ U) (k ''ᵁ V) hV ≫
      k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge =
      j.appLE (j ''ᵁ U) U (j.preimage_image_eq U).ge ≫ f'.appLE U V hV' := by
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    exact appLE_congr h _ _ _ _
  exact (h₁.trans (congrArg (k.appLE (k ''ᵁ V) V (k.preimage_image_eq V).ge) h₂)).trans
    ((congrArg (fun a => a ((closedInclusion I).app (j ''ᵁ U) s)) hh).trans
      ((congrArg (f'.appLE U V hV') h₄).symm.trans h₃.symm))

theorem pullback_open_square_bijective_iff {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X'.Opens) (V : Y'.Opens)
    (hV : k ''ᵁ V ≤ f ⁻¹ᵁ (j ''ᵁ U)) (hV' : V ≤ f' ⁻¹ᵁ U) :
    Function.Bijective (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV) ↔
      Function.Bijective (pullback f' (I.comap j) U V hV') := by
  exact bijective_iff_of_square
    (pullback f I (j ''ᵁ U) (k ''ᵁ V) hV)
    (pullback f' (I.comap j) U V hV')
    (sectionsEquiv I j U)
    (fun z => idealCongr (squareIdeal f j k f' h I) V
      (sectionsEquiv (I.comap f) k V z))
    (sectionsEquiv I j U).bijective
    ((idealCongr (squareIdeal f j k f' h I) V).bijective.comp
      (sectionsEquiv (I.comap f) k V).bijective)
    (pullback_open_square f j k f' h I U V hV hV')

theorem comap_app_bijective_iff_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f I).app U) ↔
      Function.Bijective ((GeometrySupport.IdealPullbackMap.comap f' (I.comap j)).app U') := by
  subst U
  exact (pullback_bijective_iff_comap f I (j ''ᵁ U') (k ''ᵁ V') hk.le hk).symm.trans
    ((pullback_open_square_bijective_iff f j k f' h I U' V' hk.le hv.le).trans
      (pullback_bijective_iff_comap f' (I.comap j) U' V' hv.le hv))

end PiExponent.IdealSectionRestriction

end

end OAI
end Source0814

-- Source: OAI/NumberTheory/PiExponent/Geometry/CanonicalRecoveryProperties.lean
section Source0815
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CanonicalRecoveryProperties.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CanonicalRecoveryProperties
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open GeometrySupport

def ComapBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (U : X.Opens) : Prop :=
  Function.Bijective ((IdealPullbackMap.comap f I).app U)

def OrdinaryBijective {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) : Prop :=
  Function.Bijective ((ExceptionalRecoveryMap.ordinaryMap f I E ι hE n).app U)

theorem ordinary_iff_comap {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)
    (n : ℕ) (U : X.Opens) :
    OrdinaryBijective f I E ι hE n U ↔ ComapBijective f (I^n) U := by
  have hb := ConcreteCategory.bijective_of_isIso
    ((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U))
  change Function.Bijective
    (((PresentedIdealIso.powerIso I f E ι hE n).inv.app (f ⁻¹ᵁ U)) ∘
      ((IdealPullbackMap.comap f (I^n)).app U)) ↔ _
  exact hb.of_comp_iff' _

theorem comap_open_square {X Y X' Y' : Scheme.{0}}
    (f : Y ⟶ X) [QuasiCompact f]
    (j : X' ⟶ X) [IsOpenImmersion j]
    (k : Y' ⟶ Y) [IsOpenImmersion k]
    (f' : Y' ⟶ X') [QuasiCompact f'] (h : k ≫ f = f' ≫ j)
    (I : X.IdealSheafData) (U : X.Opens) (U' : X'.Opens) (V' : Y'.Opens)
    (hj : j ''ᵁ U' = U) (hk : k ''ᵁ V' = f ⁻¹ᵁ U)
    (hv : V' = f' ⁻¹ᵁ U') :
    ComapBijective f I U ↔ ComapBijective f' (I.comap j) U' :=
  IdealSectionRestriction.comap_app_bijective_iff_open_square f j k f' h I U U' V' hj hk hv

end PiExponent.CanonicalRecoveryProperties

end

end OAI
end Source0815

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffineIdealSections.lean
section Source0816
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineIdealSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.AffineIdealSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.IdealPullback
variable {R : Type} [CommRing R] (A : Ideal R)

def value (s : Γ(closedModule (specIdeal A), ⊤)) : R :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((closedInclusion (specIdeal A)).app ⊤ s)

theorem value_mem (s : Γ(closedModule (specIdeal A), ⊤)) : value A s ∈ A := by
  have hs : (closedInclusion (specIdeal A)).app ⊤ s ∈
      A.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    rw [← specIdeal_top A, ← closed_image (specIdeal A) ⟨⊤, isAffineOpen_top _⟩]
    exact ⟨s,rfl⟩
  obtain ⟨a,ha,he⟩ := (Ideal.mem_map_iff_of_surjective _
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).surjective).mp hs
  unfold value
  rw [← he, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  exact ha

def toIdeal : Γ(closedModule (specIdeal A), ⊤) →+ A where
  toFun s := ⟨value A s, value_mem A s⟩
  map_zero' := by
    apply Subtype.ext
    change value A 0 = 0
    simp [value]
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.map_zero
  map_add' s t := by
    apply Subtype.ext
    change value A (s+t) = value A s + value A t
    simp [value]
    exact (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.map_add _ _

theorem toIdeal_injective : Function.Injective (toIdeal A) := by
  intro s t h
  have hh : value A s = value A t := congrArg Subtype.val h
  have hv := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective hh
  let : Mono (closedInclusion (specIdeal A)) :=
    inferInstanceAs (Mono (inclusion (specIdeal A).subschemeι))
  let : Mono (closedInclusion (specIdeal A)).val := inferInstanceAs
    (Mono ((Scheme.Modules.toPresheafOfModules (Spec (CommRingCat.of R))).map
      (closedInclusion (specIdeal A))))
  exact PresheafOfModules.injective_of_mono
    (closedInclusion (specIdeal A)).val (op ⊤) hv

theorem toIdeal_surjective : Function.Surjective (toIdeal A) := by
  intro a
  have ha : (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val ∈
      (specIdeal A).ideal ⟨⊤,isAffineOpen_top _⟩ := by
    rw [specIdeal_top]
    exact Ideal.mem_map_of_mem _ a.property
  rw [← closed_image] at ha
  obtain ⟨s,hs⟩ := ha
  change (closedInclusion (specIdeal A)).app ⊤ s =
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val at hs
  refine ⟨s,?_⟩
  apply Subtype.ext
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom
    ((closedInclusion (specIdeal A)).app ⊤ s) = a.val
  rw [hs, ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

def equiv : Γ(closedModule (specIdeal A), ⊤) ≃+ A :=
  AddEquiv.ofBijective (toIdeal A) ⟨toIdeal_injective A, toIdeal_surjective A⟩

@[simp] theorem equiv_inclusion (s : Γ(closedModule (specIdeal A), ⊤)) :
    (equiv A s).val = (Scheme.ΓSpecIso (CommRingCat.of R)).hom
      ((closedInclusion (specIdeal A)).app ⊤ s) := rfl

@[simp] theorem equiv_symm_inclusion (a : A) :
    (closedInclusion (specIdeal A)).app ⊤ ((equiv A).symm a) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val := by
  apply (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom).injective
  rw [← equiv_inclusion, AddEquiv.apply_symm_apply,
    ← CommRingCat.comp_apply, Iso.inv_hom_id]
  rfl

end
end PiExponent.GeometrySupport.AffineIdealSections

end OAI
end Source0816

-- Source: OAI/NumberTheory/PiExponent/Approximation/CanonicalAffineRecovery.lean
section Source0817
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CanonicalAffineRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CanonicalAffineRecovery
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.IdealPullback
open GeometrySupport

private theorem bijective_iff_of_square {A B C D : Type*}
    (p : A → B) (q : C → D) (a : A → C) (b : B → D)
    (ha : Function.Bijective a) (hb : Function.Bijective b)
    (h : ∀ x, b (p x) = q (a x)) : Function.Bijective p ↔ Function.Bijective q := by
  have he : b ∘ p = q ∘ a := funext h
  rw [← hb.of_comp_iff' p, he]
  exact Function.Bijective.of_comp_iff q ha

theorem bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι)
    (r : I → Γ(L.sheaf,⊤))
    (hr : ∀ a : I, ι.app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔
      Function.Bijective ((IdealPullbackMap.comap f (specIdeal I)).app ⊤) := by
  let t := PresentedIdealIso.toIdealModule (specIdeal I) f L ι hL
  have ht : Function.Bijective (t.app ⊤) := ConcreteCategory.bijective_of_isIso _
  have hdiag (a : I) :
      t.app ⊤ (r a) =
        IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp)
          ((AffineIdealSections.equiv I).symm a) := by
    apply IdealSectionRestriction.inclusion_injective ((specIdeal I).comap f) ⊤
    have h₁ := congrArg (fun g => g.app ⊤ (r a))
      (PresentedIdealIso.toIdealModule_inclusion (specIdeal I) f L ι hL)
    have h₂ := IdealSectionRestriction.pullback_inclusion f (specIdeal I) ⊤ ⊤
      (by simp) ((AffineIdealSections.equiv I).symm a)
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop := f.appLE_eq_app
    rw [htop] at h₂
    have h₃ := AffineIdealSections.equiv_symm_inclusion I a
    exact (h₁.trans (hr a)).trans
      ((congrArg f.appTop h₃).symm.trans h₂.symm)
  exact (bijective_iff_of_square r
    (IdealSectionRestriction.pullback f (specIdeal I) ⊤ ⊤ (by simp))
    (AffineIdealSections.equiv I).symm (t.app ⊤)
    (AffineIdealSections.equiv I).symm.bijective ht hdiag).trans
      (IdealSectionRestriction.pullback_bijective_iff_comap f (specIdeal I) ⊤ ⊤
        (by simp) (by simp))

theorem power_bijective_iff_comap {R : Type} [CommRing R] {Y : Scheme.{0}}
    (I : Ideal R) (f : Y ⟶ Spec (CommRingCat.of R)) [QuasiCompact f]
    (L : LineBundle Y) (ι : L.sheaf ⟶ structureSheaf Y)
    (hL : PresentsPullbackIdeal (specIdeal I) f L ι) (n : ℕ)
    (r : ↥(I^n : Ideal R) → Γ((L.pow n).sheaf,⊤))
    (hr : ∀ a : ↥(I^n : Ideal R), (idealPowerInclusion L ι n).app ⊤ (r a) =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv a.val)) :
    Function.Bijective r ↔ CanonicalRecoveryProperties.ComapBijective f (specIdeal (I^n)) ⊤ := by
  have hp : PresentsPullbackIdeal (specIdeal (I^n)) f (L.pow n) (idealPowerInclusion L ι n) := by
    rw [specIdeal_pow]
    exact PresentedIdealIso.idealPower_presents (specIdeal I) f L ι hL n
  exact bijective_iff_comap (I^n) f (L.pow n) (idealPowerInclusion L ι n) hp r hr

end PiExponent.CanonicalAffineRecovery

end

end OAI
end Source0817

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealFiniteGenerators.lean
section Source0818
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealFiniteGenerators.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.IdealFiniteGenerators

theorem exists_generators {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) : ∃ m : ℕ, ∃ a : Fin m → I,
      Ideal.span (Set.range fun j => (a j).val) = I := by
  obtain ⟨m,b,hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (IsNoetherian.noetherian I)
  let a : Fin m → I := fun j => ⟨b j, by
    rw [← hb]
    exact Submodule.subset_span ⟨j,rfl⟩⟩
  exact ⟨m,a,hb⟩

end PiExponent.IdealFiniteGenerators

end OAI
end Source0818

-- Source: OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean
section Source0819
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/AffineReesCanonicalRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AffineReesCanonicalRecovery
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.ReesGrading PiExponentSeshadri.IdealPullback
open CanonicalRecoveryProperties
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion
  ReesSheafCechRecovery.ordinaryGlobalSection

theorem eventually_comap_bijective {R : Type} [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ComapBijective (projection I) (specIdeal (I^n)) ⊤ := by
  classical
  obtain ⟨m,a,ha⟩ := IdealFiniteGenerators.exists_generators I
  obtain ⟨N,hN⟩ := ReesSheafCechRecovery.eventually_recovery_and_cohomology I a ha
  refine ⟨N, ?_⟩
  intro n hn
  exact (CanonicalAffineRecovery.power_bijective_iff_comap I (projection I)
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n
    (ReesSheafCechRecovery.ordinaryGlobalSection I a ha n)
    (ReesSheafCechRecovery.ordinaryGlobalSection_inclusion I a ha n)).mp (hN n hn).1

end PiExponent.AffineReesCanonicalRecovery

end

end OAI
end Source0819

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalExceptionalComparison.lean
section Source0820
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalExceptionalComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSeshadri.BlowupGluing
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

abbrev affineCenterIdeal :=
  (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top U.1.toScheme⟩

@[reassoc (attr := simp)] theorem affineRestrictionIso_hom_reesProjection :
    (affineRestrictionIso I U).hom ≫ ReesGrading.projection (affineCenterIdeal I U) =
      ((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom := by
  have h := congrArg (fun f => f ≫ U.1.toScheme.isoSpec.hom)
    (affineRestrictionIso_hom_projection I U)
  simpa only [AffineBlowup.projection, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using h

def restrictedExceptionalLineBundle :=
  (exceptionalLineBundle I).restrict ((projection I) ⁻¹ᵁ U.1).ι

def restrictedExceptionalInclusion :
    (restrictedExceptionalLineBundle I U).sheaf ⟶
      structureSheaf (((projection I) ⁻¹ᵁ U.1).toScheme) :=
  InvertibleLocal.restrictedInclusion (exceptionalLineBundle I)
    (exceptionalInclusion I) ((projection I) ⁻¹ᵁ U.1).ι

def affineExceptionalOnRestriction :=
  InvertibleLocal.restrictLineBundle
    (ReesGrading.exceptionalLineBundle (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom

def affineExceptionalInclusionOnRestriction :
    (affineExceptionalOnRestriction I U).sheaf ⟶
      structureSheaf (((projection I) ⁻¹ᵁ U.1).toScheme) :=
  InvertibleLocal.restrictedInclusion
    (ReesGrading.exceptionalLineBundle (affineCenterIdeal I U))
    (ReesGrading.exceptionalInclusion (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom

theorem restrictedExceptional_presents :
    PresentsPullbackIdeal (IdealPullback.specIdeal (affineCenterIdeal I U))
      (((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom)
      (restrictedExceptionalLineBundle I U) (restrictedExceptionalInclusion I U) :=
  presents_post_toSpec _ _
    (presents_morphismRestrict _ _ (exceptional_presents I) U)

theorem affineExceptionalOnRestriction_presents :
    PresentsPullbackIdeal (IdealPullback.specIdeal (affineCenterIdeal I U))
      (((projection I) ∣_ U.1) ≫ U.1.toScheme.isoSpec.hom)
      (affineExceptionalOnRestriction I U) (affineExceptionalInclusionOnRestriction I U) := by
  have h := InvertibleLocal.presents_restrict_general _ _ _ _
    (ReesGrading.exceptional_presents (affineCenterIdeal I U))
    (affineRestrictionIso I U).hom
  rw [affineRestrictionIso_hom_reesProjection] at h
  exact h

def exceptionalAffineIso :
    (restrictedExceptionalLineBundle I U).sheaf ≅
      (affineExceptionalOnRestriction I U).sheaf :=
  PiExponent.PresentedIdealIso.iso _ _ _ _ _ _
    (restrictedExceptional_presents I U) (affineExceptionalOnRestriction_presents I U)

@[reassoc (attr := simp)] theorem exceptionalAffineIso_hom_inclusion :
    (exceptionalAffineIso I U).hom ≫ affineExceptionalInclusionOnRestriction I U =
      restrictedExceptionalInclusion I U :=
  PiExponent.PresentedIdealIso.iso_hom_inclusion _ _ _ _ _ _ _ _

def exceptionalAffinePowerIso (n : ℕ) :
    ((restrictedExceptionalLineBundle I U).pow n).sheaf ≅
      ((affineExceptionalOnRestriction I U).pow n).sheaf :=
  (modulePowFunctor n).mapIso (exceptionalAffineIso I U)

@[reassoc (attr := simp)] theorem exceptionalAffinePowerIso_hom_inclusion (n : ℕ) :
    (exceptionalAffinePowerIso I U n).hom ≫
      modulePowMap (affineExceptionalInclusionOnRestriction I U) n =
        modulePowMap (restrictedExceptionalInclusion I U) n := by
  change modulePowMap (exceptionalAffineIso I U).hom n ≫
    modulePowMap (affineExceptionalInclusionOnRestriction I U) n = _
  rw [← modulePowMap_comp, exceptionalAffineIso_hom_inclusion]

def restrictedExceptionalPowerAffineIso (n : ℕ) :
    ((exceptionalLineBundle I).pow n).sheaf.restrict ((projection I) ⁻¹ᵁ U.1).ι ≅
      ((affineExceptionalOnRestriction I U).pow n).sheaf :=
  modulePowRestrict ((projection I) ⁻¹ᵁ U.1) (exceptionalLineBundle I).sheaf n ≪≫
    exceptionalAffinePowerIso I U n

end PiExponentSeshadri.BlowupGluing

end

end OAI
end Source0820

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupAffineSquare.lean
section Source0821
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalBlowupAffineSquare.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.BlowupGluing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}} (I : X.IdealSheafData) (U : X.affineOpens)

def baseChart : Spec (CommRingCat.of Γ(U.1.toScheme, ⊤)) ⟶ X :=
  U.1.toScheme.isoSpec.inv ≫ U.1.ι

def totalChart : ReesGrading.affineBlowup (affineCenterIdeal I U) ⟶ scheme I :=
  (affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι

instance baseChart_isOpenImmersion : IsOpenImmersion (baseChart (X := X) U) := by
  dsimp [baseChart]
  infer_instance

instance totalChart_isOpenImmersion : IsOpenImmersion (totalChart I U) := by
  dsimp [totalChart]
  infer_instance

@[reassoc (attr := simp)] theorem totalChart_projection :
    totalChart I U ≫ projection I =
      ReesGrading.projection (affineCenterIdeal I U) ≫ baseChart U := by
  have he : (affineRestrictionIso I U).inv ≫ ((projection I) ∣_ U.1) =
      ReesGrading.projection (affineCenterIdeal I U) ≫ U.1.toScheme.isoSpec.inv := by
    apply (cancel_mono U.1.toScheme.isoSpec.hom).mp
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← affineRestrictionIso_hom_reesProjection I U, Iso.inv_hom_id_assoc]
  rw [totalChart, Category.assoc, ← morphismRestrict_ι, ← Category.assoc, he,
    Category.assoc]
  rfl

@[simp] theorem baseChart_opensRange : (baseChart (X := X) U).opensRange = U.1 := by
  change (U.1.toScheme.isoSpec.inv ≫ U.1.ι).opensRange = U.1
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem totalChart_opensRange :
    (totalChart I U).opensRange = projection I ⁻¹ᵁ U.1 := by
  change ((affineRestrictionIso I U).inv ≫ ((projection I) ⁻¹ᵁ U.1).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

@[simp] theorem center_comap_baseChart :
    I.comap (baseChart U) = IdealPullback.specIdeal (affineCenterIdeal I U) := by
  rw [baseChart, Scheme.IdealSheafData.comap_comp, IdealPullback.comap_isoSpec_inv]

end
end PiExponentSeshadri.BlowupGluing

end OAI
end Source0821

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalReesRecoveryComparison.lean
section Source0822
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalReesRecoveryComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
open GeometrySupport CanonicalRecoveryProperties

attribute [local irreducible] PiExponentSeshadri.BlowupGluing.affineRestrictionIso
  PiExponentSeshadri.ReesGrading.affineBlowup PiExponentSeshadri.ReesGrading.projection
  IdealPullbackMap.map IdealPullbackMap.comap

local instance affineChartNoetherian {X : Scheme.{0}} [IsLocallyNoetherian X]
    (U : X.affineOpens) : IsNoetherianRing Γ(U.1.toScheme, ⊤) := by
  let : IsAffine U.1.toScheme := U.2
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩

instance affineProjection_quasiCompact {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    QuasiCompact (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) := by infer_instance

theorem comap_app_bijective_iff_affine_raw {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I J : X.IdealSheafData) (U : X.affineOpens) :
    ComapBijective (PiExponentSeshadri.BlowupGluing.projection I) J U.1 ↔
      ComapBijective (PiExponentSeshadri.ReesGrading.projection
        (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (J.comap (PiExponentSeshadri.BlowupGluing.baseChart U)) ⊤ :=
  CanonicalRecoveryProperties.comap_open_square
    (PiExponentSeshadri.BlowupGluing.projection I)
    (PiExponentSeshadri.BlowupGluing.baseChart U)
    (PiExponentSeshadri.BlowupGluing.totalChart I U)
    (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
    (PiExponentSeshadri.BlowupGluing.totalChart_projection I U) J U.1 ⊤ ⊤
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      PiExponentSeshadri.BlowupGluing.baseChart_opensRange])
    (by simp only [Scheme.Hom.image_top_eq_opensRange,
      PiExponentSeshadri.BlowupGluing.totalChart_opensRange])
    (by simp)

theorem comap_app_bijective_iff_affine {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) (n : ℕ) :
    ComapBijective (PiExponentSeshadri.BlowupGluing.projection I) (I^n) U.1 ↔
      ComapBijective (PiExponentSeshadri.ReesGrading.projection
        (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U))
        (PiExponentSeshadri.IdealPullback.specIdeal
          ((PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n)) ⊤ := by
  have hh := comap_app_bijective_iff_affine_raw I (I^n) U
  have he : (I^n).comap (PiExponentSeshadri.BlowupGluing.baseChart U) =
      PiExponentSeshadri.IdealPullback.specIdeal
        ((PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)^n) := by
    rw [PiExponentSeshadri.IdealPullback.comap_pow,
      PiExponentSeshadri.BlowupGluing.center_comap_baseChart,
      PiExponentSeshadri.IdealPullback.specIdeal_pow]
  exact hh.trans (iff_of_eq (congrArg (fun J => ComapBijective
    (PiExponentSeshadri.ReesGrading.projection
      (PiExponentSeshadri.BlowupGluing.affineCenterIdeal I U)) J ⊤) he))

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end Source0822

-- Source: OAI/NumberTheory/PiExponent/Ampleness/GlobalReesCanonicalRecovery.lean
section Source0823
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/GlobalReesCanonicalRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.GlobalReesRecoveryComparison
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.BlowupGluing
open CanonicalRecoveryProperties

theorem eventually_ordinaryMap_app_bijective {X : Scheme.{0}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      OrdinaryBijective (projection I) I (exceptionalLineBundle I)
        (exceptionalInclusion I) (exceptional_presents I) n U.1 := by
  let : IsAffine U.1.toScheme := U.2
  let : IsNoetherianRing Γ(U.1.toScheme,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U.1.toScheme⟩
  obtain ⟨N,hN⟩ := AffineReesCanonicalRecovery.eventually_comap_bijective (affineCenterIdeal I U)
  exact ⟨N, fun n hn => (ordinary_iff_comap (projection I) I
    (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I) n U.1).mpr
      ((comap_app_bijective_iff_affine I U n).mpr (hN n hn))⟩

end PiExponent.GlobalReesRecoveryComparison

end

end OAI
end Source0823

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupJetSurjectivityComplete.lean
section Source0824
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupJetSurjectivityComplete.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.BlowupJetSurjectivity
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {R : Type} [CommRing R] [IsNoetherianRing R]

theorem eventual_blowup_jetRestriction_surjective
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (A : LineBundle X)
    (hample : LineBundle.IsAmple _ (blowupBundle I A)) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective (jetRestriction I A n) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  exact eventual_blowup_jetRestriction_surjective_of_affine_recovery p I A hample
    (fun U => GlobalReesRecoveryComparison.eventually_ordinaryMap_app_bijective I U)

end
end PiExponent.BlowupJetSurjectivity

end OAI
end Source0824
