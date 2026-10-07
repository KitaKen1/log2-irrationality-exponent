/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part014
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveImageAffineCoordinates.lean
section Source0550
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveImageAffineCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} [IsIntegral C]
variable {ι : Type}

theorem preimage_surjective {R S : CommRingCat}
    (q : Spec S ⟶ Spec R) [IsClosedImmersion q] :
    Function.Surjective (Spec.preimage q) := by
  have he : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫ q.appTop ≫
      (Scheme.ΓSpecIso S).hom := by
    have h : Spec.preimage q = (Scheme.ΓSpecIso R).inv ≫
        (Spec.map (Spec.preimage q)).appTop ≫ (Scheme.ΓSpecIso S).hom := by
      rw [Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
    simpa only [Spec.map_preimage] using h
  rw [he]
  exact (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso S).hom).surjective.comp
    ((q.app_surjective ⊤ (isAffineOpen_top _)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso R).inv).surjective)

def presentation (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens)
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.chartAlgebra p U
    MvPolynomial ι ℂ →ₐ[ℂ] Γ(C,U.1) := by
  letI := IntegralAffineOpenDimension.chartAlgebra p U
  refine ⟨(Spec.preimage q).hom,?_⟩
  intro c
  have h : CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ) ≫
      Spec.preimage q = Spec.preimage (U.2.fromSpec ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact hq
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ Γ(C,U.1) => φ c) h

def coordinates (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) : ι → C.functionField :=
  fun i => C.germToFunctionField U.1 ((Spec.preimage q) (MvPolynomial.X i))

theorem field_properties [Finite ι] (p : C ⟶ Spec (.of ℂ)) [LocallyOfFiniteType p]
    (hdim : topologicalKrullDim C = 1) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ))) [IsClosedImmersion q]
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Algebra.EssFiniteType ℂ C.functionField ∧ Algebra.trdeg ℂ C.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates U q)) = ⊤ := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  let := functionField_isFractionRing_of_isAffineOpen C U.1 U.2
  have hdimA : ringKrullDim Γ(C,U.1) = 1 :=
    (IntegralAffineOpenDimension.affine_ring_dimension_eq p U).trans hdim
  exact CurveGeometricFunctionField.of_surjective_coordinates ℂ Γ(C,U.1) C.functionField
    (presentation p U q hq) (preimage_surjective q) hdimA

theorem coordinates_generic_map
    (p : C ⟶ Spec (.of ℂ)) (U : C.affineOpens) [Nonempty U.1]
    (q : Spec Γ(C,U.1) ⟶ Spec (.of (MvPolynomial ι ℂ)))
    (hq : q ≫ Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      U.2.fromSpec ≫ p)
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) (i : C ⟶ X)
    (hchart : q ≫ j = U.2.fromSpec ≫ i) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra p
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (coordinates U q)).toRingHom) ≫ j =
      C.fromSpecStalk (genericPoint C) ≫ i := by
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.functionFieldAlgebra p
  let := IntegralAffineOpenDimension.chart_functionField_scalarTower p U
  have he : (MvPolynomial.aeval (coordinates U q)).toRingHom =
      (C.germToFunctionField U.1).hom.comp (Spec.preimage q).hom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (coordinates U q) =
        (IsScalarTower.toAlgHom ℂ Γ(C,U.1) C.functionField).comp (presentation p U q hq) from ?_)
    apply MvPolynomial.algHom_ext
    intro a
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, ← CommRingCat.hom_comp, CommRingCat.ofHom_hom, Spec.map_comp,
    Spec.map_preimage, Category.assoc, hchart, ← Category.assoc,
    IntegralAffineOpenDimension.germToFunctionField_fromSpec]

theorem transport_field_properties {F E : Type} [Field F] [Field E]
    [Algebra ℂ F] [Algebra ℂ E] [Algebra.EssFiniteType ℂ F]
    (e : F ≃ₐ[ℂ] E) (x : ι → F)
    (hd : Algebra.trdeg ℂ F = 1)
    (hx : IntermediateField.adjoin ℂ (Set.range x) = ⊤) :
    Algebra.EssFiniteType ℂ E ∧ Algebra.trdeg ℂ E = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (e ∘ x)) = ⊤ := by
  refine ⟨Algebra.EssFiniteType.of_surjective e.toAlgHom e.surjective,
    e.trdeg_eq.symm.trans hd, ?_⟩
  rw [Set.range_comp]
  change IntermediateField.adjoin ℂ (e.toAlgHom '' Set.range x) = ⊤
  rw [← IntermediateField.adjoin_map ℂ (Set.range x) e.toAlgHom, hx,
    ← AlgHom.fieldRange_eq_map]
  exact e.fieldRange_eq_top

def fieldAlgEquiv {D : Scheme.{0}} [IsIntegral D]
    (pC : C ⟶ Spec (.of ℂ)) (pD : D ⟶ Spec (.of ℂ))
    (e : C.functionField ≅ D.functionField)
    (he : Spec.map e.hom ≫ C.fromSpecStalk (genericPoint C) ≫ pC =
      D.fromSpecStalk (genericPoint D) ≫ pD) :
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
    letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
    C.functionField ≃ₐ[ℂ] D.functionField := by
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pC
  letI := IntegralAffineOpenDimension.functionFieldAlgebra pD
  refine { e.commRingCatIsoToRingEquiv with commutes' := ?_ }
  intro c
  have h : Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ pC) ≫ e.hom =
      Spec.preimage (D.fromSpecStalk (genericPoint D) ≫ pD) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
    exact he
  exact congrArg (fun φ : CommRingCat.of ℂ ⟶ D.functionField => φ c) h

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end Source0550

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveImageAffineChart.lean
section Source0551
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveImageAffineChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CurveImageAffineCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {C X : Scheme.{0}} {ι : Type}

def affinePart (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] : C.affineOpens :=
  ⟨i ⁻¹ᵁ j.opensRange, (isAffineOpen_opensRange j).preimage i⟩

def affinePresentation (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    Spec Γ(C,(affinePart i j).1) ⟶ Spec (.of (MvPolynomial ι ℂ)) :=
  (affinePart i j).2.isoSpec.inv ≫ (i ∣_ j.opensRange) ≫ j.isoOpensRange.inv

instance affinePresentation_isClosedImmersion (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    IsClosedImmersion (affinePresentation i j) := by
  unfold affinePresentation
  have hcomp : IsClosedImmersion ((i ∣_ j.opensRange) ≫ j.isoOpensRange.inv) :=
    IsClosedImmersion.comp _ _
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hcomp

@[reassoc] theorem affinePresentation_comp (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j] :
    affinePresentation i j ≫ j = (affinePart i j).2.fromSpec ≫ i := by
  unfold affinePresentation IsAffineOpen.fromSpec
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (affinePart i j).2.isoSpec.inv ≫ k)
      ((Category.assoc _ _ _).trans
        ((congrArg (fun k => (i ∣_ j.opensRange) ≫ k)
          (Scheme.Hom.isoOpensRange_inv_comp j)).trans
          (morphismRestrict_ι i j.opensRange)))).trans
      (Category.assoc _ _ _).symm)

theorem affinePresentation_over (p : X ⟶ Spec (.of ℂ))
    (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (hj : j ≫ p = Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ))) :
    affinePresentation i j ≫ Spec.map (CommRingCat.ofHom
      (MvPolynomial.C : ℂ →+* MvPolynomial ι ℂ)) =
      (affinePart i j).2.fromSpec ≫ i ≫ p := by
  rw [← hj, ← Category.assoc, affinePresentation_comp, Category.assoc]

theorem affinePart_nonempty (i : C ⟶ X) [IsClosedImmersion i]
    (j : Spec (.of (MvPolynomial ι ℂ)) ⟶ X) [IsOpenImmersion j]
    (h : ∃ c : C, i c ∈ j.opensRange) : Nonempty (affinePart i j).1 := by
  obtain ⟨c,hc⟩ := h
  exact ⟨⟨c,hc⟩⟩

end PiExponent.CurveImageAffineCoordinates

end

end OAI
end Source0551

-- Source: LogTwo/Geometry/BlowupCurveCoordinates.lean
section Source0552
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt curve-coordinate constructions to the varying-center blowup.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Actual varying-center curve models, adapted from the corresponding
AdmissibleCurve*.lean wrappers in pinned openai/math (Apache-2.0).
Only scheme-generic APIs are imported; no fixed-Y contact bound is used. -/
namespace LogTwo.Geometry.MatrixBlowup.Coordinates
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
open LogTwo.Geometry.MatrixBlowup
open CurveImageAffineCoordinates
variable {m K : ℕ} (w : LogTwo.Interpolation.Weights m)
variable (y : Fin K → ℂ) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)
variable (C : NumericalAmpleness.IntegralCurve (space w y a T))
variable (hn : ¬ ∃ x : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {x})

abbrev imageCurve := LogTwo.Geometry.MatrixBlowup.Image.imageCurve w y a T C hn
abbrev sourceStructure := C.embedding ≫ structureMap w y a T
abbrev imageStructure := (imageCurve w y a T C hn).embedding ≫ MatrixCompactification.structureMap w
@[instance_reducible] def sourceAlgebra : Algebra ℂ C.scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (sourceStructure w y a T C)
@[instance_reducible] def imageAlgebra :
    Algebra ℂ (imageCurve w y a T C hn).scheme.functionField :=
  IntegralAffineOpenDimension.functionFieldAlgebra (imageStructure w y a T C hn)

def fieldEquiv :
    letI := imageAlgebra w y a T C hn
    letI := sourceAlgebra w y a T C
    (imageCurve w y a T C hn).scheme.functionField ≃ₐ[ℂ] C.scheme.functionField :=
  fieldAlgEquiv (imageStructure w y a T C hn) (sourceStructure w y a T C)
    (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso w y a T C hn) (by
      simpa only [imageStructure, sourceStructure, MatrixBlowup.structureMap, Category.assoc] using
        congrArg (fun f => f ≫ MatrixCompactification.structureMap w)
          (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso_generic w y a T C hn))

abbrev chart := affinePart (imageCurve w y a T C hn).embedding (MatrixCompactification.affineChart w)
abbrev chartPresentation := affinePresentation (imageCurve w y a T C hn).embedding (MatrixCompactification.affineChart w)

variable (hm : ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.affineChart w).opensRange)

include hm in
theorem chart_nonempty : Nonempty (chart w y a T C hn).1 :=
  affinePart_nonempty _ _ (LogTwo.Geometry.MatrixBlowup.Image.image_meets_chart w y a T C hn hm)

def imageCoordinates : Fin (m+1) → (imageCurve w y a T C hn).scheme.functionField :=
  letI := chart_nonempty w y a T C hn hm
  CurveImageAffineCoordinates.coordinates (chart w y a T C hn) (chartPresentation w y a T C hn)

def coordinates : Fin (m+1) → C.scheme.functionField :=
  letI := imageAlgebra w y a T C hn
  letI := sourceAlgebra w y a T C
  fieldEquiv w y a T C hn ∘ imageCoordinates w y a T C hn hm

theorem field_properties :
    letI := sourceAlgebra w y a T C
    Algebra.EssFiniteType ℂ C.scheme.functionField ∧
      Algebra.trdeg ℂ C.scheme.functionField = 1 ∧
      IntermediateField.adjoin ℂ (Set.range (coordinates w y a T C hn hm)) = ⊤ := by
  let := sourceAlgebra w y a T C
  let := imageAlgebra w y a T C hn
  let := chart_nonempty w y a T C hn hm
  obtain ⟨ht,hd,hg⟩ := CurveImageAffineCoordinates.field_properties
    (imageStructure w y a T C hn) (imageCurve w y a T C hn).dimension
    (chart w y a T C hn) (chartPresentation w y a T C hn)
    (affinePresentation_over (MatrixCompactification.structureMap w) _ _ (MatrixCompactification.affineChart_over w))
  let := ht
  exact transport_field_properties (fieldEquiv w y a T C hn)
    (imageCoordinates w y a T C hn hm) hd hg

theorem coordinates_generic_map :
    letI := sourceAlgebra w y a T C
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm)).toRingHom) ≫
      MatrixCompactification.affineChart w = C.scheme.fromSpecStalk (genericPoint C.scheme) ≫
        C.embedding ≫ projection w y a T := by
  let := sourceAlgebra w y a T C
  let := imageAlgebra w y a T C hn
  let := chart_nonempty w y a T C hn hm
  have himage := CurveImageAffineCoordinates.coordinates_generic_map
    (imageStructure w y a T C hn) (chart w y a T C hn) (chartPresentation w y a T C hn)
    (affinePresentation_over (MatrixCompactification.structureMap w) _ _ (MatrixCompactification.affineChart_over w))
    (MatrixCompactification.affineChart w) (imageCurve w y a T C hn).embedding (affinePresentation_comp _ _)
  have he : (MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm)).toRingHom =
      (LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso w y a T C hn).hom.hom.comp
        (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)).toRingHom := by
    apply congrArg AlgHom.toRingHom
      (show MvPolynomial.aeval (R := ℂ) (coordinates w y a T C hn hm) =
        (fieldEquiv w y a T C hn).toAlgHom.comp
          (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)) from ?_)
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X, AlgHom.comp_apply]
    rfl
  rw [he, CommRingCat.ofHom_comp, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc]
  rw [show Spec.map (CommRingCat.ofHom
      (MvPolynomial.aeval (R := ℂ) (imageCoordinates w y a T C hn hm)).toRingHom) ≫ MatrixCompactification.affineChart w =
      (imageCurve w y a T C hn).scheme.fromSpecStalk (genericPoint (imageCurve w y a T C hn).scheme) ≫
        (imageCurve w y a T C hn).embedding from himage]
  exact LogTwo.Geometry.MatrixBlowup.Image.functionFieldIso_generic w y a T C hn

end
end LogTwo.Geometry.MatrixBlowup.Coordinates
end Source0552

-- Source: OAI/NumberTheory/PiExponent/Geometry/BirationalOpenIso.lean
section Source0553
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/BirationalOpenIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.BirationalOpenIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

theorem exists_open_iso_of_generic_inverse (f : Y ⟶ X)
    [LocallyOfFiniteType f] [IsSeparated f]
    (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ f = X.fromSpecStalk (genericPoint X)) :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (f ∣_ U) := by
  let η : Spec X.functionField ⟶ Y :=
    Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Y.fromSpecStalk (genericPoint Y)
  have hηf : η ≫ f = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    simpa only [η, Category.assoc, Category.comp_id] using! he
  obtain ⟨U, hU, g, hη, hg⟩ := spread_out_of_isGermInjective' (𝟙 X) f η hηf
  simp only [Category.comp_id] at hg
  let V : Y.Opens := f ⁻¹ᵁ U
  have hrange : Set.range g ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨g x, ?_⟩, rfl⟩
    change f (g x) ∈ U
    have hpoint := congrArg (fun k : U.toScheme ⟶ X => k x) hg
    change f (g x) = x.1 at hpoint
    rw [hpoint]
    exact x.2
  let s : U.toScheme ⟶ V.toScheme := IsOpenImmersion.lift V.ι g hrange
  have hs : s ≫ V.ι = g := IsOpenImmersion.lift_fac _ _ _
  have hsr : s ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hs, hg, Category.id_comp]
  let : IsDominant (Y.fromSpecStalk (genericPoint Y)) :=
    CurveStalkGluing.isDominant_fromSpecFunctionField
  have hηdom : IsDominant η := by
    let : IsIso (CommRingCat.ofHom e.toRingHom) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr e.bijective
    dsimp only [η]
    infer_instance
  have : IsDominant (U.fromSpecStalkOfMem (genericPoint X) hU ≫ g) := by
    rw [← hη]
    exact hηdom
  have : IsDominant g := IsDominant.of_comp (U.fromSpecStalkOfMem (genericPoint X) hU) g
  have : IsDominant (s ≫ V.ι) := by rw [hs]; infer_instance
  have : IsDominant s := IsDominant.of_comp_of_isOpenImmersion s V.ι
  have hbase : ((f ∣_ U) ≫ s) ≫ (f ∣_ U) = (𝟙 V.toScheme) ≫ (f ∣_ U) := by
    rw [Category.assoc, hsr, Category.comp_id, Category.id_comp]
  have hdense : s ≫ ((f ∣_ U) ≫ s) = s ≫ 𝟙 V.toScheme := by
    rw [← Category.assoc, hsr, Category.id_comp, Category.comp_id]
  have hrs : (f ∣_ U) ≫ s = 𝟙 V.toScheme :=
    ext_of_isDominant_of_isSeparated (f ∣_ U) hbase s hdense
  exact ⟨U, hU, ⟨⟨s, hrs, hsr⟩⟩⟩

end PiExponent.BirationalOpenIso

end

end OAI
end Source0553

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationMorphism.lean
section Source0554
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveNormalizationMorphism.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponent.CurveNormalizationMorphism
open AlgebraicGeometry CategoryTheory
open CurveNormalizationModel

@[instance_reducible] def structureFieldAlgebra
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) : Algebra F X.functionField :=
  (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom.toAlgebra

theorem genericPoint_over_structure
    {F : Type u} [Field F] {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) :
    letI := structureFieldAlgebra p
    X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)) := by
  let := structureFieldAlgebra p
  exact (Spec.map_preimage _).symm

theorem isDominant_of_generic_identity
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (g : Y ⟶ X) (e : Y.functionField ≃+* X.functionField)
    (he : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y) ≫ g = X.fromSpecStalk (genericPoint X)) :
    IsDominant g := by
  have : IsDominant ((Spec.map (CommRingCat.ofHom e.toRingHom) ≫
      Y.fromSpecStalk (genericPoint Y)) ≫ g) := by
    rw [Category.assoc, he]
    exact CurveStalkGluing.isDominant_fromSpecFunctionField
  exact IsDominant.of_comp (Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Y.fromSpecStalk (genericPoint Y)) g

theorem nontrivial_of_dimension_one (X : Scheme.{u})
    (hdim : topologicalKrullDim X = 1) : Nontrivial X := by
  classical
  by_contra h
  have : Subsingleton X := not_nontrivial_iff_subsingleton.mp h
  have hzero := topologicalKrullDim_zero_of_discreteTopology X
  rw [hdim] at hzero
  norm_num at hzero

theorem exists_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsProper g ∧ IsDominant g := by
  obtain ⟨g, hover, hgeneric⟩ := CurveGlobalMonomial.exists_parameterCurve_extension
    f hf p (X.fromSpecStalk (genericPoint X)) hp
  have : IsProper (g ≫ p) := by
    rw [hover]
    infer_instance
  have : IsProper g := IsProper.of_comp g p
  have : IsDominant g := isDominant_of_generic_identity g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, inferInstance, inferInstance⟩

theorem exists_finite_model_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X] [Nontrivial X] [Algebra F X.functionField]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hp : X.fromSpecStalk (genericPoint X) ≫ p =
      Spec.map (CommRingCat.ofHom (algebraMap F X.functionField)))
    (f : X.functionField) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField] :
    ∃ g : parameterCurve f hf ⟶ X,
      g ≫ p = parameterCurveStructureMap f hf ∧
      parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
      IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  obtain ⟨g, hover, hgeneric, hproper, hdominant⟩ := exists_model_morphism p hp f hf
  have : IsProper g := hproper
  have : IsDominant g := hdominant
  have hfinite : IsFinite g := CurveMorphismFinite.isFinite_of_proper_dominant g
    (parameterCurve_dimension_le_one f hf)
  obtain ⟨U, hU, hUiso⟩ := BirationalOpenIso.exists_open_iso_of_generic_inverse g
    (parameterCurveFunctionFieldEquiv f hf) (by
      simpa only [parameterCurveGenericPoint, Category.assoc] using hgeneric)
  exact ⟨g, hover, hgeneric, hfinite, U, hU, hUiso⟩

theorem exists_intrinsic_normalization_morphism
    {F : Type u} [Field F] [CharZero F]
    {X : Scheme.{u}} [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of F)) [IsProper p]
    (hdim : topologicalKrullDim X = 1) :
    letI := structureFieldAlgebra p
    ∀ (f : X.functionField) (hf : Transcendental F f),
      ∀ [FiniteDimensional (IntermediateField.adjoin F {f}) X.functionField],
      ∃ g : parameterCurve f hf ⟶ X,
        g ≫ p = parameterCurveStructureMap f hf ∧
        parameterCurveGenericPoint f hf ≫ g = X.fromSpecStalk (genericPoint X) ∧
        IsFinite g ∧ ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (g ∣_ U) := by
  let := structureFieldAlgebra p
  intro f hf hfinite
  have : Nontrivial X := nontrivial_of_dimension_one X hdim
  exact exists_finite_model_morphism p (genericPoint_over_structure p) f hf

end PiExponent.CurveNormalizationMorphism

end

end OAI
end Source0554

-- Source: LogTwo/Geometry/BlowupCurveModel.lean
section Source0555
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt curve-model constructions to the varying-center blowup.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Actual varying-center curve models, adapted from the corresponding
AdmissibleCurve*.lean wrappers in pinned openai/math (Apache-2.0).
Only scheme-generic APIs are imported; no fixed-Y contact bound is used. -/
namespace LogTwo.Geometry.MatrixBlowup.CurveModel
open OAI PiExponent AlgebraicGeometry CategoryTheory TopologicalSpace
noncomputable section
open LogTwo.Geometry.MatrixBlowup CurveNormalizationModel
variable {m K : ℕ} (w : LogTwo.Interpolation.Weights m)
variable (y : Fin K → ℂ) (a : Fin K → Fin m → ℂ) (T : Fin m → ℕ)

structure ModelData (C : NumericalAmpleness.IntegralCurve (space w y a T)) where
  E : Type
  [field : Field E]
  [algebra : Algebra ℂ E]
  [essFiniteType : Algebra.EssFiniteType ℂ E]
  coordinates : Fin (m+1) → E
  coordinates_generate : IntermediateField.adjoin ℂ (Set.range coordinates) = ⊤
  trdeg_one : Algebra.trdeg ℂ E = 1
  parameter : E
  parameter_transcendental : Transcendental ℂ parameter
  [parameterFinite : FiniteDimensional (IntermediateField.adjoin ℂ {parameter}) E]
  normalization : parameterCurve parameter parameter_transcendental ⟶ C.scheme
  [normalizationFinite : IsFinite normalization]
  normalization_over : normalization ≫ C.embedding ≫ structureMap w y a T =
    parameterCurveStructureMap parameter parameter_transcendental
  chart : C.scheme.Opens
  chart_nonempty : chart ≠ ⊥
  [chartIso : IsIso (normalization ∣_ chart)]
  generic_coordinates : parameterCurveGenericPoint parameter parameter_transcendental ≫
      (normalization ≫ C.embedding ≫ projection w y a T) =
    Spec.map (CommRingCat.ofHom (MvPolynomial.aeval coordinates).toRingHom) ≫
      MatrixCompactification.affineChart w

theorem existsModelData (C : NumericalAmpleness.IntegralCurve (space w y a T))
    (hn : ¬ ∃ t : MatrixCompactification.space w, Set.range (C.embedding ≫ projection w y a T) ⊆ {t})
    (hm : ∃ c : C.scheme, (C.embedding ≫ projection w y a T) c ∈ (MatrixCompactification.affineChart w).opensRange) :
    Nonempty (ModelData w y a T C) := by
  let := LogTwo.Geometry.MatrixBlowup.Coordinates.sourceAlgebra w y a T C
  have hp := LogTwo.Geometry.MatrixBlowup.Coordinates.field_properties w y a T C hn hm
  let := hp.1
  let z := LogTwo.Geometry.MatrixBlowup.Coordinates.coordinates w y a T C hn hm
  have hfinite := CurveParameterFinite.finite_over_every_parameter ℂ C.scheme.functionField hp.2.1
  obtain ⟨i,hi⟩ := LogTwo.Geometry.nonconstant_coordinates_of_trdeg_one z hp.2.2 hp.2.1
  let f := z i
  have hf : Transcendental ℂ f := hi
  let := hfinite f hf
  obtain ⟨g,hg,hgeneric,hgfinite,W,hW,hWiso⟩ :=
    CurveNormalizationMorphism.exists_intrinsic_normalization_morphism
      (C.embedding ≫ structureMap w y a T) C.dimension f hf
  let := hgfinite
  let := hWiso
  have hWne : W ≠ ⊥ := by
    intro he
    simp only [he, Opens.mem_bot] at hW
  have hc : parameterCurveGenericPoint f hf ≫ (g ≫ C.embedding ≫ projection w y a T) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.aeval z).toRingHom) ≫
      MatrixCompactification.affineChart w := by
    rw [← Category.assoc, ← Category.assoc, hgeneric]
    exact (LogTwo.Geometry.MatrixBlowup.Coordinates.coordinates_generic_map w y a T C hn hm).symm
  exact ⟨{ E := C.scheme.functionField
           field := inferInstance
           algebra := inferInstance
           essFiniteType := hp.1
           coordinates := z
           coordinates_generate := hp.2.2
           trdeg_one := hp.2.1
           parameter := f
           parameter_transcendental := hf
           parameterFinite := inferInstance
           normalization := g
           normalizationFinite := hgfinite
           normalization_over := hg
           chart := W
           chart_nonempty := hWne
           chartIso := hWiso
           generic_coordinates := hc }⟩

end
end LogTwo.Geometry.MatrixBlowup.CurveModel
end Source0555

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistPowerSection.lean
section Source0556
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistPowerSection.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

lemma moduleTensorComm_pure (M N : X.Modules) (U : X.Opens)
    (m : Γ(M,U)) (n : Γ(N,U)) :
    (moduleTensorComm M N).hom.app U (pure M N U m n) = pure N M U n m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  have h := (adj X).unit.naturality (β_ M.val N.val).hom
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

theorem moduleTwistSection_unitIso (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    (moduleTwistSection L s n).app (structureSheaf X) ≫ (moduleTwistUnitIso L n).hom =
      powerSection s n := by
  induction n with
  | zero =>
    simp [moduleTwistSection, moduleTwistUnitIso, powerSection_zero]
    exact Category.id_comp _
  | succ n ih =>
    apply (moduleSectionEquiv (modulePow X L.sheaf (n+1))).injective
    change (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤
      ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).app ⊤
        ((moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj (structureSheaf X)) s).app ⊤
          (((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))))) =
      (powerSection s (n+1)).app ⊤ (1 : Γ(X,⊤))
    let v := ((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))
    have hm := congrArg (fun z => (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤
      ((moduleTensorMap (moduleTwistUnitIso L n).hom (𝟙 L.sheaf)).app ⊤ z))
      (moduleSectionMultiplyRight_pure ((moduleTwistFunctor L n).obj (structureSheaf X)) s ⊤ v)
    have ht := congrArg (fun z => (moduleTensorComm (modulePow X L.sheaf n) L.sheaf).hom.app ⊤ z)
      (TensorPure.map_pure (moduleTwistUnitIso L n).hom (𝟙 L.sheaf) ⊤ v
        (s.app ⊤ (1 : Γ(X,⊤))))
    have hc := moduleTensorComm_pure (modulePow X L.sheaf n) L.sheaf ⊤
      ((moduleTwistUnitIso L n).hom.app ⊤ v) (s.app ⊤ (1 : Γ(X,⊤)))
    refine hm.trans (ht.trans (hc.trans (Eq.trans ?_ (power_succ_apply s n ⊤).symm)))
    have hi := congrArg (fun f : structureSheaf X ⟶ modulePow X L.sheaf n =>
      f.app ⊤ (1 : Γ(X,⊤))) ih
    change (moduleTwistUnitIso L n).hom.app ⊤
      (((moduleTwistSection L s n).app (structureSheaf X)).app ⊤ (1 : Γ(X,⊤))) =
      (powerSection s n).app ⊤ (1 : Γ(X,⊤)) at hi
    exact congrArg (fun z => pure L.sheaf (modulePow X L.sheaf n) ⊤
      (s.app ⊤ (1 : Γ(X,⊤))) z) hi

lemma moduleTwistSection_unitIso_app (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) (U : X.Opens) (a : Γ(X,U)) :
    (moduleTwistUnitIso L n).hom.app U
      (((moduleTwistSection L s n).app (structureSheaf X)).app U a) =
      (powerSection s n).app U a :=
  congrArg (fun f : structureSheaf X ⟶ modulePow X L.sheaf n => f.app U a)
    (moduleTwistSection_unitIso L s n)

end
end PiExponentSeshadri.Geometry

end OAI
end Source0556

-- Source: OAI/NumberTheory/PiExponent/Approximation/NoetherianPowerExtension.lean
section Source0557
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NoetherianPowerExtension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames
variable {X : Scheme}

theorem LineBundle.noetherian_power_extension [NoetherianSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (f : Γ(X,sectionOpen X s)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      t.app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) =
        f • (powerSection s n).app (sectionOpen X s) (1 : Γ(X,sectionOpen X s)) := by
  have : (structureSheaf X).IsFinitePresentation :=
    PiExponent.GeometrySupport.LineBundleCoherent.structureSheaf_isFinitePresentation
  have : (structureSheaf X).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (structureSheaf X)).choose.isQuasicoherent
  obtain ⟨N, hN⟩ := PiExponent.TwistGlobalExtension.global_twist_extension_native L s
    (structureSheaf X) f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨z, hz⟩ := hN n hn
  let P := (moduleTwistFunctor L n).obj (structureSheaf X)
  let Q := modulePow X L.sheaf n
  let D := sectionOpen X s
  let e := moduleTwistUnitIso L n
  let t : GlobalSections X Q := (moduleSectionEquiv Q).symm (e.hom.app ⊤ z)
  refine ⟨t, ?_⟩
  have htop : t.app ⊤ (1 : Γ(X,⊤)) = e.hom.app ⊤ z :=
    (moduleSectionEquiv Q).apply_symm_apply _
  have ht : Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op
      (e.hom.app ⊤ z) = t.app D (1 : Γ(X,D)) :=
    (congrArg (fun x : Γ(Q,⊤) =>
      Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op x) htop).symm.trans
        (section_value_natural t (homOfLE (show D ≤ ⊤ from le_top)))
  have he := CategoryTheory.congr_fun
    (e.hom.mapPresheaf.naturality (homOfLE (show D ≤ ⊤ from le_top)).op) z
  change e.hom.app D (P.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op z) =
    Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op (e.hom.app ⊤ z) at he
  have hp := moduleTwistSection_unitIso_app L s n D f
  calc
    t.app D (1 : Γ(X,D)) =
        Q.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op (e.hom.app ⊤ z) := ht.symm
    _ = e.hom.app D (P.presheaf.map (homOfLE (show D ≤ ⊤ from le_top)).op z) := he.symm
    _ = e.hom.app D (((moduleTwistSection L s n).app (structureSheaf X)).app D f) :=
      congrArg (fun x => e.hom.app D x) hz
    _ = (powerSection s n).app D f := hp
    _ = f • (powerSection s n).app D (1 : Γ(X,D)) := by
      have hm := (powerSection s n).app_smul (r := f) (x := (1 : Γ(X,D)))
      change (powerSection s n).app D (show Γ(X,D) from f * 1) = _ at hm
      exact (congrArg ((powerSection s n).app D) (mul_one f)).symm.trans hm

theorem LineBundle.noetherian_power_extension_ratio [NoetherianSpace X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (f : Γ((sectionOpen X s).toScheme,⊤)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ t : GlobalSections X (modulePow X L.sheaf n),
      restrictSection (sectionOpen X s).ι t = scalarEnd f ≫
        restrictSection (sectionOpen X s).ι (powerSection s n) := by
  obtain ⟨N, hN⟩ := L.noetherian_power_extension s ((sectionOpen X s).topIso.hom f)
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨t, ht⟩ := hN n hn
  refine ⟨t, ?_⟩
  apply (openSectionEquiv (modulePow X L.sheaf n) (sectionOpen X s)).injective
  erw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict]
  exact ht

end
end PiExponentSeshadri.Geometry

end OAI
end Source0557

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NoetherianAmpleProjectiveSections.lean
section Source0558
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NoetherianAmpleProjectiveSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K ι : Type} [CommRing K] [Fintype ι]

theorem LineBundle.power_section_embedding_noetherian [NoetherianSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p] (L : LineBundle X)
    (s : ι → GlobalSections X L.sheaf)
    (hc : (⨆ i, sectionOpen X (s i)) = ⊤)
    (haff : ∀ i, IsAffineOpen (sectionOpen X (s i))) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  classical
  let k := p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let U (i : ι) := sectionOpen X (s i)
  have hfinite (i : ι) : ∃ m : ℕ, ∃ b : Fin m → Γ((U i).toScheme, ⊤),
      Function.Surjective (eval₂Hom ((U i).ι.appTop.hom.comp k) b) := by
    let : IsAffine (U i).toScheme := haff i
    obtain ⟨m, b, hb⟩ := affine_coordinate_generators ((U i).ι ≫ p)
    refine ⟨m, b, ?_⟩
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_assoc, k] using hb
  choose m b hb using hfinite
  choose N hN using fun i j => L.noetherian_power_extension_ratio (s i) (b i j)
  let n := max 1 (Finset.univ.sup (fun v : (i : ι) × Fin (m i) => N v.1 v.2))
  have hn : 0 < n := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hn' (i : ι) (j : Fin (m i)) : N i j ≤ n :=
    (Finset.le_sup (f := fun v : (i : ι) × Fin (m i) => N v.1 v.2)
      (Finset.mem_univ ⟨i, j⟩)).trans (le_max_right _ _)
  choose t ht using fun i j => hN i j n (hn' i j)
  let σ := ι ⊕ ((i : ι) × Fin (m i))
  let S : σ → GlobalSections X (modulePow X L.sheaf n) :=
    Sum.elim (fun i => powerSection (s i) n) (fun v => t v.1 v.2)
  have hU (i : ι) : SectionOpens.isoOpen (S (Sum.inl i)) = U i :=
    L.sectionOpen_power (s i) hn
  have hSn (i : ι) : IsIso (restrictSection (U i).ι (S (Sum.inl i))) :=
    isIso_restricted_section _ _ (hU i)
  let e (i : ι) : (modulePow X L.sheaf n).restrict (U i).ι ≅ O (U i).toScheme :=
    (asIso (restrictSection (U i).ι (S (Sum.inl i)))).symm
  have hnorm (i : ι) : coefficient (e i) (restrictSection (U i).ι (S (Sum.inl i))) = 1 :=
    coefficient_frame (e i)
  have hS : (⨆ v, SectionOpens.isoOpen (S v)) = ⊤ := by
    apply top_unique
    rw [← hc]
    apply iSup_le
    intro i
    exact (le_of_eq (hU i).symm).trans (le_iSup (fun v : σ => SectionOpens.isoOpen (S v)) (Sum.inl i))
  have hproper : IsProper (X.toSpecΓ ≫ Spec.map (CommRingCat.ofHom k)) := by
    rw [toSpec_scalarMap]
    infer_instance
  have hgen (i : ι) : Function.Surjective
      (eval₂Hom ((U i).ι.appTop.hom.comp k)
        (fun v => coefficient (e i) (restrictSection (U i).ι (S v)))) := by
    have heq : (fun v => coefficient (e i) (restrictSection (U i).ι (S v))) ∘
        (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) = b i := by
      funext j
      exact coefficient_ratio (e i) (S (Sum.inl i)) (S (Sum.inr ⟨i, j⟩)) (b i j)
        (hnorm i) (ht i j)
    intro r
    obtain ⟨q, hq⟩ := hb i r
    refine ⟨rename (fun j : Fin (m i) => Sum.inr (⟨i, j⟩ : (i : ι) × Fin (m i))) q, ?_⟩
    rw [eval₂Hom_rename, heq]
    exact hq
  have hclosed := framedSectionsMorphism_closed k S U hc e Sum.inl hnorm hU
    (fun i => haff i) hgen
  rw [framedSectionsMorphism_eq_sectionsMorphism k S hS U hc e Sum.inl hnorm] at hclosed
  exact ⟨n, hn, σ, inferInstance, S, hS, hclosed⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames PiExponentSeshadri.Projective
variable {X : Scheme} {K : Type} [CommRing K]

theorem LineBundle.ample_projective_sections_noetherian [NoetherianSpace X]
    (p : X ⟶ Spec (CommRingCat.of K)) [IsProper p]
    (L : LineBundle X) (hL : L.IsAmple) :
    ∃ n : ℕ, 0 < n ∧ ∃ σ : Type, ∃ _ : Fintype σ,
      ∃ t : σ → GlobalSections X (modulePow X L.sheaf n),
      ∃ ht : (⨆ i, SectionOpens.isoOpen (t i)) = ⊤,
        IsClosedImmersion (sectionsMorphism
          (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht) := by
  obtain ⟨d, hd, l, s, hc, ha, -⟩ := L.ample_common_degree_cover hL
  obtain ⟨n, hn', σ, hσ, t, ht, he⟩ := (L.pow d).power_section_embedding_noetherian p s hc ha
  let e : modulePow X (L.pow d).sheaf n ≅ modulePow X L.sheaf (d * n) :=
    linePowerMul L d n
  let T : σ → GlobalSections X (modulePow X L.sheaf (d*n)) := fun i => t i ≫ e.hom
  have hT : (⨆ i, SectionOpens.isoOpen (T i)) = ⊤ := by
    exact (iSup_congr (fun i => SectionOpens.isoOpen_postcomp (t i) e)).trans ht
  refine ⟨d*n, Nat.mul_pos hd hn', σ, hσ, T, hT, ?_⟩
  have htransport := sectionsMorphism_transport
    (p.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom) t ht e hT
  exact htransport.symm ▸ he

end PiExponentSeshadri.Geometry

end

end OAI
end Source0558

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechOne.lean
section Source0559
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechOne.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechOne

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

theorem hom_glue {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f : ∀ i, freeOpen R (U i) ⟶ M)
    (hf : ∀ i j, freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)) ≫ f i =
      freeOpenMap R (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)) ≫ f j) :
    ∃ g : freeOpen R V ⟶ M, ∀ i, freeOpenMap R (homOfLE (hUV i)) ≫ g = f i := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  let sf (i : J) := freeOpenEquiv R M (U i) (f i)
  have hc : TopCat.Presheaf.IsCompatible F.obj U sf := by
    intro i j
    change M.val.map (homOfLE inf_le_left).op (sf i) =
      M.val.map (homOfLE inf_le_right).op (sf j)
    rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality, hf i j]
  obtain ⟨s, hs, _⟩ := F.existsUnique_gluing' U V (fun i => homOfLE (hUV i)) hcover sf hc
  refine ⟨(freeOpenEquiv R M V).symm s, fun i => ?_⟩
  apply (freeOpenEquiv R M (U i)).injective
  rw [freeOpenEquiv_naturality]
  exact (congrArg (M.val.map (homOfLE (hUV i)).op)
    ((freeOpenEquiv R M V).apply_symm_apply s)).trans (hs i)

def restrictHom {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) : freeOpen R U ⟶ M :=
  freeOpenMap R (homOfLE h) ≫ f

@[simp] theorem restrictHom_restrictHom {M : SheafOfModules.{u} R} {U V W : Opens X}
    (h : U ≤ V) (k : V ≤ W) (f : freeOpen R W ⟶ M) :
    restrictHom R h (restrictHom R k f) = restrictHom R (h.trans k) f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE h) ≫
      (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE k) ≫ f =
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (homOfLE (h.trans k)) ≫ f
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

@[simp] theorem restrictHom_comp {M N : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    restrictHom R h (f ≫ g) = restrictHom R h f ≫ g := by
  simp only [restrictHom, Category.assoc]

@[simp] theorem restrictHom_add {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f + g) = restrictHom R h f + restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_add]

@[simp] theorem restrictHom_sub {M : SheafOfModules.{u} R} {U V : Opens X}
    (h : U ≤ V) (f g : freeOpen R V ⟶ M) :
    restrictHom R h (f - g) = restrictHom R h f - restrictHom R h g := by
  simp only [restrictHom, Preadditive.comp_sub]

theorem hom_ext {J : Type u} (U : J → Opens X) (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (M : SheafOfModules.{u} R) (f g : freeOpen R V ⟶ M)
    (hfg : ∀ i, restrictHom R (hUV i) f = restrictHom R (hUV i) g) : f = g := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} X := (SheafOfModules.toSheaf R).obj M
  apply (freeOpenEquiv R M V).injective
  apply F.eq_of_locally_eq' U V (fun i => homOfLE (hUV i)) hcover
  intro i
  change M.val.map (homOfLE (hUV i)).op _ = M.val.map (homOfLE (hUV i)).op _
  rw [← freeOpenEquiv_naturality, ← freeOpenEquiv_naturality]
  exact congrArg (freeOpenEquiv R M (U i)) (hfg i)

theorem lift_of_ext_one_zero (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (U : Opens X)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R U) S.X₁ 1, x = 0)
    (s : freeOpen R U ⟶ S.X₃) : ∃ t : freeOpen R U ⟶ S.X₂, t ≫ S.g = s := by
  obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₃ (freeOpen R U) hS (Ext.mk₀ s)
    (n₁ := 1) rfl (hzero _)
  obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).surjective t
  refine ⟨t, ?_⟩
  apply (Ext.mk₀_bijective _ _).injective
  simpa only [Ext.mk₀_comp_mk₀] using ht

def IsCocycle {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)
    (c : ∀ i j, freeOpen R (U i ⊓ U j) ⟶ M) : Prop :=
  ∀ i j k,
    restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) (c i j) +
      restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U j ⊓ U k from
        le_inf (inf_le_left.trans inf_le_right) inf_le_right) (c j k) =
    restrictHom R (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U k from
      le_inf (inf_le_left.trans inf_le_left) inf_le_right) (c i k)

def HasPrimitives {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R) : Prop :=
  ∀ c : ∀ i j, freeOpen R (U i ⊓ U j) ⟶ M, IsCocycle R U M c →
    ∃ b : ∀ i, freeOpen R (U i) ⟶ M, ∀ i j,
      c i j = restrictHom R inf_le_right (b j) - restrictHom R inf_le_left (b i)

end
end PiExponent.GeometrySupport.CechOne

end OAI
end Source0559

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCechHigher.lean
section Source0560
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCechHigher.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveMonomialCechHigher

noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech

variable {ι A K : Type*} [AddCommGroup A]

abbrev Cochain (ι A : Type*) (q : ℕ) := (Fin (q + 1) → ι) → A

def differential {q : ℕ} (c : Cochain ι A q) : Cochain ι A (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • c (t ∘ k.succAbove)

theorem differential_cons {q : ℕ} (c : Cochain ι A (q + 1))
    (p : ι) (t : Fin (q + 2) → ι) :
    differential c (Fin.cons p t) =
      c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t := by
  rw [differential, Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, Fin.val_succ,
    Fin.succAbove_zero, Fin.cons_comp_succ, Fin.cons_comp_succ_succAbove]
  change c t + (∑ k : Fin (q + 2), (-1 : ℤ) ^ (k.val + 1) •
    c (Fin.cons p (t ∘ k.succAbove))) =
    c t - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) t
  rw [differential, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [pow_succ, mul_neg_one, neg_zsmul]

theorem differential_sub {q : ℕ} (c e : Cochain ι A q) :
    differential (c - e) = differential c - differential e := by
  funext t
  simp only [differential, Pi.sub_apply, zsmul_sub, Finset.sum_sub_distrib]

@[simp] theorem differential_zero {q : ℕ} :
    differential (0 : Cochain ι A q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, zsmul_zero, Finset.sum_const_zero]

theorem differential_squared {q : ℕ} (c : Cochain ι A q) :
    differential (differential c) = 0 := by
  induction q with
  | zero =>
      funext t
      simp only [differential, Fin.sum_univ_succ, Fin.val_zero, pow_zero, one_zsmul,
        Fin.val_succ, Fin.sum_univ_zero, add_zero]
      have hsingleton (f : Fin 1 → ι) : f = fun _ => f 0 := by
        funext i
        exact congrArg f (Subsingleton.elim i 0)
      simp only [hsingleton, Function.comp_apply]
      simp [Fin.succAbove]
      abel
  | succ q ih =>
      funext t
      let p := t 0
      let u := Fin.tail t
      have ht : t = Fin.cons p u := (Fin.cons_self_tail t).symm
      rw [ht, differential_cons]
      have hfun : (fun s : Fin (q + 1 + 1) → ι => differential c (Fin.cons p s)) =
          c - differential (fun s : Fin (q + 1) → ι => c (Fin.cons p s)) := by
        funext s
        exact differential_cons c p s
      rw [hfun, differential_sub, ih]
      simp

variable [Fintype ι] [AddCommGroup K]

def Regular {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q) : Prop :=
  ∀ t, RegularOn (Set.range t) (c t)

def insertionSupport {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) : Finset (Monomial ι d) := by
  classical
  exact Finset.univ.biUnion fun p : ι => (c (Fin.cons p t)).support

def contraction {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => Finsupp.onFinset (insertionSupport c t)
    (fun a => c (Fin.cons (pivot a) t) a)
    (fun a ha => Finset.mem_biUnion.mpr
      ⟨pivot a, Finset.mem_univ _, Finsupp.mem_support_iff.mpr ha⟩)

@[simp] theorem contraction_apply {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1))
    (t : Fin (q + 1) → ι) (a : Monomial ι d) :
    contraction pivot c t a = c (Fin.cons (pivot a) t) a := rfl

theorem contraction_regular {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c) :
    Regular (contraction pivot c) := by
  intro t a ha k hk
  obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
  cases j using Fin.cases with
  | zero =>
      simp only [Fin.cons_zero] at hj
      rw [← hj] at hk
      exact False.elim ((not_lt_of_ge (hpivot a)) hk)
  | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩

theorem differential_apply {d : ℤ} {q : ℕ} (c : Cochain ι (Laurent ι K d) q)
    (t : Fin (q + 2) → ι) (a : Monomial ι d) :
    differential c t a = differential (fun s => c s a) t := by
  simp only [differential, Finsupp.finsetSum_apply, Finsupp.smul_apply]

theorem differential_regular {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (differential c) := by
  intro t a ha k hk
  by_contra hnot
  apply ha
  rw [differential_apply]
  unfold differential
  apply Finset.sum_eq_zero
  intro i _
  have hz : c (t ∘ i.succAbove) a = 0 := by
    by_contra hne
    obtain ⟨j, hj⟩ := hc (t ∘ i.succAbove) a hne k hk
    exact hnot ⟨i.succAbove j, hj⟩
  change (-1 : ℤ) ^ i.val • c (t ∘ i.succAbove) a = 0
  rw [hz, smul_zero]

theorem contraction_identity {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (c : Cochain ι (Laurent ι K d) (q + 1)) :
    contraction pivot (differential c) + differential (contraction pivot c) = c := by
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, contraction_apply, differential_apply]
  have h := differential_cons (fun s => c s a) (pivot a) t
  rw [h]
  exact sub_add_cancel _ _

theorem exact_of_pivot {d : ℤ} {q : ℕ} (pivot : Monomial ι d → ι)
    (hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a))
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  refine ⟨contraction pivot c, contraction_regular pivot hpivot c hc, ?_⟩
  have h := contraction_identity pivot c
  rw [hcocycle] at h
  have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
    funext t
    ext a
    rfl
  rw [hz, zero_add] at h
  exact h

theorem nonnegative_twist_cech_exact_all_positive {d : ℤ} (hd : 0 ≤ d) {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hcocycle : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι :=
        fun a => Classical.choose (exists_nonnegative_coordinate hd a)
      have hpivot : ∀ a : Monomial ι d, 0 ≤ a.val (pivot a) :=
        fun a => Classical.choose_spec (exists_nonnegative_coordinate hd a)
      exact exact_of_pivot pivot hpivot c hc hcocycle

end
end PiExponent.ProjectiveMonomialCechHigher

end OAI
end Source0560

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechHigher.lean
section Source0561
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechHigher.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechHigher

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open CechOne
open scoped BigOperators

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def intersection {n : ℕ} (t : Fin n → J) : Opens X := ⨅ i, U (t i)

theorem intersectionLE {m n : ℕ} (t : Fin n → J) (f : Fin m → Fin n) :
    intersection U t ≤ intersection U (t ∘ f) :=
  le_iInf fun i => iInf_le (fun j => U (t j)) (f i)

theorem faceLE {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    intersection U t ≤ intersection U (t ∘ k.succAbove) :=
  intersectionLE U t k.succAbove

abbrev Cochain (q : ℕ) :=
  ∀ t : Fin (q + 1) → J, freeOpen R (intersection U t) ⟶ M

def differential {q : ℕ} (c : Cochain R U M q) : Cochain R U M (q + 1) :=
  fun t => ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
    restrictHom R (faceLE U t k) (c (t ∘ k.succAbove))

def HasPrimitives (q : ℕ) : Prop :=
  ∀ c : Cochain R U M (q + 1), differential R U M c = 0 →
    ∃ b : Cochain R U M q, differential R U M b = c

@[simp] theorem restrictHom_refl {W : Opens X} (f : freeOpen R W ⟶ M) :
    restrictHom R le_rfl f = f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor R).map (𝟙 W) ≫ f = f
  rw [CategoryTheory.Functor.map_id]
  exact Category.id_comp f

@[simp] theorem restrictHom_sum {W V : Opens X} (h : W ≤ V)
    {T : Type*} (s : Finset T) (f : T → (freeOpen R V ⟶ M)) :
    restrictHom R h (∑ i ∈ s, f i) = ∑ i ∈ s, restrictHom R h (f i) := by
  simp only [restrictHom, Preadditive.comp_sum]

@[simp] theorem restrictHom_zsmul {W V : Opens X} (h : W ≤ V)
    (z : ℤ) (f : freeOpen R V ⟶ M) :
    restrictHom R h (z • f) = z • restrictHom R h f := by
  simp only [restrictHom, Preadditive.comp_zsmul]

def evaluate {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    ProjectiveMonomialCechHigher.Cochain L (freeOpen R W ⟶ M) q :=
  fun t => restrictHom R (le_iInf fun i => hf (t i)) (c (f ∘ t))

theorem evaluate_differential {L : Type*} (W : Opens X) (f : L → J)
    (hf : ∀ l, W ≤ U (f l)) {q : ℕ} (c : Cochain R U M q) :
    evaluate R U M W f hf (differential R U M c) =
      ProjectiveMonomialCechHigher.differential (evaluate R U M W f hf c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential]
  erw [restrictHom_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [restrictHom_zsmul, restrictHom_restrictHom]
  rfl

theorem differential_squared {q : ℕ} (c : Cochain R U M q) :
    differential R U M (differential R U M c) = 0 := by
  funext t
  let W := intersection U t
  have hf : ∀ i, W ≤ U (t i) := fun i => iInf_le (fun j => U (t j)) i
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate R U M W t hf c)) id
  rw [← evaluate_differential, ← evaluate_differential] at h
  change restrictHom R le_rfl (differential R U M (differential R U M c) t) = 0 at h
  simpa only [restrictHom_refl, Pi.zero_apply] using h

def map {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) : Cochain R U N q := fun t => c t ≫ g

theorem map_differential {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c : Cochain R U M q) :
    map R U M g (differential R U M c) = differential R U N (map R U M g c) := by
  funext t
  simp only [map, differential, Preadditive.sum_comp, Preadditive.zsmul_comp,
    restrictHom_comp]

@[simp] theorem differential_zero {q : ℕ} :
    differential R U M (0 : Cochain R U M q) = 0 := by
  funext t
  simp only [differential, Pi.zero_apply, restrictHom, comp_zero, smul_zero,
    Finset.sum_const_zero]

theorem differential_sub {q : ℕ} (c e : Cochain R U M q) :
    differential R U M (c - e) = differential R U M c - differential R U M e := by
  funext t
  simp only [differential, Pi.sub_apply, restrictHom_sub, smul_sub, Finset.sum_sub_distrib]

@[simp] theorem map_zero {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ} :
    map R U M g (0 : Cochain R U M q) = 0 := by
  funext t
  exact zero_comp

theorem map_sub {N : SheafOfModules.{u} R} (g : M ⟶ N) {q : ℕ}
    (c e : Cochain R U M q) :
    map R U M g (c - e) = map R U M g c - map R U M g e := by
  funext t
  exact Preadditive.sub_comp _ _ _

theorem map_injective {N : SheafOfModules.{u} R} (g : M ⟶ N) [Mono g] {q : ℕ} :
    Function.Injective (map R U M g (q := q)) := by
  intro c e h
  funext t
  exact (cancel_mono g).mp (congrFun h t)

theorem lift_cochain (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (q : ℕ)
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) :
    ∃ b : Cochain R U S.X₂ q, map R U S.X₂ S.g b = c := by
  classical
  choose b hb using fun t =>
    lift_of_ext_one_zero R S hS (intersection U t) (hzero t) (c t)
  exact ⟨b, funext hb⟩

theorem lift_kernel_cochain (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ} (c : Cochain R U S.X₂ q)
    (hc : map R U S.X₂ S.g c = 0) :
    ∃ b : Cochain R U S.X₁ q, map R U S.X₁ S.f b = c := by
  let : Mono S.f := hS.mono_f
  have hz (t : Fin (q + 1) → J) : c t ≫ S.g = 0 := congrFun hc t
  exact ⟨fun t => hS.exact.lift (c t) (hz t),
    funext (fun t => hS.exact.lift_f (c t) (hz t))⟩

theorem connecting_cocycle (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) {q : ℕ}
    (hzero : ∀ (t : Fin (q + 1) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (c : Cochain R U S.X₃ q) (hc : differential R U S.X₃ c = 0) :
    ∃ (b : Cochain R U S.X₂ q) (a : Cochain R U S.X₁ (q + 1)),
      map R U S.X₂ S.g b = c ∧
      map R U S.X₁ S.f a = differential R U S.X₂ b ∧
      differential R U S.X₁ a = 0 := by
  let : Mono S.f := hS.mono_f
  obtain ⟨b, hb⟩ := lift_cochain R U S hS q hzero c
  have hdb : map R U S.X₂ S.g (differential R U S.X₂ b) = 0 := by
    rw [map_differential, hb, hc]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hdb
  refine ⟨b, a, hb, ha, ?_⟩
  apply map_injective R U S.X₁ S.f
  rw [map_differential, ha, differential_squared, map_zero]

theorem primitives_of_shortExact (S : ShortComplex (SheafOfModules.{u} R))
    (hS : S.ShortExact) (q : ℕ)
    (hzero : ∀ (t : Fin (q + 2) → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hkernel : HasPrimitives R U S.X₁ (q + 1))
    (hmiddle : HasPrimitives R U S.X₂ q) : HasPrimitives R U S.X₃ q := by
  intro c hc
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c hc
  obtain ⟨e, he⟩ := hkernel a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨v, hv⟩ := hmiddle _ hcorrected
  refine ⟨map R U S.X₂ S.g v, ?_⟩
  rw [← map_differential, hv, map_sub, hb]
  have hz : map R U S.X₂ S.g (map R U S.X₁ S.f e) = 0 := by
    funext t
    change (e t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  rw [hz, sub_zero]

theorem insertLE (p : J) (hp : ∀ i, U i ≤ U p) {q : ℕ} (t : Fin (q + 1) → J) :
    intersection U t ≤ intersection U (Fin.cons p t) := by
  apply le_iInf
  intro i
  cases i using Fin.cases with
  | zero => exact (iInf_le (fun j => U (t j)) 0).trans (hp (t 0))
  | succ i => exact iInf_le (fun j => U (t j)) i

def contraction (p : J) (hp : ∀ i, U i ≤ U p) {q : ℕ}
    (c : Cochain R U M (q + 1)) : Cochain R U M q :=
  fun t => restrictHom R (insertLE U p hp t) (c (Fin.cons p t))

theorem restrict_cochain_congr {q : ℕ} (c : Cochain R U M q)
    {t t' : Fin (q + 1) → J} (ht : t = t') {W : Opens X}
    (h : W ≤ intersection U t) (h' : W ≤ intersection U t') :
    restrictHom R h (c t) = restrictHom R h' (c t') := by
  subst t'
  rfl

def sectionZero (c : Cochain R U M 0) (i : J) : freeOpen R (U i) ⟶ M :=
  restrictHom R (le_iInf fun _ => le_rfl) (c (fun _ => i))

private theorem scalar_differential_zero_degree {B I : Type*} [AddCommGroup B]
    (c : ProjectiveMonomialCechHigher.Cochain I B 0) (i j : I) :
    ProjectiveMonomialCechHigher.differential c (Fin.cons i (fun _ => j)) =
      c (fun _ => j) - c (fun _ => i) := by
  have hsingleton (f : Fin 1 → I) : f = fun _ => f 0 := by
    funext k
    exact congrArg f (Subsingleton.elim k 0)
  simp only [ProjectiveMonomialCechHigher.differential]
  simp only [hsingleton, Function.comp_apply]
  simp [Fin.succAbove, sub_eq_add_neg]

theorem sectionZero_compatible (c : Cochain R U M 0)
    (hc : differential R U M c = 0) (i j : J) :
    restrictHom R inf_le_left (sectionZero R U M c i) =
      restrictHom R inf_le_right (sectionZero R U M c j) := by
  let W := U i ⊓ U j
  let f : Fin 2 → J := Fin.cons i (fun _ => j)
  have hf : ∀ l, W ≤ U (f l) := by
    intro l
    cases l using Fin.cases with
    | zero => exact inf_le_left
    | succ l => exact inf_le_right
  have h := evaluate_differential R U M W f hf c
  rw [hc] at h
  have h' := congrFun h (Fin.cons 0 (fun _ => 1))
  have hz : evaluate R U M W f hf (0 : Cochain R U M 1)
      (Fin.cons 0 (fun _ => 1)) = 0 := comp_zero
  rw [hz, scalar_differential_zero_degree] at h'
  have he := (sub_eq_zero.mp h'.symm).symm
  have h0 : f ∘ (fun _ : Fin 1 => (0 : Fin 2)) = (fun _ => i) := by
    funext k
    rfl
  have h1 : f ∘ (fun _ : Fin 1 => (1 : Fin 2)) = (fun _ => j) := by
    funext k
    rfl
  calc
    restrictHom R inf_le_left (sectionZero R U M c i) =
        evaluate R U M W f hf c (fun _ => 0) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact (restrict_cochain_congr R U M c h0 _ _).symm
    _ = evaluate R U M W f hf c (fun _ => 1) := he
    _ = restrictHom R inf_le_right (sectionZero R U M c j) := by
      simp only [sectionZero, evaluate]
      erw [restrictHom_restrictHom]
      exact restrict_cochain_congr R U M c h1 _ _

theorem glue_zero_cocycle (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ g : freeOpen R V ⟶ M,
      ∀ i, restrictHom R (hUV i) g = sectionZero R U M c i := by
  exact hom_glue R U V hUV hcover M (sectionZero R U M c)
    (sectionZero_compatible R U M c hc)

def augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : Cochain R U M 0 :=
  fun t => restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f

@[simp] theorem augmentation_closed (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) : differential R U M (augmentation R U M V hUV f) = 0 := by
  funext t
  simp only [differential, augmentation, Pi.zero_apply]
  calc
    _ = ∑ k : Fin 2, (-1 : ℤ) ^ k.val •
        restrictHom R ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))) f := by
      apply Finset.sum_congr rfl
      intro k _
      exact congrArg (fun g : freeOpen R (intersection U t) ⟶ M => (-1 : ℤ) ^ k.val • g)
        (restrictHom_restrictHom R _ _ f)
    _ = 0 := by rw [Fin.sum_univ_two]; simp

@[simp] theorem sectionZero_augmentation (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (f : freeOpen R V ⟶ M) (i : J) :
    sectionZero R U M (augmentation R U M V hUV f) i = restrictHom R (hUV i) f := by
  simp only [sectionZero, augmentation]
  exact restrictHom_restrictHom R _ _ f

theorem shortExact_global_lift (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (S : ShortComplex (SheafOfModules.{u} R)) (hS : S.ShortExact)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) S.X₁ 1), x = 0)
    (hprimitive : HasPrimitives R U S.X₁ 0) (f : freeOpen R V ⟶ S.X₃) :
    ∃ g : freeOpen R V ⟶ S.X₂, g ≫ S.g = f := by
  let c := augmentation R U S.X₃ V hUV f
  obtain ⟨b, a, hb, ha, hclosed⟩ := connecting_cocycle R U S hS hzero c
    (augmentation_closed R U S.X₃ V hUV f)
  obtain ⟨e, he⟩ := hprimitive a hclosed
  have hcorrected : differential R U S.X₂ (b - map R U S.X₁ S.f e) = 0 := by
    rw [differential_sub, ← map_differential, he, ha, sub_self]
  obtain ⟨g, hg⟩ := glue_zero_cocycle R U S.X₂ V hUV hcover _ hcorrected
  refine ⟨g, ?_⟩
  apply hom_ext R U V hUV hcover S.X₃
  intro i
  rw [restrictHom_comp, hg i]
  change (restrictHom R _ (b (fun _ => i) - e (fun _ => i) ≫ S.f)) ≫ S.g = _
  erw [restrictHom_sub, Preadditive.sub_comp, ← restrictHom_comp,
    ← restrictHom_comp, Category.assoc, S.zero, comp_zero]
  simp only [restrictHom, comp_zero, sub_zero]
  have hi := congrFun hb (fun _ => i)
  change b (fun _ => i) ≫ S.g = c (fun _ => i) at hi
  rw [hi]
  exact sectionZero_augmentation R U S.X₃ V hUV f i

theorem ext_one_eq_zero (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ (t : Fin 1 → J)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M 1), x = 0)
    (hprimitive : HasPrimitives R U M 0)
    (x : Ext.{u+1} (freeOpen R V) M 1) : x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
  obtain ⟨g, rfl⟩ := shortExact_global_lift R U V hUV hcover S hS hzero hprimitive f
  rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    hS.comp_extClass, Ext.comp_zero] at hy
  exact hy.symm

theorem ext_succ_eq_zero_of_injective_cech
    (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hinjective : ∀ (I : SheafOfModules.{u} R) [Injective I] (q : ℕ),
      HasPrimitives R U I q)
    (n : ℕ)
    (hlocal : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
      (x : Ext.{u+1} (freeOpen R (intersection U t)) M (k + 1)), x = 0)
    (hprimitive : HasPrimitives R U M n)
    (x : Ext.{u+1} (freeOpen R V) M (n + 1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
      exact ext_one_eq_zero R U M V hUV hcover (fun t x => hlocal 0 t 0 x) hprimitive x
  | succ n ih =>
      let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
      have hS : S.ShortExact :=
        { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
      have hlocal' : ∀ (q : ℕ) (t : Fin (q + 1) → J) (k : ℕ)
          (y : Ext.{u+1} (freeOpen R (intersection U t)) S.X₃ (k + 1)), y = 0 := by
        intro q t k y
        obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
          (freeOpen R (intersection U t)) hS y (n₁ := k + 2) rfl (hlocal q t (k + 1) _)
        rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
        exact hz.symm
      have hprimitive' : HasPrimitives R U S.X₃ n :=
        primitives_of_shortExact R U S hS n
          (fun t y => hlocal (n + 1) t 0 y) hprimitive (hinjective S.X₂ n)
      obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (freeOpen R V) hS x
        (Ext.eq_zero_of_injective _) (n₀ := n + 1) rfl
      rw [ih S.X₃ hlocal' hprimitive' y, Ext.zero_comp] at hy
      exact hy.symm

abbrev schemeFreeOpen (Y : Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero_of_injective_cech
    (Y : Scheme.{u}) [IsNoetherian Y] (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J), IsAffineOpen (intersection W t))
    (hinjective : ∀ (I : Y.Modules) [Injective I] (q : ℕ),
      HasPrimitives Y.ringCatSheaf W I q)
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact ext_succ_eq_zero_of_injective_cech Y.ringCatSheaf W A V hWV hcover
    hinjective n (fun q t k y =>
      PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
        (intersection W t) (haffine q t) A k y) hprimitive x

end
end PiExponent.GeometrySupport.CechHigher

end OAI
end Source0561

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FreeCechResolution.lean
section Source0562
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FreeCechResolution.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechResolution

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace

universe u

def tupleSimplex (V : Type u) : SimplicialObject (Type u) where
  obj n := ToType n.unop → V
  map f := ↾fun t => t ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def tupleAugmented (V : Type u) : SimplicialObject.Augmented (Type u) :=
  (tupleSimplex V).augmentOfIsTerminal Types.isTerminalPUnit

def tupleExtraDegeneracy {V : Type u} (p : V) :
    (tupleAugmented V).ExtraDegeneracy where
  s' := ↾fun _ _ => p
  s n := ↾fun t => Fin.cons p t
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext t
    funext i
    fin_cases i
    rfl
  s_comp_δ₀ n := by
    ext t
    funext i
    rfl
  s_comp_δ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 3) → V) (i.succ.succAbove j.succ) = t (i.succAbove j)
      simp only [Fin.succ_succAbove_succ]
      rfl
  s_comp_σ n i := by
    ext t
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · rfl
    · change (Fin.cons p t : Fin (n + 2) → V) (i.succ.predAbove j.succ) = t (i.predAbove j)
      simp only [Fin.succ_predAbove_succ]
      rfl

def freeTupleComplex (R : RingCat.{u}) (V : Type u) : ChainComplex (ModuleCat R) ℕ :=
  AlternatingFaceMapComplex.obj (tupleSimplex V ⋙ ModuleCat.free R)

theorem freeTupleComplex_exact (R : RingCat.{u}) (V : Type u) (q : ℕ) :
    (freeTupleComplex R V).ExactAt (q + 1) := by
  classical
  cases isEmpty_or_nonempty V with
  | inl h =>
    let : IsEmpty (Fin (q + 2) → V) := ⟨fun t => isEmptyElim (t 0)⟩
    change ((freeTupleComplex R V).sc (q + 1)).Exact
    apply ShortComplex.exact_of_isZero_X₂
    have hz : Subsingleton (((Fin (q + 2) → V) →₀ R)) := inferInstance
    exact ModuleCat.isZero_of_subsingleton (ModuleCat.of R ((Fin (q + 2) → V) →₀ R))
  | inr h =>
    let p : V := Classical.choice h
    let e := ((tupleExtraDegeneracy p).map (ModuleCat.free R)).homotopyEquiv
    apply (exactAt_iff_of_quasiIsoAt e.hom (q + 1)).2
    exact HomologicalComplex.exactAt_single_obj (ComplexShape.down ℕ) 0 _
      (q + 1) (by omega)

def coverVertices {X : TopCat.{u}} {ι : Type u} (U : ι → Opens X) :
    (Opens X)ᵒᵖ ⥤ Type u where
  obj W := {i : ι // W.unop ≤ U i}
  map f := ↾fun i => ⟨i.val, (leOfHom f.unop).trans i.property⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def tuplePresheaf {C : Type u} [Category.{u} C] (V : Cᵒᵖ ⥤ Type u) :
    SimplicialObject (Cᵒᵖ ⥤ Type u) where
  obj n :=
    { obj W := ToType n.unop → V.obj W
      map f := ↾fun t i => V.map f (t i)
      map_id W := by ext t i; simp
      map_comp f g := by ext t i; simp }
  map f := { app W := ↾fun t => t ∘ f.unop.toOrderHom }
  map_id _ := rfl
  map_comp _ _ := rfl

def freePresheafComplex {C : Type u} [Category.{u} C] (R : Cᵒᵖ ⥤ RingCat.{u})
    (V : Cᵒᵖ ⥤ Type u) : ChainComplex (PresheafOfModules.{u} R) ℕ :=
  AlternatingFaceMapComplex.obj (tuplePresheaf V ⋙ PresheafOfModules.free R)

theorem exact_of_objectwise {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (S : ShortComplex (PresheafOfModules.{u} R))
    (hS : ∀ W, (S.map (PresheafOfModules.evaluation R W)).Exact) : S.Exact := by
  simp only [ShortComplex.exact_iff_isZero_homology] at hS ⊢
  rw [IsZero.iff_id_eq_zero]
  ext1 W
  apply (IsZero.of_iso (hS W)
    (S.mapHomologyIso (PresheafOfModules.evaluation R W)).symm).eq_of_src

theorem evaluation_freePresheafComplex {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (W : Cᵒᵖ) :
    ((PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (freePresheafComplex R V) = freeTupleComplex (R.obj W) (V.obj W) := by
  change ((alternatingFaceMapComplex _ ⋙
    (PresheafOfModules.evaluation R W).mapHomologicalComplex _).obj
      (tuplePresheaf V ⋙ PresheafOfModules.free R)) = _
  rw [map_alternatingFaceMapComplex]
  rfl

theorem freePresheafComplex_exact {C : Type u} [Category.{u} C]
    (R : Cᵒᵖ ⥤ RingCat.{u}) (V : Cᵒᵖ ⥤ Type u) (q : ℕ) :
    (freePresheafComplex R V).ExactAt (q + 1) := by
  change ((freePresheafComplex R V).sc (q + 1)).Exact
  apply exact_of_objectwise R
  intro W
  have h := freeTupleComplex_exact (R.obj W) (V.obj W) q
  rw [← evaluation_freePresheafComplex R V W] at h
  exact h

def freeSheafComplex {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) : ChainComplex (SheafOfModules.{u} R) ℕ :=
  ((PresheafOfModules.sheafification (𝟙 R.obj)).mapHomologicalComplex _).obj
    (freePresheafComplex R.obj V)

theorem freeSheafComplex_exact {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (V : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (freeSheafComplex R V).ExactAt (q + 1) := by
  change (((freePresheafComplex R.obj V).sc (q + 1)).map
    (PresheafOfModules.sheafification (𝟙 R.obj))).Exact
  exact (freePresheafComplex_exact R.obj V q).map _

end
end PiExponent.GeometrySupport.FreeCechResolution

end OAI
end Source0562

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FreeCechSections.lean
section Source0563
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FreeCechSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.FreeCechSections

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechHigher FreeCechResolution
open scoped Simplicial BigOperators

universe u
variable {X : TopCat.{u}} {J : Type u} (U : J → Opens X)

def canonicalTuple {q : ℕ} (t : Fin (q + 1) → J) :
    ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).obj (op (intersection U t)) :=
  fun i => ⟨t i, iInf_le (fun j => U (t j)) i⟩

def tupleNatEquiv (F : (Opens X)ᵒᵖ ⥤ Type u) (q : ℕ) :
    (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)) ⟶ F) ≃
      (∀ t : Fin (q + 1) → J, F.obj (op (intersection U t))) where
  toFun a t := a.app _ (canonicalTuple U t)
  invFun s :=
    { app W := ↾fun v =>
        F.map (homOfLE (le_iInf fun i => (v i).property)).op (s (fun i => (v i).val))
      naturality W V f := by
        ext v
        let t : Fin (q + 1) → J := fun i => (v i).val
        let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
        exact F.map_comp_apply (homOfLE h).op f (s t) }
  left_inv a := by
    ext W v
    let t : Fin (q + 1) → J := fun i => (v i).val
    let h : W.unop ≤ intersection U t := le_iInf fun i => (v i).property
    have he : (((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)).map
        (homOfLE h).op) (canonicalTuple U t) = v := by
      funext i
      apply Subtype.ext
      rfl
    have hn := NatTrans.naturality_apply a (homOfLE h).op (canonicalTuple U t)
    rw [he] at hn
    exact hn.symm
  right_inv s := by
    funext t
    change F.map (𝟙 (op (intersection U t))) (s t) = s t
    rw [CategoryTheory.Functor.map_id]
    rfl

variable (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  (M : SheafOfModules.{u} R)

def freeTerm (q : ℕ) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj ((tuplePresheaf (coverVertices U)).obj (op ⦋q⦌)))

def sectionValuesEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃
    (∀ t : Fin (q + 1) → J, M.val.obj (op (intersection U t))) :=
  ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeHomEquiv).trans (tupleNatEquiv U _ q)

def sectionsEquiv (q : ℕ) : (freeTerm U R q ⟶ M) ≃ Cochain R U M q :=
  (sectionValuesEquiv U R M q).trans
    (Equiv.piCongrRight fun t => (freeOpenEquiv R M (intersection U t)).symm)

def tupleEmbedding {q : ℕ} (t : Fin (q + 1) → J) :
    yoneda.obj (intersection U t) ⟶ (tuplePresheaf (coverVertices U)).obj (op ⦋q⦌) :=
  yonedaEquiv.symm (canonicalTuple U t)

def generator {q : ℕ} (t : Fin (q + 1) → J) :
    freeOpen R (intersection U t) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (tupleEmbedding U t))

theorem sectionsEquiv_apply (q : ℕ) (f : freeTerm U R q ⟶ M) (t : Fin (q + 1) → J) :
    sectionsEquiv U R M q f t = generator U R t ≫ f := by
  apply (freeOpenEquiv R M (intersection U t)).injective
  simp only [sectionsEquiv, Equiv.trans_apply, Equiv.piCongrRight_apply, Pi.map_apply,
    Equiv.apply_symm_apply]
  let g := (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f
  change (PresheafOfModules.freeHomEquiv g).app _ (canonicalTuple U t) =
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) (generator U R t ≫ f))
  symm
  have hs := congrArg PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv_naturality_left
      ((PresheafOfModules.free R.obj).map (tupleEmbedding U t)) f)
  have hf := congrArg yonedaEquiv
    ((PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
      (tupleEmbedding U t) g)
  exact hs.trans (hf.trans (yonedaEquiv_comp (tupleEmbedding U t)
    (PresheafOfModules.freeHomEquiv g)))

theorem tupleEmbedding_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    tupleEmbedding U t ≫ (tuplePresheaf (coverVertices U)).δ k =
      yoneda.map (homOfLE (faceLE U t k)) ≫ tupleEmbedding U (t ∘ k.succAbove) := by
  simp only [tupleEmbedding]
  ext W v
  funext i
  apply Subtype.ext
  rfl

def freeFace (q : ℕ) (k : Fin (q + 2)) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map ((tuplePresheaf (coverVertices U)).δ k))

theorem generator_face {q : ℕ} (t : Fin (q + 2) → J) (k : Fin (q + 2)) :
    generator U R t ≫ freeFace U R q k =
      freeOpenMap R (homOfLE (faceLE U t k)) ≫ generator U R (t ∘ k.succAbove) := by
  simp only [generator, freeFace]
  let F : ((Opens X)ᵒᵖ ⥤ Type u) ⥤ SheafOfModules.{u} R :=
    PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
  change F.map (tupleEmbedding U t) ≫ F.map ((tuplePresheaf (coverVertices U)).δ k) =
    F.map (yoneda.map (homOfLE (faceLE U t k))) ≫ F.map (tupleEmbedding U (t ∘ k.succAbove))
  exact (F.map_comp _ _).symm.trans
    ((congrArg (fun f => F.map f) (tupleEmbedding_face U t k)).trans (F.map_comp _ _))

def boundary (q : ℕ) : freeTerm U R (q + 1) ⟶ freeTerm U R q :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((freePresheafComplex R.obj (coverVertices U)).d (q + 1) q)

theorem boundary_eq_sum (q : ℕ) :
    boundary U R q = ∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val • freeFace U R q k := by
  let : (PresheafOfModules.sheafification (𝟙 R.obj)).Additive :=
    CategoryTheory.Functor.additive_of_preserves_binary_products _
  dsimp only [boundary, freePresheafComplex, freeTerm]
  rw [AlternatingFaceMapComplex.obj_d_eq]
  rw [CategoryTheory.Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [CategoryTheory.Functor.map_zsmul]
  rfl

theorem boundary_squared (q : ℕ) : boundary U R (q + 1) ≫ boundary U R q = 0 := by
  unfold boundary
  erw [← CategoryTheory.Functor.map_comp, HomologicalComplex.d_comp_d,
    CategoryTheory.Functor.map_zero]
  rfl

def termShortComplex (q : ℕ) : ShortComplex (SheafOfModules.{u} R) :=
  ShortComplex.mk (boundary U R (q + 1)) (boundary U R q) (boundary_squared U R q)

theorem sectionsEquiv_boundary (q : ℕ) (f : freeTerm U R q ⟶ M) :
    sectionsEquiv U R M (q + 1) (boundary U R q ≫ f) =
      differential R U M (sectionsEquiv U R M q f) := by
  funext t
  rw [sectionsEquiv_apply, ← Category.assoc, boundary_eq_sum, Preadditive.comp_sum,
    Preadditive.sum_comp]
  simp only [Preadditive.comp_zsmul, Preadditive.zsmul_comp, generator_face,
    Category.assoc, CechHigher.differential, sectionsEquiv_apply, CechOne.restrictHom]

theorem hasPrimitives_of_exact [Injective M] (q : ℕ)
    (hexact : (termShortComplex U R q).Exact) : HasPrimitives R U M q := by
  intro c hc
  let f := (sectionsEquiv U R M (q + 1)).symm c
  have hf : boundary U R (q + 1) ≫ f = 0 := by
    apply (sectionsEquiv U R M (q + 2)).injective
    rw [sectionsEquiv_boundary]
    have he : sectionsEquiv U R M (q + 1) f = c :=
      (sectionsEquiv U R M (q + 1)).apply_symm_apply c
    rw [he, hc]
    funext t
    rw [sectionsEquiv_apply, comp_zero]
    rfl
  let g : freeTerm U R q ⟶ M := hexact.descToInjective f hf
  refine ⟨sectionsEquiv U R M q g, ?_⟩
  rw [← sectionsEquiv_boundary]
  exact (congrArg (fun f : freeTerm U R (q + 1) ⟶ M => sectionsEquiv U R M (q + 1) f)
    (hexact.comp_descToInjective f hf)).trans
      ((sectionsEquiv U R M (q + 1)).apply_symm_apply c)

theorem injective_hasPrimitives [Injective M] (q : ℕ) : HasPrimitives R U M q := by
  apply hasPrimitives_of_exact U R M q
  have h := freeSheafComplex_exact R (coverVertices U) q
  exact (HomologicalComplex.exactAt_iff'
    (K := freeSheafComplex R (coverVertices U)) (i := q + 2) (j := q + 1) (k := q)
    (by simp) (by simp)).mp h

abbrev schemeFreeOpen (Y : AlgebraicGeometry.Scheme.{u}) (V : Y.Opens) : Y.Modules :=
  freeOpen Y.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem affine_ext_succ_eq_zero
    (Y : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian Y]
    (A : Y.Modules) [A.IsQuasicoherent]
    (W : J → Y.Opens) (V : Y.Opens) (hWV : ∀ i, W i ≤ V)
    (hcover : V ≤ ⨆ i, W i)
    (haffine : ∀ (q : ℕ) (t : Fin (q + 1) → J),
      AlgebraicGeometry.IsAffineOpen (intersection W t))
    (n : ℕ) (hprimitive : HasPrimitives Y.ringCatSheaf W A n)
    (x : CategoryTheory.Abelian.Ext.{u+1} (C := Y.Modules)
      (schemeFreeOpen Y V) A (n + 1)) : x = 0 := by
  exact affine_ext_succ_eq_zero_of_injective_cech Y A W V hWV hcover haffine
    (fun I hI q => @injective_hasPrimitives _ _ W Y.ringCatSheaf I hI q) n hprimitive x

end
end PiExponent.GeometrySupport.FreeCechSections

end OAI
end Source0563

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechLinear.lean
section Source0564
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechLinear.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechLinear

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped BigOperators AlgebraicGeometry

universe v
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type v} [Field K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

@[instance_reducible] def freeOpenHomAddCommGroup (V : X.Opens) (M : X.Modules) :
    AddCommGroup (freeOpen X.ringCatSheaf V ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ M))

@[instance_reducible] def higherCochainAddCommGroup (M : X.Modules) (q : ℕ) :
    AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (CechHigher.intersection U t) ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup

@[instance_reducible] def freeOpenHomModule (V : X.Opens) (M : X.Modules) :
    Module Γ(X, ⊤) (freeOpen X.ringCatSheaf V ⟶ M) :=
  sheafHomModule X (schemeFreeOpen V) M

attribute [local instance] freeOpenHomModule

def Cochain (_ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) : Type :=
  CechHigher.Cochain X.ringCatSheaf U M q

instance cochainAddCommGroup (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    AddCommGroup (Cochain U ρ M q) :=
  inferInstanceAs (AddCommGroup (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainGlobalModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module Γ(X, ⊤) (Cochain U ρ M q) :=
  letI (t : Fin (q + 1) → J) :
      Module Γ(X, ⊤) (freeOpen X.ringCatSheaf (CechHigher.intersection U t) ⟶ M) :=
    sheafHomModule X _ M
  inferInstanceAs (Module Γ(X, ⊤) (CechHigher.Cochain X.ringCatSheaf U M q))

instance cochainModule (ρ : K →+* Γ(X, ⊤)) (M : X.Modules) (q : ℕ) :
    Module K (Cochain U ρ M q) :=
  Module.compHom _ ρ

variable (ρ : K →+* Γ(X, ⊤)) (M : X.Modules)

def differentialLinear (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ M (q + 1) where
  toFun := CechHigher.differential X.ringCatSheaf U M
  map_add' c e := by
    let D : Cochain U ρ M q → Cochain U ρ M (q + 1) :=
      CechHigher.differential X.ringCatSheaf U M
    have hsub (c e : Cochain U ρ M q) : D (c - e) = D c - D e :=
      CechHigher.differential_sub X.ringCatSheaf U M c e
    have hzero : D 0 = 0 := CechHigher.differential_zero X.ringCatSheaf U M
    have hn : D (-e) = -D e := by
      simpa only [zero_sub, hzero] using hsub 0 e
    change D (c + e) = D c + D e
    simpa only [sub_neg_eq_add, hn] using hsub c (-e)
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    change (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
        (ρ r • c (t ∘ k.succAbove))) =
      ρ r • (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        CechOne.restrictHom X.ringCatSheaf (CechHigher.faceLE U t k)
          (c (t ∘ k.succAbove)))
    simp only [CechOne.restrictHom, Finset.smul_sum, smul_comm (ρ r)]
    apply Finset.sum_congr rfl
    intro k _
    exact congrArg (fun f : schemeFreeOpen (CechHigher.intersection U t) ⟶ M =>
      (-1 : ℤ) ^ k.val • f)
      (Linear.comp_smul (C := X.Modules) _ _ _
        (freeOpenMap X.ringCatSheaf (homOfLE (CechHigher.faceLE U t k))) (ρ r)
        (c (t ∘ k.succAbove)))

@[simp] theorem differentialLinear_apply (q : ℕ) (c : Cochain U ρ M q) :
    differentialLinear U ρ M q c = CechHigher.differential X.ringCatSheaf U M c := rfl

def cycles (q : ℕ) : Submodule K (Cochain U ρ M q) :=
  (differentialLinear U ρ M q).ker

@[simp] theorem mem_cycles (q : ℕ) (c : Cochain U ρ M q) :
    c ∈ cycles U ρ M q ↔ CechHigher.differential X.ringCatSheaf U M c = 0 := Iff.rfl

def boundaryToCycles (q : ℕ) : Cochain U ρ M q →ₗ[K] cycles U ρ M (q + 1) :=
  (differentialLinear U ρ M q).codRestrict (cycles U ρ M (q + 1))
    (fun c => CechHigher.differential_squared X.ringCatSheaf U M c)

@[simp] theorem boundaryToCycles_val (q : ℕ) (c : Cochain U ρ M q) :
    (boundaryToCycles U ρ M q c).val =
      CechHigher.differential X.ringCatSheaf U M c := rfl

variable {M} {N P : X.Modules}

def mapLinear (g : M ⟶ N) (q : ℕ) : Cochain U ρ M q →ₗ[K] Cochain U ρ N q where
  toFun := CechHigher.map X.ringCatSheaf U M g
  map_add' c e := by
    funext t
    change (c t + e t) ≫ g = c t ≫ g + e t ≫ g
    exact Preadditive.add_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (c t) (e t) g
  map_smul' r c := by
    let (A B : SheafOfModules.{0} X.ringCatSheaf) : Module Γ(X, ⊤) (A ⟶ B) := sheafHomModule X A B
    let : Linear Γ(X, ⊤) (SheafOfModules.{0} X.ringCatSheaf) := sheafLinear X
    funext t
    exact Linear.smul_comp (C := SheafOfModules.{0} X.ringCatSheaf) _ _ _ (ρ r) (c t) g

@[simp] theorem mapLinear_apply (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g q c = CechHigher.map X.ringCatSheaf U M g c := rfl

@[simp] theorem mapLinear_comp (g : M ⟶ N) (h : N ⟶ P) (q : ℕ) :
    mapLinear U ρ (g ≫ h) q = (mapLinear U ρ h q).comp (mapLinear U ρ g q) := by
  apply LinearMap.ext
  intro c
  funext t
  exact (Category.assoc (c t) g h).symm

@[simp] theorem mapLinear_zero (q : ℕ) :
    mapLinear U ρ (0 : M ⟶ N) q = 0 := by
  apply LinearMap.ext
  intro c
  funext t
  exact comp_zero (C := SheafOfModules.{0} X.ringCatSheaf)

theorem mapLinear_differential (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapLinear U ρ g (q + 1) (differentialLinear U ρ M q c) =
      differentialLinear U ρ N q (mapLinear U ρ g q c) :=
  CechHigher.map_differential X.ringCatSheaf U M g c

def mapCycles (g : M ⟶ N) (q : ℕ) : cycles U ρ M q →ₗ[K] cycles U ρ N q :=
  ((mapLinear U ρ g q).comp (cycles U ρ M q).subtype).codRestrict
    (cycles U ρ N q) (fun c => by
      change CechHigher.differential X.ringCatSheaf U N
        (CechHigher.map X.ringCatSheaf U M g c.val) = 0
      have hc : CechHigher.differential X.ringCatSheaf U M c.val = 0 := c.property
      exact (CechHigher.map_differential X.ringCatSheaf U M g c.val).symm.trans
        ((congrArg (fun c : Cochain U ρ M (q + 1) => CechHigher.map X.ringCatSheaf U M g c) hc).trans
          (CechHigher.map_zero X.ringCatSheaf U M g)))

@[simp] theorem mapCycles_val (g : M ⟶ N) (q : ℕ) (c : cycles U ρ M q) :
    (mapCycles U ρ g q c).val = mapLinear U ρ g q c.val := rfl

theorem mapCycles_boundary (g : M ⟶ N) (q : ℕ) (c : Cochain U ρ M q) :
    mapCycles U ρ g (q + 1) (boundaryToCycles U ρ M q c) =
      boundaryToCycles U ρ N q (mapLinear U ρ g q c) := by
  apply Subtype.ext
  exact mapLinear_differential U ρ g q c

variable (M)

theorem boundaryToCycles_surjective [hM : Injective M] (q : ℕ) :
    Function.Surjective (boundaryToCycles U ρ M q) := by
  intro c
  obtain ⟨b, hb⟩ := @FreeCechSections.injective_hasPrimitives _ J U X.ringCatSheaf M hM q
    c.val c.property
  exact ⟨b, Subtype.ext hb⟩

def primitive [Injective M] (q : ℕ) :
    cycles U ρ M (q + 1) →ₗ[K] Cochain U ρ M q :=
  Classical.choose ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))

@[simp] theorem boundaryToCycles_primitive [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    boundaryToCycles U ρ M q (primitive U ρ M q c) = c := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((boundaryToCycles U ρ M q).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (boundaryToCycles_surjective U ρ M q)))) c

@[simp] theorem primitive_spec [Injective M] (q : ℕ)
    (c : cycles U ρ M (q + 1)) :
    CechHigher.differential X.ringCatSheaf U M (primitive U ρ M q c) = c.val :=
  congrArg Subtype.val (boundaryToCycles_primitive U ρ M q c)

end
end PiExponent.GeometrySupport.CechLinear

end OAI
end Source0564

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechZero.lean
section Source0565
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechZero.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem sectionZero_restrict (c : CechHigher.Cochain R U M 0) (t : Fin 1 → J) :
    restrictHom R (iInf_le (fun j => U (t j)) 0) (sectionZero R U M c (t 0)) = c t := by
  simp only [sectionZero]
  erw [restrictHom_restrictHom]
  have ht : (fun _ : Fin 1 => t 0) = t := by
    funext k
    exact congrArg t (Subsingleton.elim 0 k)
  exact (restrict_cochain_congr R U M c ht
    ((iInf_le (fun j => U (t j)) 0).trans (le_iInf fun _ => le_rfl)) (le_refl _)).trans
    (restrictHom_refl R M (c t))

theorem sectionZero_injective : Function.Injective (sectionZero R U M) := by
  intro c d h
  funext t
  rw [← sectionZero_restrict R U M c t, ← sectionZero_restrict R U M d t, h]

theorem augmentation_injective (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    Function.Injective (augmentation R U M V hUV) := by
  intro f g h
  apply hom_ext R U V hUV hcover M f g
  intro i
  have hi := congrArg (fun c => sectionZero R U M c i) h
  simpa only [sectionZero_augmentation] using hi

theorem augmentation_exists (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (c : CechHigher.Cochain R U M 0)
    (hc : differential R U M c = 0) :
    ∃ f : freeOpen R V ⟶ M, augmentation R U M V hUV f = c := by
  obtain ⟨f, hf⟩ := glue_zero_cocycle R U M V hUV hcover c hc
  refine ⟨f, sectionZero_injective R U M ?_⟩
  funext i
  rw [sectionZero_augmentation]
  exact hf i

theorem augmentation_comp (V : Opens X) (hUV : ∀ i, U i ≤ V)
    {N : SheafOfModules.{u} R} (f : freeOpen R V ⟶ M) (g : M ⟶ N) :
    augmentation R U N V hUV (f ≫ g) =
      CechHigher.map R U M g (augmentation R U M V hUV f) := by
  funext t
  exact restrictHom_comp R _ f g

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
open scoped AlgebraicGeometry

variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
  {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤)) (M : X.Modules)

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

def augmentationLinear (V : X.Opens) (hUV : ∀ i, U i ≤ V) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) →ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  refine {
    toFun := fun f => ⟨CechHigher.augmentation X.ringCatSheaf U M V hUV f,
      CechHigher.augmentation_closed X.ringCatSheaf U M V hUV f⟩
    map_add' := ?_
    map_smul' := ?_ }
  · intro f g
    apply Subtype.ext
    funext t
    exact CechOne.restrictHom_add X.ringCatSheaf _ f g
  · intro r f
    apply Subtype.ext
    funext t
    exact Linear.comp_smul (C := X.Modules) _ _ _
      (freeOpenMap X.ringCatSheaf
        (homOfLE ((iInf_le (fun j => U (t j)) 0).trans (hUV (t 0))))) (ρ r) f

@[simp] theorem augmentationLinear_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (f : schemeFreeOpen V ⟶ M) :
    (augmentationLinear U ρ M V hUV f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

def sectionsEquiv (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
    letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
    (schemeFreeOpen V ⟶ M) ≃ₗ[K] CechLinear.cycles U ρ M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  apply LinearEquiv.ofBijective (augmentationLinear U ρ M V hUV)
  constructor
  · intro f g h
    exact augmentation_injective X.ringCatSheaf U M V hUV hcover (congrArg Subtype.val h)
  · intro c
    obtain ⟨f, hf⟩ := augmentation_exists X.ringCatSheaf U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩

@[simp] theorem sectionsEquiv_val (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : schemeFreeOpen V ⟶ M) :
    (sectionsEquiv U ρ M V hUV hcover f).val =
      CechHigher.augmentation X.ringCatSheaf U M V hUV f := rfl

theorem sectionsEquiv_comp (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules}
    (f : schemeFreeOpen V ⟶ M) (g : M ⟶ N) :
    sectionsEquiv U ρ N V hUV hcover (f ≫ g) =
      CechLinear.mapCycles U ρ g 0 (sectionsEquiv U ρ M V hUV hcover f) := by
  apply Subtype.ext
  exact augmentation_comp X.ringCatSheaf U M V hUV f g

theorem sectionsEquiv_symm_mapCycles (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) {N : X.Modules} (g : M ⟶ N)
    (c : CechLinear.cycles U ρ M 0) :
    (sectionsEquiv U ρ N V hUV hcover).symm (CechLinear.mapCycles U ρ g 0 c) =
      (sectionsEquiv U ρ M V hUV hcover).symm c ≫ g := by
  apply (sectionsEquiv U ρ N V hUV hcover).injective
  rw [LinearEquiv.apply_symm_apply, sectionsEquiv_comp, LinearEquiv.apply_symm_apply]

end PiExponent.GeometrySupport.CechZero

end

end OAI
end Source0565

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechExtFinite.lean
section Source0566
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechExtFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite Abelian
open PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
variable {X : Scheme.{0}} {J : Type} (U : J → X.Opens)
variable {K : Type*} [Field K] (ρ : K →+* Γ(X,⊤))

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

def ActualExt (_ρ : K →+* Γ(X,⊤)) (A M : X.Modules) (q : ℕ) : Type 1 := Ext.{1} A M q

instance (A M : X.Modules) (q : ℕ) : AddCommGroup (ActualExt ρ A M q) :=
  inferInstanceAs (AddCommGroup (Ext.{1} A M q))

instance globalModule (A M : X.Modules) (q : ℕ) :
    Module Γ(X,⊤) (ActualExt ρ A M q) :=
  inferInstanceAs (Module Γ(X,⊤) (Ext.{1} A M q))

instance scalarModule (A M : X.Modules) (q : ℕ) : Module K (ActualExt ρ A M q) :=
  Module.compHom _ ρ

def connecting (A : X.Modules) (S : ShortComplex X.Modules) (hS : S.ShortExact) (q : ℕ) :
    ActualExt ρ A S.X₃ q →ₗ[K] ActualExt ρ A S.X₁ (q+1) where
  toFun x := Ext.comp x hS.extClass rfl
  map_add' x y := Ext.add_comp x y hS.extClass rfl
  map_smul' a x := by
    change Ext.comp ((ρ a) • (show Ext.{1} A S.X₃ q from x)) hS.extClass rfl =
      (ρ a) • Ext.comp x hS.extClass rfl
    exact Ext.smul_comp (C := X.Modules) (R := Γ(X, ⊤)) x hS.extClass rfl (ρ a)

lemma connecting_surjective (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ) :
    Function.Surjective (connecting ρ A S hS q) := by
  intro x
  exact Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl

def LocallyAcyclic (M : X.Modules) : Prop :=
  ∀ (q : ℕ) (t : Fin (q+1) → J) (k : ℕ)
    (x : Ext.{1} (schemeFreeOpen (CechHigher.intersection U t)) M (k+1)), x = 0

lemma locallyAcyclic_quotient (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Injective S.X₂] (hlocal : LocallyAcyclic U S.X₁) : LocallyAcyclic U S.X₃ := by
  intro q t k y
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₃
    (schemeFreeOpen (CechHigher.intersection U t)) hS y
    (n₁ := k+2) rfl (hlocal q t (k+1) _)
  rw [Ext.eq_zero_of_injective z, Ext.zero_comp] at hz
  exact hz.symm

open CechLinear

def descent (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] cycles U ρ S.X₃ q :=
  ((mapLinear U ρ S.g q).comp
    ((primitive U ρ S.X₂ q).comp (mapCycles U ρ S.f (q+1)))).codRestrict
      (cycles U ρ S.X₃ q) (fun a => by
        change differentialLinear U ρ S.X₃ q
          (mapLinear U ρ S.g q (primitive U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))) = 0
        refine (mapLinear_differential U ρ S.g q _).symm.trans ?_
        refine (congrArg (mapLinear U ρ S.g (q + 1))
          (primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q + 1) a))).trans ?_
        change mapLinear U ρ S.g (q + 1) (mapLinear U ρ S.f (q + 1) a.val) = 0
        rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
        rfl)

lemma descent_lift (S : ShortComplex X.Modules) [Injective S.X₂] (q : ℕ)
    (a : cycles U ρ S.X₁ (q+1)) (b : Cochain U ρ S.X₂ q)
    (c : cycles U ρ S.X₃ q)
    (hdb : differentialLinear U ρ S.X₂ q b = mapLinear U ρ S.f (q+1) a.val)
    (hbg : mapLinear U ρ S.g q b = c.val) :
    ∃ z : cycles U ρ S.X₂ q, descent U ρ S q a - c = mapCycles U ρ S.g q z := by
  let β := primitive U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  have hβ : differentialLinear U ρ S.X₂ q β = mapLinear U ρ S.f (q+1) a.val :=
    primitive_spec U ρ S.X₂ q (mapCycles U ρ S.f (q+1) a)
  let z : cycles U ρ S.X₂ q := ⟨β-b, by
    change differentialLinear U ρ S.X₂ q (β-b) = 0
    rw [map_sub, hβ, hdb, sub_self]⟩
  refine ⟨z, ?_⟩
  apply Subtype.ext
  change mapLinear U ρ S.g q β - c.val = mapLinear U ρ S.g q (β-b)
  rw [map_sub, hbg]

def comparisonStep (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q) :
    cycles U ρ S.X₁ (q+1) →ₗ[K] ActualExt ρ A S.X₁ (q+1) :=
  (connecting ρ A S hS q).comp (F.comp (descent U ρ S q))

lemma comparisonStep_surjective (V : X.Opens) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (hlocal : LocallyAcyclic U S.X₁)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ (schemeFreeOpen V) S.X₃ q)
    (hF : Function.Surjective F)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ (schemeFreeOpen V) S hS q (F (mapCycles U ρ S.g q z)) = 0) :
    Function.Surjective (comparisonStep U ρ (schemeFreeOpen V) S hS q F) := by
  intro x
  obtain ⟨y, hy⟩ := connecting_surjective ρ (schemeFreeOpen V) S hS q x
  obtain ⟨c, hc⟩ := hF y
  obtain ⟨b,a,hb,ha,had⟩ := CechHigher.connecting_cocycle X.ringCatSheaf U S hS
    (fun t z => hlocal q t 0 z) c.val c.property
  let a' : cycles U ρ S.X₁ (q+1) := ⟨a,had⟩
  obtain ⟨z,hz⟩ := descent_lift U ρ S q a' b c ha.symm hb
  let H := (connecting ρ (schemeFreeOpen V) S hS q).comp F
  have he : H (descent U ρ S q a') = H c := by
    apply sub_eq_zero.mp
    rw [← H.map_sub, hz]
    exact hmiddle z
  refine ⟨a', ?_⟩
  change H (descent U ρ S q a') = x
  rw [he]
  change connecting ρ (schemeFreeOpen V) S hS q (F c) = x
  rw [hc,hy]

lemma comparisonStep_boundary (A : X.Modules) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) [Injective S.X₂] (q : ℕ)
    (F : cycles U ρ S.X₃ q →ₗ[K] ActualExt ρ A S.X₃ q)
    (hmiddle : ∀ z : cycles U ρ S.X₂ q,
      connecting ρ A S hS q (F (mapCycles U ρ S.g q z)) = 0)
    (b : Cochain U ρ S.X₁ q) :
    comparisonStep U ρ A S hS q F (boundaryToCycles U ρ S.X₁ q b) = 0 := by
  have hdb : differentialLinear U ρ S.X₂ q (mapLinear U ρ S.f q b) =
      mapLinear U ρ S.f (q+1) (boundaryToCycles U ρ S.X₁ q b).val :=
    (mapLinear_differential U ρ S.f q b).symm
  have hbg : mapLinear U ρ S.g q (mapLinear U ρ S.f q b) =
      (0 : cycles U ρ S.X₃ q).val := by
    rw [← LinearMap.comp_apply, ← mapLinear_comp, S.zero, mapLinear_zero]
    rfl
  obtain ⟨z,hz⟩ := descent_lift U ρ S q (boundaryToCycles U ρ S.X₁ q b)
    (mapLinear U ρ S.f q b) 0 hdb hbg
  rw [sub_zero] at hz
  change connecting ρ A S hS q (F (descent U ρ S q (boundaryToCycles U ρ S.X₁ q b))) = 0
  rw [hz]
  exact hmiddle z

def mkZeroLinear (A M : X.Modules) :
    letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
    letI := Module.compHom (A ⟶ M) ρ
    (A ⟶ M) →ₗ[K] ActualExt ρ A M 0 := by
  letI : Module Γ(X,⊤) (A ⟶ M) := sheafHomModule X A M
  letI := Module.compHom (A ⟶ M) ρ
  refine {
    toFun := Ext.mk₀
    map_add' := Ext.mk₀_add
    map_smul' := ?_ }
  intro r f
  change Ext.mk₀ ((ρ r) • f) = (ρ r) • (show Ext.{1} A M 0 from Ext.mk₀ f)
  exact Ext.mk₀_smul (C := X.Modules) (R := Γ(X,⊤)) (X := A) (Y := M) (ρ r) f

@[simp] theorem mkZeroLinear_apply (A M : X.Modules) (f : A ⟶ M) :
    mkZeroLinear ρ A M f = Ext.mk₀ f := rfl

def zeroComparison (M : X.Modules) (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) :
    cycles U ρ M 0 →ₗ[K] ActualExt ρ (schemeFreeOpen V) M 0 := by
  letI : Module Γ(X,⊤) (schemeFreeOpen V ⟶ M) := sheafHomModule X _ M
  letI := Module.compHom (schemeFreeOpen V ⟶ M) ρ
  exact (mkZeroLinear ρ (schemeFreeOpen V) M).comp
    (CechZero.sectionsEquiv U ρ M V hUV hcover).symm.toLinearMap

lemma zeroComparison_surjective (M : X.Modules) (V : X.Opens)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    Function.Surjective (zeroComparison U ρ M V hUV hcover) := by
  intro x
  obtain ⟨f,hf⟩ := (Ext.mk₀_bijective (schemeFreeOpen V) M).surjective x
  refine ⟨CechZero.sectionsEquiv U ρ M V hUV hcover f, ?_⟩
  change Ext.mk₀ ((CechZero.sectionsEquiv U ρ M V hUV hcover).symm
    (CechZero.sectionsEquiv U ρ M V hUV hcover f)) = x
  rw [LinearEquiv.symm_apply_apply,hf]

lemma zeroComparison_middle (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (z : cycles U ρ S.X₂ 0) :
    connecting ρ (schemeFreeOpen V) S hS 0
      (zeroComparison U ρ S.X₃ V hUV hcover (mapCycles U ρ S.g 0 z)) = 0 := by
  change Ext.comp (Ext.mk₀ ((CechZero.sectionsEquiv U ρ S.X₃ V hUV hcover).symm
    (mapCycles U ρ S.g 0 z))) hS.extClass rfl = 0
  rw [CechZero.sectionsEquiv_symm_mapCycles, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

theorem exists_comparison (V : X.Opens) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (n : ℕ) (M : X.Modules)
    (hlocal : LocallyAcyclic U M) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (schemeFreeOpen V) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  let : EnoughInjectives X.Modules := PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let F := zeroComparison U ρ S.X₃ V hUV hcover
    have hmid := zeroComparison_middle U ρ V hUV hcover S hS
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS 0 F,
      comparisonStep_surjective U ρ V S hS 0 hlocal F
        (zeroComparison_surjective U ρ S.X₃ V hUV hcover) hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS 0 F hmid⟩
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨F,hF,hFb⟩ := ih S.X₃ (locallyAcyclic_quotient U S hS hlocal)
    have hmid (z : cycles U ρ S.X₂ (n+1)) :
        connecting ρ (schemeFreeOpen V) S hS (n+1)
          (F (mapCycles U ρ S.g (n+1) z)) = 0 := by
      obtain ⟨b,rfl⟩ := boundaryToCycles_surjective U ρ S.X₂ n z
      rw [mapCycles_boundary,hFb,map_zero]
    exact ⟨comparisonStep U ρ (schemeFreeOpen V) S hS (n+1) F,
      comparisonStep_surjective U ρ V S hS (n+1) hlocal F hF hmid,
      comparisonStep_boundary U ρ (schemeFreeOpen V) S hS (n+1) F hmid⟩

def sourceIso {A B : X.Modules} (e : A ≅ B) (M : X.Modules) (q : ℕ) :
    ActualExt ρ A M q ≃ₗ[K] ActualExt ρ B M q where
  toFun x := (Ext.mk₀ e.inv).comp x (zero_add q)
  invFun x := (Ext.mk₀ e.hom).comp x (zero_add q)
  left_inv x := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp (show Ext.{1} A M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv x := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp (show Ext.{1} B M q from x) (zero_add q)) (zero_add q) = x
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]
  map_add' x y := Ext.comp_add _ x y _
  map_smul' a x := by
    change (Ext.mk₀ e.inv).comp ((ρ a) • (show Ext.{1} A M q from x)) _ =
      (ρ a) • (Ext.mk₀ e.inv).comp x _
    exact Ext.comp_smul (C := X.Modules) (R := Γ(X, ⊤)) (Ext.mk₀ e.inv) x (zero_add q) (ρ a)

theorem affine_exists_comparison [IsNoetherian X] (hcover : ⊤ ≤ ⨆ i, U i)
    (M : X.Modules) [M.IsQuasicoherent]
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → J), IsAffineOpen (CechHigher.intersection U t))
    (n : ℕ) :
    ∃ F : cycles U ρ M (n+1) →ₗ[K] ActualExt ρ (structureSheaf X) M (n+1),
      Function.Surjective F ∧ ∀ b : Cochain U ρ M n, F (boundaryToCycles U ρ M n b) = 0 := by
  obtain ⟨F,hF,hFb⟩ := exists_comparison U ρ ⊤ (fun _ => le_top) hcover n M
    (fun q t k y => PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (CechHigher.intersection U t) (haffine q t) M k y)
  let e := sourceIso (X := X) ρ (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M (n+1)
  refine ⟨e.toLinearMap.comp F, e.surjective.comp hF, ?_⟩
  intro b
  change e (F (boundaryToCycles U ρ M n b)) = 0
  rw [hFb,map_zero]

end
end PiExponent.GeometrySupport.CechExtFinite

end OAI
end Source0566

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveMonomialFinite.lean
section Source0567
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveMonomialFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveMonomialFinite
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher

variable {ι K : Type*} [Fintype ι]

def AllNegative {d : ℤ} (a : Monomial ι d) : Prop := ∀ i, a.val i < 0

theorem allNegative_coordinate_bounds {d : ℤ} {a : Monomial ι d}
    (ha : AllNegative a) (i : ι) : d ≤ a.val i ∧ a.val i ≤ 0 := by
  classical
  refine ⟨?_, le_of_lt (ha i)⟩
  calc
    d = ∑ j, a.val j := a.property.symm
    _ ≤ a.val i := by
      simpa using Finset.sum_le_sum_of_subset_of_nonpos
        (f := a.val) (show ({i} : Finset ι) ⊆ Finset.univ by simp)
        (fun j _ _ => le_of_lt (ha j))

instance allNegative_finite (d : ℤ) : Finite {a : Monomial ι d // AllNegative a} := by
  let f : {a : Monomial ι d // AllNegative a} → (ι → Set.Icc d 0) :=
    fun a i => ⟨a.val.val i, allNegative_coordinate_bounds a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance allNonnegative_finite (d : ℤ) :
    Finite {a : Monomial ι d // ∀ i, 0 ≤ a.val i} := by
  classical
  have hb (a : Monomial ι d) (ha : ∀ i, 0 ≤ a.val i) (i : ι) :
      a.val i ∈ Set.Icc 0 d := by
    refine ⟨ha i, ?_⟩
    calc
      a.val i ≤ ∑ j, a.val j := Finset.single_le_sum (fun j _ => ha j) (by simp)
      _ = d := a.property
  let f : {a : Monomial ι d // ∀ i, 0 ≤ a.val i} → (ι → Set.Icc 0 d) :=
    fun a i => ⟨a.val.val i, hb a.val a.property i⟩
  exact Finite.of_injective f (by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i))

instance monomial_subsingleton [Subsingleton ι] (d : ℤ) : Subsingleton (Monomial ι d) := by
  classical
  constructor
  intro a b
  apply Subtype.ext
  funext i
  have hi : (Finset.univ : Finset ι) = {i} := by
    ext j
    simp [Subsingleton.elim j i]
  have ha : a.val i = d := by simpa only [hi, Finset.sum_singleton] using a.property
  have hb : b.val i = d := by simpa only [hi, Finset.sum_singleton] using b.property
  exact ha.trans hb.symm

variable [AddCommGroup K]

def filterCochain {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) : Cochain ι (Laurent ι K d) q := by
  classical
  exact fun t => (c t).filter p

@[simp] theorem filterCochain_apply {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (t : Fin (q + 1) → ι)
    (a : Monomial ι d) : filterCochain p c t a = if p a then c t a else 0 := by
  classical
  rfl

theorem filterCochain_regular {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : Regular c) :
    Regular (filterCochain p c) := by
  classical
  intro t a ha i hi
  have hn : c t a ≠ 0 := by
    intro hz
    simp [filterCochain_apply, hz] at ha
  exact hc t a hn i hi

theorem differential_filterCochain {d : ℤ} {q : ℕ}
    (p : Monomial ι d → Prop) (c : Cochain ι (Laurent ι K d) q) :
    differential (filterCochain p c) = filterCochain p (differential c) := by
  classical
  funext t
  ext a
  simp only [differential_apply, filterCochain_apply]
  by_cases h : p a
  · simp only [h, ite_true]
  · simp [differential, h]

theorem filterCochain_closed {d : ℤ} {q : ℕ} (p : Monomial ι d → Prop)
    (c : Cochain ι (Laurent ι K d) q) (hc : differential c = 0) :
    differential (filterCochain p c) = 0 := by
  rw [differential_filterCochain, hc]
  funext t
  ext a
  simp

theorem exact_of_obstruction_zero {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0)
    (hzero : ∀ t a, AllNegative a → c t a = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q, Regular b ∧ differential b = c := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
      refine ⟨fun t => isEmptyElim (t 0), ?_, ?_⟩
      · intro t
        exact isEmptyElim (t 0)
      · funext t
        exact isEmptyElim (t 0)
  | inr h =>
      let pivot : Monomial ι d → ι := fun a =>
        if ha : ∃ i, 0 ≤ a.val i then Classical.choose ha else Classical.choice h
      have hpivot (a : Monomial ι d) (ha : ¬ AllNegative a) : 0 ≤ a.val (pivot a) := by
        have hex : ∃ i, 0 ≤ a.val i := by
          simpa only [AllNegative, not_forall, not_lt] using ha
        simp only [pivot, dite_eq_left hex]
        exact Classical.choose_spec hex
      refine ⟨contraction pivot c, ?_, ?_⟩
      · intro t a ha k hk
        have hn : ¬ AllNegative a := by
          intro hb
          exact ha (hzero (Fin.cons (pivot a) t) a hb)
        obtain ⟨j, hj⟩ := hc (Fin.cons (pivot a) t) a ha k hk
        cases j using Fin.cases with
        | zero =>
            simp only [Fin.cons_zero] at hj
            rw [← hj] at hk
            exact False.elim ((not_lt_of_ge (hpivot a hn)) hk)
        | succ j => exact ⟨j, by simpa only [Fin.cons_succ] using hj⟩
      · have hid := contraction_identity pivot c
        rw [hclosed] at hid
        have hz : contraction pivot (0 : Cochain ι (Laurent ι K d) (q + 2)) = 0 := by
          funext t
          ext a
          rfl
        simpa only [hz, zero_add] using hid

theorem cocycle_eq_boundary_add_negative {d : ℤ} {q : ℕ}
    (c : Cochain ι (Laurent ι K d) (q + 1)) (hc : Regular c)
    (hclosed : differential c = 0) :
    ∃ b : Cochain ι (Laurent ι K d) q,
      Regular b ∧ c = differential b + filterCochain AllNegative c := by
  classical
  let good := filterCochain (fun a => ¬ AllNegative a) c
  have hgood : Regular good := filterCochain_regular _ c hc
  have hgoodclosed : differential good = 0 := filterCochain_closed _ c hclosed
  obtain ⟨b, hb, hdb⟩ := exact_of_obstruction_zero good hgood hgoodclosed (by
    intro t a ha
    simp [good, ha])
  refine ⟨b, hb, ?_⟩
  rw [hdb]
  funext t
  ext a
  simp only [Pi.add_apply, Finsupp.add_apply, good, filterCochain_apply]
  by_cases ha : AllNegative a <;> simp [ha]

end
end PiExponent.ProjectiveMonomialFinite

end OAI
end Source0567

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCohomology.lean
section Source0568
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveMonomialCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveMonomialCohomology
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCech ProjectiveMonomialCechHigher ProjectiveMonomialFinite

variable {ι K : Type*} [Fintype ι] [CommRing K]

def differentialLinear (d : ℤ) (q : ℕ) :
    Cochain ι (Laurent ι K d) q →ₗ[K] Cochain ι (Laurent ι K d) (q + 1) where
  toFun := differential
  map_add' c e := by
    funext t
    simp only [differential, Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' r c := by
    funext t
    simp only [differential, Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _

def regularCochains (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) where
  carrier := {c | Regular c}
  zero_mem' := by intro t a h; exact (h rfl).elim
  add_mem' {c e} hc he := by
    intro t a h i hi
    by_cases hca : c t a = 0
    · apply he t a _ i hi
      simpa only [Pi.add_apply, Finsupp.add_apply, hca, zero_add] using h
    · exact hc t a hca i hi
  smul_mem' r c hc := by
    intro t a h i hi
    apply hc t a _ i hi
    intro hz
    apply h
    simp [hz]

def cycles (d : ℤ) (q : ℕ) : Submodule K (Cochain ι (Laurent ι K d) q) :=
  regularCochains d q ⊓ (differentialLinear d q).ker

theorem degreeZero_coeff_eq {d : ℤ} (c : cycles (ι := ι) (K := K) d 0) (i j : ι) :
    c.val (fun _ => i) = c.val (fun _ => j) := by
  have hc := congrFun c.property.2 ![i, j]
  change differential c.val ![i, j] = 0 at hc
  rw [differential, Fin.sum_univ_two] at hc
  have h0 : (![i, j] ∘ (0 : Fin 2).succAbove) = (fun _ : Fin 1 => j) := by
    funext k
    fin_cases k
    rfl
  have h1 : (![i, j] ∘ (1 : Fin 2).succAbove) = (fun _ : Fin 1 => i) := by
    funext k
    fin_cases k
    rfl
  have hh : c.val (fun _ => j) - c.val (fun _ => i) = 0 := by
    simpa only [h0, h1, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_zsmul,
      neg_one_zsmul, sub_eq_add_neg] using hc
  exact (sub_eq_zero.mp hh).symm

theorem degreeZero_nonnegative [Nontrivial ι] {d : ℤ}
    (c : cycles (ι := ι) (K := K) d 0) (t : Fin 1 → ι) (a : Monomial ι d)
    (ha : c.val t a ≠ 0) : ∀ i, 0 ≤ a.val i := by
  intro i
  by_contra hi
  have hin : a.val i < 0 := lt_of_not_ge hi
  obtain ⟨j, hj⟩ := exists_ne i
  have ht : t = (fun _ => t 0) := by
    funext k
    exact congrArg t (Fin.eq_zero k)
  have he : c.val t = c.val (fun _ => j) := by
    rw [ht]
    exact degreeZero_coeff_eq c (t 0) j
  rw [he] at ha
  obtain ⟨k, hk⟩ := c.property.1 (fun _ => j) a ha i hin
  exact hj hk

def degreeZeroCoefficients (d : ℤ) (i : ι) :
    cycles (ι := ι) (K := K) d 0 →ₗ[K]
      ({a : Monomial ι d // ∀ j, 0 ≤ a.val j} → K) where
  toFun c a := c.val (fun _ => i) a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem degreeZeroCoefficients_injective [Nontrivial ι] (d : ℤ) (i : ι) :
    Function.Injective (degreeZeroCoefficients (ι := ι) (K := K) d i) := by
  intro c e h
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : ∀ j, 0 ≤ a.val j
  · have hc : c.val t = c.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq c (t 0) i
    have he : e.val t = e.val (fun _ => i) := by
      have ht : t = (fun _ => t 0) := by
        funext k
        exact congrArg t (Fin.eq_zero k)
      rw [ht]
      exact degreeZero_coeff_eq e (t 0) i
    rw [hc, he]
    exact congrFun h ⟨a, ha⟩
  · have hc : c.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative c t a hh)
    have he : e.val t a = 0 := by
      by_contra hh
      exact ha (degreeZero_nonnegative e t a hh)
    rw [hc, he]

instance degreeZero_finite [IsNoetherianRing K] (d : ℤ) :
    Module.Finite K (cycles (ι := ι) (K := K) d 0) := by
  cases subsingleton_or_nontrivial ι with
  | inl h => infer_instance
  | inr h =>
      let i : ι := Classical.choice (inferInstance : Nonempty ι)
      exact Module.Finite.of_injective (degreeZeroCoefficients d i)
        (degreeZeroCoefficients_injective d i)

def boundaryMap (d : ℤ) (q : ℕ) :
    regularCochains (ι := ι) (K := K) d q →ₗ[K] cycles (ι := ι) (K := K) d (q + 1) :=
  ((differentialLinear (ι := ι) (K := K) d q).comp (regularCochains d q).subtype).codRestrict
    (cycles d (q + 1)) (fun c =>
      ⟨differential_regular c.val c.property, differential_squared c.val⟩)

def negativeCycles (d : ℤ) (q : ℕ) : Submodule K (cycles (ι := ι) (K := K) d (q + 1)) where
  carrier := {c | ∀ t a, ¬ AllNegative a → c.val t a = 0}
  zero_mem' := by
    intro t a ha
    rfl
  add_mem' {c e} hc he := by
    intro t a ha
    change c.val t a + e.val t a = 0
    rw [hc t a ha, he t a ha, zero_add]
  smul_mem' r c hc := by
    intro t a ha
    change r • (c.val t a) = 0
    rw [hc t a ha, smul_zero]

def negativeCoefficients (d : ℤ) (q : ℕ) :
    negativeCycles (ι := ι) (K := K) d q →ₗ[K]
      ((Fin (q + 2) → ι) → ({a : Monomial ι d // AllNegative a} → K)) where
  toFun c t a := c.val.val t a.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem negativeCoefficients_injective (d : ℤ) (q : ℕ) :
    Function.Injective (negativeCoefficients (ι := ι) (K := K) d q) := by
  intro c e h
  apply Subtype.ext
  apply Subtype.ext
  funext t
  ext a
  by_cases ha : AllNegative a
  · exact congrFun (congrFun h t) ⟨a, ha⟩
  · rw [c.property t a ha, e.property t a ha]

instance negativeCycles_finite [IsNoetherianRing K] (d : ℤ) (q : ℕ) :
    Module.Finite K (negativeCycles (ι := ι) (K := K) d q) :=
  Module.Finite.of_injective (negativeCoefficients d q) (negativeCoefficients_injective d q)

theorem exists_negative_representative (d : ℤ) (q : ℕ)
    (c : cycles (ι := ι) (K := K) d (q + 1)) :
    ∃ z : negativeCycles (ι := ι) (K := K) d q,
      ∃ b : regularCochains (ι := ι) (K := K) d q,
        c = boundaryMap d q b + z.val := by
  classical
  let z : cycles (ι := ι) (K := K) d (q + 1) :=
    ⟨filterCochain AllNegative c.val,
      filterCochain_regular _ c.val c.property.1,
      filterCochain_closed _ c.val c.property.2⟩
  have hz : z ∈ negativeCycles d q := by
    intro t a ha
    change filterCochain AllNegative c.val t a = 0
    simp [ha]
  obtain ⟨b, hb, heq⟩ := cocycle_eq_boundary_add_negative c.val c.property.1 c.property.2
  exact ⟨⟨z, hz⟩, ⟨b, hb⟩, Subtype.ext heq⟩

theorem finite_of_boundary_annihilating_surjective [IsNoetherianRing K] (d : ℤ) (q : ℕ)
    {V : Type*} [AddCommGroup V] [Module K V]
    (f : cycles (ι := ι) (K := K) d (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (boundaryMap d q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g : negativeCycles (ι := ι) (K := K) d q →ₗ[K] V :=
    f.comp (negativeCycles d q).subtype
  apply Module.Finite.of_surjective g
  intro x
  obtain ⟨c, hc⟩ := hsurj x
  obtain ⟨z, b, heq⟩ := exists_negative_representative d q c
  refine ⟨z, ?_⟩
  change f z.val = x
  rw [← hc, heq, map_add, hboundary, zero_add]

end
end PiExponent.ProjectiveMonomialCohomology

end OAI
end Source0568

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveTwistCech.lean
section Source0569
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveTwistCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveTwistCech

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

structure LaurentCechPresentation (U : ι → X.Opens) (M : X.Modules) (d : ℤ) where
  coefficient : ∀ q (t : Fin (q + 1) → ι),
    (schemeFreeOpen (GeometrySupport.CechHigher.intersection U t) ⟶ M) →+
      Laurent ι K d
  injective : ∀ q t, Function.Injective (coefficient q t)
  regular : ∀ q t b, RegularOn (Set.range t) (coefficient q t b)
  surjective : ∀ q t p, RegularOn (Set.range t) p → ∃ b, coefficient q t b = p
  restriction : ∀ q (t : Fin (q + 2) → ι) (k : Fin (q + 2)) b,
    coefficient (q + 1) t
      (GeometrySupport.CechOne.restrictHom X.ringCatSheaf
        (GeometrySupport.CechHigher.faceLE U t k) b) =
      coefficient q (t ∘ k.succAbove) b

namespace LaurentCechPresentation

variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
    (P : LaurentCechPresentation (K := K) U M d)

def toLaurent {q : ℕ} (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    ProjectiveMonomialCechHigher.Cochain ι (Laurent ι K d) q :=
  fun t => P.coefficient q t (c t)

theorem toLaurent_differential {q : ℕ}
    (c : GeometrySupport.CechHigher.Cochain X.ringCatSheaf U M q) :
    P.toLaurent (GeometrySupport.CechHigher.differential X.ringCatSheaf U M c) =
      ProjectiveMonomialCechHigher.differential (P.toLaurent c) := by
  funext t
  simp only [toLaurent, GeometrySupport.CechHigher.differential,
    ProjectiveMonomialCechHigher.differential]
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.restriction]

include P in

theorem hasPrimitives (hd : 0 ≤ d) (q : ℕ) :
    GeometrySupport.CechHigher.HasPrimitives X.ringCatSheaf U M q := by
  intro c hc
  have hregular : ProjectiveMonomialCechHigher.Regular (P.toLaurent c) :=
    fun t => P.regular _ t _
  have hclosed : ProjectiveMonomialCechHigher.differential (P.toLaurent c) = 0 := by
    rw [← P.toLaurent_differential, hc]
    funext t
    exact map_zero _
  obtain ⟨B, hB, hCB⟩ :=
    ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive hd
      (P.toLaurent c) hregular hclosed
  choose b hb using fun t => P.surjective q t (B t) (hB t)
  refine ⟨b, ?_⟩
  funext t
  apply P.injective (q + 1) t
  have hcochain : P.toLaurent b = B := funext hb
  have h := congrFun (P.toLaurent_differential b) t
  rw [hcochain, hCB] at h
  exact h

end LaurentCechPresentation

end
end PiExponent.ProjectiveTwistCech

end OAI
end Source0569

-- Source: OAI/NumberTheory/PiExponent/Cohomology/LaurentCechFinite.lean
section Source0570
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/LaurentCechFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.LaurentCechFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open ProjectiveTwistCech

variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
  {U : ι → X.Opens} {M : X.Modules} {d : ℤ}

abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

@[instance_reducible] def freeOpenHomAddCommGroup (V : X.Opens) (N : X.Modules) :
    AddCommGroup (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ N))

attribute [local instance] freeOpenHomAddCommGroup

local instance (V : X.Opens) (N : X.Modules) :
    Module Γ(X, ⊤) (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  sheafHomModule X _ N

variable (ρ : K →+* Γ(X, ⊤)) (P : LaurentCechPresentation (K := K) U M d)
  (hlinear : ∀ q t (r : K) b,
    P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)

def cochainMap (q : ℕ) :
    CechLinear.Cochain U ρ M q →ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c, fun t => P.regular q t (c t)⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c t) (e t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c t)

theorem cochainMap_injective (q : ℕ) :
    Function.Injective (cochainMap ρ P hlinear q) := by
  intro c e h
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cochainMap_surjective (q : ℕ) :
    Function.Surjective (cochainMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property t)
  exact ⟨b, Subtype.ext (funext hb)⟩

def cochainEquiv (q : ℕ) :
    CechLinear.Cochain U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cochainMap ρ P hlinear q)
    ⟨cochainMap_injective ρ P hlinear q, cochainMap_surjective ρ P hlinear q⟩

def cyclesMap (q : ℕ) :
    CechLinear.cycles U ρ M q →ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q where
  toFun c := ⟨P.toLaurent c.val, fun t => P.regular q t _, by
    change ProjectiveMonomialCechHigher.differential (P.toLaurent c.val) = 0
    have hc : CechLinear.differentialLinear U ρ M q c.val = 0 := c.property
    refine (P.toLaurent_differential c.val).symm.trans
      ((congrArg (fun c : CechLinear.Cochain U ρ M (q + 1) => P.toLaurent c) hc).trans ?_)
    funext t
    exact map_zero _⟩
  map_add' c e := by
    apply Subtype.ext
    funext t
    exact map_add (P.coefficient q t) (c.val t) (e.val t)
  map_smul' r c := by
    apply Subtype.ext
    funext t
    exact hlinear q t r (c.val t)

theorem cyclesMap_injective (q : ℕ) :
    Function.Injective (cyclesMap ρ P hlinear q) := by
  intro c e h
  apply Subtype.ext
  funext t
  apply P.injective q t
  exact congrFun (congrArg Subtype.val h) t

theorem cyclesMap_surjective (q : ℕ) :
    Function.Surjective (cyclesMap ρ P hlinear q) := by
  intro c
  choose b hb using fun t => P.surjective q t (c.val t) (c.property.1 t)
  have he : P.toLaurent b = c.val := funext hb
  have hc : CechLinear.differentialLinear U ρ M q b = 0 := by
    funext t
    apply P.injective (q + 1) t
    have h := P.toLaurent_differential b
    have hc : ProjectiveMonomialCechHigher.differential c.val = 0 := c.property.2
    rw [he, hc] at h
    exact (congrFun h t).trans (map_zero (P.coefficient (q + 1) t)).symm
  exact ⟨⟨b, hc⟩, Subtype.ext he⟩

def cyclesEquiv (q : ℕ) :
    CechLinear.cycles U ρ M q ≃ₗ[K] ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d q :=
  LinearEquiv.ofBijective (cyclesMap ρ P hlinear q)
    ⟨cyclesMap_injective ρ P hlinear q, cyclesMap_surjective ρ P hlinear q⟩

theorem cyclesEquiv_boundary (q : ℕ) (c : CechLinear.Cochain U ρ M q) :
    cyclesEquiv ρ P hlinear (q + 1) (CechLinear.boundaryToCycles U ρ M q c) =
      ProjectiveMonomialCohomology.boundaryMap d q (cochainEquiv ρ P hlinear q c) := by
  apply Subtype.ext
  exact P.toLaurent_differential c

theorem cyclesEquiv_symm_boundary (q : ℕ) (b : ProjectiveMonomialCohomology.regularCochains (ι := ι) (K := K) d q) :
    (cyclesEquiv ρ P hlinear (q + 1)).symm (ProjectiveMonomialCohomology.boundaryMap d q b) =
      CechLinear.boundaryToCycles U ρ M q ((cochainEquiv ρ P hlinear q).symm b) := by
  apply (cyclesEquiv ρ P hlinear (q + 1)).injective
  rw [LinearEquiv.apply_symm_apply, cyclesEquiv_boundary, LinearEquiv.apply_symm_apply]

include P hlinear in

theorem degreeZero_finite : Module.Finite K (CechLinear.cycles U ρ M 0) := by
  let : Module.Finite K (ProjectiveMonomialCohomology.cycles (ι := ι) (K := K) d 0) :=
    ProjectiveMonomialCohomology.degreeZero_finite d
  exact Module.Finite.of_surjective (cyclesEquiv ρ P hlinear 0).symm.toLinearMap
    (cyclesEquiv ρ P hlinear 0).symm.surjective

include P hlinear in

theorem finite_of_comparison (q : ℕ) {V : Type*} [AddCommGroup V] [Module K V]
    (f : CechLinear.cycles U ρ M (q + 1) →ₗ[K] V)
    (hboundary : ∀ b, f (CechLinear.boundaryToCycles U ρ M q b) = 0)
    (hsurj : Function.Surjective f) : Module.Finite K V := by
  let g := f.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.toLinearMap
  apply ProjectiveMonomialCohomology.finite_of_boundary_annihilating_surjective d q g
  · intro b
    change f ((cyclesEquiv ρ P hlinear (q + 1)).symm
      (ProjectiveMonomialCohomology.boundaryMap d q b)) = 0
    rw [cyclesEquiv_symm_boundary]
    exact hboundary _
  · exact hsurj.comp (cyclesEquiv ρ P hlinear (q + 1)).symm.surjective

end
end PiExponent.GeometrySupport.LaurentCechFinite

end OAI
end Source0570

-- Source: OAI/NumberTheory/PiExponent/Cohomology/LaurentExtFinite.lean
section Source0571
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/LaurentExtFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ActualLaurentExtFinite
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}} {ι K : Type} [Fintype ι] [Field K]
variable {U : ι → X.Opens} {M : X.Modules} {d : ℤ}
variable (ρ : K →+* Γ(X,⊤)) (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
abbrev schemeFreeOpen (V : X.Opens) : X.Modules :=
  PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V

@[instance_reducible] def freeOpenHomAddCommGroup (V : X.Opens) (N : X.Modules) :
    AddCommGroup (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen V ⟶ N))

attribute [local instance] freeOpenHomAddCommGroup

local instance (V : X.Opens) (N : X.Modules) :
    Module Γ(X,⊤) (PiExponentSeshadri.ModuleFlasque.freeOpen X.ringCatSheaf V ⟶ N) :=
  sheafHomModule X _ N
variable (hlinear : ∀ q t (r : K) b,
  P.coefficient q t ((ρ r) • b) = r • P.coefficient q t b)
include P hlinear

theorem actualExt_zero_finite (hcover : ⊤ ≤ ⨆ i, U i) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M 0) := by
  let := LaurentCechFinite.degreeZero_finite ρ P hlinear
  let F := CechExtFinite.zeroComparison U ρ M ⊤ (fun _ => le_top) hcover
  let e := CechExtFinite.sourceIso (X := X) ρ
    (A := schemeFreeOpen ⊤) (B := structureSheaf X)
    (PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf) M 0
  exact Module.Finite.of_surjective (e.toLinearMap.comp F)
    (e.surjective.comp (CechExtFinite.zeroComparison_surjective U ρ M ⊤
      (fun _ => le_top) hcover))

theorem actualExt_succ_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M (q+1)) := by
  obtain ⟨F, hF, hboundary⟩ :=
    CechExtFinite.affine_exists_comparison U ρ hcover M haffine q
  exact LaurentCechFinite.finite_of_comparison ρ P hlinear q F hboundary hF

theorem actualExt_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    Module.Finite K (CechExtFinite.ActualExt ρ (structureSheaf X) M q) := by
  cases q with
  | zero => exact actualExt_zero_finite ρ P hlinear hcover
  | succ q => exact actualExt_succ_finite ρ P hlinear hcover haffine q

theorem cohomology_finite [IsNoetherian X] [M.IsQuasicoherent]
    (hcover : ⊤ ≤ ⨆ i, U i)
    (haffine : ∀ (q : ℕ) (t : Fin (q+1) → ι),
      IsAffineOpen (CechHigher.intersection U t)) (q : ℕ) :
    letI := Module.compHom (cohomology M q) ρ
    Module.Finite K (cohomology M q) := by
  exact actualExt_finite ρ P hlinear hcover haffine q

end
end PiExponent.GeometrySupport.ActualLaurentExtFinite

end OAI
end Source0571

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/SerreDimensionShift.lean
section Source0572
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/SerreDimensionShift.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.SerreDimensionShift

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe w v u t
variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

theorem ext_eq_zero_of_shortExact (A : C) {S : ShortComplex C} (hS : S.ShortExact)
    (q : ℕ) (hmid : ∀ x : Ext.{w} A S.X₂ q, x = 0)
    (hleft : ∀ x : Ext.{w} A S.X₁ (q + 1), x = 0)
    (x : Ext.{w} A S.X₃ q) : x = 0 := by
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ A hS x rfl (hleft _)
  rw [hmid y, Ext.zero_comp] at hy
  exact hy.symm

theorem ext_eq_zero_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hzero : ∀ j, ∀ x : Ext.{w} A (B j) q, x = 0)
    (x : Ext.{w} A c.pt q) : x = 0 := by
  apply (Ext.addEquivBiproduct A hc q).injective
  ext j
  exact (hzero j _).trans ((map_zero (Ext.addEquivBiproduct A hc q)) ▸ rfl)

structure AcyclicPresentation {ι : Type t} (A : C) (F : ι → ℕ → C) (i : ι) where
  kernel : ι
  shift : ℕ
  middle : ℕ → C
  left : ∀ n, F kernel n ⟶ middle n
  right : ∀ n, middle n ⟶ F i (shift + n)
  comp_zero : ∀ n, left n ≫ right n = 0
  shortExact : ∀ n, (ShortComplex.mk (left n) (right n) (comp_zero n)).ShortExact
  acyclic : ∀ n q, 0 < q → ∀ x : Ext.{w} A (middle n) q, x = 0

theorem eventual_ext_zero_of_presentations {ι : Type t} (A : C) (F : ι → ℕ → C)
    (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i)
    (q : ℕ) (hq : 0 < q) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  have hstep : ∀ r q, 0 < q → l ≤ q + r → ∀ i,
      ∃ N, ∀ n, N ≤ n → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
    intro r
    induction r with
    | zero =>
      intro q hq hl i
      exact ⟨0, fun n _ x => hbound i n q (by simpa using hl) x⟩
    | succ r ih =>
      intro q hq hl i
      let P := presentation i
      obtain ⟨N, hN⟩ := ih (q + 1) (by omega) (by omega) P.kernel
      refine ⟨P.shift + N, fun n hn => ?_⟩
      have hnshift : P.shift ≤ n := by omega
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hnshift
      apply ext_eq_zero_of_shortExact A (P.shortExact t) q
      · exact P.acyclic t q hq
      · exact hN t (by omega)
  exact hstep l q hq (by omega) i

theorem eventual_all_positive_ext_zero_of_presentations {ι : Type t}
    (A : C) (F : ι → ℕ → C) (l : ℕ)
    (hbound : ∀ i n q, l ≤ q → ∀ x : Ext.{w} A (F i n) q, x = 0)
    (presentation : ∀ i, AcyclicPresentation A F i) (i : ι) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ x : Ext.{w} A (F i n) q, x = 0 := by
  classical
  have h : ∀ q : Fin l, ∃ N, ∀ n, N ≤ n →
      ∀ x : Ext.{w} A (F i n) (q.val + 1), x = 0 :=
    fun q => eventual_ext_zero_of_presentations A F l hbound presentation
      (q.val + 1) (by omega) i
  choose N hN using h
  refine ⟨Finset.univ.sup N, fun n hn q hq x => ?_⟩
  cases q with
  | zero => omega
  | succ q =>
    by_cases hl : l ≤ q + 1
    · exact hbound i n (q + 1) hl x
    · exact hN ⟨q, by omega⟩ n
        (le_trans (Finset.le_sup (f := N) (Finset.mem_univ _)) hn) x

end
end PiExponent.GeometrySupport.SerreDimensionShift

end OAI
end Source0572

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistPresentations.lean
section Source0573
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistPresentations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.TwistPresentations
noncomputable section
universe w
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry

abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X : Scheme.{0}}

def twistShiftIso (L : LineBundle X) (M : X.Modules) (n0 n : ℕ) :
    (moduleTwistFunctor L n).obj ((moduleTwistFunctor L n0).obj M) ≅
      (moduleTwistFunctor L (n0+n)).obj M :=
  eqToIso (by rw [moduleTwistFunctor_add]; rfl)

def twistFreeIsoBiproduct [HasFiniteBiproducts X.Modules]
    (L : LineBundle X) (n : ℕ) (I : Type) [Fintype I] :
    (moduleTwistFunctor L n).obj (SheafOfModules.free (R := X.ringCatSheaf) I) ≅
      ⨁ (fun _ : I => modulePow X L.sheaf n) :=
  (moduleTwistFunctor L n).mapIso
      (biproduct.isoCoproduct (fun _ : I => structureSheaf X)).symm ≪≫
    (moduleTwistFunctor L n).mapBiproduct (fun _ : I => structureSheaf X) ≪≫
    biproduct.mapIso (fun _ : I => moduleTwistUnitIso L n)

variable (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections)

abbrev presentationKernel : X.Modules := kernel (C := X.Modules) s.π

abbrev presentationMiddle (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj (SheafOfModules.free s.I)

def presentationLeft (n : ℕ) :
    (moduleTwistFunctor L n).obj (presentationKernel L s) ⟶ presentationMiddle L s n :=
  (moduleTwistFunctor L n).map (kernel.ι (C := X.Modules) s.π)

def presentationRight (n : ℕ) :
    presentationMiddle L s n ⟶ (moduleTwistFunctor L (n0+n)).obj M :=
  (moduleTwistFunctor L n).map s.π ≫ (twistShiftIso L M n0 n).hom

theorem presentation_comp_zero (n : ℕ) :
    presentationLeft L s n ≫ presentationRight L s n = 0 := by
  unfold presentationLeft presentationRight
  erw [← Category.assoc, ← Functor.map_comp, kernel.condition, Functor.map_zero, zero_comp]

theorem presentation_shortExact (n : ℕ) :
    (ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n)).ShortExact := by
  have : Epi s.π := s.epi
  have hbase : (ShortComplex.kernelSequence (C := X.Modules) s.π).ShortExact := {
    exact := ShortComplex.kernelSequence_exact s.π
    mono_f := equalizer.ι_mono (C := X.Modules) (f := s.π)
    epi_g := s.epi }
  have : Functor.PreservesZeroMorphisms (C := X.Modules) (D := X.Modules)
      (moduleTwistFunctor L n) := inferInstance
  let T := (ShortComplex.kernelSequence (C := X.Modules) s.π).map (moduleTwistFunctor L n)
  let e : T ≅ ShortComplex.mk (presentationLeft L s n) (presentationRight L s n)
      (presentation_comp_zero L s n) :=
    ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (twistShiftIso L M n0 n)
      (by
        simp only [presentationLeft]
        exact (Category.id_comp _).trans (Category.comp_id _).symm)
      (by
        simp only [presentationRight]
        exact Category.id_comp _)
  exact ShortComplex.shortExact_of_iso e (moduleTwistFunctor_shortExact L n _ hbase)

theorem presentationKernel_isFinitePresentation [IsLocallyNoetherian X]
    [M.IsFinitePresentation] [s.IsFiniteType] : (presentationKernel L s).IsFinitePresentation := by
  have := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n0 M
  let : ((moduleTwistFunctor L n0).obj M).IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      ((moduleTwistFunctor L n0).obj M)).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_generators_isFinitePresentation _ s

theorem presentationMiddle_ext_zero [HasExt.{w} X.Modules]
    (L : LineBundle X) {M : X.Modules} {n0 : ℕ}
    (s : ((moduleTwistFunctor L n0).obj M).GeneratingSections) [hs : s.IsFiniteType]
    (A : X.Modules)
    (hpow : ∀ n q, 0 < q → ∀ x : Ext.{w} A (modulePow X L.sheaf n) q, x = 0)
    (n q : ℕ) (hq : 0 < q) (x : Ext.{w} A (presentationMiddle L s n) q) : x = 0 := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let e := twistFreeIsoBiproduct L n s.I
  let e' := (extFunctorObj A q).mapIso e
  apply (ConcreteCategory.bijective_of_isIso e'.hom).injective
  change e'.hom x = e'.hom 0
  rw [map_zero]
  exact SerreDimensionShift.ext_eq_zero_of_biproduct A
    (biproduct.isBilimit (fun _ : s.I => modulePow X L.sheaf n)) q
    (fun _ => hpow n q hq) (e'.hom x)

def coherentTwistFamily (L : LineBundle X)
    (M : {M : X.Modules // M.IsFinitePresentation}) (n : ℕ) : X.Modules :=
  (moduleTwistFunctor L n).obj M.val

def acyclicPresentationOfGenerators [IsLocallyNoetherian X] [HasExt.{w} X.Modules]
    (L : LineBundle X) (M : {M : X.Modules // M.IsFinitePresentation}) (n0 : ℕ)
    (s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections) [s.IsFiniteType]
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{w} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0) :
    SerreDimensionShift.AcyclicPresentation.{w} (C := X.Modules) (schemeUnit X)
      (coherentTwistFamily L) M := by
  have : M.val.IsFinitePresentation := M.property
  exact {
    kernel := ⟨presentationKernel L s, presentationKernel_isFinitePresentation L s⟩
    shift := n0
    middle := presentationMiddle L s
    left := presentationLeft L s
    right := presentationRight L s
    comp_zero := presentation_comp_zero L s
    shortExact := presentation_shortExact L s
    acyclic := presentationMiddle_ext_zero L s (schemeUnit X) hpow }

end
end PiExponent.GeometrySupport.TwistPresentations

end OAI
end Source0573

-- Source: OAI/NumberTheory/PiExponent/Approximation/SerreAssembly.lean
section Source0574
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SerreAssembly.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.SerreAssembly

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
open TwistPresentations

abbrev schemeUnit (X : Scheme.{0}) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

variable {X : Scheme.{0}} [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance : HasExt.{1} X.Modules := HasExt.standard _

theorem eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (U : Fin l → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (hgenerate : ∀ M : {M : X.Modules // M.IsFinitePresentation},
      ∃ n0, ∃ s : ((moduleTwistFunctor L n0).obj M.val).GeneratingSections, s.IsFiniteType)
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  have hbound : ∀ i n q, l ≤ q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (coherentTwistFamily L i n) q,
        x = 0 := by
    intro i n q hq x
    let : i.val.IsFinitePresentation := i.property
    have := PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation L n i.val
    let : ((moduleTwistFunctor L n).obj i.val).IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
        ((moduleTwistFunctor L n).obj i.val)).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover
      ((moduleTwistFunctor L n).obj i.val) q hq x
  choose n0 s hs using hgenerate
  let presentation (i : {M : X.Modules // M.IsFinitePresentation}) :
      SerreDimensionShift.AcyclicPresentation.{1} (schemeUnit X)
        (coherentTwistFamily L) i := by
    let : (s i).IsFiniteType := hs i
    exact acyclicPresentationOfGenerators.{1} L i (n0 i) (s i) hpow
  exact SerreDimensionShift.eventual_all_positive_ext_zero_of_presentations
    (schemeUnit X) (coherentTwistFamily L) l hbound presentation
      ⟨M, inferInstance⟩

theorem eventual_twist_ext_zero_of_section_cover
    (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hpow : ∀ n q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X) (modulePow X L.sheaf n) q, x = 0)
    (M : X.Modules) [M.IsFinitePresentation] :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q →
      ∀ x : Ext.{1} (C := X.Modules) (schemeUnit X)
        ((moduleTwistFunctor L n).obj M) q, x = 0 := by
  apply eventual_twist_ext_zero_of_generation_and_standard_acyclicity
    L l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover
    _ hpow M
  intro A
  let : A.val.IsFinitePresentation := A.property
  obtain ⟨N, hN⟩ := PiExponent.AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A.val s hcover haffine
  obtain ⟨G, hG⟩ := hN N le_rfl
  exact ⟨N, G, hG⟩

end
end PiExponent.GeometrySupport.SerreAssembly

end OAI
end Source0574
