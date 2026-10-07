/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic zero-ideal, section-divisor and inverse-line-bundle degree arguments.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionDivisor
public import OAI.NumberTheory.PiExponent.Geometry.CurvePlaceSectionOrder
public import OAI.NumberTheory.PiExponent.Geometry.ProjectivePullbackFrames
public import OAI.NumberTheory.PiExponent.LocalAlgebra.IdealTensorPowers
public import OAI.NumberTheory.PiExponent.LocalAlgebra.PresentedIdealIso
public import OAI.NumberTheory.PiExponent.LocalAlgebra.SectionZeroIdeal

@[expose] public section

/-! Generic zero-ideal, section-divisor and Euler-degree bridges adapted from
openai/math Ampleness/ExceptionalCurveDegree.lean (Apache-2.0).
Only scheme-generic statements are extracted; no fixed-Y contact theorem.
See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.SectionIdealBridge
noncomputable section
open OAI AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open OAI.PiExponent PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

def inverseSection (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) :
    GlobalSections Y J.inverse.sheaf :=
  (lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι

theorem inverseSection_zeroIdeal (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    [J.sheaf.IsQuasicoherent] :
    zeroIdeal J.inverse (inverseSection J ι) = imageIdealSheaf ι := by
  classical
  have hc (y : Y) := common_affine_frames J J.inverse y
  choose U hy e f using hc
  let e' y := (e y).some
  let f' y := (f y).some
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let V := U y
    let a := Scheme.Modules.restrictUnitIso V.1.ι
    let b := tensorFrame J J.inverse V.1 (e' y) (f' y)
    rw [zeroIdeal_on_frame J.inverse (inverseSection J ι) V (f' y),
      imageIdealSheaf_on_frame ι V (e' y)]
    change Ideal.span {affineMapCoefficient V a (f' y)
      ((lineTensorInverseIso J).inv ≫ tensorInclusion J J.inverse ι)} = _
    erw [affineMapCoefficient_comp V a b (f' y),
      ← Ideal.span_singleton_mul_span_singleton]
    have hu : IsUnit (affineMapCoefficient V a b (lineTensorInverseIso J).inv) := by
      apply IsUnit.map V.1.topIso.hom.hom
      exact (end_isIso_iff _).mp
        (a.symm ≪≫ ((Scheme.Modules.restrictFunctor V.1.ι).mapIso
          (lineTensorInverseIso J)).symm ≪≫ b).isIso_hom
    rw [Ideal.span_singleton_eq_top.mpr hu, Ideal.top_mul]
    exact tensor_inclusion_ideal J J.inverse ι V (e' y) (f' y)

theorem inverseSection_zeroIdeal_eq_comap
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι) :
    zeroIdeal J.inverse (inverseSection J ι) = I.comap π := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  rw [inverseSection_zeroIdeal, PresentedIdealIso.imageIdealSheaf_eq_comap I π J ι hJ]

theorem zeroIdeal_pullback (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (f : Y ⟶ X) :
    zeroIdeal (L.pullback f) (pullbackSection f s) = (zeroIdeal L s).comap f := by
  classical
  have hlocal (y : Y) : ∃ V : Y.affineOpens, y ∈ V.1 ∧
      (zeroIdeal (L.pullback f) (pullbackSection f s)).ideal V =
        ((zeroIdeal L s).comap f).ideal V := by
    obtain ⟨U, hU, ⟨e⟩⟩ := PiExponentSeshadri.InvertibleLocal.affine_frame L (f y)
    obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset
      (show y ∈ f ⁻¹ᵁ U.1 from hU)
    let g := f.resLE U.1 V hVU
    obtain ⟨eF, he⟩ := exists_restricted_pullback_frame_all_of_factor f U.1 V g
      (Scheme.Hom.resLE_comp_ι f hVU).symm e
    refine ⟨⟨V, hV⟩, hyV, ?_⟩
    rw [zeroIdeal_on_frame (L.pullback f) (pullbackSection f s) ⟨V, hV⟩ eF,
      PiExponentSeshadri.IdealPullback.comap_ideal (zeroIdeal L s) f ⟨V, hV⟩ U hVU,
      zeroIdeal_on_frame L s U e, Ideal.map_span, Set.image_singleton]
    erw [he s]
    congr 2
    change V.topIso.hom ((f.resLE U.1 V hVU).appTop _) = _
    have ht : (f.resLE U.1 V hVU).appTop = U.1.topIso.hom ≫
        f.appLE U.1 V hVU ≫ V.topIso.inv := by
      simpa only [Scheme.Hom.appTop, Scheme.Hom.appLE_eq_app] using!
        (Scheme.Hom.resLE_app_top f hVU)
    rw [ht]
    simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  choose V hy hV using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top V
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · exact hV

theorem zeroIdeal_zero (L : LineBundle X) : zeroIdeal L 0 = ⊥ := by
  classical
  choose U hx e using fun x : X => PiExponentSeshadri.InvertibleLocal.affine_frame L x
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    rw [zeroIdeal_on_frame L 0 (U x) (e x).some]
    erw [restrictSection_zero, coefficient_zero, map_zero, Ideal.span_singleton_zero]
    rfl

theorem pullback_inverseSection_zeroIdeal
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) :
    zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)) =
      I.comap (g ≫ π) := by
  rw [zeroIdeal_pullback, inverseSection_zeroIdeal_eq_comap I π J ι hJ,
    Scheme.IdealSheafData.comap_comp]

theorem pullback_inverseSection_ne_zero
    (I : X.IdealSheafData) (π : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
    (hJ : PresentsPullbackIdeal I π J ι)
    {Z : Scheme.{0}} (g : Z ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥) :
    pullbackSection g (inverseSection J ι) ≠ 0 := by
  intro hs
  have h := pullback_inverseSection_zeroIdeal I π J ι hJ g
  rw [hs] at h
  exact hg (h.symm.trans (zeroIdeal_zero _))

theorem zeroIdeal_spec_top {A : Type} [CommRing A]
    (L : LineBundle (Spec (CommRingCat.of A)))
    (s : GlobalSections _ L.sheaf) (e : L.sheaf ≅ O (Spec (CommRingCat.of A))) :
    ((zeroIdeal L s).ideal ⟨⊤, isAffineOpen_top _⟩).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom =
        Ideal.span {LocalSectionOrder.localCoefficient e s} := by
  change (imageIdeal (L.dualSection s) ⊤).map _ = _
  rw [imageIdeal_top_of_frame (L.dualSection s)
    (InverseFrames.pairingFrame (lineTensorInverseIso L) e)]
  change (Ideal.span {endValue ((InverseFrames.pairingFrame (lineTensorInverseIso L) e).inv ≫
    InverseFrames.dualMap (lineTensorInverseIso L) s)}).map _ = _
  erw [InverseFrames.dualMap_coefficient]
  rw [Ideal.map_span, Set.image_singleton]
  rfl

def localIdeal {A : Type} [CommRing A] (I : X.IdealSheafData)
    (q : Spec (CommRingCat.of A) ⟶ X) : Ideal A :=
  ((I.comap q).ideal ⟨⊤, isAffineOpen_top _⟩).map
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom


section Curve
open CurveNormalizationModel CurveValuationCenter CurvePlaceCenter
open LocalSectionOrder
variable {E : Type} [Field E] [Algebra ℂ E]
variable (f : E) (hf : Transcendental ℂ f)
variable [FiniteDimensional (IntermediateField.adjoin ℂ {f}) E]

theorem divisor_eq_localIdeal_length
    (L : LineBundle (parameterCurve f hf))
    (s : GlobalSections _ L.sheaf) (hs : s ≠ 0) (p : NormalizedPlace ℂ E) :
    CurvePlaceSectionDivisor.divisor f hf L s hs p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸ localIdeal (zeroIdeal L s) (centerMorphism f hf p))).toNat := by
  let q := centerMorphism f hf p
  obtain ⟨e, he⟩ := LocalPullbackSectionOrder.exists_frame_coefficient_germ q L
  have hn : localCoefficient e (pullbackSection q s) ≠ 0 := by
    rw [he s]
    apply (map_ne_zero_iff _
      (ConcreteCategory.bijective_of_isIso (Scheme.stalkClosedPointTo q)).injective).mpr
    exact SectionZeroStalk.sectionGerm_ne_zero L s hs
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).openSet
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).frame _
      (CurveSectionDegree.affineFrameAt L (q (IsLocalRing.closedPoint _))).mem
  have hi : localIdeal (zeroIdeal L s) q =
      Ideal.span {localCoefficient e (pullbackSection q s)} := by
    unfold localIdeal
    rw [← zeroIdeal_pullback L s q]
    exact zeroIdeal_spec_top (L.pullback q) (pullbackSection q s) e
  rw [CurvePlaceSectionOrder.divisor_eq_local_order f hf L s hs p e, hi,
    CurveLocalOrder.length_quotient_span_eq_addVal hn]
  rfl

variable (I : X.IdealSheafData) (π : Y ⟶ X)
variable (J : LineBundle Y) (ι : J.sheaf ⟶ O Y)
variable (hJ : PresentsPullbackIdeal I π J ι)
variable (g : parameterCurve f hf ⟶ Y) (hg : I.comap (g ≫ π) ≠ ⊥)

def idealDivisor : NormalizedPlace ℂ E →₀ ℕ :=
  CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)

theorem idealDivisor_apply (p : NormalizedPlace ℂ E) :
    idealDivisor f hf I π J ι hJ g hg p =
      (Module.length (PlaceValuationRing.ring p)
        ((PlaceValuationRing.ring p) ⧸
          localIdeal I (centerMorphism f hf p ≫ g ≫ π))).toNat := by
  erw [idealDivisor, divisor_eq_localIdeal_length]
  have hi : localIdeal
      (zeroIdeal (J.inverse.pullback g) (pullbackSection g (inverseSection J ι)))
        (centerMorphism f hf p) = localIdeal I (centerMorphism f hf p ≫ g ≫ π) := by
    simp only [localIdeal, pullback_inverseSection_zeroIdeal I π J ι hJ g,
      Scheme.IdealSheafData.comap_comp]
  rw [hi]

theorem degree_eq_neg_idealDivisor_sum :
    eulerCharacteristic (parameterCurveStructureMap f hf) 1 (J.pullback g).sheaf -
      eulerCharacteristic (parameterCurveStructureMap f hf) 1
        (structureSheaf (parameterCurve f hf)) =
      -(idealDivisor f hf I π J ι hJ g hg).sum (fun _ n => (n : ℤ)) := by
  have hd := CurvePlaceSectionDivisor.degree_eq_euler_difference_full f hf
    (J.inverse.pullback g) (pullbackSection g (inverseSection J ι))
    (pullback_inverseSection_ne_zero I π J ι hJ g hg)
  have ht := parameterCurve_tensor_euler_add f hf (J.pullback g) (J.inverse.pullback g)
  let e : ((J.pullback g).tensor (J.inverse.pullback g)).sheaf ≅
      structureSheaf (parameterCurve f hf) :=
    (PiExponentSeshadri.PullbackTensor.iso g J J.inverse).symm ≪≫
      (Scheme.Modules.pullback g).mapIso (lineTensorInverseIso J) ≪≫ pullbackUnitIso g
  have he := eulerCharacteristic_iso (parameterCurveStructureMap f hf) e 1
  change _ = -(CurvePlaceSectionDivisor.divisor f hf (J.inverse.pullback g)
    (pullbackSection g (inverseSection J ι)) _).sum (fun _ n => (n : ℤ))
  omega


end Curve
end
end LogTwo.Geometry.SectionIdealBridge
