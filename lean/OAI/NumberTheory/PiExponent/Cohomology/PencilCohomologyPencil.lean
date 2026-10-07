/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/PencilCohomologyPencil.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyCharts
public import OAI.NumberTheory.PiExponent.Cohomology.PencilCohomologyFiniteCharts

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry.BaseSections
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {K : Type} [CommRing K] {X : Scheme.{0}}

lemma congr_apply (k : K →+* Γ(X,⊤)) (M : X.Modules) {U V : X.Opens}
    (h : U = V) (m : Sections k M U) :
    congr k M h m = M.presheaf.map (eqToHom h.symm).op m := by
  subst V
  change m = M.presheaf.map (𝟙 (op U)) m
  exact congrArg (fun f : M.presheaf.obj (op U) ⟶ M.presheaf.obj (op U) => f m)
    (M.presheaf.map_id (op U)).symm

def nestedRestriction (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    (M.restrict U.ι).restrict (X.homOfLE h) ≅ M.restrict W.ι :=
  ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M

lemma nestedBase (k : K →+* Γ(X,⊤)) {U W : X.Opens} (h : W ≤ U) :
    (X.homOfLE h).appTop.hom.comp (U.ι.appTop.hom.comp k) = W.ι.appTop.hom.comp k := by
  rw [← RingHom.comp_assoc, ← CommRingCat.hom_comp, ← Scheme.Hom.comp_appTop,
    Scheme.homOfLE_ι]

lemma chartTop_nested (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (m : Sections (U.ι.appTop.hom.comp k) (M.restrict U.ι) ⊤) :
    chartTop k M W (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k)
      (X.homOfLE h) (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h) m) =
        res k M h (chartTop k M U m) := by
  simp only [chartTop, LinearEquiv.trans_apply, restrictEquiv, congr_apply,
    chartMap, chartModuleMap, LinearMap.coe_comp,
    chartModuleEquiv, moduleIsoSections, openImmersionTop, restrictedOpenSections,
    nestedRestriction, Iso.trans_hom, Iso.symm_hom, Iso.app_hom]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ m))) =
    M.presheaf.map _ (M.presheaf.map _ m)
  have map_comp_apply {A B C : X.Opensᵒᵖ} (f : A ⟶ B) (g : B ⟶ C)
      (x : M.presheaf.obj A) :
      M.presheaf.map g (M.presheaf.map f x) = M.presheaf.map (f ≫ g) x := by
    exact (congrArg (fun h : M.presheaf.obj A ⟶ M.presheaf.obj C => h x)
      (M.presheaf.map_comp f g)).symm
  simp only [map_comp_apply]
  refine (map_comp_apply _ _ _).trans ?_
  symm
  exact map_comp_apply _ _ _

lemma chartMap_range_coherent (k : K →+* Γ(X,⊤)) (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U) :
    (chartMap (U.ι.appTop.hom.comp k) (W.ι.appTop.hom.comp k) (X.homOfLE h)
      (nestedBase k h) (M.restrict U.ι) (nestedRestriction M h)).range.map
        (chartTop k M W).toLinearMap = (res k M h).range := by
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨chartTop k M U z, (chartTop_nested k M h z).symm⟩
  · rintro ⟨z,rfl⟩
    refine ⟨_, ⟨(chartTop k M U).symm z,rfl⟩, ?_⟩
    exact (chartTop_nested k M h _).trans
      (congrArg (res k M h) ((chartTop k M U).apply_symm_apply z))

end
end PiExponentSeshadri.Geometry.BaseSections

end OAI
