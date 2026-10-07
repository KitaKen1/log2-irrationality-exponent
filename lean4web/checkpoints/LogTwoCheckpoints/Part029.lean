/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part009
public import LogTwoCheckpoints.Part011
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part021
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part024
public import LogTwoCheckpoints.Part025
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part027
public import LogTwoCheckpoints.Part028
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.ENat.BigOperators
public import Mathlib.Data.ENat.SuccOrder
public import Mathlib.Data.Opposite
public import Mathlib.RingTheory.Length
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentLocalLengths.lean
section Source0725
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentLocalLengths.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentJets.W28.LocalIntersection
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames

instance finite_componentsThrough {X : Scheme.{0}} [IsLocallyNoetherian X] (x : X) :
    Finite {C : irreducibleComponents X // x ∈ C.val} := by
  let : Finite (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).to_subtype
  exact Finite.of_equiv _ (stalkMinimalPrimesEquivComponentsThrough X x)

def componentLocalPrime (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val}) :
    Ideal (X.presheaf.stalk x) :=
  ((stalkMinimalPrimesEquivComponentsThrough X x).symm C).val

def componentLocalCutLength (X : Scheme.{0}) (x : X)
    (C : {C : irreducibleComponents X // x ∈ C.val})
    (c : X.presheaf.stalk x) : ℕ∞ :=
  Module.length (X.presheaf.stalk x)
    ((X.presheaf.stalk x) ⧸ (componentLocalPrime X x C ⊔ Ideal.span {c}))

theorem minimalPrimeCutSum_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (x : X) (c : X.presheaf.stalk x) :
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    minimalPrimeCutSum (⊥ : Ideal (X.presheaf.stalk x)) c =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C c := by
  classical
  let : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
  let : Fintype (minimalPrimes (X.presheaf.stalk x)) :=
    ((⊥ : Ideal (X.presheaf.stalk x)).finite_minimalPrimes_of_isNoetherianRing _).fintype
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (stalkMinimalPrimesEquivComponentsThrough X x)
  intro P
  let : P.val.IsPrime := P.property.1.1
  rw [Ideal.map_bot]
  have hlength := SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (RingEquiv.quotientBot (Localization.AtPrime P.val))
  have hsc : Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) =
      Module.length (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val)))
        (Localization.AtPrime P.val ⧸ (⊥ : Ideal (Localization.AtPrime P.val))) :=
    Module.length_eq_of_surjective (M := Localization.AtPrime P.val ⧸
      (⊥ : Ideal (Localization.AtPrime P.val))) Ideal.Quotient.mk_surjective
  rw [hsc,hlength,localMinimalPrime_length_eq_componentMultiplicity x P]
  congr 1
  exact (congrArg (fun Q : minimalPrimes (X.presheaf.stalk x) =>
    Module.length (X.presheaf.stalk x)
      ((X.presheaf.stalk x) ⧸ (Q.val ⊔ Ideal.span {c})))
    ((stalkMinimalPrimesEquivComponentsThrough X x).symm_apply_apply P)).symm

theorem zero_stalk_length_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (y : (SectionZeroIdeal.zeroIdeal L s).subscheme)
    (hy : (SectionZeroIdeal.zeroIdeal L s).subschemeι y ∈ U.1) :
    let x := (SectionZeroIdeal.zeroIdeal L s).subschemeι y
    letI : Fintype {C : irreducibleComponents X // x ∈ C.val} := Fintype.ofFinite _
    Module.length ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y)
      ((SectionZeroIdeal.zeroIdeal L s).subscheme.presheaf.stalk y) =
      ∑ C : {C : irreducibleComponents X // x ∈ C.val},
        (componentMultiplicity X C.val : ℕ∞) * componentLocalCutLength X x C
          (SectionZeroStalk.sectionGerm L s U e x hy) := by
  exact (zero_stalk_length_eq_minimalPrimeCutSum hd L s U e y hy).trans
    (minimalPrimeCutSum_eq_component_sum _ _)

end
end PiExponent.CurveCycle

end OAI
end Source0725

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentZeroPoints.lean
section Source0726
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentZeroPoints.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

def componentZeroToGlobal {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subscheme := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  refine ⟨i (J.subschemeι z), ?_⟩
  have hz := z.property
  change J.subschemeι z ∈ (J.support : Set (reducedComponent X C)) at hz
  change i (J.subschemeι z) ∈ ((zeroIdeal L s).support : Set X)
  erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)] at hz
  erw [zeroIdeal_support L s]
  change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
  rw [pullback_isoOpen_eq L s i] at hz
  exact hz

theorem componentZeroToGlobal_mem {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme) :
    (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ C.val :=
  reducedComponentι_mem X C _

def componentZeroPointEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X) :
    (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme ≃
    {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val} := by
  let i := reducedComponentι X C
  let I := zeroIdeal L s
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let g : J.subscheme → {y : I.subscheme // I.subschemeι y ∈ C.val} :=
    fun z => ⟨componentZeroToGlobal L s C z,componentZeroToGlobal_mem L s C z⟩
  apply Equiv.ofBijective g
  constructor
  · intro z w h
    apply J.subschemeι.isEmbedding.injective
    apply i.isEmbedding.injective
    exact congrArg (fun q => I.subschemeι q.val) h
  · intro y
    have hymem : I.subschemeι y.val ∈ Set.range i := by
      rw [reducedComponentι_range]
      exact y.property
    obtain ⟨z,hz⟩ := hymem
    have hzJ : z ∈ (J.support : Set (reducedComponent X C)) := by
      erw [zeroIdeal_support (L.pullback i) (pullbackSection i s)]
      change z ∉ isoOpen (pullbackSection i s)
      rw [pullback_isoOpen_eq L s i]
      change i z ∉ isoOpen s
      rw [hz]
      have hy := y.val.property
      change I.subschemeι y.val ∈ (I.support : Set X) at hy
      erw [zeroIdeal_support L s] at hy
      exact hy
    refine ⟨⟨z,hzJ⟩, ?_⟩
    apply Subtype.ext
    apply I.subschemeι.isEmbedding.injective
    exact hz

instance finite_componentZero {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    [Finite (zeroIdeal L s).subscheme] :
    Finite (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
  Finite.of_equiv _ (componentZeroPointEquiv L s C).symm

end
end PiExponent.CurveCycle

end OAI
end Source0726

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveCutQuotient.lean
section Source0727
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveCutQuotient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def cutQuotientEquivOfSurjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    A ⧸ (RingHom.ker f ⊔ Ideal.span {a}) ≃+* B ⧸ Ideal.span {f a} := by
  let g := (Ideal.Quotient.mk (Ideal.span {f a})).comp f
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hf
  have hk : RingHom.ker g = RingHom.ker f ⊔ Ideal.span {a} := by
    have he : RingHom.ker g = (Ideal.span {f a}).comap f := by
      ext b
      change Ideal.Quotient.mk (Ideal.span {f a}) (f b) = 0 ↔ f b ∈ Ideal.span {f a}
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [he]
    rw [← Set.image_singleton, ← Ideal.map_span, Ideal.comap_map_of_surjective f hf]
    rw [← RingHom.ker_eq_comap_bot,sup_comm]
  exact (Ideal.quotEquivOfEq hk.symm).trans (g.quotientKerEquivOfSurjective hg)

theorem cut_length_eq_of_surjective {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Surjective f) (a : A) :
    Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length B (B ⧸ Ideal.span {f a}) := by
  have hA : Module.length A (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) =
      Module.length (A ⧸ (RingHom.ker f ⊔ Ideal.span {a}))
        (A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) :=
    Module.length_eq_of_surjective
      (M := A ⧸ (RingHom.ker f ⊔ Ideal.span {a})) Ideal.Quotient.mk_surjective
  have hB : Module.length B (B ⧸ Ideal.span {f a}) =
      Module.length (B ⧸ Ideal.span {f a}) (B ⧸ Ideal.span {f a}) :=
    Module.length_eq_of_surjective
      (M := B ⧸ Ideal.span {f a}) Ideal.Quotient.mk_surjective
  exact hA.trans ((SectionZeroStalk.intrinsic_length_eq_of_ringEquiv
    (cutQuotientEquivOfSurjective f hf a)).trans hB.symm)

theorem reducedComponent_cut_length (X : Scheme.{0}) (C : irreducibleComponents X)
    (z : reducedComponent X C) (a : X.presheaf.stalk (reducedComponentι X C z)) :
    Module.length (X.presheaf.stalk (reducedComponentι X C z))
      ((X.presheaf.stalk (reducedComponentι X C z)) ⧸
        ((reducedComponentStalkPrime X C z).val ⊔ Ideal.span {a})) =
      Module.length ((reducedComponent X C).presheaf.stalk z)
        (((reducedComponent X C).presheaf.stalk z) ⧸
          Ideal.span {(reducedComponentι X C).stalkMap z a}) := by
  rw [← reducedComponentι_stalkMap_ker]
  exact cut_length_eq_of_surjective ((reducedComponentι X C).stalkMap z).hom
    ((reducedComponentι X C).stalkMap_surjective z) a

end
end PiExponent.CurveCycle

end OAI
end Source0727

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentCutLengths.lean
section Source0728
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentCutLengths.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal PiExponent.SectionZeroStalk

theorem componentLocalCutLength_eq_zero_stalk {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (z : (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme)
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z) ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι (componentZeroToGlobal L s C z))
      ⟨C,componentZeroToGlobal_mem L s C z⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z)
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk z) := by
  let i := reducedComponentι X C
  let J := zeroIdeal (L.pullback i) (pullbackSection i s)
  let y := J.subschemeι z
  let a := sectionGerm L s U e (i y) hy
  obtain ⟨eF,heF⟩ := exists_pullback_frame_sectionGerm i L s U e
  let V : (reducedComponent X C).affineOpens := ⟨i ⁻¹ᵁ U.1,U.2.preimage i⟩
  let b := sectionGerm (L.pullback i) (pullbackSection i s) V eF y hy
  have hb : b = i.stalkMap y a := heF y hy
  have hcut := reducedComponent_cut_length X C y a
  change componentLocalCutLength X (i y) ⟨C,reducedComponentι_mem X C y⟩ a =
    Module.length (J.subscheme.presheaf.stalk z) (J.subscheme.presheaf.stalk z)
  change Module.length (X.presheaf.stalk (i y))
    ((X.presheaf.stalk (i y)) ⧸ ((reducedComponentStalkPrime X C y).val ⊔ Ideal.span {a})) = _
  rw [hcut,← hb]
  have hsc : Module.length ((reducedComponent X C).presheaf.stalk y)
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) =
    Module.length (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b})
      (((reducedComponent X C).presheaf.stalk y) ⧸ Ideal.span {b}) :=
    Module.length_eq_of_surjective (M := ((reducedComponent X C).presheaf.stalk y) ⧸
      Ideal.span {b}) Ideal.Quotient.mk_surjective
  exact hsc.trans (intrinsic_length_eq_of_ringEquiv
    (zeroStalkQuotientEquiv (L.pullback i) (pullbackSection i s) V eF z hy))

theorem componentLocalCutLength_eq_zero_stalk_at {X : Scheme.{0}}
    (L : LineBundle X) (s : GlobalSections X L.sheaf) (C : irreducibleComponents X)
    (t : {y : (zeroIdeal L s).subscheme // (zeroIdeal L s).subschemeι y ∈ C.val})
    (U : X.affineOpens) (e : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (hy : (zeroIdeal L s).subschemeι t.val ∈ U.1) :
    componentLocalCutLength X ((zeroIdeal L s).subschemeι t.val) ⟨C,t.property⟩
      (sectionGerm L s U e _ hy) =
    Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
        ((componentZeroPointEquiv L s C).symm t))
      ((zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk
          ((componentZeroPointEquiv L s C).symm t)) := by
  obtain ⟨z,rfl⟩ := (componentZeroPointEquiv L s C).surjective t
  exact (componentLocalCutLength_eq_zero_stalk L s C z U e hy).trans
    (congrArg (fun w : (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme =>
      Module.length ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w)
        ((zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme.presheaf.stalk w))
      ((componentZeroPointEquiv L s C).symm_apply_apply z)).symm

end
end PiExponent.CurveCycle

end OAI
end Source0728

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentIncidence.lean
section Source0729
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentIncidence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

def sectionZeroIncidenceEquiv {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) :
    (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) ≃
    (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) where
  toFun p := ⟨p.2.val, (componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩⟩
  invFun q := ⟨(componentZeroPointEquiv L s q.1 q.2).val,
    ⟨q.1,(componentZeroPointEquiv L s q.1 q.2).property⟩⟩
  left_inv p := by
    rcases p with ⟨y,C,hC⟩
    dsimp only
    have h := (componentZeroPointEquiv L s C).apply_symm_apply ⟨y,hC⟩
    exact congrArg (fun t : {y : (zeroIdeal L s).subscheme //
      (zeroIdeal L s).subschemeι y ∈ C.val} =>
      (⟨t.val,⟨C,t.property⟩⟩ : Σ y : (zeroIdeal L s).subscheme,
        {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val})) h
  right_inv q := by
    rcases q with ⟨C,z⟩
    dsimp only
    exact congrArg (Sigma.mk C) ((componentZeroPointEquiv L s C).symm_apply_apply z)

theorem sum_component_zero_incidence {X : Scheme.{0}} (L : LineBundle X)
    (s : GlobalSections X L.sheaf) [Fintype (irreducibleComponents X)]
    [Fintype (zeroIdeal L s).subscheme]
    {R : Type*} [AddCommMonoid R]
    (w : ∀ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme → R) :
    letI : ∀ y : (zeroIdeal L s).subscheme,
      Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
        fun _ => Fintype.ofFinite _
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme,
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        w C.val ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)) =
      ∑ C : irreducibleComponents X, ∑ z, w C z := by
  classical
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme :=
        fun _ => Fintype.ofFinite _
  let a : (Σ y : (zeroIdeal L s).subscheme,
      {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val}) → R :=
    fun p => w p.2.val ((componentZeroPointEquiv L s p.2.val).symm ⟨p.1,p.2.property⟩)
  let b : (Σ C : irreducibleComponents X,
      (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme) → R :=
    fun q => w q.1 q.2
  exact (Fintype.sum_sigma a).symm.trans
    ((Fintype.sum_equiv (sectionZeroIncidenceEquiv L s) a b (fun _ => rfl)).trans
      (Fintype.sum_sigma b))

end
end PiExponent.CurveCycle

end OAI
end Source0729

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveCycleLengths.lean
section Source0730
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleLengths.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.SectionZeroIdeal

def stalkLength (Y : Scheme.{0}) (y : Y) : ℕ∞ :=
  Module.length (Y.presheaf.stalk y) (Y.presheaf.stalk y)

theorem zero_stalk_lengthNat_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (y : (zeroIdeal L s).subscheme) :
    letI : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      Fintype.ofFinite _
    (stalkLength (zeroIdeal L s).subscheme y).toNat =
      ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
        componentMultiplicity X C.val *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
            (pullbackSection (reducedComponentι X C.val) s)).subscheme
              ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat := by
  classical
  let : Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
    Fintype.ofFinite _
  let f := fun C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} =>
    (componentMultiplicity X C.val : ℕ∞) *
      stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
        (pullbackSection (reducedComponentι X C.val) s)).subscheme
          ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)
  have hlocal : stalkLength (zeroIdeal L s).subscheme y = ∑ C, f C := by
    obtain ⟨U,hy,⟨e⟩,_⟩ := common_affine_frames L L ((zeroIdeal L s).subschemeι y)
    refine (zero_stalk_length_eq_component_sum hd L s U e y hy).trans ?_
    apply Finset.sum_congr rfl
    intro C _
    exact congrArg (fun n : ℕ∞ => (componentMultiplicity X C.val : ℕ∞) * n)
      (componentLocalCutLength_eq_zero_stalk_at L s C.val ⟨y,C.property⟩ U e hy)
  have hsum : ∑ C, f C ≠ ⊤ := by
    rw [← hlocal]
    exact zero_stalk_length_ne_top hd L s y
  have hn := congrArg ENat.toNat hlocal
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsum)] at hn
  simpa only [f,ENat.toNat_mul,ENat.toNat_natCast] using hn

theorem zero_lengthNat_eq_component_sum {X : Scheme.{0}} [IsLocallyNoetherian X]
    [Fintype (irreducibleComponents X)] (hd : topologicalKrullDim X ≤ 1)
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    [Fintype (zeroIdeal L s).subscheme] :
    letI : ∀ C : irreducibleComponents X,
      Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
        (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
      ∑ C : irreducibleComponents X, componentMultiplicity X C *
        ∑ z, (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat := by
  classical
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  let : ∀ y : (zeroIdeal L s).subscheme,
    Fintype {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val} :=
      fun _ => Fintype.ofFinite _
  calc
    (∑ y : (zeroIdeal L s).subscheme, (stalkLength (zeroIdeal L s).subscheme y).toNat) =
        ∑ y : (zeroIdeal L s).subscheme,
          ∑ C : {C : irreducibleComponents X // (zeroIdeal L s).subschemeι y ∈ C.val},
            componentMultiplicity X C.val *
              (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C.val))
                (pullbackSection (reducedComponentι X C.val) s)).subscheme
                  ((componentZeroPointEquiv L s C.val).symm ⟨y,C.property⟩)).toNat :=
      Finset.sum_congr rfl (fun y _ => zero_stalk_lengthNat_eq_component_sum hd L s y)
    _ = ∑ C : irreducibleComponents X, ∑ z,
        componentMultiplicity X C *
          (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat :=
      sum_component_zero_incidence L s (fun C z => componentMultiplicity X C *
        (stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat)
    _ = _ := Finset.sum_congr rfl (fun C _ => (Finset.mul_sum _ _ _).symm)

end
end PiExponent.CurveCycle

end OAI
end Source0730

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CurveCycleEuler.lean
section Source0731
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveCycleEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

def componentEulerDegree {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : irreducibleComponents X) : ℤ :=
  eulerCharacteristic (reducedComponentι X C ≫ p) 1
    (L.pullback (reducedComponentι X C)).sheaf -
  eulerCharacteristic (reducedComponentι X C ≫ p) 1 (structureSheaf (reducedComponent X C))

def cycleEulerDegree {X : Scheme.{0}} [NoetherianSpace X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) : ℤ := by
  classical
  letI : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  exact ∑ C : irreducibleComponents X,
    (componentMultiplicity X C : ℤ) * componentEulerDegree p L C

theorem componentEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (C : irreducibleComponents X) :
    componentEulerDegree p (L.tensor M) C =
      componentEulerDegree p L C + componentEulerDegree p M C := by
  let i := reducedComponentι X C
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : CompactSpace (reducedComponent X C) :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : IsNoetherian (reducedComponent X C) := {}
  have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
    i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  have h := tensor_euler_add (i ≫ p) hdim (H.pullback i)
    (hH.pullback_closedImmersion H i) (L.pullback i) (M.pullback i)
  have he := eulerCharacteristic_iso (i ≫ p) (PiExponentSeshadri.PullbackTensor.iso i L M) 1
  unfold componentEulerDegree
  change eulerCharacteristic (i ≫ p) 1 ((L.tensor M).pullback i).sheaf =
    eulerCharacteristic (i ≫ p) 1 ((L.pullback i).tensor (M.pullback i)).sheaf at he
  rw [he]
  dsimp only [i] at h he ⊢
  omega

theorem cycleEulerDegree_tensor {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    cycleEulerDegree p (L.tensor M) = cycleEulerDegree p L + cycleEulerDegree p M := by
  classical
  unfold cycleEulerDegree
  simp only [componentEulerDegree_tensor p hd H hH L M,mul_add,Finset.sum_add_distrib]

theorem componentEulerDegree_zero_of_dimension_le_zero {X : Scheme.{0}}
    [IsLocallyNoetherian X] (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : irreducibleComponents X)
    (hdim : topologicalKrullDim (reducedComponent X C) ≤ 0) :
    componentEulerDegree p L C = 0 := by
  let : IsLocallyNoetherian (reducedComponent X C) :=
    LocallyOfFiniteType.isLocallyNoetherian (reducedComponentι X C)
  obtain ⟨e⟩ := NumericalAmpleness.lineBundle_trivial_of_dim_le_zero hdim
    (L.pullback (reducedComponentι X C))
  exact sub_eq_zero.mpr (eulerCharacteristic_iso (reducedComponentι X C ≫ p) e 1)

theorem regular_section_tensor_euler_eq_cycle {X : Scheme.{0}}
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s] :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  classical
  let : Fintype (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.fintype
  let : Finite (zeroIdeal L s).subscheme :=
    GeneralCartierDegreeLength.finite_zeroIdeal_of_mono p hd L s
  let : Fintype (zeroIdeal L s).subscheme := Fintype.ofFinite _
  let : ∀ C : irreducibleComponents X,
    Fintype (zeroIdeal (L.pullback (reducedComponentι X C))
      (pullbackSection (reducedComponentι X C) s)).subscheme := fun _ => Fintype.ofFinite _
  have hcomponent (C : irreducibleComponents X) :
      componentEulerDegree p L C =
        ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
          (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    let i := reducedComponentι X C
    let LC := L.pullback i
    let sC := pullbackSection i s
    have hsC : Mono sC := regular_component_section_mono X C L s
    have hdim : topologicalKrullDim (reducedComponent X C) ≤ 1 :=
      i.isEmbedding.isInducing.topologicalKrullDim_le.trans hd
    have hc := @regular_section_tensor_euler_eq_lengths _ inferInstance (i ≫ p)
      inferInstance hdim (H.pullback i) (hH.pullback_closedImmersion H i)
      LC (LC.pow 0) sC hsC
    have he := eulerCharacteristic_iso (i ≫ p) (moduleTensorRightUnit LC.sheaf) 1
    change eulerCharacteristic (i ≫ p) 1 (LC.tensor (LC.pow 0)).sheaf =
      eulerCharacteristic (i ≫ p) 1 LC.sheaf at he
    rw [he] at hc
    exact hc
  have hlength := zero_lengthNat_eq_component_sum hd L s
  have hlengthZ :
      (∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ)) =
        ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := by
    exact_mod_cast hlength
  calc
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
        ∑ y : (zeroIdeal L s).subscheme, ((stalkLength (zeroIdeal L s).subscheme y).toNat : ℤ) :=
      regular_section_tensor_euler_eq_lengths p hd H hH L M s
    _ = ∑ C : irreducibleComponents X, (componentMultiplicity X C : ℤ) *
          ∑ z, ((stalkLength (zeroIdeal (L.pullback (reducedComponentι X C))
            (pullbackSection (reducedComponentι X C) s)).subscheme z).toNat : ℤ) := hlengthZ
    _ = cycleEulerDegree p L := by
      unfold cycleEulerDegree
      apply Finset.sum_congr rfl
      intro C _
      exact congrArg (fun n : ℤ => (componentMultiplicity X C : ℤ) * n) (hcomponent C).symm

theorem tensor_euler_eq_cycle {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (H : LineBundle X) (hH : H.IsAmple)
    (L M : LineBundle X) :
    eulerCharacteristic p 1 (L.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf =
      cycleEulerDegree p L := by
  obtain ⟨B,s,t,hs,ht⟩ := NumericalAmpleness.exists_regular_twist_pair p H L hH
  let : Mono s := hs
  let : Mono t := ht
  have h₁ := regular_section_tensor_euler_eq_cycle p hd H hH (L.tensor B) M s
  have h₂ := regular_section_tensor_euler_eq_cycle p hd H hH B (L.tensor M) t
  have hcycle := cycleEulerDegree_tensor p hd H hH L B
  have ha := eulerCharacteristic_iso p
    (moduleTensorIso (moduleTensorComm L.sheaf B.sheaf) (Iso.refl M.sheaf) ≪≫
      lineTensorAssoc B L M) 1
  change eulerCharacteristic p 1 ((L.tensor B).tensor M).sheaf =
    eulerCharacteristic p 1 (B.tensor (L.tensor M)).sheaf at ha
  omega

end
end PiExponent.CurveCycle

end OAI
end Source0731

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveComponentsDimension.lean
section Source0732
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveComponentsDimension.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

def componentIntegralCurve {X : Scheme.{0}} (C : irreducibleComponents X)
    (hd : topologicalKrullDim (reducedComponent X C) = 1) :
    NumericalAmpleness.IntegralCurve X where
  scheme := reducedComponent X C
  embedding := reducedComponentι X C
  closedImmersion := inferInstance
  integral := inferInstance
  dimension := hd

theorem component_dimension_one_or_zero {X : Scheme.{0}}
    (hd : topologicalKrullDim X ≤ 1) (C : irreducibleComponents X) :
    topologicalKrullDim (reducedComponent X C) = 1 ∨
      topologicalKrullDim (reducedComponent X C) ≤ 0 := by
  have hdim := (reducedComponentι X C).isEmbedding.isInducing.topologicalKrullDim_le.trans hd
  by_cases h : topologicalKrullDim (reducedComponent X C) = 1
  · exact Or.inl h
  · right
    change topologicalKrullDim (reducedComponent X C) ≤ ((0 : ℕ) : WithBot ℕ∞)
    rw [← ENat.WithBot.lt_add_one_iff]
    simpa using lt_of_le_of_ne hdim h

end
end PiExponent.CurveCycle

end OAI
end Source0732

-- Source: OAI/NumberTheory/PiExponent/Geometry/CurveCycleNumerical.lean
section Source0733
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CurveCycleNumerical.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CurveCycle
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem cycleEulerDegree_margin {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * (cycleEulerDegree p H : ℝ) ≤ (cycleEulerDegree p L : ℝ) := by
  classical
  have hc (C : irreducibleComponents X) :
      ε * (componentEulerDegree p H C : ℝ) ≤ (componentEulerDegree p L C : ℝ) := by
    rcases component_dimension_one_or_zero hd C with hC | hC
    · exact hmargin (componentIntegralCurve C hC)
    · rw [componentEulerDegree_zero_of_dimension_le_zero p H C hC,
        componentEulerDegree_zero_of_dimension_le_zero p L C hC]
      simp
  unfold cycleEulerDegree
  simp only [Int.cast_sum,Int.cast_mul,Int.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro C _
  calc
    ε * ((componentMultiplicity X C : ℝ) * (componentEulerDegree p H C : ℝ)) =
        (componentMultiplicity X C : ℝ) * (ε * (componentEulerDegree p H C : ℝ)) := by ring
    _ ≤ (componentMultiplicity X C : ℝ) * (componentEulerDegree p L C : ℝ) :=
      mul_le_mul_of_nonneg_left (hc C) (Nat.cast_nonneg _)

theorem tensor_euler_margin {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (hd : topologicalKrullDim X ≤ 1) (A : LineBundle X) (hA : A.IsAmple)
    (L H M N : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : NumericalAmpleness.IntegralCurve X,
      ε * (NumericalAmpleness.curveDegree p H C : ℝ) ≤
        (NumericalAmpleness.curveDegree p L C : ℝ)) :
    ε * ((eulerCharacteristic p 1 (H.tensor M).sheaf - eulerCharacteristic p 1 M.sheaf : ℤ) : ℝ) ≤
      ((eulerCharacteristic p 1 (L.tensor N).sheaf - eulerCharacteristic p 1 N.sheaf : ℤ) : ℝ) := by
  rw [tensor_euler_eq_cycle p hd A hA H M,tensor_euler_eq_cycle p hd A hA L N]
  exact cycleEulerDegree_margin p hd L H ε hmargin

end
end PiExponent.CurveCycle

end OAI
end Source0733

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCurveMargin.lean
section Source0734
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerCurveMargin.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal

theorem mixedTop_curve_margin_aux (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H L : LineBundle X), H.IsAmple →
      topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞) →
      ∀ ε : ℝ, (∀ C : IntegralCurve X,
        ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) →
      ∀ ls : List (LineBundle X), ls.length = d →
      (∀ A ∈ ls, A.IsAmple) →
      ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
        (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) := by
  induction d with
  | zero =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    have hz : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    exact CurveCycle.tensor_euler_margin p hdim.le H hH L H
      (structureLineBundle X) (structureLineBundle X) ε hmargin
  | succ d ih =>
    intro X _ _ p _ H L hH hdim ε hmargin ls hlen hamp
    cases ls with
    | nil => simp at hlen
    | cons A ls =>
      have hlen' : ls.length = d := by simpa using hlen
      have hA : A.IsAmple := hamp A (by simp)
      obtain ⟨n, hn, s, hs⟩ := exists_positive_power_regular_section p A hA
      let := hs
      let D := zeroIdeal (A.pow n) s
      let j := D.subschemeι
      have hd := regular_ample_sectionZero_dimension p (A.pow n) (hA.pow n hn) s (d+1) hdim
      let : Nonempty D.subscheme := hd.1
      let : IsLocallyNoetherian D.subscheme := LocallyOfFiniteType.isLocallyNoetherian j
      let : CompactSpace D.subscheme := QuasiCompact.compactSpace_of_compactSpace j
      let : IsNoetherian D.subscheme := {}
      have hHD := LineBundle.IsAmple.pullback_closedImmersion H hH j
      have hm := ih (j ≫ p) (H.pullback j) (L.pullback j) hHD hd.2 ε
        (uniform_curve_margin_restrict p L H ε hmargin j)
        (ls.map (fun B => B.pullback j)) (by simpa using hlen') (by
          intro B hB
          obtain ⟨C, hC, rfl⟩ := List.mem_map.mp hB
          exact LineBundle.IsAmple.pullback_closedImmersion C (hamp C (by simp [hC])) j)
      have hrestrict (B : LineBundle X) :
          (n : ℤ) * mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) =
            mixedTop (lineEuler (j ≫ p) (d+1))
              (B.pullback j :: ls.map (fun C => C.pullback j)) := by
        have he := mixedTop_power_cartier_restriction p H hH (d+1)
          (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le)
          A n s (B :: ls) (by simp [hlen'])
        have hswap := congrFun
          (mixedDifference_perm (List.Perm.swap B A ls) (lineEuler p (d+1+1))
            (lineEuler_isoInvariant p (d+1+1))) (structureLineBundle X)
        change mixedTop (lineEuler p (d+1+1)) (A :: B :: ls) =
          mixedTop (lineEuler p (d+1+1)) (B :: A :: ls) at hswap
        rw [hswap] at he
        exact he
      rw [← hrestrict H, ← hrestrict L] at hm
      push_cast at hm
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn
      apply (mul_le_mul_iff_right₀ hnR).mp
      nlinarith [hm]

theorem mixedTop_curve_margin {X : Scheme.{0}} [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (ls : List (LineBundle X)) (hlen : ls.length = d) (hamp : ∀ A ∈ ls, A.IsAmple) :
    ε * (mixedTop (lineEuler p (d+1)) (H :: ls) : ℝ) ≤
      (mixedTop (lineEuler p (d+1)) (L :: ls) : ℝ) :=
  mixedTop_curve_margin_aux d p H L hH hdim ε hmargin ls hlen hamp

end
end PiExponent.NumericalAmpleness

end OAI
end Source0734

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerTop.lean
section Source0735
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerTop.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def topEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ) (L : LineBundle X) : ℤ :=
  (fwdDiff (1 : ℕ))^[d] (fun n => eulerCharacteristic p d (L.pow n).sheaf) 0

def mixedEuler (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (ls : List (LineBundle X)) : ℤ := mixedTop (lineEuler p d) ls

theorem mixedEuler_replicate (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L : LineBundle X) : mixedEuler p d (List.replicate d L) = topEuler p d L :=
  mixedTop_replicate L _ (lineEuler_isoInvariant p d) d

theorem mixedEuler_perm (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    {ls ks : List (LineBundle X)} (h : ls.Perm ks) :
    mixedEuler p d ls = mixedEuler p d ks :=
  congrFun (mixedDifference_perm h _ (lineEuler_isoInvariant p d)) (structureLineBundle X)

theorem lineEuler_mixedDegreeLE [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) : MixedDegreeLE d (lineEuler p d) :=
  mixedDifference_lineEuler_of_ample p H hH d hdim

theorem mixedEuler_tensor_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d)
    (A B : LineBundle X) (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (A.tensor B :: ls) = mixedEuler p d (A :: ls) + mixedEuler p d (B :: ls) :=
  congrFun (mixedDifference_tensor_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B ls hlen) (structureLineBundle X)

theorem topEuler_tensor_powers_binomial [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A B : LineBundle X) (a b : ℕ) :
    topEuler p d ((A.pow a).tensor (B.pow b)) =
      ∑ k ∈ Finset.range (d+1), (d.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(d-k) *
        mixedEuler p d (List.replicate k A ++ List.replicate (d-k) B) := by
  rw [← mixedEuler_replicate]
  exact mixedTop_tensor_powers_binomial (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B a b

theorem mixedEuler_tensor_powers_binomial_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (A B : LineBundle X) (a b n : ℕ)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    mixedEuler p d (List.replicate n ((A.pow a).tensor (B.pow b)) ++ ls) =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℤ) * (a : ℤ)^k * (b : ℤ)^(n-k) *
        mixedEuler p d (List.replicate k A ++ List.replicate (n-k) B ++ ls) :=
  mixedTop_tensor_powers_binomial_append (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) A B a b n ls hlen

end
end PiExponent.NumericalAmpleness

end OAI
end Source0735

-- Source: OAI/NumberTheory/PiExponent/Polynomials/MixedSlopePolynomial.lean
section Source0736
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/MixedSlopePolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open Polynomial Finset

def mixedSlopePolynomial (d : ℕ) (c : ℕ → ℝ) : Polynomial ℝ :=
  ∑ k ∈ range (d+1), C ((d.choose k : ℝ) * c k) * X^k

lemma mixedSlopePolynomial_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial d c).eval t =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * t^k := by
  simp only [mixedSlopePolynomial, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem mixedSlopePolynomial_derivative (d : ℕ) (c : ℕ → ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative =
      C ((d+1 : ℕ) : ℝ) * mixedSlopePolynomial d (fun k => c (k+1)) := by
  unfold mixedSlopePolynomial
  rw [Polynomial.derivative_sum, Finset.sum_range_succ']
  simp only [Polynomial.derivative_C_mul_X_pow, Nat.cast_zero, mul_zero,
    C_0, zero_mul, add_zero, Nat.add_sub_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have h : (((d+1).choose (k+1) : ℕ) : ℝ) * ((k+1 : ℕ) : ℝ) =
      ((d+1 : ℕ) : ℝ) * (d.choose k : ℝ) := by
    exact_mod_cast (Nat.add_one_mul_choose_eq d k).symm
  rw [← mul_assoc, ← C_mul]
  congr 2
  calc
    _ = (((d+1).choose (k+1) : ℝ) * ((k+1 : ℕ) : ℝ)) * c (k+1) := by ring
    _ = _ := by rw [h]; ring

lemma mixedSlopePolynomial_derivative_eval (d : ℕ) (c : ℕ → ℝ) (t : ℝ) :
    (mixedSlopePolynomial (d+1) c).derivative.eval t =
      (d+1 : ℕ) * (mixedSlopePolynomial d (fun k => c (k+1))).eval t := by
  rw [mixedSlopePolynomial_derivative]
  simp

theorem mixedSlopePolynomial_eval_div (d : ℕ) (c : ℕ → ℝ)
    (a b : ℝ) (hb : b ≠ 0) :
    b^d * (mixedSlopePolynomial d c).eval (a/b) =
      ∑ k ∈ range (d+1), (d.choose k : ℝ) * c k * b^(d-k) * a^k := by
  rw [mixedSlopePolynomial_eval, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp : b^d = b^(d-k) * b^k := by
    rw [← pow_add, Nat.sub_add_cancel hk']
  rw [div_pow, hp]
  field_simp

end
end PiExponent.NumericalAmpleness

end OAI
end Source0736

-- Source: OAI/NumberTheory/PiExponent/Cohomology/MixedEulerSlope.lean
section Source0737
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/MixedEulerSlope.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def eulerSlopeCoefficient (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) : ℝ :=
  mixedEuler p d (List.replicate k H ++ List.replicate (d-k) L)

def eulerSlopePolynomial (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) : Polynomial ℝ :=
  mixedSlopePolynomial d (eulerSlopeCoefficient p d L H)

theorem topEuler_iso (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) : topEuler p d L = topEuler p d M := by
  have he : (fun n => eulerCharacteristic p d (L.pow n).sheaf) =
      fun n => eulerCharacteristic p d (M.pow n).sheaf := by
    funext n
    exact eulerCharacteristic_iso p ((modulePowFunctor n).mapIso e) d
  unfold topEuler
  rw [he]

theorem mixedEuler_replicate_iso_append (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L M : LineBundle X) (e : L.sheaf ≅ M.sheaf) (n : ℕ) (ls : List (LineBundle X)) :
    mixedEuler p d (List.replicate n L ++ ls) =
      mixedEuler p d (List.replicate n M ++ ls) := by
  have he : mixedDifference (List.replicate n L ++ ls) (lineEuler p d) =
      mixedDifference (List.replicate n M ++ ls) (lineEuler p d) := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [List.replicate_succ, List.cons_append]
        rw [mixedDifference_iso_cons L M e _ _ (lineEuler_isoInvariant p d)]
        exact congrArg (tensorDifference M) ih
  exact congrFun he (structureLineBundle X)

theorem topEuler_slopeBundle_eq [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (a b : ℕ) (hb : 0 < b) :
    (topEuler p d (slopeBundle L H a b) : ℝ) =
      (b : ℝ)^d * (eulerSlopePolynomial p d L H).eval ((a : ℝ)/b) := by
  have he := topEuler_iso p d (slopeBundle L H a b) ((H.pow a).tensor (L.pow b))
    (moduleTensorComm (L.pow b).sheaf (H.pow a).sheaf)
  rw [he, topEuler_tensor_powers_binomial p H hH d hdim H L a b,
    eulerSlopePolynomial, mixedSlopePolynomial_eval_div d _ _ _ (by exact_mod_cast (Nat.ne_of_gt hb))]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  dsimp only [eulerSlopeCoefficient]
  ring

theorem mixedEuler_slopeBundle_eq_append [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (a b n : ℕ) (hb : 0 < b)
    (ls : List (LineBundle X)) (hlen : n+ls.length=d) :
    (mixedEuler p d (List.replicate n (slopeBundle L H a b) ++ ls) : ℝ) =
      (b : ℝ)^n * (mixedSlopePolynomial n (fun k =>
        (mixedEuler p d (List.replicate k H ++ List.replicate (n-k) L ++ ls) : ℝ))).eval
          ((a : ℝ)/b) := by
  rw [mixedEuler_replicate_iso_append p d (slopeBundle L H a b)
      ((H.pow a).tensor (L.pow b))
      (moduleTensorComm (L.pow b).sheaf (H.pow a).sheaf),
    mixedEuler_tensor_powers_binomial_append p H hH d hdim H L a b n ls hlen,
    mixedSlopePolynomial_eval_div n _ _ _ (by exact_mod_cast (Nat.ne_of_gt hb))]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem eulerSlopeCoefficient_succ (p : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (L H : LineBundle X) (k : ℕ) :
    eulerSlopeCoefficient p (d+1) L H (k+1) =
      (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
  dsimp only [eulerSlopeCoefficient]
  congr 1
  apply mixedEuler_perm
  simpa only [List.replicate_succ, List.cons_append, Nat.add_sub_add_right,
    List.append_nil] using
    (List.perm_middle (a := H)
      (l₁ := List.replicate k H ++ List.replicate (d-k) L) (l₂ := [])).symm

theorem eulerSlopePolynomial_derivative_eval_nat_div [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) (hb : 0 < b) :
    (b : ℝ)^d * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a : ℝ)/b) =
      (d+1 : ℕ) *
        (mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) : ℝ) := by
  rw [eulerSlopePolynomial, mixedSlopePolynomial_derivative_eval]
  have hc : (fun k => eulerSlopeCoefficient p (d+1) L H (k+1)) =
      fun k => (mixedEuler p (d+1)
        (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ) := by
    funext k
    exact eulerSlopeCoefficient_succ p d L H k
  rw [hc]
  have he := mixedEuler_slopeBundle_eq_append p H hH L (d+1)
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim) a b d hb [H] (by simp)
  have hp : mixedEuler p (d+1) (List.replicate d (slopeBundle L H a b) ++ [H]) =
      mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
    apply mixedEuler_perm
    simpa only [List.append_nil] using
      (List.perm_middle (a := H) (l₁ := List.replicate d (slopeBundle L H a b)) (l₂ := []))
  rw [hp] at he
  calc
    _ = (d+1 : ℕ) * ((b : ℝ)^d * (mixedSlopePolynomial d (fun k =>
        (mixedEuler p (d+1) (List.replicate k H ++ List.replicate (d-k) L ++ [H]) : ℝ))).eval
          ((a : ℝ)/b)) := by ring
    _ = _ := by rw [← he]

theorem mixedEuler_pow_cons [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d) (L : LineBundle X) (n : ℕ)
    (ls : List (LineBundle X)) (hlen : ls.length+1=d) :
    mixedEuler p d (L.pow n :: ls) = (n : ℤ) * mixedEuler p d (L :: ls) := by
  have he := congrFun (mixedDifference_pow_cons_of_degree (lineEuler_isoInvariant p d)
    (lineEuler_mixedDegreeLE p H hH d hdim) L n ls hlen) (structureLineBundle X)
  simpa only [mixedEuler, mixedTop, Pi.smul_apply, nsmul_eq_mul,
    Pi.mul_apply, Pi.natCast_apply] using he

theorem topEuler_slopeBundle_split [IsNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple) (L : LineBundle X) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ d+1) (a b : ℕ) :
    topEuler p (d+1) (slopeBundle L H a b) =
      (b : ℤ) * mixedEuler p (d+1) (L :: List.replicate d (slopeBundle L H a b)) +
      (a : ℤ) * mixedEuler p (d+1) (H :: List.replicate d (slopeBundle L H a b)) := by
  have hd : topologicalKrullDim X ≤ ((d+1 : ℕ) : WithBot ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim
  rw [← mixedEuler_replicate p (d+1), List.replicate_succ]
  change mixedEuler p (d+1) (((L.pow b).tensor (H.pow a)) ::
    List.replicate d (slopeBundle L H a b)) = _
  rw [mixedEuler_tensor_cons p H hH (d+1) hd _ _ _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd L b _ (by simp),
    mixedEuler_pow_cons p H hH (d+1) hd H a _ (by simp)]

end
end PiExponent.NumericalAmpleness

end OAI
end Source0737

-- Source: OAI/NumberTheory/PiExponent/Cohomology/NumericalEulerSlopeInputs.lean
section Source0738
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NumericalEulerSlopeInputs.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

theorem eulerSlopePolynomial_pos_of_ample [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = d) (a b : ℕ) (hb : 0 < b)
    (hamp : (slopeBundle L H a b).IsAmple) :
    0 < (eulerSlopePolynomial p d L H).eval ((a:ℝ)/b) := by
  have hp : (0:ℝ) < (topEuler p d (slopeBundle L H a b) : ℝ) := by
    exact_mod_cast topEuler_pos_of_ample p (slopeBundle L H a b) hamp d hdim
  rw [topEuler_slopeBundle_eq p H hH L d hdim.le a b hb] at hp
  exact (mul_pos_iff_of_pos_left (pow_pos (by exact_mod_cast hb : (0:ℝ)<b) d)).mp hp

theorem eulerSlopePolynomial_derivative_margin [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (ε : ℝ) (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (a b : ℕ) (hb : 0 < b) (hamp : (slopeBundle L H a b).IsAmple) :
    ((a:ℝ)/b+ε) * (eulerSlopePolynomial p (d+1) L H).derivative.eval ((a:ℝ)/b) ≤
      ((d+1:ℕ):ℝ) * (eulerSlopePolynomial p (d+1) L H).eval ((a:ℝ)/b) := by
  let M := slopeBundle L H a b
  let TL : ℝ := mixedEuler p (d+1) (L :: List.replicate d M)
  let TH : ℝ := mixedEuler p (d+1) (H :: List.replicate d M)
  let P := eulerSlopePolynomial p (d+1) L H
  have hdimle : topologicalKrullDim X ≤ d+1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  have hvolume := topEuler_slopeBundle_eq p H hH L (d+1) hdim.le a b hb
  have hsplit : (topEuler p (d+1) M : ℝ) = (b:ℝ)*TL+(a:ℝ)*TH := by
    dsimp only [M, TL, TH]
    exact_mod_cast topEuler_slopeBundle_split p H hH L d hdimle a b
  have heq : (b:ℝ)*TL+(a:ℝ)*TH = (b:ℝ)^(d+1)*P.eval ((a:ℝ)/b) :=
    hsplit.symm.trans hvolume
  have hderivative : (b:ℝ)^d * P.derivative.eval ((a:ℝ)/b) = ((d+1:ℕ):ℝ)*TH :=
    eulerSlopePolynomial_derivative_eval_nat_div p H hH L d hdimle a b hb
  have hmix : ε*TH ≤ TL := mixedTop_curve_margin p H L hH d hdim ε hmargin
    (List.replicate d M) (by simp) (by
      intro A hA
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp hA
      exact hamp)
  have hbR : (0:ℝ) < b := by exact_mod_cast hb
  have hm : ((a:ℝ)+(b:ℝ)*ε)*TH ≤ (b:ℝ)*TL+(a:ℝ)*TH := by
    have h := mul_le_mul_of_nonneg_left hmix hbR.le
    nlinarith
  apply (mul_le_mul_iff_right₀ (pow_pos hbR (d+1))).mp
  change (b:ℝ)^(d+1) * (((a:ℝ)/b+ε)*P.derivative.eval ((a:ℝ)/b)) ≤
    (b:ℝ)^(d+1) * (((d+1:ℕ):ℝ)*P.eval ((a:ℝ)/b))
  calc
    _ = ((a:ℝ)+(b:ℝ)*ε) * ((b:ℝ)^d * P.derivative.eval ((a:ℝ)/b)) := by
      rw [pow_succ]
      field_simp [ne_of_gt hbR]
    _ = ((d+1:ℕ):ℝ) * (((a:ℝ)+(b:ℝ)*ε)*TH) := by rw [hderivative]; ring
    _ ≤ ((d+1:ℕ):ℝ) * ((b:ℝ)*TL+(a:ℝ)*TH) :=
      mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg _)
    _ = _ := by rw [heq]; ring

theorem isAmple_of_lower_numerical_criterion [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (r : ℕ) (i : X ⟶ ProjectiveO1.projectiveSpace ℂ (Fin (r+1))) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ (Fin (r+1)) = p)
    (H L : LineBundle X) (hH : H.IsAmple) (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1:ℕ):WithBot ℕ∞))
    (hlower : LowerClosedNumericalCriterion p H d)
    (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  exact isAmple_of_lower_criterion_of_euler_slope_polynomial p r i hi H L hH d
    (by simpa only [Nat.cast_add, Nat.cast_one] using hdim.le) hlower ε hε hmargin
    (eulerSlopePolynomial p (d+1) L H)
    (fun a b hb => topEuler_slopeBundle_eq p H hH L (d+1) hdim.le a b hb)
    (eulerSlopePolynomial_pos_of_ample p H L hH (d+1) hdim)
    (eulerSlopePolynomial_derivative_margin p H L hH d hdim ε hmargin)

end
end PiExponent.NumericalAmpleness

end OAI
end Source0738

-- Source: OAI/NumberTheory/PiExponent/Ampleness/NumericalAmplenessTheorem.lean
section Source0739
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NumericalAmplenessTheorem.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry

theorem isAmple_of_uniform_curve_margin_dimension (d : ℕ) :
    ∀ {X : Scheme.{0}} [IsNoetherian X]
      (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
      (H L : LineBundle X), H.IsAmple → topologicalKrullDim X ≤ d →
      ∀ ε : ℝ, 0 < ε →
        (∀ C : IntegralCurve X,
          ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) → L.IsAmple := by
  induction d with
  | zero =>
    intro X _ p _ H L hH hdim ε hε hmargin
    exact isAmple_of_proper_dimension_zero p (by simpa using hdim) L
  | succ d ih =>
    have hintegral : ∀ {Y : Scheme.{0}} [IsNoetherian Y] [IsIntegral Y]
        (p : Y ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
        (H L : LineBundle Y), H.IsAmple → topologicalKrullDim Y ≤ ((d+1:ℕ):WithBot ℕ∞) →
        ∀ ε : ℝ, 0 < ε →
          (∀ C : IntegralCurve Y,
            ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) → L.IsAmple := by
      intro Y _ _ p _ H L hH hdim ε hε hmargin
      by_cases hsmall : topologicalKrullDim Y ≤ d
      · exact ih p H L hH hsmall ε hε hmargin
      have heq : topologicalKrullDim Y = ((d+1:ℕ):WithBot ℕ∞) := by
        apply le_antisymm hdim
        have hnot : ¬ topologicalKrullDim Y < (d:WithBot ℕ∞)+1 := by
          simpa only [ENat.WithBot.lt_add_one_iff] using hsmall
        simpa only [Nat.cast_add, Nat.cast_one] using le_of_not_gt hnot
      obtain ⟨r, i, hiClosed, hi⟩ := ample_finite_projective_embedding p H hH
      let : IsClosedImmersion i := hiClosed
      apply isAmple_of_lower_numerical_criterion p r i hi H L hH d heq _ ε hε hmargin
      intro I hI M δ hδ hM
      let : IsLocallyNoetherian I.subscheme :=
        LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
      let : CompactSpace I.subscheme := QuasiCompact.compactSpace_of_compactSpace I.subschemeι
      let : IsNoetherian I.subscheme := {}
      exact ih (I.subschemeι ≫ p) (H.pullback I.subschemeι) M
        (hH.pullback_closedImmersion H I.subschemeι) hI δ hδ hM
    intro X _ p _ H L hH hdim ε hε hmargin
    apply isAmple_of_integral_closed_restrictions p L H hH
    intro Y _ j _
    let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian j
    let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace j
    let : IsNoetherian Y := {}
    apply hintegral (j ≫ p) (H.pullback j) (L.pullback j)
      (hH.pullback_closedImmersion H j)
      ((ProperAmpleFiniteDimension.closedImmersion_dimension_le j).trans hdim) ε hε
    exact uniform_curve_margin_restrict p L H ε hmargin j

theorem isAmple_of_uniform_curve_margin {X : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H L : LineBundle X) (hH : H.IsAmple) (ε : ℝ) (hε : 0 < ε)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ)) : L.IsAmple := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let : IsNoetherian X := {}
  obtain ⟨d,hd⟩ := ProperAmpleFiniteDimension.exists_dimension_bound_of_proper_ample p H hH
  exact isAmple_of_uniform_curve_margin_dimension d p H L hH hd ε hε hmargin

end
end PiExponent.NumericalAmpleness

end OAI
end Source0739

-- Source: LogTwo/Geometry/MatrixAmpleness.lean
section Source0740
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Ampleness of the actual interpolation bundle A tensor J follows from
the constructed auxiliary ample bundle and the proved uniform curve margin.
Bounded-degree jet surjectivity and the determinant estimate remain later steps. -/
namespace LogTwo.Geometry.MatrixBlowup
open OAI PiExponent AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry NumericalAmpleness
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

theorem chosenWeights_interpolationBundle_ample
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m) *
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    ∀ (y : Fin w.K → ℂ), (∀ j, y j ≠ 0) → Function.Injective y →
      ∀ (a : Fin w.K → Fin m → ℂ) (F : ℚ), 1 / w.theta < F →
      (interpolationBundle w y a (truncationOrders w F)).IsAmple := by
  dsimp only
  intro y hy0 hy a F hF
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  exact isAmple_of_uniform_curve_margin (structureMap w y a (truncationOrders w F))
    (H w y hy0 a (truncationOrders w F)) (interpolationBundle w y a (truncationOrders w F))
    (H_ample w y hy0 a (truncationOrders w F)) (degreeMargin w y hy0 a (truncationOrders w F))
    (degreeMargin_pos w y hy0 a (truncationOrders w F))
    (chosenWeights_uniform_curve_margin n hn m q hq hgrowth y hy0 hy a F hF)

end
end LogTwo.Geometry.MatrixBlowup
end Source0740

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalPowerSections.lean
section Source0741
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalPowerSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.Geometry
variable {X Y : Scheme}

lemma InvertibleLocal.pullback_frame_equation {I : X.IdealSheafData} {f : Y ⟶ X}
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    (I.ideal V).map (f.appLE V.1 U.1 hUV).hom =
      Ideal.span {affineMapCoefficient U e (Scheme.Modules.restrictUnitIso U.1.ι) ι} := by
  let g : O U.1.toScheme ⟶ O U.1.toScheme :=
    e.inv ≫ PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι
  have H : ((I.comap f).comap U.1.ι).ideal ⟨⊤,isAffineOpen_top _⟩ =
      Ideal.span {endValue g} := by
    change _ = Ideal.span {UnitEndomorphism.equation g ⊤}
    rw [← UnitEndomorphism.image_principal g ⊤,
      ← PiExponentSeshadri.InvertibleLocal.restricted_image_on_chart J ι hJ U.1.ι
        ⟨⊤,isAffineOpen_top _⟩ V (by simpa only [Scheme.Opens.ι_image_top] using hUV)]
    ext r
    change (∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤) s = r) ↔
      ∃ s, (PiExponentSeshadri.InvertibleLocal.restrictedInclusion J ι U.1.ι).val.app (.op ⊤)
        (e.inv.val.app (.op ⊤) s) = r
    constructor
    · rintro ⟨s,hs⟩
      refine ⟨e.hom.val.app (.op ⊤) s,?_⟩
      have ht : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s :=
        congrArg (fun k : J.sheaf.restrict U.1.ι ⟶ J.sheaf.restrict U.1.ι =>
          k.val.app (.op ⊤) s) e.hom_inv_id
      rw [ht]; exact hs
    · rintro ⟨s,hs⟩; exact ⟨e.inv.val.app (.op ⊤) s,hs⟩
  rw [IdealPullback.comap_ι_top,IdealPullback.comap_ideal I f U V hUV] at H
  have H' := congrArg (Ideal.map U.1.topIso.hom.hom) H
  rw [Ideal.map_map,Ideal.map_span,Set.image_singleton] at H'
  have hi : U.1.topIso.hom.hom.comp U.1.topIso.inv.hom = RingHom.id _ := by
    ext x; exact U.1.topIso.inv_hom_id_apply x
  rw [hi,Ideal.map_id] at H'
  exact H'

theorem framed_section_range {Z : Scheme} {M : Z.Modules}
    (e : M ≅ O Z) (a : M ⟶ O Z) :
    (a.val.app (.op ⊤)).hom.range =
      Ideal.span {endValue (e.inv ≫ a)} := by
  rw [show endValue (e.inv ≫ a) =
    UnitEndomorphism.equation (e.inv ≫ a) ⊤ from rfl,
    ← UnitEndomorphism.image_principal]
  ext r
  change (∃ s, a.val.app (.op ⊤) s = r) ↔
    ∃ s, a.val.app (.op ⊤) (e.inv.val.app (.op ⊤) s) = r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨e.hom.val.app (.op ⊤) s, ?_⟩
    have h : e.inv.val.app (.op ⊤) (e.hom.val.app (.op ⊤) s) = s := by
      exact congrArg (fun k : M ⟶ M => k.val.app (.op ⊤) s) e.hom_inv_id
    rw [h]
    exact hs
  · rintro ⟨s, hs⟩
    exact ⟨e.inv.val.app (.op ⊤) s, hs⟩

theorem idealPower_restricted_range (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    ((PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
      (idealPowerInclusion J ι n) U.1.ι).val.app (.op ⊤)).hom.range =
      (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom := by
  erw [framed_section_range (idealPowerFrame J U.1 e n)]
  have h := idealPowerInclusion_ideal J ι U e n
  rw [← InvertibleLocal.pullback_frame_equation J ι hJ U V hUV, ← Ideal.map_pow] at h
  have h' := congrArg (Ideal.map U.1.topIso.inv.hom) h
  rw [Ideal.map_span, Set.image_singleton] at h'
  simpa only [affineMapCoefficient, U.1.topIso.hom_inv_id_apply,
    PiExponentSeshadri.InvertibleLocal.restrictedInclusion, Category.assoc] using! h'

def powerChartIdeal (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ)
    (U : Y.affineOpens) (V : X.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    Ideal Γ(U.1.toScheme, ⊤) :=
  (((I.ideal V)^n).map (f.appLE V.1 U.1 hUV).hom).map U.1.topIso.inv.hom

abbrev powerSections (J : LineBundle Y) (n : ℕ) (U : Y.Opens) :
    ModuleCat Γ(U.toScheme, ⊤) := ((J.pow n).sheaf.restrict U.ι).val.obj (.op ⊤)

def idealPowerSectionsEquiv (f : Y ⟶ X) (I : X.IdealSheafData)
    (J : LineBundle Y) (ι : J.sheaf ⟶ O Y) (hJ : PresentsPullbackIdeal I f J ι)
    (n : ℕ) (U : Y.affineOpens) (V : X.affineOpens)
    (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    powerSections J n U.1 ≃ₗ[Γ(U.1.toScheme, ⊤)]
      ↥(powerChartIdeal f I n U V hUV) := by
  letI : Mono ι := hJ.1
  letI := idealPowerInclusion_mono J ι n
  let a := PiExponentSeshadri.InvertibleLocal.restrictedInclusion (J.pow n)
    (idealPowerInclusion J ι n) U.1.ι
  have ha : Mono (C := U.1.toScheme.Modules) a :=
    @PiExponentSeshadri.InvertibleLocal.restrictedInclusion_mono Y U.1.toScheme
      (J.pow n) (idealPowerInclusion J ι n) U.1.ι inferInstance
      (@idealPowerInclusion_mono Y J ι hJ.1 n)
  have hinj : Function.Injective (a.val.app (.op ⊤)) := by
    let : Mono a.val :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.toPresheafOfModules U.1.toScheme)
        inferInstance _ _ a ha
    exact PresheafOfModules.injective_of_mono a.val (.op ⊤)
  let φ : powerSections J n U.1 →ₗ[Γ(U.1.toScheme, ⊤)]
      Γ(U.1.toScheme, ⊤) := (a.val.app (.op ⊤)).hom
  have hr : φ.range = (powerChartIdeal f I n U V hUV : Submodule Γ(U.1.toScheme, ⊤) _) :=
    idealPower_restricted_range f I J ι hJ n U V hUV e
  exact (LinearEquiv.ofInjective φ hinj).trans (LinearEquiv.ofEq _ _ hr)

end PiExponentSeshadri.Geometry
end

end OAI
end Source0741

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalPowerPresentation.lean
section Source0742
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalPowerPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PresentedIdealIso
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule PiExponentSeshadri.Frames
open PiExponent.SectionImageIdeal
variable {X Y : Scheme.{0}}

theorem imageIdealSheaf_idealPowerInclusion
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) (n : ℕ)
    [J.sheaf.IsQuasicoherent] [(J.pow n).sheaf.IsQuasicoherent] :
    imageIdealSheaf (idealPowerInclusion J ι n) = (imageIdealSheaf ι)^n := by
  classical
  have hlocal (y : Y) : ∃ U : Y.affineOpens, y ∈ U.1 ∧
      Nonempty (J.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
    obtain ⟨V, hyV, ⟨e⟩⟩ := J.locallyRankOne y
    obtain ⟨U, hU, hyU, hUV⟩ := exists_isAffineOpen_mem_and_subset hyV
    exact ⟨⟨U,hU⟩,hyU,⟨restrictOpenFrame hUV e⟩⟩
  choose U hy he using hlocal
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U
  · apply top_unique
    intro y _
    exact Opens.mem_iSup.mpr ⟨y, hy y⟩
  · intro y
    let e := Classical.choice (he y)
    rw [Scheme.IdealSheafData.ideal_pow]
    change (imageIdealSheaf (idealPowerInclusion J ι n)).ideal (U y) =
      ((imageIdealSheaf ι).ideal (U y))^n
    erw [imageIdealSheaf_on_frame (idealPowerInclusion J ι n) (U y)
        (idealPowerFrame J (U y).1 e n),
      imageIdealSheaf_on_frame ι (U y) e]
    exact idealPowerInclusion_ideal J ι (U y) e n

theorem idealPower_presents
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    PresentsPullbackIdeal (I^n) f (J.pow n) (idealPowerInclusion J ι n) := by
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation J
  let := GeometrySupport.LineBundleCoherent.lineBundle_isFinitePresentation (J.pow n)
  let : J.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData J.sheaf).choose.isQuasicoherent
  let : (J.pow n).sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (J.pow n).sheaf).choose.isQuasicoherent
  let : Mono ι := hJ.1
  refine ⟨@idealPowerInclusion_mono Y J ι hJ.1 n, ?_⟩
  intro U V hUV
  have h := imageIdealSheaf_idealPowerInclusion J ι n
  rw [imageIdealSheaf_eq_comap I f J ι hJ,
    ← PiExponentSeshadri.IdealPullback.comap_pow] at h
  have hu := congrArg (fun K : Y.IdealSheafData => K.ideal U) h
  exact hu.trans (PiExponentSeshadri.IdealPullback.comap_ideal (I^n) f U V hUV)

def powerIso
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (J.pow n).sheaf ≅ closedModule ((I^n).comap f) :=
  @asIso Y.Modules _ _ _
    (toIdealModule (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))
    (toIdealModule_isIso (I^n) f (J.pow n) (idealPowerInclusion J ι n)
      (idealPower_presents I f J ι hJ n))

@[reassoc (attr := simp)] theorem powerIso_hom_inclusion
    (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y)
    (hJ : PresentsPullbackIdeal I f J ι) (n : ℕ) :
    (powerIso I f J ι hJ n).hom ≫ closedInclusion ((I^n).comap f) =
      idealPowerInclusion J ι n :=
  toIdealModule_inclusion (I^n) f (J.pow n) (idealPowerInclusion J ι n)
    (idealPower_presents I f J ι hJ n)

end PiExponent.PresentedIdealIso

end

end OAI
end Source0742

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPullbackMap.lean
section Source0743
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealPullbackMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.IdealPullbackMap
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (J : Y.IdealSheafData) (hIJ : I ≤ J.map f)

include hIJ in

theorem comp_quotient_zero :
    (closedInclusion I ≫ structureMap f) ≫
      (Scheme.Modules.pushforward f).map (structureMap J.subschemeι) = 0 := by
  apply hom_ext_affine
  intro U
  ext x
  have hr : (closedInclusion I).app U.1 x ∈ I.ideal U := by
    rw [← closed_image I U]
    exact ⟨x, rfl⟩
  let r : Γ(X, U.1) := (closedInclusion I).app U.1 x
  have hz : r ∈ (J.subschemeι ≫ f).ker.ideal U := (hIJ U) hr
  rw [Scheme.Hom.ker_apply] at hz
  change (J.subschemeι ≫ f).app U.1 r = 0 at hz
  rw [Scheme.Hom.comp_app] at hz
  exact hz

def map : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule J) :=
  kernel.lift ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι))
    (closedInclusion I ≫ structureMap f) (comp_quotient_zero f I J hIJ) ≫
      (PreservesKernel.iso (Scheme.Modules.pushforward f) (structureMap J.subschemeι)).inv

@[reassoc (attr := simp)] theorem map_inclusion :
    map f I J hIJ ≫ (Scheme.Modules.pushforward f).map (closedInclusion J) =
      closedInclusion I ≫ structureMap f := by
  rw [map]
  erw [Category.assoc]
  have he : (PreservesKernel.iso (Scheme.Modules.pushforward f)
      (structureMap J.subschemeι)).inv ≫
      (Scheme.Modules.pushforward f).map (closedInclusion J) =
      kernel.ι ((Scheme.Modules.pushforward f).map (structureMap J.subschemeι)) :=
    PreservesKernel.iso_inv_ι _ _
  erw [he, kernel.lift_ι]

def comap : closedModule I ⟶ (Scheme.Modules.pushforward f).obj (closedModule (I.comap f)) :=
  map f I (I.comap f) (I.le_map_comap f)

@[reassoc (attr := simp)] theorem comap_inclusion :
    comap f I ≫ (Scheme.Modules.pushforward f).map (closedInclusion (I.comap f)) =
      closedInclusion I ≫ structureMap f := map_inclusion _ _ _ _

end
end PiExponent.GeometrySupport.IdealPullbackMap

end OAI
end Source0743

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRecoveryMap.lean
section Source0744
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRecoveryMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

def ordinaryMap (n : ℕ) : closedModule (I^n) ⟶
    (Scheme.Modules.pushforward f).obj (modulePow Y E.sheaf n) :=
  IdealPullbackMap.comap f (I^n) ≫
    (Scheme.Modules.pushforward f).map (PresentedIdealIso.powerIso I f E ι hE n).inv

@[reassoc (attr := simp)] theorem ordinaryMap_inclusion (n : ℕ) :
    ordinaryMap f I E ι hE n ≫
      (Scheme.Modules.pushforward f).map (idealPowerInclusion E ι n) =
    closedInclusion (I^n) ≫ structureMap f := by
  have he : (PresentedIdealIso.powerIso I f E ι hE n).inv ≫
      idealPowerInclusion E ι n = closedInclusion ((I^n).comap f) := by
    rw [← PresentedIdealIso.powerIso_hom_inclusion I f E ι hE n]
    exact Iso.inv_hom_id_assoc _ _
  rw [ordinaryMap, Category.assoc]
  erw [← Functor.map_comp, he]
  exact IdealPullbackMap.comap_inclusion f (I^n)

def twistedMap (A : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor A n).obj (closedModule (I^n)) ⟶
      (Scheme.Modules.pushforward f).obj ((E.tensor (A.pullback f)).pow n).sheaf :=
  (moduleTwistFunctor A n).map (ordinaryMap f I E ι hE n) ≫
    (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).inv ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n).hom ≫
          (lineTensorPow E (A.pullback f) n).inv)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end Source0744

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TwistLocalSections.lean
section Source0745
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TwistLocalSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
variable {X : Scheme.{0}}

theorem moduleTwist_app_bijective (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    {M N : X.Modules} (β : M ⟶ N) (n : ℕ)
    (h : Function.Bijective (β.app U)) :
    Function.Bijective (((moduleTwistFunctor L n).map β).app U) := by
  let E := SheafOfModules.evaluation U.toScheme.ringCatSheaf (op (⊤ : U.toScheme.Opens))
  have he := NatIso.isIso_map_iff
    (Functor.isoWhiskerRight (moduleTwistRestrictFrame L U e n) E) β
  have hright : IsIso (((Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (β.app (U.ι ''ᵁ ⊤))
    exact U.ι_image_top.symm ▸ h
  have hleft := he.mpr hright
  have hb := ConcreteCategory.bijective_of_isIso
    ((((moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι) ⋙ E).map β))
  change Function.Bijective (((moduleTwistFunctor L n).map β).app (U.ι ''ᵁ ⊤)) at hb
  exact U.ι_image_top ▸ hb

end
end PiExponentSeshadri.Geometry

end OAI
end Source0745

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRecoveryTwist.lean
section Source0746
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ExceptionalRecoveryTwist.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ExceptionalRecoveryMap
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealModule
variable {X Y : Scheme.{0}} (f : Y ⟶ X) [QuasiCompact f]
    (I : X.IdealSheafData) (E : LineBundle Y)
    (ι : E.sheaf ⟶ structureSheaf Y) (hE : PresentsPullbackIdeal I f E ι)

theorem twistedMap_app_bijective (A : LineBundle X) (n : ℕ) (U : X.Opens)
    (e : A.sheaf.restrict U.ι ≅ structureSheaf U.toScheme)
    (h : Function.Bijective ((ordinaryMap f I E ι hE n).app U)) :
    Function.Bijective ((twistedMap f I E ι hE A n).app U) := by
  let a := (ProjectionFormula.twistIso f (modulePow Y E.sheaf n) A n).symm ≪≫
    (Scheme.Modules.pushforward f).mapIso
      (moduleTwistPowerIso (A.pullback f) (modulePow Y E.sheaf n) n ≪≫
        (lineTensorPow E (A.pullback f) n).symm)
  let : IsIso ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom) :=
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso a).isIso_hom
  have ha := ConcreteCategory.bijective_of_isIso
    ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map a.hom)
  exact ha.comp (moduleTwist_app_bijective A U e (ordinaryMap f I E ι hE n) n h)

end
end PiExponent.GeometrySupport.ExceptionalRecoveryMap

end OAI
end Source0746

-- Source: OAI/NumberTheory/PiExponent/Ampleness/FiniteAffineFrames.lean
section Source0747
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/FiniteAffineFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme.{0}}

theorem LineBundle.finite_affine_frame_cover [CompactSpace X] (L : LineBundle X) :
    ∃ k : ℕ, ∃ U : Fin k → X.affineOpens,
      (⨆ i, (U i).1) = ⊤ ∧
      ∀ i, Nonempty (L.sheaf.restrict (U i).1.ι ≅ structureSheaf (U i).1.toScheme) := by
  classical
  have hex (x : X) := common_affine_frames L L x
  choose V hx he _ using hex
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => ((V x).1 : Set X)) (fun x => (V x).1.isOpen)
    (by intro x _; exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let e := (Fintype.equivFin s).symm
  refine ⟨Fintype.card s, fun i => V (e i).val, ?_, fun i => he (e i).val⟩
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (show x ∈ Set.univ from trivial))
  obtain ⟨hi, hx⟩ := Set.mem_iUnion.mp hi
  exact Opens.mem_iSup.mpr ⟨e.symm ⟨i, hi⟩, by simpa using hx⟩

end
end PiExponentSeshadri.Geometry

end OAI
end Source0747

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechOneConverse.lean
section Source0748
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechOneConverse.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.GeometrySupport.CechOneConverse
section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

theorem hasPrimitives_of_ext_one_zero (V : Opens X)
    (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i)
    (hzero : ∀ x : Ext.{u+1} (freeOpen R V) M 1, x = 0) :
    CechHigher.HasPrimitives R U M 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  let : Mono S.f := hS.mono_f
  intro c hc
  have hcI : differential R U S.X₂ (CechHigher.map R U M S.f c) = 0 := by
    rw [← map_differential, hc, CechHigher.map_zero]
  obtain ⟨b, hb⟩ := FreeCechSections.injective_hasPrimitives U R S.X₂ 0
    (CechHigher.map R U M S.f c) hcI
  have hcomp : CechHigher.map R U S.X₂ S.g (CechHigher.map R U M S.f c) = 0 := by
    funext t
    change (c t ≫ S.f) ≫ S.g = 0
    rw [Category.assoc, S.zero, comp_zero]
  have hclosed : differential R U S.X₃ (CechHigher.map R U S.X₂ S.g b) = 0 := by
    rw [← map_differential, hb, hcomp]
  obtain ⟨g, hg⟩ := CechZero.augmentation_exists R U S.X₃ V hUV hcover _ hclosed
  obtain ⟨t, ht⟩ := CechOne.lift_of_ext_one_zero R S hS V hzero g
  have hkernel : CechHigher.map R U S.X₂ S.g
      (b - augmentation R U S.X₂ V hUV t) = 0 := by
    rw [CechHigher.map_sub, ← CechZero.augmentation_comp, ht, hg, sub_self]
  obtain ⟨a, ha⟩ := lift_kernel_cochain R U S hS _ hkernel
  refine ⟨a, ?_⟩
  apply map_injective R U M S.f
  rw [map_differential, ha, differential_sub, augmentation_closed, sub_zero, hb]

end

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque PiExponentSeshadri.Geometry
universe u
variable {Y : Scheme.{u}} {J : Type u} (U : J → Y.Opens) (M : Y.Modules)
local instance : HasExt.{u+1} Y.Modules := HasExt.standard _

abbrev schemeUnit : Y.Modules := SheafOfModules.unit Y.ringCatSheaf

abbrev schemeFreeOpen (V : Y.Opens) : Y.Modules := freeOpen Y.ringCatSheaf V

theorem hasPrimitives_of_cohomology_one_zero
    (hcover : (⨆ i, U i) = ⊤)
    (hzero : ∀ x : Ext.{u+1} (C := Y.Modules) schemeUnit M 1, x = 0) :
    CechHigher.HasPrimitives Y.ringCatSheaf U M 0 := by
  let e : schemeFreeOpen ⊤ ≅ schemeUnit :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso Y.ringCatSheaf
  apply hasPrimitives_of_ext_one_zero Y.ringCatSheaf U M ⊤ (fun _ => le_top)
    (by rw [hcover])
  change ∀ x : Ext.{u+1} (C := Y.Modules) (schemeFreeOpen ⊤) M 1, x = 0
  intro x
  have h := congrArg (fun z => (Ext.mk₀ e.hom).comp z (zero_add 1))
    (hzero ((Ext.mk₀ e.inv).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end PiExponent.GeometrySupport.CechOneConverse

end

end OAI
end Source0748

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechH1Transfer.lean
section Source0749
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechH1Transfer.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechH1Transfer
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher

universe u
variable {X Y : Scheme.{u}} {J : Type u}

abbrev schemeFreeOpen (Z : Scheme.{u}) (U : Z.Opens) : Z.Modules :=
  freeOpen Z.ringCatSheaf U

abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

@[instance_reducible] def freeOpenHomAddCommGroup
    (Z : Scheme.{u}) (U : Z.Opens) (M : Z.Modules) :
    AddCommGroup (freeOpen Z.ringCatSheaf U ⟶ M) :=
  inferInstanceAs (AddCommGroup (schemeFreeOpen Z U ⟶ M))

@[instance_reducible] def higherCochainAddCommGroup
    (Z : Scheme.{u}) (U : J → Z.Opens) (M : Z.Modules) (q : ℕ) :
    AddCommGroup (CechHigher.Cochain Z.ringCatSheaf U M q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen Z (intersection U t) ⟶ M))

attribute [local instance] freeOpenHomAddCommGroup higherCochainAddCommGroup
  PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

structure SectionComparison (U : J → X.Opens) (V : J → Y.Opens)
    (M : X.Modules) (N : Y.Modules) where
  vertex : ∀ t : Fin 1 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) ≃+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair : ∀ t : Fin 2 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  triple : ∀ t : Fin 3 → J,
    (schemeFreeOpen X (intersection U t) ⟶ M) →+
      (schemeFreeOpen Y (intersection V t) ⟶ N)
  pair_injective : ∀ t, Function.Injective (pair t)
  pair_restrict : ∀ (t : Fin 2 → J) (k : Fin 2) b,
    pair t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (vertex (t ∘ k.succAbove) b)
  triple_restrict : ∀ (t : Fin 3 → J) (k : Fin 3) b,
    triple t (restrictHom X.ringCatSheaf (faceLE U t k) b) =
      restrictHom Y.ringCatSheaf (faceLE V t k) (pair (t ∘ k.succAbove) b)

namespace SectionComparison
variable {U : J → X.Opens} {V : J → Y.Opens} {M : X.Modules} {N : Y.Modules}
    (P : SectionComparison U V M N)

def cochainZero : CechHigher.Cochain X.ringCatSheaf U M 0 ≃+
    CechHigher.Cochain Y.ringCatSheaf V N 0 where
  toFun b t := P.vertex t (b t)
  invFun b t := (P.vertex t).symm (b t)
  left_inv b := by funext t; exact (P.vertex t).symm_apply_apply _
  right_inv b := by funext t; exact (P.vertex t).apply_symm_apply _
  map_add' b c := by funext t; exact map_add (P.vertex t) _ _

def cochainOne : CechHigher.Cochain X.ringCatSheaf U M 1 →+
    CechHigher.Cochain Y.ringCatSheaf V N 1 where
  toFun b t := P.pair t (b t)
  map_zero' := by funext t; exact map_zero (P.pair t)
  map_add' b c := by funext t; exact map_add (P.pair t) _ _

def cochainTwo : CechHigher.Cochain X.ringCatSheaf U M 2 →+
    CechHigher.Cochain Y.ringCatSheaf V N 2 where
  toFun b t := P.triple t (b t)
  map_zero' := by funext t; exact map_zero (P.triple t)
  map_add' b c := by funext t; exact map_add (P.triple t) _ _

theorem cochainOne_injective : Function.Injective P.cochainOne := by
  intro a b h
  funext t
  exact P.pair_injective t (congrFun h t)

theorem map_differential_zero (b : CechHigher.Cochain X.ringCatSheaf U M 0) :
    P.cochainOne (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainZero b) := by
  funext t
  change P.pair t (∑ k : Fin 2, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.pair_restrict]
  rfl

theorem map_differential_one (b : CechHigher.Cochain X.ringCatSheaf U M 1) :
    P.cochainTwo (differential X.ringCatSheaf U M b) =
      differential Y.ringCatSheaf V N (P.cochainOne b) := by
  funext t
  change P.triple t (∑ k : Fin 3, (-1 : ℤ) ^ k.val •
    restrictHom X.ringCatSheaf (faceLE U t k) (b (t ∘ k.succAbove))) = _
  erw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  erw [map_zsmul, P.triple_restrict]
  rfl

include P

theorem hasPrimitives (h : CechHigher.HasPrimitives Y.ringCatSheaf V N 0) :
    CechHigher.HasPrimitives X.ringCatSheaf U M 0 := by
  intro c hc
  have hclosed : differential Y.ringCatSheaf V N (P.cochainOne c) = 0 := by
    rw [← P.map_differential_one, hc]
    exact P.cochainTwo.map_zero
  obtain ⟨b, hb⟩ := h (P.cochainOne c) hclosed
  refine ⟨P.cochainZero.symm b, ?_⟩
  apply P.cochainOne_injective
  rw [P.map_differential_zero, AddEquiv.apply_symm_apply, hb]

theorem cohomology_one_zero [IsNoetherian X] [M.IsQuasicoherent]
    (hU : ∀ i, IsAffineOpen (U i)) (hcoverU : (⨆ i, U i) = ⊤)
    (hcoverV : (⨆ i, V i) = ⊤)
    (hN : ∀ z : Ext.{u+1} (C := Y.Modules) (schemeUnit Y) N 1, z = 0)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M 1) : x = 0 := by
  have hprimitive := P.hasPrimitives
    (CechOneConverse.hasPrimitives_of_cohomology_one_zero V N hcoverV hN)
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M 1, z = 0 := by
    apply CechHigher.ext_one_eq_zero X.ringCatSheaf U M ⊤ (fun _ => le_top)
      (by rw [hcoverU]) _ hprimitive
    intro t z
    have he : intersection U t = U (t 0) := by
      apply le_antisymm (iInf_le _ 0)
      apply le_iInf
      intro i
      exact le_of_eq (congrArg (fun j => U (t j)) (Subsingleton.elim 0 i))
    have ha : IsAffineOpen (intersection U t) := he.symm ▸ hU (t 0)
    exact PiExponentSeshadri.FiniteCoverCohomology.affine_open_ext_zero
      (intersection U t) ha M 0 z
  let e : schemeFreeOpen X ⊤ ≅ schemeUnit X :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have h := congrArg (fun z => (Ext.mk₀ e.inv).comp z (zero_add 1))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add 1)))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end SectionComparison
end
end PiExponent.GeometrySupport.CechH1Transfer

end OAI
end Source0749
