/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part006
public import LogTwoCheckpoints.Part007
public import LogTwoCheckpoints.Part008
public import Batteries.Logic
public import Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Module.SnakeLemma
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.Data.FunLike.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.KrullDimension.LocalRing
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/EndomorphismEulerAdditivity.lean
section Source0225
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/EndomorphismEulerAdditivity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.EndomorphismEuler

section InducedMaps

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

def kernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) : LinearMap.ker u →ₗ[A] LinearMap.ker v :=
  (f.domRestrict (LinearMap.ker u)).codRestrict (LinearMap.ker v) (by
    intro x
    change v (f x) = 0
    rw [← show f (u x) = v (f x) from DFunLike.congr_fun comm (x : M),
      show u x = 0 from x.property, map_zero])

@[simp] theorem kernelMap_apply (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : LinearMap.ker u) :
    (kernelMap u v f comm x : N) = f x := rfl

theorem kernelMap_injective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Injective f) :
    Function.Injective (kernelMap u v f comm) := by
  intro x y h
  apply Subtype.ext
  apply hf
  exact congrArg Subtype.val h

def cokernelMap (u : M →ₗ[A] M) (v : N →ₗ[A] N) (f : M →ₗ[A] N)
    (comm : f.comp u = v.comp f) :
    (M ⧸ LinearMap.range u) →ₗ[A] (N ⧸ LinearMap.range v) :=
  Submodule.mapQ (LinearMap.range u) (LinearMap.range v) f (by
    rintro x ⟨y, rfl⟩
    exact ⟨f y, (DFunLike.congr_fun comm y).symm⟩)

@[simp] theorem cokernelMap_mk (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (x : M) :
    cokernelMap u v f comm ((LinearMap.range u).mkQ x) =
      (LinearMap.range v).mkQ (f x) := rfl

theorem cokernelMap_surjective (u : M →ₗ[A] M) (v : N →ₗ[A] N)
    (f : M →ₗ[A] N) (comm : f.comp u = v.comp f) (hf : Function.Surjective f) :
    Function.Surjective (cokernelMap u v f comm) := by
  intro y
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range v) y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨(LinearMap.range u).mkQ x, rfl⟩

end InducedMaps

section ActualSnake

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

variable (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
  (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
  (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
  (hf : Function.Injective f) (hg : Function.Surjective g)

include hExact hf in

theorem kernelMap_exact :
    Function.Exact (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright) := by
  intro x
  constructor
  · intro hx
    have hgx : g x = 0 := congrArg Subtype.val hx
    obtain ⟨y, hy⟩ := (hExact x).mp hgx
    have huy : u₁ y = 0 := by
      apply hf
      calc
        f (u₁ y) = u₂ (f y) := DFunLike.congr_fun hleft y
        _ = 0 := by rw [hy]; exact x.property
        _ = f 0 := (map_zero f).symm
    exact ⟨⟨y, huy⟩, Subtype.ext hy⟩
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    exact hExact.apply_apply_eq_zero (y : M₁)

include hExact hg in

theorem cokernelMap_exact :
    Function.Exact (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₂) x
  constructor
  · intro hx
    change (LinearMap.range u₃).mkQ (g x) = 0 at hx
    have hmem : g x ∈ LinearMap.range u₃ := (Submodule.Quotient.mk_eq_zero (LinearMap.range u₃)).mp hx
    obtain ⟨z, hz⟩ := hmem
    obtain ⟨y, hy⟩ := hg z
    have hxy : g (x - u₂ y) = 0 := by
      rw [map_sub, show g (u₂ y) = u₃ (g y) from DFunLike.congr_fun hright y,
        hy, hz, sub_self]
    obtain ⟨w, hw⟩ := (hExact (x - u₂ y)).mp hxy
    refine ⟨(LinearMap.range u₁).mkQ w, ?_⟩
    change (LinearMap.range u₂).mkQ (f w) = (LinearMap.range u₂).mkQ x
    rw [hw, map_sub]
    have hz₂ : (LinearMap.range u₂).mkQ (u₂ y) = 0 :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range u₂)).mpr ⟨y, rfl⟩
    rw [hz₂, sub_zero]
  · rintro ⟨y, hy⟩
    rw [← hy]
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range u₁) y
    change (LinearMap.range u₃).mkQ (g (f y)) = 0
    rw [hExact.apply_apply_eq_zero, map_zero]

noncomputable def connecting :
    LinearMap.ker u₃ →ₗ[A] (M₁ ⧸ LinearMap.range u₁) :=
  SnakeLemma.δ' u₁ u₂ u₃ f g hExact f g hExact hleft hright
    (LinearMap.ker u₃).subtype (LinearMap.exact_subtype_ker_map u₃)
    (LinearMap.range u₁).mkQ (LinearMap.exact_map_mkQ_range u₁) hg hf

theorem exact_kernel_connecting :
    Function.Exact (kernelMap u₂ u₃ g hright)
      (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg) := by
  exact SnakeLemma.exact_δ'_right
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₂ := (LinearMap.ker u₂).subtype) (hι₂ := LinearMap.exact_subtype_ker_map u₂)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    hg hf (kernelMap u₂ u₃ g hright) (by ext x; rfl)
    (Submodule.subtype_injective _)

theorem exact_connecting_cokernel :
    Function.Exact (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
      (cokernelMap u₁ u₂ f hleft) := by
  exact SnakeLemma.exact_δ'_left
    (i₁ := u₁) (i₂ := u₂) (i₃ := u₃)
    (f₁ := f) (f₂ := g) (hf := hExact) (g₁ := f) (g₂ := g) (hg := hExact)
    (h₁ := hleft) (h₂ := hright)
    (ι₃ := (LinearMap.ker u₃).subtype) (hι₃ := LinearMap.exact_subtype_ker_map u₃)
    (π₁ := (LinearMap.range u₁).mkQ) (hπ₁ := LinearMap.exact_map_mkQ_range u₁)
    (π₂ := (LinearMap.range u₂).mkQ) (hπ₂ := LinearMap.exact_map_mkQ_range u₂)
    hg hf (cokernelMap u₁ u₂ f hleft) (by ext x; rfl)
    (Submodule.mkQ_surjective _)

end ActualSnake

section LengthAlgebra

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem length_eq_kernel_add_range (f : M →ₗ[A] N) :
    Module.length A M = Module.length A (LinearMap.ker f) +
      Module.length A (LinearMap.range f) := by
  calc
    Module.length A M = Module.length A (LinearMap.ker f) +
        Module.length A (M ⧸ LinearMap.ker f) :=
      Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
        (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
        (LinearMap.exact_subtype_mkQ _)
    _ = _ := by rw [(LinearMap.quotKerEquivRange f).length_eq]

end LengthAlgebra

section SixTerm

variable {A X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [CommRing A]
  [AddCommGroup X₁] [Module A X₁] [AddCommGroup X₂] [Module A X₂]
  [AddCommGroup X₃] [Module A X₃] [AddCommGroup X₄] [Module A X₄]
  [AddCommGroup X₅] [Module A X₅] [AddCommGroup X₆] [Module A X₆]

theorem six_term_length_cross_add
    (a : X₁ →ₗ[A] X₂) (b : X₂ →ₗ[A] X₃) (c : X₃ →ₗ[A] X₄)
    (d : X₄ →ₗ[A] X₅) (e : X₅ →ₗ[A] X₆)
    (ha : Function.Injective a) (he : Function.Surjective e)
    (hab : Function.Exact a b) (hbc : Function.Exact b c)
    (hcd : Function.Exact c d) (hde : Function.Exact d e) :
    Module.length A X₅ + Module.length A X₁ + Module.length A X₃ =
      Module.length A X₂ + Module.length A X₄ + Module.length A X₆ := by
  have h₁ : Module.length A X₁ = Module.length A (LinearMap.range a) :=
    (LinearEquiv.ofInjective a ha).length_eq
  have h₂ : Module.length A X₂ = Module.length A (LinearMap.range a) +
      Module.length A (LinearMap.range b) := by
    rw [length_eq_kernel_add_range b, ← LinearMap.exact_iff.mp hab]
  have h₃ : Module.length A X₃ = Module.length A (LinearMap.range b) +
      Module.length A (LinearMap.range c) := by
    rw [length_eq_kernel_add_range c, ← LinearMap.exact_iff.mp hbc]
  have h₄ : Module.length A X₄ = Module.length A (LinearMap.range c) +
      Module.length A (LinearMap.range d) := by
    rw [length_eq_kernel_add_range d, ← LinearMap.exact_iff.mp hcd]
  have h₅ : Module.length A X₅ = Module.length A (LinearMap.range d) +
      Module.length A (LinearMap.range e) := by
    rw [length_eq_kernel_add_range e, ← LinearMap.exact_iff.mp hde]
  have h₆ : Module.length A (LinearMap.range e) = Module.length A X₆ := by
    rw [LinearMap.range_eq_top.mpr he]
    exact Module.length_top
  rw [h₁, h₂, h₃, h₄, h₅, ← h₆]
  ac_rfl

end SixTerm

section Euler

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem endomorphism_euler_cross_add
    (u₁ : M₁ →ₗ[A] M₁) (u₂ : M₂ →ₗ[A] M₂) (u₃ : M₃ →ₗ[A] M₃)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃) (hExact : Function.Exact f g)
    (hleft : f.comp u₁ = u₂.comp f) (hright : g.comp u₂ = u₃.comp g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range u₂) +
        Module.length A (LinearMap.ker u₁) + Module.length A (LinearMap.ker u₃) =
      Module.length A (LinearMap.ker u₂) + Module.length A (M₁ ⧸ LinearMap.range u₁) +
        Module.length A (M₃ ⧸ LinearMap.range u₃) := by
  exact six_term_length_cross_add
    (kernelMap u₁ u₂ f hleft) (kernelMap u₂ u₃ g hright)
    (connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap u₁ u₂ f hleft) (cokernelMap u₂ u₃ g hright)
    (kernelMap_injective u₁ u₂ f hleft hf) (cokernelMap_surjective u₂ u₃ g hright hg)
    (kernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hf := hf))
    (exact_kernel_connecting u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (exact_connecting_cokernel u₁ u₂ u₃ f g hExact hleft hright hf hg)
    (cokernelMap_exact (u₁ := u₁) (u₂ := u₂) (u₃ := u₃) (f := f) (g := g)
      (hExact := hExact) (hleft := hleft) (hright := hright) (hg := hg))

end Euler

end PiExponentJets.EndomorphismEuler

end OAI
end Source0225

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionTransport.lean
section Source0226
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M N : Type*} [CommRing A]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]

theorem map_scalar_kernel (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change x • e z = 0
    change x • z = 0 at hz
    rw [← map_smul, hz, map_zero]
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change x • e.symm y = 0
    change x • y = 0 at hy
    rw [← map_smul, hy, map_zero]

theorem map_scalar_range (e : M ≃ₗ[A] N) (x : A) :
    (LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))).map e.toLinearMap =
      LinearMap.range (x • (LinearMap.id : N →ₗ[A] N)) := by
  ext y
  constructor
  · rintro ⟨z, ⟨w, rfl⟩, rfl⟩
    refine ⟨e w, ?_⟩
    change x • e w = e (x • w)
    exact (map_smul e x w).symm
  · rintro ⟨z, rfl⟩
    refine ⟨x • e.symm z, ⟨e.symm z, rfl⟩, ?_⟩
    change e (x • e.symm z) = x • z
    rw [map_smul, e.apply_symm_apply]

noncomputable def scalarKernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)) ≃ₗ[A]
      LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N)) :=
  e.ofSubmodules _ _ (map_scalar_kernel e x)

noncomputable def scalarCokernelEquiv (e : M ≃ₗ[A] N) (x : A) :
    (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) ≃ₗ[A]
      (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  Submodule.Quotient.equiv _ _ e (map_scalar_range e x)

theorem scalar_kernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarKernelEquiv e x).length_eq

theorem scalar_cokernel_length_eq (e : M ≃ₗ[A] N) (x : A) :
    Module.length A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) =
      Module.length A (N ⧸ LinearMap.range (x • (LinearMap.id : N →ₗ[A] N))) :=
  (scalarCokernelEquiv e x).length_eq

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0226

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionExactStep.lean
section Source0227
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionExactStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A M₁ M₂ M₃ : Type*} [CommRing A]
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

theorem scalar_euler_cross_add (x : A)
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hExact : Function.Exact f g) (hf : Function.Injective f)
    (hg : Function.Surjective g) :
    Module.length A (M₂ ⧸ LinearMap.range (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (LinearMap.ker (x • (LinearMap.id : M₃ →ₗ[A] M₃))) =
      Module.length A (LinearMap.ker (x • (LinearMap.id : M₂ →ₗ[A] M₂))) +
        Module.length A (M₁ ⧸ LinearMap.range (x • (LinearMap.id : M₁ →ₗ[A] M₁))) +
        Module.length A (M₃ ⧸ LinearMap.range (x • (LinearMap.id : M₃ →ₗ[A] M₃))) := by
  apply EndomorphismEuler.endomorphism_euler_cross_add
    (x • LinearMap.id) (x • LinearMap.id) (x • LinearMap.id) f g hExact
  · ext m
    exact map_smul f x m
  · ext m
    exact map_smul g x m
  · exact hf
  · exact hg

theorem cyclic_ideal_step_cross_add (I : Ideal A) (f x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) +
        Module.length A (((I.colon {f}).colon {x}) ⧸
          (I.colon {f}).submoduleOf ((I.colon {f}).colon {x})) +
        Module.length A (((I ⊔ Ideal.span {f}).colon {x}) ⧸
          (I ⊔ Ideal.span {f}).submoduleOf ((I ⊔ Ideal.span {f}).colon {x})) =
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) +
        Module.length A (A ⧸ ((I.colon {f}) ⊔ Ideal.span {x})) +
        Module.length A (A ⧸ ((I ⊔ Ideal.span {f}) ⊔ Ideal.span {x})) := by
  let J : Ideal A := I ⊔ Ideal.span {f}
  let T : Submodule A (A ⧸ I) := Submodule.map I.mkQ J
  let eT : (A ⧸ I.colon {f}) ≃ₗ[A] T :=
    (W22.cyclicFactorEquiv I f).trans (W22.subquotientEquivImage I J)
  let eQ : ((A ⧸ I) ⧸ T) ≃ₗ[A] (A ⧸ J) :=
    Submodule.quotientQuotientEquivQuotient I J le_sup_left
  have h := scalar_euler_cross_add x T.subtype T.mkQ
    (LinearMap.exact_subtype_mkQ T) (Submodule.subtype_injective T)
    (Submodule.mkQ_surjective T)
  rw [scalar_kernel_length_eq eT.symm x, scalar_kernel_length_eq eQ x,
    scalar_cokernel_length_eq eT.symm x, scalar_cokernel_length_eq eQ x] at h
  change Module.length A ((A ⧸ I) ⧸ LinearMap.range (quotientMul I x)) +
      Module.length A (LinearMap.ker (quotientMul (I.colon {f}) x)) +
      Module.length A (LinearMap.ker (quotientMul J x)) =
    Module.length A (LinearMap.ker (quotientMul I x)) +
      Module.length A ((A ⧸ I.colon {f}) ⧸ LinearMap.range (quotientMul (I.colon {f}) x)) +
      Module.length A ((A ⧸ J) ⧸ LinearMap.range (quotientMul J x)) at h
  simpa only [cokernel_length_eq_cut, kernel_length_eq_colon, J] using h

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0227

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFiltration.lean
section Source0228
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

omit [IsNoetherianRing A] in
theorem quotient_annihilator_eq_colon (J : Ideal A) (f : A) :
    (⊥ : Submodule A (A ⧸ J)).colon {J.mkQ f} = J.colon {f} := by
  ext a
  simp only [Submodule.mem_colon_singleton, Submodule.mem_bot]
  change a • J.mkQ f = 0 ↔ a * f ∈ J
  rw [← J.mkQ.map_smul, smul_eq_mul, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]

theorem exists_cyclic_prime_filtration_nat :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      ∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i} := by
  classical
  obtain ⟨s, hshead, hslast⟩ :=
    IsNoetherianRing.exists_relSeries_isQuotientEquivQuotientPrime A A
  have hsmono : Monotone s := Fin.monotone_iff_le_succ.mpr fun i => (s.step i).1
  let J : ℕ → Ideal A := fun i =>
    s ⟨min i s.length, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hd : ∀ i : Fin s.length, ∃ f : A,
      ((s i.castSucc).colon {f}).IsPrime ∧
        s i.succ = s i.castSucc ⊔ Ideal.span {f} := by
    intro i
    obtain ⟨f, hp, hf⟩ :=
      Submodule.isQuotientEquivQuotientPrime_iff.mp (s.step i)
    exact ⟨f, by simpa only [quotient_annihilator_eq_colon] using hp, hf⟩
  let generators : Fin s.length → A := fun i => (hd i).choose
  let f : ℕ → A := fun i => if hi : i < s.length then generators ⟨i, hi⟩ else 0
  refine ⟨s.length, J, f, ?_, ?_, ?_, ?_⟩
  · intro i
    apply hsmono
    exact min_le_min_right s.length (Nat.le_succ i)
  · change s.head = (⊥ : Submodule A A)
    exact hshead
  · simpa only [J, min_self, RelSeries.last, Fin.last] using hslast
  · intro i hi
    have hleft : J i = s (Fin.castSucc ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt hi)
    have hright : J (i + 1) = s (Fin.succ ⟨i, hi⟩) := by
      apply congrArg s
      apply Fin.ext
      exact min_eq_left (Nat.succ_le_of_lt hi)
    simpa only [f, dite_eq_left hi, generators, hleft, hright] using (hd ⟨i, hi⟩).choose_spec

theorem exists_cyclic_filtration_all_local_counts :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i, J i ≤ J (i + 1)) ∧ J 0 = ⊥ ∧ J n = ⊤ ∧
      (∀ i < n, ((J i).colon {f i}).IsPrime ∧
        J (i + 1) = J i ⊔ Ideal.span {f i}) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  obtain ⟨n, J, f, hmono, hstart, hend, hstep⟩ :=
    exists_cyclic_prime_filtration_nat (A := A)
  refine ⟨n, J, f, hmono, hstart, hend, hstep, ?_⟩
  intro P hP hp
  exact W22.localized_cyclic_filtration_length ⊥ P hp J hmono hstart n hend f
    (fun i hi => (hstep i hi).2) (fun i hi => (hstep i hi).1)

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0228

-- Source: OAI/NumberTheory/PiExponent/Cohomology/LocalIntersectionEulerFiltration.lean
section Source0229
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/LocalIntersectionEulerFiltration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A]

noncomputable def cutEuler (I : Ideal A) (x : A) : ℤ :=
  ((Module.length A (A ⧸ (I ⊔ Ideal.span {x}))).toNat : ℤ) -
    (Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x}))).toNat

private theorem finite_cross_add_to_integer
    (a b c d e f : ℕ∞) (ha : a ≠ ⊤) (hb : b ≠ ⊤) (hc : c ≠ ⊤)
    (hd : d ≠ ⊤) (he : e ≠ ⊤) (hf : f ≠ ⊤)
    (h : a + b + c = d + e + f) :
    (a.toNat : ℤ) - d.toNat =
      ((e.toNat : ℤ) - b.toNat) + ((f.toNat : ℤ) - c.toNat) := by
  lift a to ℕ using ha
  lift b to ℕ using hb
  lift c to ℕ using hc
  lift d to ℕ using hd
  lift e to ℕ using he
  lift f to ℕ using hf
  have hn : a + b + c = d + e + f := by exact_mod_cast h
  simp only [ENat.toNat_natCast]
  omega

theorem cutEuler_cyclic_step (I : Ideal A) (f x : A)
    (hcut : ∀ J : Ideal A, Module.length A (A ⧸ (J ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ J : Ideal A,
      Module.length A ((J.colon {x}) ⧸ J.submoduleOf (J.colon {x})) ≠ ⊤) :
    cutEuler I x = cutEuler (I.colon {f}) x + cutEuler (I ⊔ Ideal.span {f}) x := by
  exact finite_cross_add_to_integer _ _ _ _ _ _
    (hcut I) (hker (I.colon {f})) (hker (I ⊔ Ideal.span {f}))
    (hker I) (hcut (I.colon {f})) (hcut (I ⊔ Ideal.span {f}))
    (cyclic_ideal_step_cross_add I f x)

@[simp] theorem cutEuler_top (x : A) : cutEuler (⊤ : Ideal A) x = 0 := by
  simp [cutEuler, Module.length_eq_zero]

theorem cutEuler_filtration (J : ℕ → Ideal A) (f : ℕ → A) (x : A) (n : ℕ)
    (hstep : ∀ i < n, J (i + 1) = J i ⊔ Ideal.span {f i})
    (hcut : ∀ I : Ideal A, Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤)
    (hker : ∀ I : Ideal A,
      Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤) :
    cutEuler (J 0) x = (∑ i ∈ Finset.range n, cutEuler ((J i).colon {f i}) x) +
      cutEuler (J n) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi)),
      cutEuler_cyclic_step (J n) (f n) x hcut hker,
      ← hstep n (Nat.lt_succ_self n), Finset.sum_range_succ, add_assoc]

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0229

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFactors.lean
section Source0230
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionPrimeFactors.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem prime_quotientMul_injective (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) : Function.Injective (quotientMul P x) := by
  have hx0 : Ideal.Quotient.mk P x ≠ 0 := by
    simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using hx
  intro y z hyz
  change x • y = x • z at hyz
  simp only [Algebra.smul_def] at hyz
  exact mul_left_cancel₀ hx0 hyz

theorem prime_colon_length_zero (P : Ideal A) [P.IsPrime]
    (x : A) (hx : x ∉ P) :
    Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) = 0 :=
  regular_colon_length_zero P x (prime_quotientMul_injective P x hx)

noncomputable def minimalPrimeCutSum [IsNoetherianRing A]
    (I : Ideal A) (x : A) : ℕ∞ := by
  classical
  letI : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  exact ∑ P : I.minimalPrimes,
    letI : P.val.IsPrime := P.property.1.1
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸
        I.map (algebraMap A (Localization.AtPrime P.val))) *
      Module.length A (A ⧸ (P.val ⊔ Ideal.span {x}))

def LocalOneCutLengthStatement (A : Type*) [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] : Prop :=
  ∀ (I : Ideal A) (x : A),
    ringKrullDim (A ⧸ I) = 1 →
    Function.Injective (quotientMul I x) →
    (I ⊔ Ideal.span {x}).IsPrimary →
    (I ⊔ Ideal.span {x}).radical = IsLocalRing.maximalIdeal A →
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0230

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionDimensionOne.lean
section Source0231
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionDimensionOne.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem maximal_factor_cut_eq_colon (P : Ideal A) [P.IsMaximal] (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x})) := by
  let : IsSimpleModule A (A ⧸ P) :=
    isSimpleModule_iff_isCoatom.mpr (Ideal.isMaximal_def.mp inferInstance)
  apply finite_length_cut_eq_colon P x
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_one A (A ⧸ P)]
  exact ENat.one_ne_top

theorem regular_not_mem_minimalPrime (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) (hP : P ∈ minimalPrimes A) : x ∉ P := by
  exact fun hxP => Set.disjoint_left.mp
    (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hP) hxP hx

theorem dimension_one_prime_factor_dichotomy
    [Ring.KrullDimLE 1 A] [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A)
    (P : Ideal A) [P.IsPrime] :
    (P ∈ minimalPrimes A ∧ Function.Injective (quotientMul P x)) ∨
    (P = IsLocalRing.maximalIdeal A ∧
      Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A ((P.colon {x}) ⧸ P.submoduleOf (P.colon {x}))) := by
  rcases (Ring.krullDimLE_one_iff.mp inferInstance) P inferInstance with hP | hP
  · exact Or.inl ⟨hP,
      prime_quotientMul_injective P x (regular_not_mem_minimalPrime x hx P hP)⟩
  · let : P.IsMaximal := hP
    exact Or.inr ⟨IsLocalRing.eq_maximalIdeal hP, maximal_factor_cut_eq_colon P x⟩

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0231

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterKilledFiniteLength.lean
section Source0232
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterKilledFiniteLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W06

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem isArtinianRing_quotient_parameter {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsArtinianRing (A ⧸ Ideal.span {x}) := by
  have hlength : IsFiniteLength A (A ⧸ Ideal.span {x}) :=
    isFiniteLength_quotient_span_singleton A hx
  have hart : IsArtinian A (A ⧸ Ideal.span {x}) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hlength).2
  exact isArtinian_of_tower A hart

variable {M : Type*} [AddCommGroup M] [Module A M]

theorem isFiniteLength_of_parameter_killed [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) (hkill : ∀ m : M, x • m = 0) :
    IsFiniteLength A M := by
  have ht : Module.IsTorsionBy A M x := fun {m} => hkill m
  have hs : Module.IsTorsionBySet A M (Ideal.span {x}) :=
    (Module.isTorsionBySet_span_singleton_iff x).mpr ht
  let : Module (A ⧸ Ideal.span {x}) M := hs.module
  let : IsScalarTower A (A ⧸ Ideal.span {x}) M := hs.isScalarTower
  let : IsArtinianRing (A ⧸ Ideal.span {x}) := isArtinianRing_quotient_parameter hx
  let : Module.Finite (A ⧸ Ideal.span {x}) M :=
    Module.Finite.of_restrictScalars_finite A (A ⧸ Ideal.span {x}) M
  let : IsArtinian (A ⧸ Ideal.span {x}) M := inferInstance
  have hart : IsArtinian A M :=
    isArtinian_of_surjective_algebraMap (R := A ⧸ Ideal.span {x}) (S := A)
      (M := M) (Ideal.Quotient.mk_surjective (I := Ideal.span {x}))
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, hart⟩

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_kernel (x : A) :
    ∀ m : LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  intro m
  apply Subtype.ext
  change x • (m : M) = 0
  simpa only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply] using m.property

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in

theorem parameter_kills_mul_cokernel (x : A) :
    ∀ m : M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M)), x • m = 0 := by
  have ht : Module.IsTorsionBy A
      (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) x :=
    (Module.isTorsionBy_quotient_iff _ x).mpr (fun m => ⟨m, rfl⟩)
  exact fun m => @ht m

theorem isFiniteLength_ker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := by
  let : IsNoetherian A M := inferInstance
  let : Module.Finite A (LinearMap.ker (x • (LinearMap.id : M →ₗ[A] M))) := inferInstance
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_kernel x)

theorem isFiniteLength_coker_parameter_mul [Module.Finite A M]
    {x : A} (hx : x ∈ nonZeroDivisors A) :
    IsFiniteLength A (M ⧸ LinearMap.range (x • (LinearMap.id : M →ₗ[A] M))) := by
  exact isFiniteLength_of_parameter_killed hx (parameter_kills_mul_cokernel x)

end PiExponentJets.W06

end OAI
end Source0232

-- Source: OAI/NumberTheory/PiExponent/Cohomology/LocalIntersectionRegularEuler.lean
section Source0233
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/LocalIntersectionRegularEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]

theorem regular_cut_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) ≠ ⊤ := by
  rw [← cokernel_length_eq_cut]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_coker_parameter_mul (M := A ⧸ I) hx)

theorem regular_colon_length_ne_top (x : A) (hx : x ∈ nonZeroDivisors A) (I : Ideal A) :
    Module.length A ((I.colon {x}) ⧸ I.submoduleOf (I.colon {x})) ≠ ⊤ := by
  rw [← kernel_length_eq_colon]
  exact Module.length_ne_top_iff.mpr
    (W06.isFiniteLength_ker_parameter_mul (M := A ⧸ I) hx)

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem regular_colon_bot (x : A) (hx : x ∈ nonZeroDivisors A) :
    (⊥ : Ideal A).colon {x} = ⊥ := by
  ext a
  simp only [Submodule.mem_colon_singleton, smul_eq_mul, Submodule.mem_bot]
  exact mul_right_mem_nonZeroDivisors_eq_zero_iff hx

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] in
theorem cutEuler_bot_regular (x : A) (hx : x ∈ nonZeroDivisors A) :
    cutEuler (⊥ : Ideal A) x =
      ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) := by
  have hz : Module.length A
      (((⊥ : Ideal A).colon {x}) ⧸ (⊥ : Ideal A).submoduleOf ((⊥ : Ideal A).colon {x})) = 0 := by
    rw [regular_colon_bot x hx]
    exact Module.length_eq_zero
  have hlen : Module.length A (A ⧸ ((⊥ : Ideal A) ⊔ Ideal.span {x})) =
      Module.length A (A ⧸ Ideal.span {x}) :=
    (Submodule.quotEquivOfEq _ _ (bot_sup_eq (Ideal.span {x}))).length_eq
  simp only [cutEuler, hz, ENat.toNat_zero, Nat.cast_zero, sub_zero]
  exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hlen

omit [IsNoetherianRing A] in
theorem cutEuler_prime_regular [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) (P : Ideal A) [P.IsPrime] :
    cutEuler P x = if P ∈ minimalPrimes A then
      ((Module.length A (A ⧸ (P ⊔ Ideal.span {x}))).toNat : ℤ) else 0 := by
  classical
  by_cases hp : P ∈ minimalPrimes A
  · have hz := prime_colon_length_zero P x (regular_not_mem_minimalPrime x hx P hp)
    simp [cutEuler, hp, hz]
  · rcases dimension_one_prime_factor_dichotomy x hx P with hmin | hmax
    · exact False.elim (hp hmin.1)
    · simp only [hp, ↓reduceIte, cutEuler, hmax.2, sub_self]

theorem exists_regular_onecut_sum_and_local_counts [IsLocalRing A]
    (x : A) (hx : x ∈ nonZeroDivisors A) :
    ∃ (n : ℕ) (J : ℕ → Ideal A) (f : ℕ → A),
      (∀ i < n, ((J i).colon {f i}).IsPrime) ∧
      (((Module.length A (A ⧸ Ideal.span {x})).toNat : ℤ) =
        ∑ i ∈ Finset.range n, if (J i).colon {f i} ∈ minimalPrimes A then
          ((Module.length A (A ⧸ ((J i).colon {f i} ⊔ Ideal.span {x}))).toNat : ℤ) else 0) ∧
      ∀ (P : Ideal A) [P.IsPrime], P ∈ minimalPrimes A →
        Module.length (Localization.AtPrime P)
          (Localization.AtPrime P ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P))) =
          ∑ i ∈ Finset.range n, if (J i).colon {f i} = P then 1 else 0 := by
  classical
  obtain ⟨n, J, f, hm, h0, hn, hs, hcounts⟩ :=
    exists_cyclic_filtration_all_local_counts (A := A)
  refine ⟨n, J, f, (fun i hi => (hs i hi).1), ?_, hcounts⟩
  have he := cutEuler_filtration J f x n (fun i hi => (hs i hi).2)
    (regular_cut_length_ne_top x hx) (regular_colon_length_ne_top x hx)
  rw [h0, hn, cutEuler_top, add_zero, cutEuler_bot_regular x hx] at he
  refine he.trans (Finset.sum_congr rfl ?_)
  intro i hi
  let : ((J i).colon {f i}).IsPrime := (hs i (Finset.mem_range.mp hi)).1
  exact cutEuler_prime_regular x hx ((J i).colon {f i})

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0233

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionMinimalSum.lean
section Source0234
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionMinimalSum.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]
  [Ring.KrullDimLE 1 A] [IsLocalRing A]

omit [IsNoetherianRing A] [Ring.KrullDimLE 1 A] [IsLocalRing A] in
private theorem subtype_indicator_sum
    (S : Set (Ideal A)) [Fintype S] (P : Ideal A) (w : Ideal A → ℕ∞) :
    (∑ Q : S, if P = Q.val then w Q.val else 0) =
      if P ∈ S then w P else 0 := by
  classical
  by_cases hp : P ∈ S
  · rw [ite_eq_left hp]
    calc
      (∑ Q : S, if P = Q.val then w Q.val else 0) =
          (if P = P then w P else 0) := by
        apply Finset.sum_eq_single (⟨P, hp⟩ : S)
        · intro Q hQ hne
          have hne' : P ≠ Q.val := by
            intro h
            apply hne
            exact Subtype.ext h.symm
          simp only [hne', ↓reduceIte]
        · simp
      _ = w P := ite_eq_left rfl
  · rw [ite_eq_right hp]
    apply Finset.sum_eq_zero
    intro Q hQ
    have hne : P ≠ Q.val := fun h => hp (h.symm ▸ Q.property)
    simp only [hne, ↓reduceIte]

theorem regular_ring_onecut_length (x : A) (hx : x ∈ nonZeroDivisors A) :
    Module.length A (A ⧸ Ideal.span {x}) =
      minimalPrimeCutSum (⊥ : Ideal A) x := by
  classical
  obtain ⟨n, J, f, hp, he, hcounts⟩ := exists_regular_onecut_sum_and_local_counts x hx
  let ps : ℕ → Ideal A := fun i => (J i).colon {f i}
  let w : Ideal A → ℕ∞ := fun P => Module.length A (A ⧸ (P ⊔ Ideal.span {x}))
  have hsumNat : (Module.length A (A ⧸ Ideal.span {x})).toNat =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then (w (ps i)).toNat else 0 := by
    exact_mod_cast he
  have hsumENat : ((Module.length A (A ⧸ Ideal.span {x})).toNat : ℕ∞) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then ((w (ps i)).toNat : ℕ∞) else 0 := by
    exact_mod_cast hsumNat
  have hzeroCut : Module.length A (A ⧸ Ideal.span {x}) ≠ ⊤ := by
    exact Module.length_ne_top_iff.mpr (isFiniteLength_quotient_span_singleton A hx)
  rw [ENat.natCast_toNat hzeroCut] at hsumENat
  have hsum : Module.length A (A ⧸ Ideal.span {x}) =
      ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := by
    refine hsumENat.trans (Finset.sum_congr rfl ?_)
    intro i hi
    split_ifs with hmin
    · exact ENat.natCast_toNat (regular_cut_length_ne_top x hx (ps i))
    · rfl
  let : Fintype ((⊥ : Ideal A).minimalPrimes) :=
    ((⊥ : Ideal A).finite_minimalPrimes_of_isNoetherianRing A).fintype
  have hterm (P : (⊥ : Ideal A).minimalPrimes) :
      (letI : P.val.IsPrime := P.property.1.1
       Module.length (Localization.AtPrime P.val)
          (Localization.AtPrime P.val ⧸ (⊥ : Ideal A).map
            (algebraMap A (Localization.AtPrime P.val))) * w P.val) =
        ∑ i ∈ Finset.range n, if ps i = P.val then w P.val else 0 := by
    let : P.val.IsPrime := P.property.1.1
    rw [hcounts P.val P.property, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : ps i = P.val
    · simp only [ps] at h
      simp only [h, ↓reduceIte, one_mul, ps]
    · simp only [ps] at h
      simp only [h, ↓reduceIte, zero_mul, ps]
  calc
    Module.length A (A ⧸ Ideal.span {x}) =
        ∑ i ∈ Finset.range n, if ps i ∈ minimalPrimes A then w (ps i) else 0 := hsum
    _ = ∑ i ∈ Finset.range n, ∑ P : (⊥ : Ideal A).minimalPrimes,
        if ps i = P.val then w P.val else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (subtype_indicator_sum ((⊥ : Ideal A).minimalPrimes) (ps i) w).symm
    _ = ∑ P : (⊥ : Ideal A).minimalPrimes, ∑ i ∈ Finset.range n,
        if ps i = P.val then w P.val else 0 := Finset.sum_comm
    _ = minimalPrimeCutSum (⊥ : Ideal A) x := by
      unfold minimalPrimeCutSum
      apply Finset.sum_congr rfl
      intro P hP
      exact (hterm P).symm

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0234

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionQuotientTransport.lean
section Source0235
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionQuotientTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

variable {A : Type*} [CommRing A]

theorem quotient_cut_length (I J : Ideal A) :
    Module.length A (A ⧸ (I ⊔ J)) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) := by
  calc
    Module.length A (A ⧸ (I ⊔ J)) =
        Module.length (A ⧸ (I ⊔ J)) (A ⧸ (I ⊔ J)) :=
      PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _
    _ = Module.length ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I))
        ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.intrinsic_length_eq_of_ringEquiv
        (DoubleQuot.quotQuotEquivQuotSup I J)).symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸ J.map (Ideal.Quotient.mk I)) :=
      (PiExponentSiegel.W23.quotient_module_length_eq_intrinsic _).symm

theorem quotient_principal_cut_length (I : Ideal A) (x : A) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) := by
  have hmap : (Ideal.span {x}).map (Ideal.Quotient.mk I) =
      Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_span, Set.image_singleton]
  exact (quotient_cut_length I (Ideal.span {x})).trans
    (Submodule.quotEquivOfEq _ _ hmap).length_eq

theorem quotient_prime_cut_length (I P : Ideal A) (hIP : I ≤ P) (x : A) :
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
      Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) := by
  have hleft : I ⊔ (P ⊔ Ideal.span {x}) = P ⊔ Ideal.span {x} :=
    sup_eq_right.mpr (hIP.trans le_sup_left)
  have hright : (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I) =
      P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x} := by
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  calc
    Module.length A (A ⧸ (P ⊔ Ideal.span {x})) =
        Module.length A (A ⧸ (I ⊔ (P ⊔ Ideal.span {x}))) :=
      (Submodule.quotEquivOfEq _ _ hleft).length_eq.symm
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P ⊔ Ideal.span {x}).map (Ideal.Quotient.mk I)) :=
      quotient_cut_length I (P ⊔ Ideal.span {x})
    _ = Module.length (A ⧸ I) ((A ⧸ I) ⧸
        (P.map (Ideal.Quotient.mk I) ⊔ Ideal.span {Ideal.Quotient.mk I x})) :=
      (Submodule.quotEquivOfEq _ _ hright).length_eq

noncomputable def quotientMinimalPrimesEquiv (I : Ideal A) :
    minimalPrimes (A ⧸ I) ≃ I.minimalPrimes := by
  classical
  let f : minimalPrimes (A ⧸ I) → I.minimalPrimes := fun Q =>
    ⟨Q.val.comap (Ideal.Quotient.mk I), by
      rw [I.minimalPrimes_eq_comap]
      exact ⟨Q.val, Q.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro Q R h
    apply Subtype.ext
    apply Ideal.comap_injective_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    exact congrArg Subtype.val h
  · intro P
    have hmem : P.val ∈ Ideal.comap (Ideal.Quotient.mk I) '' minimalPrimes (A ⧸ I) :=
      Eq.mp (congrArg (fun S : Set (Ideal A) => P.val ∈ S) I.minimalPrimes_eq_comap) P.property
    obtain ⟨Q, hQ, hQP⟩ := hmem
    exact ⟨⟨Q, hQ⟩, Subtype.ext hQP⟩

@[simp] theorem quotientMinimalPrimesEquiv_apply (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (quotientMinimalPrimesEquiv I Q).val = Q.val.comap (Ideal.Quotient.mk I) := rfl

theorem quotient_minimal_local_length (I : Ideal A)
    (Q : minimalPrimes (A ⧸ I)) :
    (letI : (quotientMinimalPrimesEquiv I Q).val.IsPrime :=
       (quotientMinimalPrimesEquiv I Q).property.1.1
     Module.length (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)
       (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val ⧸
        I.map (algebraMap A (Localization.AtPrime (quotientMinimalPrimesEquiv I Q).val)))) =
    (letI : Q.val.IsPrime := Q.property.1.1
     Module.length (Localization.AtPrime Q.val)
       (Localization.AtPrime Q.val ⧸ (⊥ : Ideal (A ⧸ I)).map
        (algebraMap (A ⧸ I) (Localization.AtPrime Q.val)))) := by
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : PiExponentSiegel.W23.quotientParameterPrime I P hIP = Q.val := by
    exact Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hlocal := PiExponentSiegel.W23.quotient_localized_length_eq_explicit I P hIP
  have hprime :
      (⟨PiExponentSiegel.W23.quotientParameterPrime I P hIP,
        PiExponentSiegel.W23.quotientParameterPrime_isPrime I P hIP⟩ : PrimeSpectrum (A ⧸ I)) =
      ⟨Q.val, Q.property.1.1⟩ := PrimeSpectrum.ext hmap
  have hlength := congrArg (fun p : PrimeSpectrum (A ⧸ I) =>
    Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) hprime
  refine (hlocal.trans hlength).trans ?_
  rw [Ideal.map_bot]
  exact ((⊥ : Submodule (Localization.AtPrime Q.val) (Localization.AtPrime Q.val)).quotEquivOfEqBot
    rfl).length_eq.symm

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0235

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionFormula.lean
section Source0236
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalIntersectionFormula.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W28.LocalIntersection

open scoped BigOperators

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

theorem minimalPrimeCutSum_quotient (I : Ideal A) (x : A) :
    minimalPrimeCutSum I x =
      minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) := by
  classical
  let : Fintype I.minimalPrimes :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).fintype
  let : Fintype (minimalPrimes (A ⧸ I)) :=
    ((⊥ : Ideal (A ⧸ I)).finite_minimalPrimes_of_isNoetherianRing (A ⧸ I)).fintype
  symm
  unfold minimalPrimeCutSum
  apply Fintype.sum_equiv (quotientMinimalPrimesEquiv I)
  intro Q
  let P := (quotientMinimalPrimesEquiv I Q).val
  let : P.IsPrime := (quotientMinimalPrimesEquiv I Q).property.1.1
  let : Q.val.IsPrime := Q.property.1.1
  have hIP : I ≤ P := (quotientMinimalPrimesEquiv I Q).property.1.2
  have hmap : P.map (Ideal.Quotient.mk I) = Q.val :=
    Ideal.map_comap_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective Q.val
  have hc := quotient_prime_cut_length I P hIP x
  rw [hmap] at hc
  exact congrArg₂ HMul.hMul (quotient_minimal_local_length I Q).symm hc.symm

omit [IsNoetherianRing A] in
theorem quotient_parameter_mem_nonZeroDivisors (I : Ideal A) (x : A)
    (hregular : Function.Injective (quotientMul I x)) :
    Ideal.Quotient.mk I x ∈ nonZeroDivisors (A ⧸ I) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro y hy
  apply hregular
  change x • y = x • (0 : A ⧸ I)
  rw [smul_zero, Algebra.smul_def]
  exact hy

theorem local_onecut_length [IsLocalRing A]
    (I : Ideal A) (x : A) (hdim : ringKrullDim (A ⧸ I) = 1)
    (hregular : Function.Injective (quotientMul I x)) :
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) = minimalPrimeCutSum I x := by
  have hnot : ¬ Subsingleton (A ⧸ I) := by
    intro hsub
    let := hsub
    have hbot : ringKrullDim (A ⧸ I) = ⊥ := ringKrullDim_eq_bot_of_subsingleton
    rw [hdim] at hbot
    exact WithBot.one_ne_bot hbot
  let : Nontrivial (A ⧸ I) := not_subsingleton_iff_nontrivial.mp hnot
  let : IsLocalRing (A ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : Ring.KrullDimLE 1 (A ⧸ I) := Ring.krullDimLE_iff.mpr hdim.le
  calc
    Module.length A (A ⧸ (I ⊔ Ideal.span {x})) =
        Module.length (A ⧸ I) ((A ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I x}) :=
      quotient_principal_cut_length I x
    _ = minimalPrimeCutSum (⊥ : Ideal (A ⧸ I)) (Ideal.Quotient.mk I x) :=
      regular_ring_onecut_length _ (quotient_parameter_mem_nonZeroDivisors I x hregular)
    _ = minimalPrimeCutSum I x := (minimalPrimeCutSum_quotient I x).symm

end PiExponentJets.W28.LocalIntersection

end OAI
end Source0236

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPrimeTower.lean
section Source0237
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalPrimeTower.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

noncomputable def localPrimeTowerEquiv
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ≃ₐ[A]
      Localization.AtPrime p :=
  IsLocalization.localizationLocalizationAtPrimeIsoLocalization Q.primeCompl p

@[simp] theorem localPrimeTowerEquiv_algebraMap
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (a : A) :
    localPrimeTowerEquiv Q p
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))) a) =
      algebraMap A (Localization.AtPrime p) a :=
  (localPrimeTowerEquiv Q p).commutes a

theorem localPrimeTower_map_ideal
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    (I.map (algebraMap A (Localization.AtPrime Q))).map
      (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p)) =
    (I.map (algebraMap A
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))).map
        (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom := by
  have he : (localPrimeTowerEquiv Q p).toRingEquiv.toRingHom.comp
      (algebraMap A (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))) =
      algebraMap A (Localization.AtPrime p) := by
    ext a
    exact localPrimeTowerEquiv_algebraMap Q p a
  rw [Ideal.map_map, Ideal.map_map, he,
    ← IsScalarTower.algebraMap_eq A (Localization.AtPrime Q) (Localization.AtPrime p)]

theorem localPrimeTower_quotient_length
    (Q : Ideal A) [Q.IsPrime] (p : Ideal (Localization.AtPrime Q)) [p.IsPrime] (I : Ideal A) :
    Module.length (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))))
      (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q))) ⧸
        I.map (algebraMap A
          (Localization.AtPrime (p.comap (algebraMap A (Localization.AtPrime Q)))))) =
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ (I.map (algebraMap A (Localization.AtPrime Q))).map
        (algebraMap (Localization.AtPrime Q) (Localization.AtPrime p))) :=
  quotient_length_eq_of_ringEquiv (localPrimeTowerEquiv Q p).toRingEquiv _ _
    (localPrimeTower_map_ideal Q p I)

end PiExponentJets.W22

end OAI
end Source0237

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedMinimalPrimeFamily.lean
section Source0238
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedMinimalPrimeFamily.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {A : Type*} [CommRing A]

def MinimalParentsBelow (I Q : Ideal A) := {P : Ideal A // P ∈ I.minimalPrimes ∧ P ≤ Q}

noncomputable instance minimalParentsBelow_fintype [IsNoetherianRing A] (I Q : Ideal A) :
    Fintype (MinimalParentsBelow I Q) := by
  have hfinite : {P : Ideal A | P ∈ I.minimalPrimes ∧ P ≤ Q}.Finite :=
    (I.finite_minimalPrimes_of_isNoetherianRing A).subset (fun _ h => h.1)
  exact hfinite.fintype

instance {I Q : Ideal A} (P : MinimalParentsBelow I Q) : P.val.IsPrime := P.property.1.1.1

noncomputable def localizedMinimalPrimesEquiv (I Q : Ideal A) [Q.IsPrime] :
    (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes ≃ MinimalParentsBelow I Q := by
  classical
  let L := Localization.AtPrime Q
  let e := IsLocalization.AtPrime.orderIsoOfPrime L Q
  let f : (I.map (algebraMap A L)).minimalPrimes → MinimalParentsBelow I Q := fun p =>
    ⟨p.val.comap (algebraMap A L), by
      have hmin : p.val.comap (algebraMap A L) ∈ I.minimalPrimes :=
        (Set.ext_iff.mp (IsLocalization.minimalPrimes_map Q.primeCompl L I) p.val).mp p.property
      exact ⟨hmin, (e ⟨p.val, p.property.1.1⟩).property.2⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro p q h
    apply Subtype.ext
    apply (IsLocalization.orderEmbedding Q.primeCompl L).injective
    exact congrArg Subtype.val h
  · intro P
    let p := e.symm ⟨P.val, P.property.1.1.1, P.property.2⟩
    have heq : p.val.comap (algebraMap A L) = P.val :=
      congrArg Subtype.val (e.apply_symm_apply ⟨P.val, P.property.1.1.1, P.property.2⟩)
    have hp : p.val ∈ (I.map (algebraMap A L)).minimalPrimes := by
      rw [IsLocalization.minimalPrimes_map Q.primeCompl L I]
      change p.val.comap (algebraMap A L) ∈ I.minimalPrimes
      rw [heq]
      exact P.property.1
    exact ⟨⟨p.val, hp⟩, Subtype.ext heq⟩

@[simp] theorem localizedMinimalPrimesEquiv_apply
    (I Q : Ideal A) [Q.IsPrime]
    (p : (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes) :
    (localizedMinimalPrimesEquiv I Q p).val =
      p.val.comap (algebraMap A (Localization.AtPrime Q)) := rfl

end PiExponentJets.W22

end OAI
end Source0238

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean
section Source0239
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedOneCutPropagation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W28.LocalIntersection
open scoped BigOperators Classical

variable {A : Type*} [CommRing A] [IsNoetherianRing A]

noncomputable def globalParentCutSum (I Q : Ideal A) [Q.IsPrime] (x : A) : ℕ∞ :=
  ∑ P : MinimalParentsBelow I Q,
    Module.length (Localization.AtPrime P.val)
      (Localization.AtPrime P.val ⧸ I.map (algebraMap A (Localization.AtPrime P.val))) *
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (P.val ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)))

omit [IsNoetherianRing A] in
theorem localization_map_cut (I Q : Ideal A) [Q.IsPrime] (x : A) :
    (I ⊔ Ideal.span {x}).map (algebraMap A (Localization.AtPrime Q)) =
      I.map (algebraMap A (Localization.AtPrime Q)) ⊔
        Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

theorem minimalPrimeCutSum_localization (I Q : Ideal A) [Q.IsPrime] (x : A) :
    minimalPrimeCutSum (I.map (algebraMap A (Localization.AtPrime Q)))
      (algebraMap A (Localization.AtPrime Q) x) = globalParentCutSum I Q x := by
  classical
  let : Fintype (I.map (algebraMap A (Localization.AtPrime Q))).minimalPrimes :=
    ((I.map (algebraMap A (Localization.AtPrime Q))).finite_minimalPrimes_of_isNoetherianRing
      (Localization.AtPrime Q)).fintype
  unfold minimalPrimeCutSum globalParentCutSum
  apply Fintype.sum_equiv (localizedMinimalPrimesEquiv I Q)
  intro p
  let : p.val.IsPrime := p.property.1.1
  have htower := localPrimeTower_quotient_length Q p.val I
  have hcut :
      ((p.val.comap (algebraMap A (Localization.AtPrime Q))) ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q)) =
      p.val ⊔ Ideal.span {algebraMap A (Localization.AtPrime Q) x} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton,
      IsLocalization.map_under Q.primeCompl (Localization.AtPrime Q) p.val]
  have hcutlen := congrArg
    (fun K : Ideal (Localization.AtPrime Q) =>
      Module.length (Localization.AtPrime Q) (Localization.AtPrime Q ⧸ K)) hcut
  exact congrArg₂ HMul.hMul htower.symm hcutlen.symm

theorem localized_onecut_parent_recurrence
    (I Q : Ideal A) [Q.IsPrime] (x : A)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap A (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (quotientMul (I.map (algebraMap A (Localization.AtPrime Q)))
        (algebraMap A (Localization.AtPrime Q) x))) :
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I ⊔ Ideal.span {x}).map
        (algebraMap A (Localization.AtPrime Q))) = globalParentCutSum I Q x := by
  rw [localization_map_cut]
  exact (local_onecut_length _ _ hdim hregular).trans
    (minimalPrimeCutSum_localization I Q x)

end PiExponentJets.W22

end OAI
end Source0239

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/NaturalMultiplicityPropagation.lean
section Source0240
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/NaturalMultiplicityPropagation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra

theorem minimal_cut_of_intermediate_parent
    {A : Type*} [CommRing A] (I P Q : Ideal A) (x : A)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes) (hIP : I ≤ P) (hPQ : P ≤ Q) :
    Q ∈ (P ⊔ Ideal.span {x}).minimalPrimes := by
  refine ⟨⟨hQ.1.1, sup_le hPQ (le_sup_right.trans hQ.1.2)⟩, ?_⟩
  intro K hK hKQ
  exact hQ.2 ⟨hK.1, (sup_le_sup hIP le_rfl).trans hK.2⟩ hKQ

universe u
variable {k σ : Type u} [Field k] [Fintype σ]

omit [Fintype σ] in
theorem cut_ideal_homogeneous
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d) :
    (I ⊔ Ideal.span {x}).IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k) := by
  simpa only [sup_comm] using primeCut_isHomogeneous I hI x hx

theorem natural_local_onecut_recurrence
    (I Q : Ideal (MvPolynomial σ k)) [Q.IsPrime]
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (hQ : Q ∈ (I ⊔ Ideal.span {x}).minimalPrimes)
    (hdim : ringKrullDim (Localization.AtPrime Q ⧸
      I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q))) = 1)
    (hregular : Function.Injective
      (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q) x))) :
    actualLocalLength (I ⊔ Ideal.span {x}) Q =
      ∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q := by
  have hrec := localized_onecut_parent_recurrence I Q x hdim hregular
  have hsum : globalParentCutSum I Q x =
      ((∑ P : MinimalParentsBelow I Q, actualLocalLength I P.val *
        actualLocalLength (P.val ⊔ Ideal.span {x}) Q : ℕ) : ℕ∞) := by
    unfold globalParentCutSum
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro P _
    have hP := PiExponentSiegel.W17.ConeLocalLength.minimalPrime_isHomogeneous
      I P.val hI P.property.1
    have hQP := minimal_cut_of_intermediate_parent I P.val Q x hQ
      P.property.1.1.2 P.property.2
    rw [actualLocalLength_spec I P.val hI P.property.1,
      actualLocalLength_spec (P.val ⊔ Ideal.span {x}) Q
        (cut_ideal_homogeneous P.val hP x hx) hQP, Nat.cast_mul]
  rw [actualLocalLength_spec (I ⊔ Ideal.span {x}) Q
    (cut_ideal_homogeneous I hI x hx) hQ, hsum] at hrec
  exact_mod_cast hrec

noncomputable def parentChildIncidenceEquiv
    (I T : Ideal (MvPolynomial σ k)) (x : MvPolynomial σ k) :
    (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T, MinimalParentsBelow I Q.val) ≃
      (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}) where
  toFun z := ⟨⟨z.2.val, z.2.property.1, z.2.property.2.trans z.1.property.2⟩,
    z.1, z.2.property.2⟩
  invFun z := ⟨z.2.val, z.1.val, z.1.property.1, z.2.property⟩
  left_inv := by rintro ⟨Q,P⟩; rfl
  right_inv := by rintro ⟨P,Q⟩; rfl

end PiExponentJets.W22

end OAI
end Source0240

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/MultiplicityCycles.lean
section Source0241
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/MultiplicityCycles.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

noncomputable def actualMultiplicityCycle
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    RetainedPrimeCycle.{u,u,u} k σ where
  Index := RetainedMinimalPrime I T
  finiteIndex := inferInstance
  component := RetainedMinimalPrime.toComponent hI v hv
  coefficient := fun P => actualLocalLength I P.val

theorem actualMultiplicityCycle_coefficient
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (P : RetainedMinimalPrime I T) :
    (actualMultiplicityCycle I hI T v hv).coefficientAt
      (RetainedMinimalPrime.toComponent hI v hv P) = actualLocalLength I P.val := by
  unfold RetainedPrimeCycle.coefficientAt
  change (∑ Q : RetainedMinimalPrime I T,
    if RetainedMinimalPrime.toComponent hI v hv Q = RetainedMinimalPrime.toComponent hI v hv P
      then actualLocalLength I Q.val else 0) = _
  rw [Finset.sum_eq_single P]
  · exact ite_eq_left rfl
  · intro Q _ hQP
    exact ite_eq_right (fun heq => hQP (RetainedMinimalPrime.toComponent_injective hI v hv heq))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ P))

theorem actualMultiplicityCycle_cut_expansion
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    {d : ℕ} (x : MvPolynomial σ k) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree =
      ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
          (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
          (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree := by
  let D := actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv
  have hrec (Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T) :=
    natural_local_onecut_recurrence I Q.val hI x hx Q.property.1 (hdim Q) (hregular Q)
  calc
    D.degree = ∑ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        ∑ P : MinimalParentsBelow I Q.val,
          (actualLocalLength I P.val : ℚ) *
            (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val : ℚ) *
              (D.component Q).hilbertDegree := by
      unfold RetainedPrimeCycle.degree
      apply Finset.sum_congr rfl
      intro Q _
      let : Q.val.IsPrime := Q.property.1.1.1
      change (actualLocalLength (I ⊔ Ideal.span {x}) Q.val : ℚ) * (D.component Q).hilbertDegree = _
      rw [hrec Q, Nat.cast_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro P _
      rw [Nat.cast_mul]
    _ = ∑ z : (Σ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
        MinimalParentsBelow I Q.val),
          (actualLocalLength I z.2.val : ℚ) *
            (actualLocalLength (z.2.val ⊔ Ideal.span {x}) z.1.val : ℚ) *
              (D.component z.1).hilbertDegree := by rw [Fintype.sum_sigma]
    _ = ∑ z : (Σ P : RetainedMinimalPrime I T,
        {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}),
          (actualLocalLength I z.1.val : ℚ) *
            (actualLocalLength (z.1.val ⊔ Ideal.span {x}) z.2.val.val : ℚ) *
              (D.component z.2.val).hilbertDegree := by
      apply Fintype.sum_equiv (parentChildIncidenceEquiv I T x)
      intro z
      rfl
    _ = _ := by
      rw [Fintype.sum_sigma]
      simp only [Finset.mul_sum, mul_assoc, D, actualMultiplicityCycle]

theorem actualMultiplicityCycle_parent_budget
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (P : RetainedMinimalPrime I T) :
    (∑ Q : {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val},
      (actualLocalLength (P.val ⊔ Ideal.span {x}) Q.val.val : ℚ) *
        (RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv Q.val).hilbertDegree) ≤
      (d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree := by
  let C := actualMultiplicityCycle I hI T v hv
  let Qs := {Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T // P.val ≤ Q.val}
  let Q : Qs → Ideal (MvPolynomial σ k) := fun q => q.val.val
  let E : Qs → ProjectiveComponent k σ := fun q =>
    RetainedMinimalPrime.toComponent (cut_ideal_homogeneous I hI x hx) v hv q.val
  have hQmin : ∀ q : Qs, Q q ∈ (Ideal.span {x} ⊔ P.val).minimalPrimes := by
    intro q
    simpa only [sup_comm] using minimal_cut_of_intermediate_parent I P.val q.val.val x
      q.val.property.1 P.property.1.1.2 q.property
  have hQdegree : ∀ q : Qs, (actualHP (Q q) (E q).homogeneous).natDegree = s := by
    intro q
    have hdim := RetainedPrimeCycle.retainedChild_dimension C x havoid s hparent T P
      ⟨Q q, hQmin q, q.val.property.2⟩
    exact actualHP_natDegree_of_prime_dimension (Q q) (E q).homogeneous
      (E q).coordinate (E q).coordinate_not_mem s hdim
  have hinj : Function.Injective Q := by
    intro q r h
    exact Subtype.ext (Subtype.ext h)
  have hb := prime_cut_component_budget P.val (C.component P).homogeneous x hx
    (havoid P) hd s (hparent P) Q hinj (fun q => (E q).homogeneous) hQmin
    (fun q => (E q).coordinate) (fun q => (E q).coordinate_not_mem) hQdegree
  change (∑ q : Qs,
    (actualLocalLength (P.val ⊔ Ideal.span {x}) (Q q) : ℚ) *
      actualMultiplicity (Q q) (E q).homogeneous
        (actualHP (Q q) (E q).homogeneous).natDegree) ≤
    (d : ℚ) * actualMultiplicity P.val (C.component P).homogeneous
      (actualHP P.val (C.component P).homogeneous).natDegree
  simp only [hQdegree, hparent]
  simpa only [sup_comm] using hb

theorem actualMultiplicityCycle_cut_degree_le
    (I : Ideal (MvPolynomial σ k))
    (hI : I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k))
    (x : MvPolynomial σ k) (d : ℕ) (hd : 0 < d) (hx : x.IsHomogeneous d)
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (havoid : ∀ P : RetainedMinimalPrime I T, x ∉ P.val)
    (s : ℕ) (hparent : ∀ P : RetainedMinimalPrime I T,
      (actualHP P.val (RetainedMinimalPrime.toComponent hI v hv P).homogeneous).natDegree = s+1)
    (hdim : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      ringKrullDim (Localization.AtPrime Q.val ⧸
        I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1)
    (hregular : ∀ Q : RetainedMinimalPrime (I ⊔ Ideal.span {x}) T,
      Function.Injective (W28.LocalIntersection.quotientMul
        (I.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) x))) :
    (actualMultiplicityCycle (I ⊔ Ideal.span {x}) (cut_ideal_homogeneous I hI x hx) T v hv).degree ≤
      (d : ℚ) * (actualMultiplicityCycle I hI T v hv).degree := by
  rw [actualMultiplicityCycle_cut_expansion I hI x hx T v hv hdim hregular]
  calc
    _ ≤ ∑ P : RetainedMinimalPrime I T, (actualLocalLength I P.val : ℚ) *
        ((d : ℚ) * (RetainedMinimalPrime.toComponent hI v hv P).hilbertDegree) := by
      apply Finset.sum_le_sum
      intro P _
      exact mul_le_mul_of_nonneg_left
        (actualMultiplicityCycle_parent_budget I hI x d hd hx T v hv havoid s hparent P)
        (Nat.cast_nonneg _)
    _ = _ := by
      rw [RetainedPrimeCycle.degree, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro P _
      dsimp only [actualMultiplicityCycle]
      ring

end PiExponentJets.W22

end OAI
end Source0241

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularCutHistory.lean
section Source0242
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularCutHistory.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k] [Fintype σ]

abbrev HomogeneousPolynomialIdeal (k σ : Type u) [Field k] :=
  {I : Ideal (MvPolynomial σ k) // I.IsHomogeneous (MvPolynomial.homogeneousSubmodule σ k)}

noncomputable def zeroHomogeneousIdeal : HomogeneousPolynomialIdeal k σ :=
  ⟨⊥, Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)⟩

structure RegularPrefixCut
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S : HomogeneousPolynomialIdeal k σ) where
  polynomial : MvPolynomial σ k
  polynomialDegree : ℕ
  positiveDegree : 0 < polynomialDegree
  homogeneous : polynomial.IsHomogeneous polynomialDegree
  avoidsParent : ∀ P : RetainedMinimalPrime S.val T, polynomial ∉ P.val
  dimensionIndex : ℕ
  parentDegree : ∀ P : RetainedMinimalPrime S.val T,
    (actualHP P.val (RetainedMinimalPrime.toComponent S.property v hv P).homogeneous).natDegree =
      dimensionIndex+1
  localDimension : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    ringKrullDim (Localization.AtPrime Q.val ⧸
      S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) = 1
  regularAtChild : ∀ Q : RetainedMinimalPrime (S.val ⊔ Ideal.span {polynomial}) T,
    Function.Injective (W28.LocalIntersection.quotientMul
      (S.val.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val)))
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val) polynomial))

namespace RegularPrefixCut

variable {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
  {S : HomogeneousPolynomialIdeal k σ}

noncomputable def next (F : RegularPrefixCut T v hv S) : HomogeneousPolynomialIdeal k σ :=
  ⟨S.val ⊔ Ideal.span {F.polynomial}, cut_ideal_homogeneous S.val S.property F.polynomial F.homogeneous⟩

theorem degree_step (F : RegularPrefixCut T v hv S) :
    (actualMultiplicityCycle F.next.val F.next.property T v hv).degree ≤
      (F.polynomialDegree : ℚ) * (actualMultiplicityCycle S.val S.property T v hv).degree :=
  actualMultiplicityCycle_cut_degree_le S.val S.property F.polynomial F.polynomialDegree
    F.positiveDegree F.homogeneous T v hv F.avoidsParent F.dimensionIndex F.parentDegree
    F.localDimension F.regularAtChild

end RegularPrefixCut

inductive ActualRegularCutHistory
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T)
    (S₀ : HomogeneousPolynomialIdeal k σ) : HomogeneousPolynomialIdeal k σ → ℕ → Prop
  | nil : ActualRegularCutHistory T v hv S₀ S₀ 1
  | step {S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
      (previous : ActualRegularCutHistory T v hv S₀ S e)
      (F : RegularPrefixCut T v hv S) :
      ActualRegularCutHistory T v hv S₀ F.next (e * F.polynomialDegree)

theorem ActualRegularCutHistory.degree_bound
    {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
    {S₀ S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
    (h : ActualRegularCutHistory T v hv S₀ S e) :
    (actualMultiplicityCycle S.val S.property T v hv).degree ≤
      (e : ℚ) * (actualMultiplicityCycle S₀.val S₀.property T v hv).degree := by
  induction h with
  | nil => simp
  | @step S e previous F ih =>
    calc
      _ ≤ (F.polynomialDegree : ℚ) *
          (actualMultiplicityCycle S.val S.property T v hv).degree := F.degree_step
      _ ≤ (F.polynomialDegree : ℚ) * ((e : ℚ) *
          (actualMultiplicityCycle S₀.val S₀.property T v hv).degree) :=
        mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg _)
      _ = _ := by rw [Nat.cast_mul]; ring

theorem actualMultiplicityCycle_zero_degree
    (T : Ideal (MvPolynomial σ k)) (v : σ) (hv : MvPolynomial.X v ∉ T) :
    (actualMultiplicityCycle (⊥ : Ideal (MvPolynomial σ k))
      (Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)) T v hv).degree = 1 := by
  let hbot := Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)
  have hminimal : (⊥ : Ideal (MvPolynomial σ k)) ∈ (⊥ : Ideal (MvPolynomial σ k)).minimalPrimes :=
    ⟨⟨inferInstance, le_rfl⟩, fun _ _ _ => bot_le⟩
  let B : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T := ⟨⊥, hminimal, bot_le⟩
  have hevery (P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T) : P = B := by
    apply Subtype.ext
    exact le_antisymm (P.property.1.2 ⟨inferInstance, le_rfl⟩ bot_le) bot_le
  have hlength : actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ = 1 := by
    unfold actualLocalLength
    rw [localized_prime_factor_length_one]
    exact ENat.toNat_natCast 1
  let degrees : Fin ([] : List (MvPolynomial σ k)).length → ℕ := fun i => Fin.elim0 i
  have hhom : ∀ i : Fin ([] : List (MvPolynomial σ k)).length,
      ([] : List (MvPolynomial σ k))[i].IsHomogeneous (degrees i) := fun i => Fin.elim0 i
  have hreg := RingTheory.Sequence.IsRegular.nil (MvPolynomial σ k) (MvPolynomial σ k)
  have hlen : ([] : List (MvPolynomial σ k)).length < Fintype.card σ :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  have hnilhom : (Ideal.ofList ([] : List (MvPolynomial σ k))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by simpa only [Ideal.ofList_nil] using hbot
  have hdegree : actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot
      (actualHP ⊥ hbot).natDegree = 1 := by
    simpa only [Ideal.ofList_nil, List.length_nil, Finset.range_zero, Finset.prod_empty,
      Nat.cast_one] using actualMultiplicity_regular_sequence [] degrees hhom hreg hlen hnilhom
  unfold RetainedPrimeCycle.degree
  change (∑ P : RetainedMinimalPrime (⊥ : Ideal (MvPolynomial σ k)) T,
    (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) P.val : ℚ) *
      (RetainedMinimalPrime.toComponent hbot v hv P).hilbertDegree) = 1
  rw [Finset.sum_eq_single B]
  · change (actualLocalLength (⊥ : Ideal (MvPolynomial σ k)) ⊥ : ℚ) *
      actualMultiplicity (⊥ : Ideal (MvPolynomial σ k)) hbot (actualHP ⊥ hbot).natDegree = 1
    rw [hlength, Nat.cast_one, hdegree, one_mul]
  · intro P _ hne
    exact False.elim (hne (hevery P))
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ B))

theorem ActualRegularCutHistory.local_length_bound
    {T : Ideal (MvPolynomial σ k)} {v : σ} {hv : MvPolynomial.X v ∉ T}
    {S : HomogeneousPolynomialIdeal k σ} {e : ℕ}
    (h : ActualRegularCutHistory T v hv (zeroHomogeneousIdeal (k := k) (σ := σ)) S e)
    (Q : RetainedMinimalPrime S.val T) :
    Module.length (Localization.AtPrime Q.val)
      (Localization.AtPrime Q.val ⧸ S.val.map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime Q.val))) ≤ (e : ℕ∞) := by
  let C := actualMultiplicityCycle S.val S.property T v hv
  have hc := C.coefficientAt_le_degree (RetainedMinimalPrime.toComponent S.property v hv Q)
  rw [actualMultiplicityCycle_coefficient S.val S.property T v hv Q] at hc
  have hd := h.degree_bound
  dsimp only [zeroHomogeneousIdeal] at hd
  rw [actualMultiplicityCycle_zero_degree T v hv, mul_one] at hd
  have hn : actualLocalLength S.val Q.val ≤ e := by exact_mod_cast hc.trans hd
  rw [actualLocalLength_spec S.val Q.val S.property Q.property.1]
  exact_mod_cast hn

end PiExponentJets.W22

end OAI
end Source0242

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousListHistory.lean
section Source0243
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousListHistory.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open scoped BigOperators Classical
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable {k σ : Type u} [Field k]

noncomputable def homogeneousListPrefix
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i)) (j : ℕ) :
    HomogeneousPolynomialIdeal k σ :=
  ⟨Ideal.ofList (gs.take j), PiExponentSiegel.W20.prefixIdeal_homogeneous gs degrees hhom j⟩

theorem homogeneousListPrefix_succ
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (j : ℕ) (hj : j < gs.length) :
    (homogeneousListPrefix gs degrees hhom (j+1)).val =
      (homogeneousListPrefix gs degrees hhom j).val ⊔ Ideal.span {gs[j]} := by
  simpa only [homogeneousListPrefix, Fin.getElem_fin, sup_comm] using
    PiExponentSiegel.W20.prefixIdeal_succ gs ⟨j,hj⟩

theorem local_regular_list_avoids_parent
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime]
    (gs : List (MvPolynomial σ k))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (j : ℕ) (hj : j < gs.length)
    (P : Ideal (MvPolynomial σ k))
    (hP : P ∈ (Ideal.ofList (gs.take j)).minimalPrimes) (hPT : P ≤ T) : gs[j] ∉ P := by
  have hregular : IsSMulRegular
      (Localization.AtPrime T ⧸ (Ideal.ofList (gs.take j)).map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime T)))
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime T) gs[j]) :=
    W16.regularPrefix_quotientMul_injective T T le_rfl gs hreg j hj
  exact PiExponentSiegel.W17.IsolatedIntersection.local_regular_avoids_retained_minimalPrime
    (Ideal.ofList (gs.take j)) T hP hPT hregular

variable [Fintype σ]

theorem actualHP_zero_natDegree
    (v : σ) (hbot : (⊥ : Ideal (MvPolynomial σ k)).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k)) :
    (actualHP ⊥ hbot).natDegree = Fintype.card σ - 1 := by
  let degrees : Fin ([] : List (MvPolynomial σ k)).length → ℕ := fun i => Fin.elim0 i
  have hhom : ∀ i : Fin ([] : List (MvPolynomial σ k)).length,
      ([] : List (MvPolynomial σ k))[i].IsHomogeneous (degrees i) := fun i => Fin.elim0 i
  have hreg := RingTheory.Sequence.IsRegular.nil (MvPolynomial σ k) (MvPolynomial σ k)
  have hlen : ([] : List (MvPolynomial σ k)).length < Fintype.card σ :=
    Fintype.card_pos_iff.mpr ⟨v⟩
  have hnil : (Ideal.ofList ([] : List (MvPolynomial σ k))).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule σ k) := by simpa only [Ideal.ofList_nil] using hbot
  simpa only [Ideal.ofList_nil, List.length_nil, Nat.sub_zero] using
    actualHP_regular_sequence_natDegree [] degrees hhom hreg hlen hnil

theorem homogeneous_prefix_hilbert_degree
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ P : RetainedMinimalPrime (homogeneousListPrefix gs degrees hhom j).val T,
      (actualHP P.val (RetainedMinimalPrime.toComponent
        (homogeneousListPrefix gs degrees hhom j).property v hv P).homogeneous).natDegree =
          Fintype.card σ - j - 1 := by
  induction j with
  | zero =>
    intro P
    have hPbot : P.val ∈ (⊥ : Ideal (MvPolynomial σ k)).minimalPrimes := by
      simpa only [homogeneousListPrefix, List.take_zero, Ideal.ofList_nil] using P.property.1
    have heq : P.val = ⊥ := le_antisymm (hPbot.2 ⟨inferInstance,le_rfl⟩ bot_le) bot_le
    have hbot := Ideal.IsHomogeneous.bot (MvPolynomial.homogeneousSubmodule σ k)
    exact (congrArg Polynomial.natDegree (actualHP_congr _ hbot heq)).trans
      (by simpa only [Nat.sub_zero] using actualHP_zero_natDegree v hbot)
  | succ j ih =>
    intro Q
    have hjlt : j < gs.length := by omega
    have hprev := ih (by omega)
    let S := homogeneousListPrefix gs degrees hhom j
    let C := actualMultiplicityCycle S.val S.property T v hv
    let s := Fintype.card σ - j - 2
    have hparent : ∀ P : RetainedMinimalPrime S.val T,
        (actualHP P.val (C.component P).homogeneous).natDegree = s+1 := by
      intro P
      rw [hprev P]
      dsimp [s]
      omega
    have havoid : ∀ P : RetainedMinimalPrime S.val T, gs[j] ∉ P.val := fun P =>
      local_regular_list_avoids_parent T gs hreg j hjlt P.val P.property.1 P.property.2
    have hQcut : Q.val ∈ (S.val ⊔ Ideal.span {gs[j]}).minimalPrimes := by
      have heq := homogeneousListPrefix_succ gs degrees hhom j hjlt
      simpa only [heq] using Q.property.1
    obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (le_sup_left.trans hQcut.1.2)
    let P' : RetainedMinimalPrime S.val T := ⟨P,hP,hPQ.trans Q.property.2⟩
    have hQP : Q.val ∈ (Ideal.span {gs[j]} ⊔ P).minimalPrimes := by
      simpa only [sup_comm] using minimal_cut_of_intermediate_parent S.val P Q.val gs[j]
        hQcut hP.1.2 hPQ
    have hdim := RetainedPrimeCycle.retainedChild_dimension C gs[j] havoid s hparent T P'
      ⟨Q.val,hQP,Q.property.2⟩
    have hdeg := actualHP_natDegree_of_prime_dimension Q.val
      (RetainedMinimalPrime.toComponent
        (homogeneousListPrefix gs degrees hhom (j+1)).property v hv Q).homogeneous
      v (fun hx => hv (Q.property.2 hx)) s hdim
    have hs : s = Fintype.card σ - (j+1) - 1 := by dsimp [s]; omega
    exact hs ▸ hdeg

theorem homogeneous_list_actual_history
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ) (j : ℕ) (hj : j ≤ gs.length) :
    ActualRegularCutHistory T v hv (zeroHomogeneousIdeal (k := k) (σ := σ))
      (homogeneousListPrefix gs degrees hhom j)
      (∏ i ∈ Finset.range j, degreeAt degrees i) := by
  induction j with
  | zero =>
    have hzero : homogeneousListPrefix gs degrees hhom 0 = zeroHomogeneousIdeal := by
      apply Subtype.ext
      simp only [homogeneousListPrefix, zeroHomogeneousIdeal, List.take_zero, Ideal.ofList_nil]
    rw [hzero]
    simpa only [Finset.range_zero, Finset.prod_empty] using
      (ActualRegularCutHistory.nil (T := T) (v := v) (hv := hv)
        (S₀ := zeroHomogeneousIdeal (k := k) (σ := σ)))
  | succ j ih =>
    have hjlt : j < gs.length := by omega
    let S := homogeneousListPrefix gs degrees hhom j
    let F : RegularPrefixCut T v hv S :=
      { polynomial := gs[j]
        polynomialDegree := degrees ⟨j,hjlt⟩
        positiveDegree := homogeneous_degrees_pos_of_local_regular T gs degrees hhom hreg ⟨j,hjlt⟩
        homogeneous := by simpa only [Fin.getElem_fin] using hhom ⟨j,hjlt⟩
        avoidsParent := fun P =>
          local_regular_list_avoids_parent T gs hreg j hjlt P.val P.property.1 P.property.2
        dimensionIndex := Fintype.card σ - j - 2
        parentDegree := by
          intro P
          rw [homogeneous_prefix_hilbert_degree T v hv gs degrees hhom hreg hlen j (by omega) P]
          omega
        localDimension := fun Q => W29.regularPrefix_local_cut_dimension_one T Q.val Q.property.2
          gs hreg j hjlt Q.property.1
        regularAtChild := fun Q => W16.regularPrefix_quotientMul_injective T Q.val Q.property.2
          gs hreg j hjlt }
    have hnext : F.next = homogeneousListPrefix gs degrees hhom (j+1) := by
      apply Subtype.ext
      exact (homogeneousListPrefix_succ gs degrees hhom j hjlt).symm
    have hs := ActualRegularCutHistory.step (ih (by omega)) F
    rw [hnext] at hs
    simpa only [Finset.prod_range_succ, degreeAt, dite_eq_left hjlt] using hs

theorem homogeneous_local_regular_bezout
    (T : Ideal (MvPolynomial σ k)) [T.IsPrime] (v : σ) (hv : MvPolynomial.X v ∉ T)
    (gs : List (MvPolynomial σ k)) (degrees : Fin gs.length → ℕ)
    (hhom : ∀ i : Fin gs.length, gs[i].IsHomogeneous (degrees i))
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime T)
      (gs.map (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (hlen : gs.length < Fintype.card σ)
    (hT : T ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime T)
      (Localization.AtPrime T ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
      ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞) := by
  have hh := homogeneous_list_actual_history T v hv gs degrees hhom hreg hlen gs.length le_rfl
  have hT' : T ∈ (homogeneousListPrefix gs degrees hhom gs.length).val.minimalPrimes := by
    simpa only [homogeneousListPrefix, List.take_length] using hT
  have hbound := hh.local_length_bound (⟨T,hT',le_rfl⟩ :
    RetainedMinimalPrime (homogeneousListPrefix gs degrees hhom gs.length).val T)
  change Module.length (Localization.AtPrime T)
    (Localization.AtPrime T ⧸ (Ideal.ofList (gs.take gs.length)).map
      (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))) ≤
      ((∏ i ∈ Finset.range gs.length, degreeAt degrees i : ℕ) : ℕ∞) at hbound
  have hlength := congrArg
    (fun js : List (MvPolynomial σ k) =>
      Module.length (Localization.AtPrime T)
        (Localization.AtPrime T ⧸ (Ideal.ofList js).map
          (algebraMap (MvPolynomial σ k) (Localization.AtPrime T))))
    (List.take_length (l := gs))
  exact hlength.symm.le.trans hbound

end PiExponentJets.W22

end OAI
end Source0243

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/AffineLocalRegularBezout.lean
section Source0244
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/AffineLocalRegularBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open PiExponentJets.W64
open PiExponentSiegel.W17.ConeLocalLength
open scoped BigOperators Classical

theorem span_range_list_get {R : Type*} [CommSemiring R] (gs : List R) :
    Ideal.span (Set.range gs.get) = Ideal.ofList gs := by
  congr 1
  ext x
  exact List.mem_iff_get.symm

theorem span_range_map_list_get {R S : Type*} [CommSemiring S]
    (gs : List R) (f : R → S) :
    Ideal.span (Set.range (fun i => f (gs.get i))) = Ideal.ofList (gs.map f) := by
  congr 1
  ext x
  change (∃ i, f (gs.get i) = x) ↔ x ∈ gs.map f
  constructor
  · rintro ⟨i,rfl⟩
    exact List.mem_map.mpr ⟨gs.get i,List.mem_iff_get.mpr ⟨i,rfl⟩,rfl⟩
  · intro hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp ha
    exact ⟨i,rfl⟩

theorem finiteLength_localized_minimal_quotient
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I P : Ideal R) [P.IsPrime] (hP : P ∈ I.minimalPrimes) :
    IsFiniteLength (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) := by
  let L := Localization.AtPrime P
  let J := I.map (algebraMap R L)
  have hrad : J.radical = IsLocalRing.maximalIdeal L :=
    localized_radical_eq_maximal_of_mem_minimalPrimes I P hP
  let : J.radical.IsPrime := by rw [hrad]; infer_instance
  have hmin : IsLocalRing.maximalIdeal L ∈ J.minimalPrimes := by
    rw [← hrad]
    exact radical_mem_minimalPrimes J
  let : IsArtinianRing (L ⧸ J) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing J hmin
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_of_surjective (M := L ⧸ J)
    (show Function.Surjective (algebraMap L (L ⧸ J)) from Ideal.Quotient.mk_surjective)]
  exact Module.length_ne_top

theorem affine_local_regular_list_bezout
    {k : Type} [Field k] (n : ℕ)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (gs : List (MvPolynomial (Fin n) k)) (D : ℕ)
    (hdegree : ∀ g ∈ gs, g.totalDegree ≤ D)
    (hreg : RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))))
    (hlen : gs.length ≤ n) (hP : P ∈ (Ideal.ofList gs).minimalPrimes) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ gs.length : ℕ) : ℕ∞) := by
  let hs := gs.map homogenize
  let degrees : Fin hs.length → ℕ := fun i =>
    (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt)).totalDegree
  have hhom : ∀ i : Fin hs.length, hs[i].IsHomogeneous (degrees i) := by
    intro i
    simpa only [hs, List.getElem_map, Fin.getElem_fin, degrees] using
      homogenize_isHomogeneous (gs[i.val]'(by simpa only [hs,List.length_map] using i.isLt))
  have hconeReg := homogenized_list_regular_at_cone k (Fin n) P gs hreg
  have hget : P ∈ (Ideal.span (Set.range gs.get)).minimalPrimes := by
    simpa only [span_range_list_get] using hP
  have hconeMin := conePrime_minimal_over_homogenized k (Fin n) P gs.get hget
  rw [span_range_map_list_get] at hconeMin
  have hconeLen : hs.length < Fintype.card (Option (Fin n)) := by
    simp only [hs,List.length_map,Fintype.card_option,Fintype.card_fin]
    omega
  have hbound := homogeneous_local_regular_bezout (conePrime k (Fin n) P) none
    (homogenizing_coordinate_not_mem_conePrime k (Fin n) P)
    hs degrees hhom hconeReg hconeLen hconeMin
  have hfinite := finiteLength_localized_minimal_quotient
    (Ideal.span (Set.range gs.get)) P hget
  have hlength := homogenized_cone_local_length_eq k (Fin n) P gs.get hfinite
  rw [span_range_list_get, span_range_map_list_get] at hlength
  have hprod : (∏ i ∈ Finset.range hs.length, degreeAt degrees i) ≤ D ^ gs.length := by
    calc
      _ ≤ ∏ _i ∈ Finset.range hs.length, D := by
        apply Finset.prod_le_prod
        intro i hi
        have hi' : i < hs.length := Finset.mem_range.mp hi
        simp only [degreeAt,dite_eq_left hi',degrees]
        exact hdegree _ (List.getElem_mem _)
      _ = D ^ gs.length := by simp only [Finset.prod_const,Finset.card_range,hs,List.length_map]
  calc
    _ = Module.length (Localization.AtPrime (conePrime k (Fin n) P))
      (Localization.AtPrime (conePrime k (Fin n) P) ⧸ (Ideal.ofList hs).map
        (algebraMap (MvPolynomial (Option (Fin n)) k)
          (Localization.AtPrime (conePrime k (Fin n) P)))) := hlength.symm
    _ ≤ ((∏ i ∈ Finset.range hs.length, degreeAt degrees i : ℕ) : ℕ∞) := hbound
    _ ≤ _ := by exact_mod_cast hprod

end PiExponentJets.W22

end OAI
end Source0244

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterCombinations.lean
section Source0245
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterCombinations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

open scoped BigOperators

variable {k σ ι : Type*} [CommRing k]

noncomputable def parameterCombination (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) : MvPolynomial σ k :=
  ∑ i ∈ s, MvPolynomial.C (c i) * f i

theorem parameterCombination_totalDegree_le (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) {d : ℕ}
    (hf : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (parameterCombination s c f).totalDegree ≤ d := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  calc
    (MvPolynomial.C (c i) * f i).totalDegree ≤
        (MvPolynomial.C (c i) : MvPolynomial σ k).totalDegree + (f i).totalDegree :=
      MvPolynomial.totalDegree_mul _ _
    _ = (f i).totalDegree := by rw [MvPolynomial.totalDegree_C, zero_add]
    _ ≤ d := hf i hi

theorem parameterCombination_mem (s : Finset ι) (c : ι → k)
    (f : ι → MvPolynomial σ k) (J : Ideal (MvPolynomial σ k))
    (hf : ∀ i ∈ s, f i ∈ J) : parameterCombination s c f ∈ J := by
  apply J.sum_mem
  intro i hi
  exact J.mul_mem_left _ (hf i hi)

end PiExponentJets.W22

end OAI
end Source0245

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FinsuppCandidates.lean
section Source0246
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FinsuppCandidates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {k σ ι : Type*} [CommRing k]

theorem linearCombination_eq_parameterCombination (f : ι → MvPolynomial σ k) (c : ι →₀ k) :
    Finsupp.linearCombination k f c = parameterCombination c.support c f := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, parameterCombination,
    MvPolynomial.C_mul']

theorem linearCombination_totalDegree_le (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    {d : ℕ} (hf : ∀ i, (f i).totalDegree ≤ d) :
    (Finsupp.linearCombination k f c).totalDegree ≤ d := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_totalDegree_le c.support c f (fun i _ => hf i)

theorem linearCombination_mem_ideal (f : ι → MvPolynomial σ k) (c : ι →₀ k)
    (J : Ideal (MvPolynomial σ k)) (hf : ∀ i, f i ∈ J) :
    Finsupp.linearCombination k f c ∈ J := by
  rw [linearCombination_eq_parameterCombination]
  exact parameterCombination_mem c.support c f J (fun i _ => hf i)

end PiExponentJets.W22

end OAI
end Source0246

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterAvoidance.lean
section Source0247
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterAvoidance.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem isSMulRegular_of_avoids_associatedPrimes
    (M : Type*) [AddCommGroup M] [Module R M] (x : R)
    (hx : ∀ P : Ideal R, IsAssociatedPrime P M → x ∉ P) :
    IsSMulRegular M x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro y hy
  by_contra hne
  have hzero : x ∈ {r : R | ∃ z : M, z ≠ 0 ∧ r • z = 0} := ⟨y, hne, hy⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors R M] at hzero
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.mp hzero
  exact hx P hP hxP

variable [IsLocalRing R]

omit [IsNoetherianRing R] in
theorem regular_append_singleton_of_quotient_smulRegular
    (rs : List R) (hreg : IsRegular R rs) (x : R)
    (hx : x ∈ maximalIdeal R)
    (hregular : IsSMulRegular (R ⧸ Ideal.ofList rs) x) :
    IsRegular R (rs ++ [x]) := by
  apply (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
    (M := R) (rs := rs ++ [x]) ?_).mpr
  · apply (isWeaklyRegular_append_iff R rs [x]).mpr
    refine ⟨hreg.toIsWeaklyRegular, ?_⟩
    have heq : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs :=
      (Ideal.ofList rs).mul_top
    rw [heq, isWeaklyRegular_singleton_iff]
    exact hregular
  · intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · exact (le_maximalIdeal (PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg))
        (Ideal.subset_span hy)
    · have heq : y = x := List.mem_singleton.mp hy
      simpa only [heq] using hx

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

theorem exists_constant_regular_extension
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (rs : List R) (hreg : IsRegular R rs)
    (hnot : ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ c : J →₀ k,
      Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) ∧
      IsRegular R (rs ++ [Finsupp.linearCombination k generators c]) := by
  classical
  let ass := associatedPrimes R (R ⧸ Ideal.ofList rs)
  let : Fintype ass := (associatedPrimes.finite R (R ⧸ Ideal.ofList rs)).fintype
  have hbelow (P : ass) : P.val < maximalIdeal R := by
    refine lt_iff_le_and_ne.mpr ⟨le_maximalIdeal P.property.isPrime.ne_top, ?_⟩
    intro heq
    exact hnot (heq ▸ P.property)
  obtain ⟨c, hc⟩ := PiExponentSiegel.W20.exists_linearCombination_avoiding_primes_below_radical
    (K := k) generators (maximalIdeal R) hrad (fun P : ass => P.val)
    (fun P => P.property.isPrime) hbelow
  have hlin : Finsupp.linearCombination k generators c ∈
      Submodule.span k (Set.range generators) := by
    rw [← Finsupp.range_linearCombination]
    exact ⟨c, rfl⟩
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k := by
    apply Submodule.span_le.mpr
    exact fun _ h => Ideal.subset_span h
  have hin : Finsupp.linearCombination k generators c ∈
      Ideal.span (Set.range generators) := hspan hlin
  refine ⟨c, hin, regular_append_singleton_of_quotient_smulRegular rs hreg _ ?_ ?_⟩
  · rw [← hrad]
    exact Ideal.le_radical hin
  · apply isSMulRegular_of_avoids_associatedPrimes
    intro P hP
    exact hc ⟨P, hP⟩

end PiExponentSiegel.W58

end

end OAI
end Source0247

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection2.lean
section Source0248
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection2.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open IsLocalRing RingTheory.Sequence
namespace PiExponentSiegel.W58

variable {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

theorem regular_full_length_radical_eq_maximalIdeal (rs : List R)
    (hreg : IsRegular R rs) (hdim : ringKrullDim R = rs.length) :
    (Ideal.ofList rs).radical = maximalIdeal R := by
  let I := Ideal.ofList rs
  have hproper : I ≠ ⊤ := PiExponentSiegel.W20.regular_sequence_ideal_ne_top rs hreg
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hzero : ringKrullDim (R ⧸ I) = 0 := by
    apply (ENat.WithBot.add_natCast_cancel (c := rs.length)).mp
    simpa only [zero_add, hdim] using
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular rs hreg
  let : Ring.KrullDimLE 0 (R ⧸ I) :=
    ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr hzero
  have hnil := Ring.KrullDimLE.radical_eq_maximalIdeal
    (⊥ : Ideal (R ⧸ I)) bot_ne_top
  have hc := congrArg (Ideal.comap (Ideal.Quotient.mk I)) hnil
  rw [Ideal.comap_radical, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
    IsLocalRing.maximalIdeal_comap] at hc
  exact hc

variable {k J : Type*} [Field k] [Infinite k] [Algebra k R]

omit [IsNoetherianRing R] [IsLocalRing R] [Infinite k] in
theorem constant_linearCombination_mem_ideal (generators : J → R) (c : J →₀ k) :
    Finsupp.linearCombination k generators c ∈ Ideal.span (Set.range generators) := by
  have hspan : Submodule.span k (Set.range generators) ≤
      (Ideal.span (Set.range generators)).restrictScalars k :=
    Submodule.span_le.mpr (fun _ h => Ideal.subset_span h)
  apply hspan
  rw [← Finsupp.range_linearCombination]
  exact ⟨c, rfl⟩

theorem exists_constant_regular_parameters_of_no_maximal_associated
    (generators : J → R)
    (hrad : (Ideal.span (Set.range generators)).radical = maximalIdeal R)
    (h : ℕ) (hdim : ringKrullDim R = h)
    (hnot : ∀ rs : List R, IsRegular R rs → rs.length < h →
      ¬ IsAssociatedPrime (maximalIdeal R) (R ⧸ Ideal.ofList rs)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal R := by
  have build : ∀ t : ℕ, t ≤ h → ∃ cs : List (J →₀ k), cs.length = t ∧
      IsRegular R (cs.map (Finsupp.linearCombination k generators)) := by
    intro t
    induction t with
    | zero =>
      intro _
      exact ⟨[], rfl, IsRegular.nil R R⟩
    | succ t ih =>
      intro ht
      obtain ⟨cs, hlen, hreg⟩ := ih (Nat.le_trans (Nat.le_succ t) ht)
      have hshort : (cs.map (Finsupp.linearCombination k generators)).length < h := by
        simpa only [List.length_map, hlen] using (Nat.lt_of_succ_le ht)
      obtain ⟨c, _, hc⟩ := exists_constant_regular_extension (k := k) generators hrad _ hreg
        (hnot _ hreg hshort)
      refine ⟨cs ++ [c], by simp [hlen], ?_⟩
      simpa only [List.map_append, List.map_cons, List.map_nil] using hc
  obtain ⟨cs, hlen, hreg⟩ := build h le_rfl
  refine ⟨cs, hlen, hreg, ?_, regular_full_length_radical_eq_maximalIdeal _ hreg ?_⟩
  · apply Ideal.span_le.mpr
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hx
    exact constant_linearCombination_mem_ideal generators c
  · simpa only [List.length_map, hlen] using hdim

end PiExponentSiegel.W58

end

end OAI
end Source0248

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFreeResolutionExt.lean
section Source0249
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteFreeResolutionExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe w v u

namespace PiExponentSiegelAux.W31
open Module
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open HomologicalComplex

section General
variable {C : Type u} [Category.{v} C] [Abelian C]

def projectiveResolutionOfExact (P : ChainComplex C ℕ) (M : C)
    (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : (ShortComplex.mk (P.d 1 0) ε hε).Exact)
    (hepi : Epi ε) (hexact : ∀ n : ℕ, P.ExactAt (n + 1))
    (hproj : ∀ n : ℕ, CategoryTheory.Projective (P.X n)) :
    CategoryTheory.ProjectiveResolution M where
  complex := P
  projective := hproj
  π := (ChainComplex.toSingle₀Equiv P M).symm ⟨ε, hε⟩
  quasiIso := ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff,
        ShortComplex.quasiIso_iff_of_zeros' _ (by simp) (by simp; rfl)
          (by simp; rfl)]
      simpa [ChainComplex.toSingle₀Equiv] using! And.intro hzero hepi
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' (hL := ChainComplex.exactAt_succ_single_obj ..)]
      exact hexact n⟩

variable [HasExt.{w} C]

def resolutionExtAddEquiv (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Ext M Y n ≃+
      CochainComplex.HomComplex.CohomologyClass P.cochainComplex
        ((CochainComplex.singleFunctor C 0).obj Y) n :=
  P.extAddEquivCohomologyClass

theorem ext_subsingleton_iff_cocycles_are_boundaries
    (M Y : C) (P : ProjectiveResolution M) (n : ℕ) :
    Subsingleton (Ext M Y (n + 1)) ↔
      ∀ (f : P.complex.X (n + 1) ⟶ Y),
        P.complex.d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : P.complex.X n ⟶ Y, P.complex.d (n + 1) n ≫ g = f := by
  constructor
  · intro h f hf
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mp
      (h.elim _ 0)
  · intro h
    apply subsingleton_of_forall_eq 0
    intro e
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective e (n + 2) rfl
    exact (P.extMk_eq_zero_iff f (n + 2) rfl hf n rfl).mpr (h f hf)

end General

variable {R : Type u} [CommRing R]

theorem module_exactAt_succ_of_range_eq_ker (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (n : ℕ)
    (h : LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom) : P.ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  exact h

def finiteFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (rank : ℕ → ℕ) (basis : ∀ n : ℕ, Basis (Fin (rank n)) R (P.X n)) :
    ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => ModuleCat.projective_of_free (basis n))

def moduleFreeResolutionOfExact (P : ChainComplex (ModuleCat.{u} R) ℕ)
    (M : ModuleCat.{u} R) (ε : P.X 0 ⟶ M) (hε : P.d 1 0 ≫ ε = 0)
    (hzero : LinearMap.range (P.d 1 0).hom = LinearMap.ker ε.hom)
    (hepi : Function.Surjective ε.hom)
    (hexact : ∀ n : ℕ, LinearMap.range (P.d (n + 2) (n + 1)).hom =
      LinearMap.ker (P.d (n + 1) n).hom)
    (hfree : ∀ n : ℕ, Module.Free R (P.X n)) : ProjectiveResolution M :=
  projectiveResolutionOfExact P M ε hε
    ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr hzero)
    ((ModuleCat.epi_iff_surjective ε).mpr hepi)
    (fun n => module_exactAt_succ_of_range_eq_ker P n (hexact n))
    (fun n => by
      let := hfree n
      exact ModuleCat.projective_of_free (Module.Free.chooseBasis R (P.X n)))

end PiExponentSiegelAux.W31

end

end OAI
end Source0249
