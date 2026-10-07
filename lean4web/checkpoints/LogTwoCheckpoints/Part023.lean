/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part013
public import LogTwoCheckpoints.Part015
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part017
public import LogTwoCheckpoints.Part018
public import LogTwoCheckpoints.Part020
public import LogTwoCheckpoints.Part022
public import Batteries.Logic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Opposite
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Topology.Sheaves.Flasque
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveTwistAcyclicity.lean
section Source0575
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveTwistAcyclicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ProjectiveTwistAcyclicity

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Abelian
open PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport.CechOne
open PiExponent.ProjectiveMonomialCech

universe u
variable {X : Scheme.{u}} {ι K : Type u} [Fintype ι] [AddCommGroup K]

abbrev schemeFreeOpen (V : X.Opens) : X.Modules := freeOpen X.ringCatSheaf V

abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

structure LaurentChartPresentation (U : ι → X.Opens) (M : X.Modules) (d : ℤ) where
  vertex : ∀ i, (schemeFreeOpen (U i) ⟶ M) →+ Laurent ι K d
  vertex_regular : ∀ i b, RegularOn {i} (vertex i b)
  vertex_surjective : ∀ i p, RegularOn {i} p → ∃ b, vertex i b = p
  pair : ∀ i j, (schemeFreeOpen (U i ⊓ U j) ⟶ M) →+ Laurent ι K d
  pair_injective : ∀ i j, Function.Injective (pair i j)
  pair_regular : ∀ i j c, RegularOn {i, j} (pair i j c)
  pair_left : ∀ i j b, pair i j (restrictHom X.ringCatSheaf inf_le_left b) = vertex i b
  pair_right : ∀ i j b, pair i j (restrictHom X.ringCatSheaf inf_le_right b) = vertex j b
  triple : ∀ i j k, (schemeFreeOpen ((U i ⊓ U j) ⊓ U k) ⟶ M) →+ Laurent ι K d
  triple_first : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf inf_le_left c) = pair i j c
  triple_second : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) c) = pair j k c
  triple_outer : ∀ i j k c, triple i j k
      (restrictHom X.ringCatSheaf
        (le_inf (inf_le_left.trans inf_le_left) inf_le_right) c) = pair i k c

theorem ext_succ_eq_zero_of_laurent_cech_charts [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    {U : ι → X.Opens} (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (d : ℤ) (hd : 0 ≤ d)
    (P : ProjectiveTwistCech.LaurentCechPresentation (K := K) U M d)
    (q : ℕ) (x : Ext.{u+1} (C := X.Modules) (schemeUnit (X := X)) M (q + 1)) : x = 0 := by
  let e : schemeFreeOpen (X := X) ⊤ ≅ schemeUnit (X := X) :=
    PiExponentSeshadri.FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen ⊤) M (q + 1), z = 0 := by
    apply GeometrySupport.CechHigher.affine_ext_succ_eq_zero_of_injective_cech
      X M U ⊤ (fun _ => le_top) (by rw [hcover])
    · intro n t
      exact IsAffineOpen.iInf (fun i => hU (t i))
    · intro I hI n
      exact @GeometrySupport.FreeCechSections.injective_hasPrimitives _ _ U X.ringCatSheaf I hI n
    · exact P.hasPrimitives hd q
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (q + 1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add (q + 1))))
  simpa only [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp, Ext.comp_zero] using h

end
end PiExponent.ProjectiveTwistAcyclicity

end OAI
end Source0575

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLaurentTransitions.lean
section Source0576
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveLaurentTransitions.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveLaurentTransitions
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
variable {ι R : Type*} [Fintype ι] [CommRing R]

def standardExponent (i : ι) (d : ℤ) : ι → ℤ := fun k => if k = i then d else 0

omit [Fintype ι] in
@[simp] theorem standardExponent_self (i : ι) (d : ℤ) : standardExponent i d i = d := by
  simp [standardExponent]

omit [Fintype ι] in
@[simp] theorem standardExponent_other (i k : ι) (d : ℤ) (hk : k ≠ i) :
    standardExponent i d k = 0 := by simp [standardExponent, hk]

def zeroDegreeExponent (i : ι) : ({j : ι // j ≠ i} → ℤ) →+ (ι → ℤ) where
  toFun b := (fullEncode i 0 b).val
  map_zero' := by
    funext k
    by_cases hk : k = i
    · subst k; simp
    · exact fullEncode_other i 0 0 ⟨k, hk⟩
  map_add' a b := by
    funext k
    by_cases hk : k = i
    · subst k; simp [fullEncode_self, Finset.sum_add_distrib, add_comm]
    · change (fullEncode i 0 (a + b)).val (⟨k, hk⟩ : {j : ι // j ≠ i}) = _
      rw [fullEncode_other i 0 (a + b) ⟨k, hk⟩]
      change a ⟨k, hk⟩ + b ⟨k, hk⟩ = (fullEncode i 0 a).val k + (fullEncode i 0 b).val k
      rw [show (fullEncode i 0 a).val k = a ⟨k, hk⟩ from fullEncode_other i 0 a ⟨k, hk⟩,
        show (fullEncode i 0 b).val k = b ⟨k, hk⟩ from fullEncode_other i 0 b ⟨k, hk⟩]

theorem fullEncode_eq_standard_add (i : ι) (d : ℤ)
    (b : {j : ι // j ≠ i} → ℤ) :
    (fullEncode i d b).val = standardExponent i d + zeroDegreeExponent i b := by
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, sub_eq_add_neg]
  · simp only [Pi.add_apply, standardExponent_other i k d hk, zero_add]
    exact (fullEncode_other i d b ⟨k, hk⟩).trans (fullEncode_other i 0 b ⟨k, hk⟩).symm

theorem zeroDegreeExponent_coordinate (i : ι) (j : {j : ι // j ≠ i}) :
    zeroDegreeExponent i (natExponentHom i (Finsupp.single j 1)) =
      standardExponent j.val 1 - standardExponent i 1 := by
  classical
  funext k
  by_cases hk : k = i
  · subst k
    simp [zeroDegreeExponent, fullEncode_self, natExponentHom, standardExponent,
      Ne.symm j.property, Finsupp.single_apply]
  · change (fullEncode i 0 _).val k = _
    rw [show (fullEncode i 0 _).val k =
      natExponentHom i (Finsupp.single j 1) ⟨k, hk⟩ from fullEncode_other i 0 _ ⟨k, hk⟩]
    simp [natExponentHom, standardExponent, hk, Finsupp.single_apply, Subtype.ext_iff, eq_comm]

abbrev FullGroupAlgebra := AddMonoidAlgebra R (ι → ℤ)

def chartToFull (i : ι) : chartGroupAlgebra (R := R) i →+* FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.mapDomainRingHom R (zeroDegreeExponent i)

def laurentToFull (d : ℤ) : Laurent ι R d →+ FullGroupAlgebra (ι := ι) (R := R) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    (Finsupp.mapDomain.addMonoidHom (fun a : Monomial ι d => a.val))

theorem laurentToFull_injective (d : ℤ) : Function.Injective (laurentToFull (ι := ι) (R := R) d) :=
  AddMonoidAlgebra.coeffAddEquiv.symm.injective.comp
    (Finsupp.mapDomain_injective Subtype.val_injective)

@[simp] theorem laurentToFull_single (d : ℤ) (a : Monomial ι d) (r : R) :
    laurentToFull d (Finsupp.single a r) = AddMonoidAlgebra.single a.val r := by
  simp [laurentToFull]

theorem laurentToFull_groupAlgebraToLaurent (i : ι) (d : ℤ)
    (p : chartGroupAlgebra (R := R) i) :
    laurentToFull d (groupAlgebraToLaurent i d p) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * chartToFull i p := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq, mul_add]
  | single a r =>
      change laurentToFull d (Finsupp.domCongr (fullExponentEquiv i d) (Finsupp.single a r)) = _
      simp [chartToFull, laurentToFull_single,
        fullExponentEquiv, AddMonoidAlgebra.single_mul_single]
      exact congrArg (fun exponent => AddMonoidAlgebra.single exponent r)
        (fullEncode_eq_standard_add i d a)

def overlapToFull (i : ι) (s : Finset {j : ι // j ≠ i}) :
    Localization.Away (chartProduct (R := R) i s) →+* FullGroupAlgebra (ι := ι) (R := R) :=
  (chartToFull i).comp (overlapToGroupAlgebra i s)

@[simp] theorem laurentToFull_overlapLaurent (i : ι) (d : ℤ)
    (s : Finset {j : ι // j ≠ i}) (z : Localization.Away (chartProduct (R := R) i s)) :
    laurentToFull d (overlapLaurent i d s z) =
      AddMonoidAlgebra.single (standardExponent i d) 1 * overlapToFull i s z :=
  laurentToFull_groupAlgebraToLaurent i d _

@[simp] theorem overlapToFull_X (i : ι) (s : Finset {j : ι // j ≠ i})
    (k : {j : ι // j ≠ i}) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.X (R := R) k)) =
      AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1 := by
  simp [overlapToFull, chartToFull, zeroDegreeExponent_coordinate]

@[simp] theorem overlapToFull_C (i : ι) (s : Finset {j : ι // j ≠ i}) (r : R) :
    overlapToFull (R := R) i s (algebraMap _ _ (MvPolynomial.C (σ := {j : ι // j ≠ i}) r)) =
      AddMonoidAlgebra.single 0 r := by
  simp only [overlapToFull, RingHom.comp_apply, overlapToGroupAlgebra_base]
  change AddMonoidAlgebra.mapDomain (zeroDegreeExponent i)
    (AddMonoidAlgebra.mapDomain (natExponentHom i) (AddMonoidAlgebra.single 0 r)) = _
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single]
  simp only [map_zero]

theorem overlapToFull_natural_of_generators (i j : ι)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hC : ∀ r : R, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.C (σ := {k : ι // k ≠ i}) r))) =
        AddMonoidAlgebra.single 0 r)
    (hX : ∀ k : {k : ι // k ≠ i}, overlapToFull j t
      (f (algebraMap _ _ (MvPolynomial.X (R := R) k))) =
        AddMonoidAlgebra.single (standardExponent k.val 1 - standardExponent i 1) 1) :
    (overlapToFull j t).comp f = overlapToFull i s := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (chartProduct (R := R) i s))
  apply MvPolynomial.ringHom_ext
  · intro r
    simpa only [RingHom.comp_apply, overlapToFull_C] using hC r
  · intro k
    simpa only [RingHom.comp_apply, overlapToFull_X] using hX k

theorem overlapLaurent_change_pivot (i j : ι) (d : ℤ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : Localization.Away (chartProduct (R := R) j t))
    (hu : overlapToFull j t u =
      AddMonoidAlgebra.single (standardExponent i d - standardExponent j d) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j d t (u * f z) = overlapLaurent i d s z := by
  apply laurentToFull_injective d
  rw [laurentToFull_overlapLaurent, laurentToFull_overlapLaurent, map_mul, hu, ← mul_assoc,
    AddMonoidAlgebra.single_mul_single]
  have he : standardExponent j d + (standardExponent i d - standardExponent j d) =
      standardExponent i d := by abel
  rw [he, one_mul]
  have hz := RingHom.congr_fun hf z
  change overlapToFull j t (f z) = overlapToFull i s z at hz
  rw [hz]

theorem overlapLaurent_change_pivot_pow (i j : ι) (n : ℕ)
    (s : Finset {k : ι // k ≠ i}) (t : Finset {k : ι // k ≠ j})
    (f : Localization.Away (chartProduct (R := R) i s) →+*
      Localization.Away (chartProduct (R := R) j t))
    (hf : (overlapToFull j t).comp f = overlapToFull i s)
    (u : Localization.Away (chartProduct (R := R) j t))
    (hu : overlapToFull j t u =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (z : Localization.Away (chartProduct (R := R) i s)) :
    overlapLaurent j (n : ℤ) t (u ^ n * f z) = overlapLaurent i (n : ℤ) s z := by
  apply overlapLaurent_change_pivot i j (n : ℤ) s t f hf (u ^ n) _ z
  rw [map_pow, hu, AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  funext k
  simp [standardExponent, mul_sub]

def fullMonomialUnit (a : ι → ℤ) : (FullGroupAlgebra (ι := ι) (R := R))ˣ where
  val := AddMonoidAlgebra.single a 1
  inv := AddMonoidAlgebra.single (-a) 1
  val_inv := by rw [AddMonoidAlgebra.single_mul_single]; simp only [add_neg_cancel, one_mul]; rfl
  inv_val := by rw [AddMonoidAlgebra.single_mul_single]; simp only [neg_add_cancel, one_mul]; rfl

def fullMonomialUnits : Multiplicative (ι → ℤ) →* (FullGroupAlgebra (ι := ι) (R := R))ˣ where
  toFun a := fullMonomialUnit a.toAdd
  map_one' := by apply Units.ext; rfl
  map_mul' a b := by
    apply Units.ext
    change AddMonoidAlgebra.single (a.toAdd + b.toAdd) 1 =
      AddMonoidAlgebra.single a.toAdd 1 * AddMonoidAlgebra.single b.toAdd 1
    rw [AddMonoidAlgebra.single_mul_single, one_mul]

omit [Fintype ι] in

theorem fullMonomialUnit_zpow (a : ι → ℤ) (d : ℤ) :
    fullMonomialUnit (R := R) (d • a) = (fullMonomialUnit a) ^ d := by
  have h := map_zpow (fullMonomialUnits (ι := ι) (R := R)) (Multiplicative.ofAdd a) d
  exact h

theorem overlapToFull_ratio (i j k : ι) (t : Finset {l : ι // l ≠ j})
    (x y yinv : Localization.Away (chartProduct (R := R) j t))
    (hx : overlapToFull j t x =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent j 1) 1)
    (hy : overlapToFull j t y =
      AddMonoidAlgebra.single (standardExponent i 1 - standardExponent j 1) 1)
    (hinv : y * yinv = 1) :
    overlapToFull j t (x * yinv) =
      AddMonoidAlgebra.single (standardExponent k 1 - standardExponent i 1) 1 := by
  have hcancel := congrArg (overlapToFull j t) hinv
  rw [map_mul, hy, map_one] at hcancel
  have hunit : IsUnit (AddMonoidAlgebra.single
      (standardExponent i 1 - standardExponent j 1) (1 : R)) :=
    (fullMonomialUnit (R := R) (standardExponent i 1 - standardExponent j 1)).isUnit
  have hi : overlapToFull j t yinv = AddMonoidAlgebra.single
      (standardExponent j 1 - standardExponent i 1) 1 := by
    apply hunit.mul_left_cancel
    rw [hcancel, AddMonoidAlgebra.single_mul_single]
    have he : standardExponent i 1 - standardExponent j 1 +
        (standardExponent j 1 - standardExponent i 1) = 0 := by abel
    rw [he, one_mul]
    rfl
  rw [map_mul, hx, hi, AddMonoidAlgebra.single_mul_single]
  have he : standardExponent k 1 - standardExponent j 1 +
      (standardExponent j 1 - standardExponent i 1) =
      standardExponent k 1 - standardExponent i 1 := by abel
  rw [he, one_mul]

end
end PiExponent.GeometrySupport.ProjectiveLaurentTransitions

end OAI
end Source0576

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFiniteValues.lean
section Source0577
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFiniteValues.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_restrict_apply (i : σ) (a : Finset (ChartVariables i))
    (x : Γ(X,SectionOpens.isoOpen (s i))) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op x) =
      algebraMap _ _ (coordinateSectionRingEquiv M k s hc f hf i x) := by
  have h := coordinateFiniteRingEquiv_restrict M k s hc f hf i a
    (coordinateSectionRingEquiv M k s hc f hf i x)
  simpa only [RingEquiv.symm_apply_apply] using h

lemma coordinateFiniteRingEquiv_coordinate (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j))))) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) := by
  rw [coordinateFiniteRingEquiv_restrict_apply, coordinateSectionRingEquiv_coordinate]

lemma coordinateFiniteRingEquiv_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r) := by
  have h := coordinateFiniteRingEquiv_restrict_apply M s k hc f hf i a
    (X.presheaf.map (homOfLE (show SectionOpens.isoOpen (s i) ≤ ⊤ from le_top)).op (k r))
  rw [coordinateSectionRingEquiv_constant] at h
  convert h using 1
  change _ = coordinateFiniteRingEquiv M s k hc f hf i a
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r))
  rw [← Functor.map_comp]
  rfl

lemma coordinateFiniteRingEquiv_symm_constant (i : σ) (a : Finset (ChartVariables i)) (r : K) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
    X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤ ⊤ from le_top)).op (k r) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_constant]

lemma coordinateFiniteRingEquiv_symm_X (i : σ) (a : Finset (ChartVariables i))
    (j : ChartVariables i) :
    (coordinateFiniteRingEquiv M s k hc f hf i a).symm
      (algebraMap _ _ (MvPolynomial.X (R := K) j)) =
      X.presheaf.map (homOfLE (show coordinateFiniteOpen M s i a ≤
        SectionOpens.isoOpen (s i) from inf_le_left)).op
        ((SectionOpens.isoOpen (s i)).topIso.hom
          (coefficient (sectionFrame (s i))
            (restrictSection (SectionOpens.isoOpen (s i)).ι (s j.val)))) := by
  apply (coordinateFiniteRingEquiv M s k hc f hf i a).injective
  rw [RingEquiv.apply_symm_apply, coordinateFiniteRingEquiv_coordinate,
    chartToPoly_coordinate, dite_eq_right j.property]

def coordinateFiniteTransition (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    Localization.Away (chartProduct (R := K) i a) →+*
      Localization.Away (chartProduct (R := K) j b) :=
  (coordinateFiniteRingEquiv M s k hc f hf j b).toRingHom.comp
    ((X.presheaf.map (homOfLE h).op).hom.comp
      (coordinateFiniteRingEquiv M s k hc f hf i a).symm.toRingHom)

lemma coordinateFiniteTransition_constant (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) (r : K) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.C (σ := ChartVariables i) r)) =
      algebraMap _ _ (MvPolynomial.C (σ := ChartVariables j) r) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_constant]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    ((X.presheaf.map _ ≫ X.presheaf.map _) (k r)) = _
  rw [← Functor.map_comp]
  exact coordinateFiniteRingEquiv_constant M s k hc f hf j b r

end
end PiExponentSeshadri.Projective

end OAI
end Source0577

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateRatios.lean
section Source0578
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateRatios.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry Frames ModuleFlasque RestrictionCohomology
open PiExponentSeshadri.ProjectiveChartSections
variable {X : Scheme} {M : X.Modules}

def coordinateRatioOn (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : Γ(X,W) :=
  X.presheaf.map (homOfLE hi).op
    ((SectionOpens.isoOpen si).topIso.hom
      (coefficient (sectionFrame si)
        (restrictSection (SectionOpens.isoOpen si).ι sk)))

lemma coordinateRatioOn_eq_coefficient (si sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) :
    coordinateRatioOn si sk hi = W.topIso.hom
      (coefficient (restrictOpenFrame hi (sectionFrame si)) (restrictSection W.ι sk)) := by
  rw [restrictOpenFrame_coefficient_global, topIso_hom_restrict]
  rfl

@[simp] lemma coordinateRatioOn_self (si : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) : coordinateRatioOn si si hi = 1 := by
  simp only [coordinateRatioOn, sectionFrame_normalized, map_one]

lemma coordinateRatioOn_change (si sj sk : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj sk hj = coordinateRatioOn sj si hj * coordinateRatioOn si sk hi := by
  rw [coordinateRatioOn_eq_coefficient sj sk hj,
    coefficient_change (restrictOpenFrame hi (sectionFrame si)),
    frameChange_restrictOpenFrame hi hj _ _ si (sectionFrame_normalized si),
    map_mul, topIso_hom_restrict, ← coordinateRatioOn_eq_coefficient]
  rfl

lemma coordinateRatioOn_reciprocal (si sj : O X ⟶ M) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    coordinateRatioOn sj si hj * coordinateRatioOn si sj hi = 1 := by
  rw [← coordinateRatioOn_change si sj sj hi hj, coordinateRatioOn_self]

lemma coordinateRatioOn_restrict (si sk : O X ⟶ M) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen si) (h : W ≤ U) :
    X.presheaf.map (homOfLE h).op (coordinateRatioOn si sk hi) =
      coordinateRatioOn si sk (h.trans hi) := by
  unfold coordinateRatioOn
  change (X.presheaf.map (homOfLE hi).op ≫ X.presheaf.map (homOfLE h).op) _ = _
  rw [← Functor.map_comp]
  rfl

lemma framedHomCoefficientsEquiv_change (W : X.Opens) (N : X.Modules)
    (e f : N.restrict W.ι ≅ structureSheaf W.toScheme)
    (b : freeOpen X.ringCatSheaf W ⟶ N) :
    framedHomCoefficientsEquiv W N f b =
      W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) *
        framedHomCoefficientsEquiv W N e b := by
  let x := (restrictionSectionsIso W N).inv (freeOpenEquiv X.ringCatSheaf N W b)
  change W.topIso.hom (f.hom.app ⊤ x) =
    W.topIso.hom (frameChange e f : Γ(W.toScheme,⊤)) * W.topIso.hom (e.hom.app ⊤ x)
  erw [← map_mul]
  apply congrArg W.topIso.hom
  have hx : e.inv.app ⊤ (e.hom.app ⊤ x) = x :=
    congrArg (fun g => g.app ⊤ x) e.hom_inv_id
  have hc := end_apply (e.inv ≫ f.hom) ⊤ (e.hom.app ⊤ x)
  change f.hom.app ⊤ (e.inv.app ⊤ (e.hom.app ⊤ x)) =
    (show Γ(W.toScheme,⊤) from e.hom.app ⊤ x) *
      (frameChange e f : Γ(W.toScheme,⊤)) at hc
  rw [hx, mul_comm] at hc
  exact hc

lemma coordinatePowerFrame_hom_change (si sj : O X ⟶ M) (n : ℕ) {W : X.Opens}
    (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj)
    (b : freeOpen X.ringCatSheaf W ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame hj (coordinatePowerFrame sj n)) b =
    coordinateRatioOn sj si hj ^ n *
      framedHomCoefficientsEquiv W (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b := by
  erw [framedHomCoefficientsEquiv_change W _
    (restrictOpenFrame hi (coordinatePowerFrame si n)),
    coordinatePowerFrame_frameChange, map_pow, topIso_hom_restrict]
  rfl

lemma framedHomCoefficientsEquiv_eq_of_normalized (W : X.Opens) (N : X.Modules)
    (e f : N.restrict W.ι ≅ structureSheaf W.toScheme)
    (t : O W.toScheme ⟶ N.restrict W.ι)
    (he : coefficient e t = 1) (hf : coefficient f t = 1)
    (b : freeOpen X.ringCatSheaf W ⟶ N) :
    framedHomCoefficientsEquiv W N f b = framedHomCoefficientsEquiv W N e b := by
  have hc := coefficient_change e f t
  rw [he, hf, mul_one] at hc
  rw [framedHomCoefficientsEquiv_change W N e f, ← hc, map_one, one_mul]

lemma coordinatePowerFrame_hom_restrict (si : O X ⟶ M) (n : ℕ) {U W : X.Opens}
    (hi : U ≤ SectionOpens.isoOpen si) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
    X.presheaf.map (homOfLE h).op
      (framedHomCoefficientsEquiv U (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b) := by
  have he : coefficient
      (restrictOpenFrame h (restrictOpenFrame hi (coordinatePowerFrame si n)))
      (restrictSection W.ι (powerSection si n)) = 1 := by
    erw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
      coordinatePowerFrame_normalized, map_one, map_one]
  have hf : coefficient
      (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
      (restrictSection W.ι (powerSection si n)) = 1 := by
    erw [restrictOpenFrame_coefficient_global, coordinatePowerFrame_normalized, map_one]
  erw [framedHomCoefficientsEquiv_eq_of_normalized W (modulePow X M n)
    (restrictOpenFrame h (restrictOpenFrame hi (coordinatePowerFrame si n)))
    (restrictOpenFrame (h.trans hi) (coordinatePowerFrame si n))
    (restrictSection W.ι (powerSection si n)) he hf]
  exact framedHomCoefficientsEquiv_restrict (modulePow X M n) h _ b

lemma coordinatePowerFrame_hom_change_restrict (si sj : O X ⟶ M) (n : ℕ)
    {U W : X.Opens} (hi : U ≤ SectionOpens.isoOpen si)
    (hj : W ≤ SectionOpens.isoOpen sj) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ modulePow X M n) :
    framedHomCoefficientsEquiv W (modulePow X M n)
      (restrictOpenFrame hj (coordinatePowerFrame sj n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
    coordinateRatioOn sj si hj ^ n * X.presheaf.map (homOfLE h).op
      (framedHomCoefficientsEquiv U (modulePow X M n)
        (restrictOpenFrame hi (coordinatePowerFrame si n)) b) := by
  erw [coordinatePowerFrame_hom_change si sj n (h.trans hi) hj,
    coordinatePowerFrame_hom_restrict]

end
end PiExponentSeshadri.Projective

end OAI
end Source0578

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateTransitions.lean
section Source0579
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateTransitions.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_ratio (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left)) =
      algebraMap _ _ (chartToPoly (R := K) i (chartCoordinate i j)) :=
  coordinateFiniteRingEquiv_coordinate M s k hc f hf i a j

lemma coordinateFiniteTransition_X (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l)) =
      coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s l.val) (h.trans inf_le_left)) := by
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op
      ((coordinateFiniteRingEquiv M s k hc f hf i a).symm _)) = _
  rw [coordinateFiniteRingEquiv_symm_X]
  change coordinateFiniteRingEquiv M s k hc f hf j b
    (X.presheaf.map (homOfLE h).op (coordinateRatioOn (s i) (s l.val) inf_le_left)) = _
  erw [coordinateRatioOn_restrict]

variable [Fintype σ]

lemma coordinateFiniteRingEquiv_ratio_full (i : σ) (a : Finset (ChartVariables i)) (j : σ) :
    overlapToFull i a (coordinateFiniteRingEquiv M s k hc f hf i a
      (coordinateRatioOn (s i) (s j)
        (show coordinateFiniteOpen M s i a ≤ SectionOpens.isoOpen (s i) from inf_le_left))) =
      AddMonoidAlgebra.single (standardExponent j 1 - standardExponent i 1) 1 := by
  classical
  rw [coordinateFiniteRingEquiv_ratio, chartToPoly_coordinate]
  by_cases hji : j = i
  · subst j
    simp only [dite_true, map_one, sub_self]
    rfl
  · rw [dite_eq_right hji, overlapToFull_X]

lemma coordinateFiniteTransition_X_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (l : ChartVariables i) :
    overlapToFull j b (coordinateFiniteTransition M s k hc f hf i j a b h
      (algebraMap _ _ (MvPolynomial.X (R := K) l))) =
      AddMonoidAlgebra.single (standardExponent l.val 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i) := h.trans inf_le_left
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l.val) hj) *
          r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateFiniteTransition_X,
        coordinateRatioOn_change (s j) (s i) (s l.val) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l.val b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l.val)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateFiniteTransition_full (i j : σ) (a : Finset (ChartVariables i))
    (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a) :
    (overlapToFull j b).comp (coordinateFiniteTransition M s k hc f hf i j a b h) =
      overlapToFull i a := by
  apply overlapToFull_natural_of_generators
  · intro r
    rw [coordinateFiniteTransition_constant, overlapToFull_C]
  · intro l
    exact coordinateFiniteTransition_X_full M s k hc f hf i j a b h l

end
end PiExponentSeshadri.Projective

end OAI
end Source0579

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateOverlapNaturality.lean
section Source0580
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateOverlapNaturality.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
open PiExponentSeshadri.ProjectiveChartSections
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinatePowerOverlap_restrict (n : ℕ) (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : freeOpen X.ringCatSheaf (coordinateFiniteOpen M s i a) ⟶ modulePow X M n) :
    coordinatePowerOverlap M s k hc f hf n j b
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      coordinatePowerOverlap M s k hc f hf n i a z := by
  let ci := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) (modulePow X M n)
    (restrictOpenFrame inf_le_left (coordinatePowerFrame (s i) n)) z
  let ri := coordinateFiniteRingEquiv M s k hc f hf i a
  let rj := coordinateFiniteRingEquiv M s k hc f hf j b
  let u := coordinateRatioOn (s j) (s i)
    (show coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) from inf_le_left)
  have ht : coordinateFiniteTransition M s k hc f hf i j a b h (ri ci) =
      rj (X.presheaf.map (homOfLE h).op ci) := by
    simp only [coordinateFiniteTransition, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ri, RingEquiv.symm_apply_apply, rj]
  change overlapLaurent j (n : ℤ) b
    (rj (framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) (modulePow X M n)
      (restrictOpenFrame inf_le_left (coordinatePowerFrame (s j) n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z))) =
    overlapLaurent i (n : ℤ) a (ri ci)
  have hcoef : framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) (modulePow X M n)
      (restrictOpenFrame inf_le_left (coordinatePowerFrame (s j) n))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      u ^ n * X.presheaf.map (homOfLE h).op ci :=
    coordinatePowerFrame_hom_change_restrict (s i) (s j) n
      (U := coordinateFiniteOpen M s i a) (W := coordinateFiniteOpen M s j b)
      inf_le_left inf_le_left h z
  rw [hcoef, map_mul, map_pow]
  change overlapLaurent j (n : ℤ) b
    ((rj u) ^ n * rj (X.presheaf.map (homOfLE h).op ci)) = _
  rw [← ht]
  exact overlapLaurent_change_pivot_pow i j n a b
    (coordinateFiniteTransition M s k hc f hf i j a b h)
    (coordinateFiniteTransition_full M s k hc f hf i j a b h) (rj u)
    (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) (ri ci)

end
end PiExponentSeshadri.Projective

end OAI
end Source0580

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveTupleCharts.lean
section Source0581
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveTupleCharts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveTupleCharts

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry

universe u
variable {σ : Type u} [Fintype σ]

def tupleVariables {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    Finset {j : σ // j ≠ t p} := by
  classical
  exact Finset.univ.filter (fun j => j.val ∈ Set.range t)

@[simp] theorem mem_tupleVariables {q : ℕ} (t : Fin (q + 1) → σ)
    (p : Fin (q + 1)) (j : {j : σ // j ≠ t p}) :
    j ∈ tupleVariables t p ↔ j.val ∈ Set.range t := by
  classical
  simp [tupleVariables]

theorem tupleVariables_support {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    ({t p} : Set σ) ∪ Subtype.val '' (tupleVariables t p : Set {j : σ // j ≠ t p}) =
      Set.range t := by
  classical
  ext j
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact h ▸ Set.mem_range_self p
    · exact (mem_tupleVariables t p a).mp ha
  · intro hj
    by_cases hp : j = t p
    · exact Or.inl hp
    · exact Or.inr ⟨⟨j, hp⟩, (mem_tupleVariables t p _).mpr hj, rfl⟩

theorem tupleVariables_inf {α : Type*} [CompleteLattice α]
    (U : σ → α) {q : ℕ} (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    U (t p) ⊓ (tupleVariables t p).inf (fun j => U j.val) = ⨅ i, U (t i) := by
  classical
  apply le_antisymm
  · apply le_iInf
    intro i
    by_cases h : t i = t p
    · rw [h]
      exact inf_le_left
    · exact inf_le_right.trans (Finset.inf_le
        ((mem_tupleVariables t p ⟨t i, h⟩).mpr (Set.mem_range_self i)))
  · apply le_inf (iInf_le _ p)
    apply Finset.le_inf
    intro j hj
    obtain ⟨i, hi⟩ := (mem_tupleVariables t p j).mp hj
    exact hi ▸ iInf_le (fun i => U (t i)) i

theorem coordinateFiniteOpen_tuple {X : Scheme} {σ : Type} [Fintype σ]
    (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) {q : ℕ}
    (t : Fin (q + 1) → σ) (p : Fin (q + 1)) :
    coordinateFiniteOpen M s (t p) (tupleVariables t p) =
      CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t := by
  change PiExponentSeshadri.SectionOpens.isoOpen (s (t p)) ⊓
    (tupleVariables t p).inf (fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j.val)) = _
  exact tupleVariables_inf (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t p

open PiExponentSeshadri.ModuleFlasque
open PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def freeOpenHomCongr {X : Scheme} (M : X.Modules) {U V : X.Opens} (h : U = V) :
    (schemeFreeOpen X V ⟶ M) ≃+ (schemeFreeOpen X U ⟶ M) where
  toFun b := freeOpenMap X.ringCatSheaf (eqToHom h) ≫ b
  invFun b := freeOpenMap X.ringCatSheaf (eqToHom h.symm) ≫ b
  left_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  right_inv b := by
    subst h
    simp [freeOpenMap]
    erw [Category.id_comp, Category.id_comp]
  map_add' b c := Preadditive.comp_add (C := X.Modules) _ _ _ _ b c

theorem freeOpenHomCongr_restrict {X : Scheme} (M : X.Modules)
    {U U' V V' : X.Opens} (hU : U' = U) (hV : V' = V) (h : V ≤ U)
    (b : schemeFreeOpen X U ⟶ M) :
    freeOpenHomCongr M hV (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      freeOpenMap X.ringCatSheaf (homOfLE (hV.le.trans (h.trans hU.ge))) ≫
        freeOpenHomCongr M hU b := by
  subst hU
  subst hV
  simp [freeOpenHomCongr, freeOpenMap]
  erw [Category.id_comp]

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M))
variable (k : K →+* Γ(X,⊤)) (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)

attribute [local irreducible] coordinatePowerOverlap modulePow

include hf in
omit [Fintype σ] in

theorem coordinateOpen_isAffine (i : σ) :
    IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
  erw [sectionOpen_eq_coordinate_preimage M k s hc f hf i]
  exact (Proj.isAffineOpen_basicOpen (PolyGrade K σ) (MvPolynomial.X i)
    (poly_X_mem i) (by decide)).preimage f.hom

def coordinateTupleCoefficient (n q : ℕ) (t : Fin (q + 1) → σ) :
    (schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) →+ Laurent σ K n :=
  (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

theorem coordinateTupleCoefficient_injective (n q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateTupleCoefficient M s k hc f hf n q t) :=
  (coordinatePowerOverlap_injective M s k hc f hf n (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).injective

theorem coordinateTupleCoefficient_regular (n q : ℕ) (t : Fin (q + 1) → σ)
    (b : schemeFreeOpen X
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t) ⟶
        modulePow X M n) :
    RegularOn (Set.range t) (coordinateTupleCoefficient M s k hc f hf n q t b) := by
  have h := coordinatePowerOverlap_regular M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0) b)
  unfold coordinateTupleCoefficient
  change RegularOn (Set.range t) ((coordinatePowerOverlap M s k hc f hf n (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

theorem coordinateTupleCoefficient_surjective_regular (n q : ℕ)
    (t : Fin (q + 1) → σ) (p : Laurent σ K n) (hp : RegularOn (Set.range t) p) :
    ∃ b, coordinateTupleCoefficient M s k hc f hf n q t b = p := by
  obtain ⟨b, hb⟩ := coordinatePowerOverlap_surjective_regular M s k hc f hf n (t 0)
    (tupleVariables t 0) p (by simpa only [tupleVariables_support] using hp)
  refine ⟨(freeOpenHomCongr (modulePow X M n)
    (coordinateFiniteOpen_tuple M s t 0)).symm b, ?_⟩
  change (coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0))
    ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0))
      ((freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)).symm b)) = p
  rw [AddEquiv.apply_symm_apply]
  exact hb

end
end PiExponent.GeometrySupport.ProjectiveTupleCharts

end OAI
end Source0581

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveCoordinateAcyclicity.lean
section Source0582
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveCoordinateAcyclicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Projective PiExponentSeshadri.Geometry PiExponentSeshadri.ModuleFlasque
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (structureSheaf X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,PiExponentSeshadri.SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
attribute [local irreducible] coordinatePowerOverlap modulePow

abbrev schemeUnit : X.Modules := SheafOfModules.unit X.ringCatSheaf

attribute [local instance] PiExponentSeshadri.FiniteCoverCohomology.hasExtScheme'

theorem coordinateTupleCoefficient_restrict (n q r : ℕ) (t : Fin (q + 1) → σ)
    (g : Fin (r + 1) → Fin (q + 1))
    (b : freeOpen X.ringCatSheaf
      (CechHigher.intersection (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) (t ∘ g)) ⟶
        modulePow X M n) :
    coordinateTupleCoefficient M s k hc f hf n q t
      (CechOne.restrictHom X.ringCatSheaf
        (CechHigher.intersectionLE (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t g) b) =
      coordinateTupleCoefficient M s k hc f hf n r (t ∘ g) b := by
  change coordinatePowerOverlap M s k hc f hf n (t 0) (tupleVariables t 0)
    (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s t 0)
      (freeOpenMap X.ringCatSheaf (homOfLE
        (CechHigher.intersectionLE (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) t g)) ≫ b)) =
    coordinatePowerOverlap M s k hc f hf n ((t ∘ g) 0) (tupleVariables (t ∘ g) 0)
      (freeOpenHomCongr (modulePow X M n) (coordinateFiniteOpen_tuple M s (t ∘ g) 0) b)
  erw [freeOpenHomCongr_restrict]
  exact coordinatePowerOverlap_restrict M s k hc f hf n ((t ∘ g) 0) (t 0)
    (tupleVariables (t ∘ g) 0) (tupleVariables t 0) _ _

def coordinateLaurentCechPresentation (n : ℕ) :
    ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) (modulePow X M n) n where
  coefficient := coordinateTupleCoefficient M s k hc f hf n
  injective := coordinateTupleCoefficient_injective M s k hc f hf n
  regular := coordinateTupleCoefficient_regular M s k hc f hf n
  surjective := coordinateTupleCoefficient_surjective_regular M s k hc f hf n
  restriction q t j b :=
    coordinateTupleCoefficient_restrict M s k hc f hf n (q + 1) q t j.succAbove b

def coordinateLineBundle : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    have hx : x ∈ (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) := by
      rw [hc]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    exact ⟨PiExponentSeshadri.SectionOpens.isoOpen (s i), hi, ⟨sectionFrame (s i)⟩⟩

include hc in
omit [Fintype σ] in

theorem coordinatePower_isQuasicoherent (n : ℕ) :
    (modulePow X M n).IsQuasicoherent :=
  LineBundleCoherent.modulePow_isQuasicoherent (coordinateLineBundle M s hc) n

include hf in

theorem coordinatePower_ext_succ_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) (q + 1)) : x = 0 := by
  let : (modulePow X M n).IsQuasicoherent := coordinatePower_isQuasicoherent M s hc n
  exact ProjectiveTwistAcyclicity.ext_succ_eq_zero_of_laurent_cech_charts
    (coordinateOpen_isAffine M s k hc f hf) hc (modulePow X M n) n (Int.natCast_nonneg n)
    (coordinateLaurentCechPresentation M s k hc f hf n) q x

include hf in
theorem coordinatePower_ext_eq_zero [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))] (n q : ℕ) (hq : 0 < q)
    (x : Ext.{1} (C := X.Modules) (schemeUnit (X := X)) (modulePow X M n) q) : x = 0 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  exact coordinatePower_ext_succ_eq_zero M s k hc f hf n r x

end
end PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity

end OAI
end Source0582

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ProjectiveFramedCech.lean
section Source0583
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ProjectiveFramedCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

abbrev projectiveFramedCechFreeOpen (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

def coordinateFramedOverlap (i : σ) (a : Finset (ChartVariables i)) :
    (projectiveFramedCechFreeOpen (coordinateFiniteOpen M s i a) ⟶ N) →+ Laurent σ K d :=
  framedLaurentOverlap _ N i d a (restrictOpenFrame inf_le_left (e i))
    (coordinateFiniteRingEquiv M s k hc f hf i a)

lemma coordinateFramedOverlap_injective (i : σ) (a : Finset (ChartVariables i)) :
    Function.Injective (coordinateFramedOverlap M s k hc f hf N e d i a) :=
  framedLaurentOverlap_injective _ _ _ _ _ _ _

lemma coordinateFramedOverlap_regular (i : σ) (a : Finset (ChartVariables i))
    (b : projectiveFramedCechFreeOpen (coordinateFiniteOpen M s i a) ⟶ N) :
    RegularOn ({i} ∪ Subtype.val '' (a : Set (ChartVariables i)))
      (coordinateFramedOverlap M s k hc f hf N e d i a b) :=
  framedLaurentOverlap_regular _ _ _ _ _ _ _ b

lemma coordinateFramedOverlap_surjective (i : σ) (a : Finset (ChartVariables i))
    (p : Laurent σ K d) (hp : RegularOn ({i} ∪ Subtype.val '' (a : Set (ChartVariables i))) p) :
    ∃ b, coordinateFramedOverlap M s k hc f hf N e d i a b = p :=
  framedLaurentOverlap_surjective_regular _ _ _ _ _ _ _ p hp

attribute [local irreducible] coordinateFramedOverlap

def coordinateFramedTuple (q : ℕ) (t : Fin (q + 1) → σ) :
    (projectiveFramedCechFreeOpen
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) →+
      Laurent σ K d :=
  (coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)).comp
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).toAddMonoidHom

lemma coordinateFramedTuple_injective (q : ℕ) (t : Fin (q + 1) → σ) :
    Function.Injective (coordinateFramedTuple M s k hc f hf N e d q t) := by
  intro b c h
  apply (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).injective
  apply coordinateFramedOverlap_injective M s k hc f hf N e d (t 0) (tupleVariables t 0)
  exact h

lemma coordinateFramedTuple_regular (q : ℕ) (t : Fin (q + 1) → σ)
    (b : projectiveFramedCechFreeOpen
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    RegularOn (Set.range t) (coordinateFramedTuple M s k hc f hf N e d q t b) := by
  have h := coordinateFramedOverlap_regular M s k hc f hf N e d (t 0) (tupleVariables t 0)
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) b)
  change RegularOn (Set.range t) ((coordinateFramedOverlap M s k hc f hf N e d (t 0)
    (tupleVariables t 0)) ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)) b))
  simpa only [tupleVariables_support] using h

lemma coordinateFramedTuple_surjective (q : ℕ) (t : Fin (q + 1) → σ)
    (p : Laurent σ K d) (hp : RegularOn (Set.range t) p) :
    ∃ b, coordinateFramedTuple M s k hc f hf N e d q t b = p := by
  obtain ⟨b, hb⟩ := coordinateFramedOverlap_surjective M s k hc f hf N e d (t 0)
    (tupleVariables t 0) p (by simpa only [tupleVariables_support] using hp)
  refine ⟨(freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).symm b, ?_⟩
  change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
    ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0))
      ((freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)).symm b)) = p
  rw [AddEquiv.apply_symm_apply]
  exact hb

def coordinateFramedLaurentPresentation
    (hres : ∀ i j (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
      (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
      (z : projectiveFramedCechFreeOpen (coordinateFiniteOpen M s i a) ⟶ N),
      coordinateFramedOverlap M s k hc f hf N e d j b
        (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      coordinateFramedOverlap M s k hc f hf N e d i a z) :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N d where
  coefficient := coordinateFramedTuple M s k hc f hf N e d
  injective := coordinateFramedTuple_injective M s k hc f hf N e d
  regular := coordinateFramedTuple_regular M s k hc f hf N e d
  surjective := coordinateFramedTuple_surjective M s k hc f hf N e d
  restriction q t j z := by
    change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
      (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0)
        (freeOpenMap X.ringCatSheaf (homOfLE
          (PiExponent.GeometrySupport.CechHigher.faceLE (fun i => SectionOpens.isoOpen (s i)) t j)) ≫ z)) =
      coordinateFramedOverlap M s k hc f hf N e d ((t ∘ j.succAbove) 0)
        (tupleVariables (t ∘ j.succAbove) 0)
        (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s (t ∘ j.succAbove) 0) z)
    erw [freeOpenHomCongr_restrict]
    exact hres _ _ _ _ _ _

end
end PiExponentSeshadri.Projective

end OAI
end Source0583

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateScalars.lean
section Source0584
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ProjectiveChartSections
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry ModuleFlasque

abbrev coordinateScalarFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} (U : X.Opens) (M : X.Modules)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen :
    Module Γ(X,⊤) (coordinateScalarFreeOpen X U ⟶ M) :=
  sheafHomModule X _ M

lemma freeOpenAddEquiv_smul (r : Γ(X,⊤)) (b : coordinateScalarFreeOpen X U ⟶ M) :
    freeOpenAddEquiv U M (r • b) = restrictScalar X U r • freeOpenAddEquiv U M b := by
  rfl

lemma framedHomCoefficientsEquiv_smul
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (r : Γ(X,⊤)) (b : coordinateScalarFreeOpen X U ⟶ M) :
    framedHomCoefficientsEquiv U M e (r • b) =
      restrictScalar X U r * framedHomCoefficientsEquiv U M e b := by
  change framedCoefficientsEquiv U M e (freeOpenAddEquiv U M (r • b)) = _
  rw [freeOpenAddEquiv_smul, framedCoefficientsEquiv_smul]
  rfl
end PiExponentSeshadri.ProjectiveChartSections

namespace PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.ProjectiveMonomialCech
variable {K σ : Type} [CommRing K] [Fintype σ]

lemma groupAlgebraToLaurent_smul (i : σ) (d : ℤ) (c : K)
    (z : chartGroupAlgebra (R := K) i) :
    groupAlgebraToLaurent i d (c • z) = c • groupAlgebraToLaurent i d z := by
  ext a
  rfl

lemma overlapLaurent_constant_mul (i : σ) (d : ℤ) (a : Finset {j : σ // j ≠ i})
    (c : K) (z : Localization.Away (chartProduct (R := K) i a)) :
    overlapLaurent i d a (algebraMap (MvPolynomial {j : σ // j ≠ i} K) _ (MvPolynomial.C c) * z) =
      c • overlapLaurent i d a z := by
  change groupAlgebraToLaurent i d
    (overlapToGroupAlgebra i a (algebraMap (MvPolynomial {j : σ // j ≠ i} K) _ (MvPolynomial.C c) * z)) = _
  rw [map_mul, overlapToGroupAlgebra_base]
  have hc : polynomialToGroupAlgebra i (MvPolynomial.C c) =
      AddMonoidAlgebra.single 0 c := by
    change AddMonoidAlgebra.mapDomain _ (AddMonoidAlgebra.single 0 c) = _
    rw [AddMonoidAlgebra.mapDomain_single, map_zero]
  have hs (z' : chartGroupAlgebra (R := K) i) :
      AddMonoidAlgebra.single 0 c * z' = c • z' := by
    ext a'
    simp only [AddMonoidAlgebra.coeff_single_zero_mul, AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [hc, hs, groupAlgebraToLaurent_smul]
  rfl
end PiExponent.GeometrySupport.ProjectiveLaurentVertex

namespace PiExponentSeshadri.Projective
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (N : X.Modules)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen
    (U : X.Opens) : Module Γ(X,⊤) (coordinateScalarFreeOpen X U ⟶ N) :=
  sheafHomModule X _ N
variable (e : ∀ i, N.restrict (SectionOpens.isoOpen (s i)).ι ≅
  structureSheaf (SectionOpens.isoOpen (s i)).toScheme) (d : ℤ)

lemma coordinateFramedOverlap_smul (i : σ) (a : Finset (ChartVariables i))
    (c : K) (b : coordinateScalarFreeOpen X (coordinateFiniteOpen M s i a) ⟶ N) :
    coordinateFramedOverlap M s k hc f hf N e d i a ((k c) • b) =
      c • coordinateFramedOverlap M s k hc f hf N e d i a b := by
  let g := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) N
    (restrictOpenFrame inf_le_left (e i))
  let r := coordinateFiniteRingEquiv M s k hc f hf i a
  change overlapLaurent i d a (r (g ((k c) • b))) = c • overlapLaurent i d a (r (g b))
  have hs : g ((k c) • b) = restrictScalar X (coordinateFiniteOpen M s i a) (k c) * g b :=
    framedHomCoefficientsEquiv_smul (coordinateFiniteOpen M s i a) N
      (restrictOpenFrame inf_le_left (e i)) (k c) b
  have hr : r (restrictScalar X (coordinateFiniteOpen M s i a) (k c)) =
      algebraMap _ _ (MvPolynomial.C c) :=
    coordinateFiniteRingEquiv_constant M s k hc f hf i a c
  rw [hs, map_mul, hr]
  exact overlapLaurent_constant_mul i d a c _

attribute [local irreducible] coordinateFramedOverlap
lemma coordinateFramedTuple_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : coordinateScalarFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    coordinateFramedTuple M s k hc f hf N e d q t ((k c) • b) =
      c • coordinateFramedTuple M s k hc f hf N e d q t b := by
  have htrans : freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) ((k c) • b) =
      (k c) • freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) b := by
    change freeOpenMap X.ringCatSheaf (eqToHom (coordinateFiniteOpen_tuple M s t 0)) ≫
      ((k c) • b) = _
    exact Linear.comp_smul (C := X.Modules) _ _ _ _ (k c) b
  change coordinateFramedOverlap M s k hc f hf N e d (t 0) (tupleVariables t 0)
    (freeOpenHomCongr N (coordinateFiniteOpen_tuple M s t 0) ((k c) • b)) = _
  rw [htrans]
  exact coordinateFramedOverlap_smul M s k hc f hf N e d _ _ c _

end PiExponentSeshadri.Projective

end

end OAI
end Source0584

-- Source: OAI/NumberTheory/PiExponent/Approximation/InverseFrameRestriction.lean
section Source0585
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InverseFrameRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.InverseFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.TensorPure
variable {X : Scheme.{0}} {M N : X.Modules}

lemma restrictPairing_pure (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι,A)) (n : Γ(N.restrict U.ι,A)) :
    (restrictPairing E U).hom.app A (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A m n) =
      E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n) := by
  change (Scheme.Modules.restrictUnitIso U.ι).hom.app A
    (((Scheme.Modules.restrictFunctor U.ι).map E.hom).app A
      ((moduleTensorRestrict U M N).inv.app A
        (PiExponentSeshadri.TensorPure.pure (M.restrict U.ι) (N.restrict U.ι) A m n))) = _
  refine (congrArg (fun z => (Scheme.Modules.restrictUnitIso U.ι).hom.app A
    (((Scheme.Modules.restrictFunctor U.ι).map E.hom).app A z))
    (restrict_pure_inv U M N A m n)).trans ?_
  change (U.ι.appIso A).hom (E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n)) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

lemma inverseOpenFrame_pairing (E : moduleTensor X M N ≅ O X) (U : X.Opens)
    (e : M.restrict U.ι ≅ O U.toScheme)
    (A : U.toScheme.Opens) (m : Γ(M.restrict U.ι,A)) (n : Γ(N.restrict U.ι,A)) :
    E.hom.app (U.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (U.ι ''ᵁ A) m n) =
      regularValue e.hom A m * regularValue (inverseOpenFrame E U e).hom A n := by
  rw [← restrictPairing_pure]
  exact pairing_apply (restrictPairing E U) e A m n

lemma pairing_restrict (E : moduleTensor X M N ≅ O X) {U V : X.Opens}
    (h : V ≤ U) (m : Γ(M,U)) (n : Γ(N,U)) :
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) =
      E.hom.app V (PiExponentSeshadri.TensorPure.pure M N V (M.presheaf.map (homOfLE h).op m)
        (N.presheaf.map (homOfLE h).op n)) := by
  have hn := CategoryTheory.congr_fun (E.hom.mapPresheaf.naturality (homOfLE h).op)
    (PiExponentSeshadri.TensorPure.pure M N U m n)
  change E.hom.app V ((moduleTensor X M N).presheaf.map (homOfLE h).op
    (PiExponentSeshadri.TensorPure.pure M N U m n)) =
    X.presheaf.map (homOfLE h).op (E.hom.app U (PiExponentSeshadri.TensorPure.pure M N U m n)) at hn
  exact hn.symm.trans (congrArg (fun z => E.hom.app V z)
    (pure_restrict M N (homOfLE h) m n))

private lemma restrictionMap_cycle {C : Type*} [Category C]
    (F : X.Opensᵒᵖ ⥤ C) {U V : X.Opens} (h : V ≤ U) (k : U ≤ V) :
    F.map (homOfLE h).op ≫ F.map (homOfLE k).op = 𝟙 (F.obj (op U)) := by
  rw [← Functor.map_comp]
  rw [show (homOfLE h).op ≫ (homOfLE k).op = 𝟙 (op U) from Subsingleton.elim _ _]
  exact F.map_id _

lemma inverseOpenFrame_restrict_pairing (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme)
    (A : V.toScheme.Opens) (m : Γ(M.restrict V.ι,A)) (n : Γ(N.restrict V.ι,A)) :
    E.hom.app (V.ι ''ᵁ A) (PiExponentSeshadri.TensorPure.pure M N (V.ι ''ᵁ A) m n) =
      regularValue (restrictOpenFrame h e).hom A m *
        regularValue (restrictOpenFrame h (inverseOpenFrame E U e)).hom A n := by
  let B := X.homOfLE h ''ᵁ A
  have h₁ : V.ι ''ᵁ A ≤ U.ι ''ᵁ B := by simp [B, ← Scheme.Hom.comp_image]
  have h₂ : U.ι ''ᵁ B ≤ V.ι ''ᵁ A := by simp [B, ← Scheme.Hom.comp_image]
  let m' := M.presheaf.map (homOfLE h₂).op m
  let n' := N.presheaf.map (homOfLE h₂).op n
  have hp := inverseOpenFrame_pairing E U e B m' n'
  have hs := congrArg (fun x : Γ(U.toScheme,B) => X.presheaf.map (homOfLE h₁).op x) hp
  have hs := hs.trans ((X.presheaf.map (homOfLE h₁).op).hom.map_mul _ _)
  have hr := pairing_restrict E h₁ m' n'
  have hm : M.presheaf.map (homOfLE h₁).op m' = m := by
    change (M.presheaf.map _ ≫ M.presheaf.map _) m = m
    exact CategoryTheory.congr_fun (restrictionMap_cycle M.presheaf h₂ h₁) m
  have hn : N.presheaf.map (homOfLE h₁).op n' = n := by
    change (N.presheaf.map _ ≫ N.presheaf.map _) n = n
    exact CategoryTheory.congr_fun (restrictionMap_cycle N.presheaf h₂ h₁) n
  rw [hm, hn] at hr
  dsimp only [regularValue]
  rw [restrictOpenFrame_app, restrictOpenFrame_app]
  exact hr.symm.trans hs

lemma inverseOpenFrame_restrict (E : moduleTensor X M N ≅ O X)
    {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    restrictOpenFrame h (inverseOpenFrame E U e) =
      inverseOpenFrame E V (restrictOpenFrame h e) := by
  apply Iso.ext
  ext A n
  let eV := restrictOpenFrame h e
  have h1 := inverseOpenFrame_restrict_pairing E h e A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have h2 := inverseOpenFrame_pairing E V eV A (eV.inv.app A (1 : Γ(V.toScheme,A))) n
  have he : regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) = (1 : Γ(V.toScheme,A)) :=
    congrArg (fun g => g.app A (1 : Γ(V.toScheme,A))) eV.inv_hom_id
  change _ = regularValue eV.hom A (eV.inv.app A (1 : Γ(V.toScheme,A))) * _ at h1
  rw [he, one_mul] at h1 h2
  exact h1.symm.trans h2

end
end PiExponent.InverseFrames

end OAI
end Source0585

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeFrames.lean
section Source0586
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.InverseFrames
variable {X : Scheme} {M N : X.Modules}

def negativeCoordinateFrame (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si : O X ⟶ M) :
    N.restrict (SectionOpens.isoOpen si).ι ≅ O (SectionOpens.isoOpen si).toScheme :=
  inverseOpenFrame E _ (coordinatePowerFrame si n)

lemma negativeCoordinateFrame_frameChange (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {W : X.Opens} (hi : W ≤ SectionOpens.isoOpen si) (hj : W ≤ SectionOpens.isoOpen sj) :
    W.topIso.hom
      (frameChange (restrictOpenFrame hi (negativeCoordinateFrame n E si))
        (restrictOpenFrame hj (negativeCoordinateFrame n E sj)) : Γ(W.toScheme,⊤)) =
      coordinateRatioOn si sj hi ^ n := by
  have h := (congrArg₂
    (fun e f : N.restrict W.ι ≅ O W.toScheme => frameChange e f)
    (inverseOpenFrame_restrict E hi (coordinatePowerFrame si n))
    (inverseOpenFrame_restrict E hj (coordinatePowerFrame sj n))).trans
      (inverseOpenFrame_frameChange E W _ _)
  have hv := congrArg
    (fun z : Γ(W.toScheme,⊤)ˣ => W.topIso.hom (z : Γ(W.toScheme,⊤))) h
  refine hv.trans ?_
  erw [coordinatePowerFrame_frameChange, map_pow, topIso_hom_restrict]
  rfl

lemma negativeCoordinateFrame_hom_change_restrict (n : ℕ)
    (E : moduleTensor X (modulePow X M n) N ≅ O X) (si sj : O X ⟶ M)
    {U W : X.Opens} (hi : U ≤ SectionOpens.isoOpen si)
    (hj : W ≤ SectionOpens.isoOpen sj) (h : W ≤ U)
    (b : freeOpen X.ringCatSheaf U ⟶ N) :
    framedHomCoefficientsEquiv W N (restrictOpenFrame hj (negativeCoordinateFrame n E sj))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ b) =
      coordinateRatioOn si sj (h.trans hi) ^ n * X.presheaf.map (homOfLE h).op
        (framedHomCoefficientsEquiv U N (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b) := by
  erw [framedHomCoefficientsEquiv_change W N
    (restrictOpenFrame (h.trans hi) (negativeCoordinateFrame n E si)),
    negativeCoordinateFrame_frameChange]
  congr 1
  have hr := framedHomCoefficientsEquiv_restrict N h
    (restrictOpenFrame hi (negativeCoordinateFrame n E si)) b
  rw [restrictOpenFrame_trans] at hr
  exact hr

end
end PiExponentSeshadri.Projective

end OAI
end Source0586

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeTransitions.lean
section Source0587
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeTransitions.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveLaurentTransitions
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)

lemma coordinateFiniteRingEquiv_cross_ratio_full (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) (l : σ) :
    overlapToFull j b (coordinateFiniteRingEquiv M s k hc f hf j b
      (coordinateRatioOn (s i) (s l) hi)) =
      AddMonoidAlgebra.single (standardExponent l 1 - standardExponent i 1) 1 := by
  let r := coordinateFiniteRingEquiv M s k hc f hf j b
  let hj : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s j) := inf_le_left
  have hinv : r (coordinateRatioOn (s j) (s i) hj) *
      r (coordinateRatioOn (s i) (s j) hi) = 1 := by
    rw [← map_mul, coordinateRatioOn_reciprocal, map_one]
  calc
    _ = overlapToFull j b
        (r (coordinateRatioOn (s j) (s l) hj) * r (coordinateRatioOn (s i) (s j) hi)) := by
      rw [coordinateRatioOn_change (s j) (s i) (s l) hj hi, map_mul, mul_comm]
    _ = _ := overlapToFull_ratio i j l b _ _ _
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b l)
      (coordinateFiniteRingEquiv_ratio_full M s k hc f hf j b i) hinv

lemma coordinateNegativeFrameFactor_full (n : ℕ) (i j : σ)
    (b : Finset (ChartVariables j))
    (hi : coordinateFiniteOpen M s j b ≤ SectionOpens.isoOpen (s i)) :
    overlapToFull j b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) hi)) ^ n) =
      AddMonoidAlgebra.single
        (standardExponent i (-(n : ℤ)) - standardExponent j (-(n : ℤ))) 1 := by
  classical
  rw [map_pow, coordinateFiniteRingEquiv_cross_ratio_full,
    AddMonoidAlgebra.single_pow, one_pow]
  congr 1
  funext a
  simp only [Pi.smul_apply, Pi.sub_apply, standardExponent]
  split_ifs <;> simp

lemma coordinateNegativeLaurent_change (n : ℕ) (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : Localization.Away (chartProduct (R := K) i a)) :
    overlapLaurent j (-(n : ℤ)) b
      ((coordinateFiniteRingEquiv M s k hc f hf j b
        (coordinateRatioOn (s i) (s j) (h.trans inf_le_left))) ^ n *
        coordinateFiniteTransition M s k hc f hf i j a b h z) =
      overlapLaurent i (-(n : ℤ)) a z :=
  overlapLaurent_change_pivot i j (-(n : ℤ)) a b
    (coordinateFiniteTransition M s k hc f hf i j a b h)
    (coordinateFiniteTransition_full M s k hc f hf i j a b h) _
    (coordinateNegativeFrameFactor_full M s k hc f hf n i j b (h.trans inf_le_left)) z

end
end PiExponentSeshadri.Projective

end OAI
end Source0587

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeCoordinates.lean
section Source0588
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque ProjectiveChartSections
open PiExponent.ProjectiveMonomialCech
open PiExponent.GeometrySupport.ProjectiveLaurentVertex
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)

lemma negativeCoordinateOverlap_restrict (i j : σ)
    (a : Finset (ChartVariables i)) (b : Finset (ChartVariables j))
    (h : coordinateFiniteOpen M s j b ≤ coordinateFiniteOpen M s i a)
    (z : freeOpen X.ringCatSheaf (coordinateFiniteOpen M s i a) ⟶ N) :
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) j b (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
    coordinateFramedOverlap M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
      (-(n : ℤ)) i a z := by
  let ci := framedHomCoefficientsEquiv (coordinateFiniteOpen M s i a) N
    (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s i))) z
  let ri := coordinateFiniteRingEquiv M s k hc f hf i a
  let rj := coordinateFiniteRingEquiv M s k hc f hf j b
  let u := coordinateRatioOn (s i) (s j) (h.trans inf_le_left)
  have ht : coordinateFiniteTransition M s k hc f hf i j a b h (ri ci) =
      rj (X.presheaf.map (homOfLE h).op ci) := by
    simp only [coordinateFiniteTransition, RingHom.comp_apply,
      RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, ri, RingEquiv.symm_apply_apply, rj]
  dsimp only [coordinateFramedOverlap, framedLaurentOverlap, framedHomRingEquiv]
  dsimp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.trans_apply, RingEquiv.coe_toAddEquiv]
  change overlapLaurent j (-(n : ℤ)) b
    (rj (framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z))) =
    overlapLaurent i (-(n : ℤ)) a (ri ci)
  have hcoef : framedHomCoefficientsEquiv (coordinateFiniteOpen M s j b) N
      (restrictOpenFrame inf_le_left (negativeCoordinateFrame n E (s j)))
      (freeOpenMap X.ringCatSheaf (homOfLE h) ≫ z) =
      u ^ n * X.presheaf.map (homOfLE h).op ci :=
    negativeCoordinateFrame_hom_change_restrict n E (s i) (s j)
      (U := coordinateFiniteOpen M s i a) (W := coordinateFiniteOpen M s j b)
      inf_le_left inf_le_left h z
  rw [hcoef, map_mul, map_pow]
  change overlapLaurent j (-(n : ℤ)) b
    ((rj u) ^ n * rj (X.presheaf.map (homOfLE h).op ci)) = _
  rw [← ht]
  exact coordinateNegativeLaurent_change M s k hc f hf n i j a b h (ri ci)

def negativeCoordinateLaurentPresentation :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i)) N (-(n : ℤ)) :=
  coordinateFramedLaurentPresentation M s k hc f hf N
    (fun i => negativeCoordinateFrame n E (s i)) (-(n : ℤ))
    (negativeCoordinateOverlap_restrict M s k hc f hf n N E)

def coordinateInversePowerLaurentPresentation :
    PiExponent.ProjectiveTwistCech.LaurentCechPresentation (K := K)
      (fun i => SectionOpens.isoOpen (s i))
      (((coordinateLineBundle M s hc).pow n).inverse.sheaf) (-(n : ℤ)) :=
  negativeCoordinateLaurentPresentation M s k hc f hf n _
    (lineTensorInverseIso ((coordinateLineBundle M s hc).pow n))

end
end PiExponentSeshadri.Projective

end OAI
end Source0588

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeScalars.lean
section Source0589
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveNegativeScalars.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open PiExponentSeshadri.Frames PiExponentSeshadri.Geometry ModuleFlasque
open PiExponent.GeometrySupport.ProjectiveCoordinateAcyclicity
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] coordinateFramedTuple negativeCoordinateFrame
abbrev negativeScalarFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

variable {X : Scheme} {K σ : Type} [CommRing K] [Fintype σ]
variable (M : X.Modules) (s : σ → (O X ⟶ M)) (k : K →+* Γ(X,⊤))
variable (hc : (⨆i,SectionOpens.isoOpen (s i))=⊤)
variable (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc=f.hom)
variable (n : ℕ) (N : X.Modules) (E : moduleTensor X (modulePow X M n) N ≅ O X)
local instance instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTopHomSheafOfModulesRingCatSheafFreeOpen_1
    (U : X.Opens) (P : X.Modules) :
    Module Γ(X,⊤) (negativeScalarFreeOpen X U ⟶ P) := sheafHomModule X _ P

lemma negativeCoordinateLaurentPresentation_smul (q : ℕ) (t : Fin (q + 1) → σ)
    (c : K) (b : negativeScalarFreeOpen X
      (PiExponent.GeometrySupport.CechHigher.intersection (fun i => SectionOpens.isoOpen (s i)) t) ⟶ N) :
    (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t ((k c) • b) =
      c • (negativeCoordinateLaurentPresentation M s k hc f hf n N E).coefficient q t b :=
  coordinateFramedTuple_smul M s k hc f hf N (fun i => negativeCoordinateFrame n E (s i))
    (-(n : ℤ)) q t c b

end
end PiExponentSeshadri.Projective

end OAI
end Source0589

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedImmersionSerreTransfer.lean
section Source0590
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedImmersionSerreTransfer.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite
open PiExponentSeshadri.FlasqueCohomology

namespace PiExponent.ClosedImmersionSerreTransfer

universe u
abbrev schemeUnit (Z : Scheme.{u}) : Z.Modules :=
  SheafOfModules.unit Z.ringCatSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def structureMap : schemeUnit Y ⟶
    (Scheme.Modules.pushforward f).obj (schemeUnit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

lemma globalHom_push (M : X.Modules) (g : schemeUnit X ⟶ M) :
    globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M)
      (structureMap f ≫ (Scheme.Modules.pushforward f).map g) =
    globalHomEquiv X.ringCatSheaf M g := by
  change (g.val.app (op ⊤)) ((f.app ⊤) 1) = (g.val.app (op ⊤)) (1 : Γ(X,⊤))
  rw [map_one]
  rfl

lemma globalHom_push_bijective (M : X.Modules) :
    Function.Bijective (fun g : schemeUnit X ⟶ M =>
      structureMap f ≫ (Scheme.Modules.pushforward f).map g) := by
  constructor
  · intro a b h
    apply (globalHomEquiv X.ringCatSheaf M).injective
    exact (globalHom_push f M a).symm.trans
      ((congrArg (globalHomEquiv Y.ringCatSheaf _) h).trans (globalHom_push f M b))
  · intro b
    obtain ⟨a, ha⟩ := (globalHomEquiv X.ringCatSheaf M).surjective
      (globalHomEquiv Y.ringCatSheaf ((Scheme.Modules.pushforward f).obj M) b)
    refine ⟨a, ?_⟩
    apply (globalHomEquiv Y.ringCatSheaf _).injective
    exact (globalHom_push f M a).trans ha

instance pushforward_flasque (M : X.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf Y.ringCatSheaf).obj ((Scheme.Modules.pushforward f).obj M)) :=
  TopCat.Sheaf.IsFlasque.pushforward_isFlasque
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) f.base

local instance : HasExt.{u+1} X.Modules := HasExt.standard _
local instance : HasExt.{u+1} Y.Modules := HasExt.standard _

variable [PreservesFiniteColimits (Scheme.Modules.pushforward f)]

def cohomologyMap (M : X.Modules) (n : ℕ) :
    Ext.{u+1} (C := X.Modules) (schemeUnit X) M n →+
      Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom
    (Scheme.Modules.pushforward f) (structureMap f) M n

theorem cohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (cohomologyMap f M n) := by
  let : EnoughInjectives X.Modules :=
    PiExponentSeshadri.ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply PiExponentSeshadri.ExtSectionComparison.mapFrom_bijective
  · exact globalHom_push_bijective f
  · intro I hI q x
    let : Injective (C := SheafOfModules X.ringCatSheaf) I := hI
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      PiExponentSeshadri.ModuleFlasque.injective_isFlasque X.ringCatSheaf I
    exact flasque_ext_zero Y.ringCatSheaf q ((Scheme.Modules.pushforward f).obj I) x

def cohomologyEquiv (M : X.Modules) (n : ℕ) :
    Ext.{u+1} (C := X.Modules) (schemeUnit X) M n ≃+
      Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  AddEquiv.ofBijective (cohomologyMap f M n) (cohomologyMap_bijective f M n)

theorem ext_zero_iff (M : X.Modules) (n : ℕ) :
    (∀ x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M n, x = 0) ↔
      (∀ x : Ext.{u+1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n, x = 0) := by
  constructor
  · intro h x
    obtain ⟨y, rfl⟩ := (cohomologyEquiv f M n).surjective x
    rw [h y, map_zero]
  · intro h x
    apply (cohomologyEquiv f M n).injective
    rw [map_zero]
    exact h _

def closedCohomologyEquiv {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsClosedImmersion f] (M : X.Modules) (n : ℕ) :
    Ext.{1} (C := X.Modules) (schemeUnit X) M n ≃+
      Ext.{1} (C := Y.Modules) (schemeUnit Y)
        ((Scheme.Modules.pushforward f).obj M) n :=
  cohomologyEquiv f M n

end PiExponent.ClosedImmersionSerreTransfer

end

end OAI
end Source0590

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardLinear.lean
section Source0591
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardLinear.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ClosedImmersionSerreTransfer

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open TopologicalSpace Opposite PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}} (f : X ⟶ Y)
local instance closedPushforwardLinearSourceHasExt : HasExt.{1} X.Modules := schemeHasExt
local instance closedPushforwardLinearTargetHasExt : HasExt.{1} Y.Modules := schemeHasExt

lemma baseScalars_comp_actual (p : Y ⟶ Spec (CommRingCat.of ℂ)) :
    baseScalars (f ≫ p) = f.appTop.hom.comp (baseScalars p) := by
  ext c
  simp only [baseScalars, Scheme.Hom.comp_appTop, CommRingCat.hom_comp,
    RingHom.comp_apply]

lemma scalar_naturality (p : Y ⟶ Spec (CommRingCat.of ℂ)) (U : Y.Opens) (r : ℂ) :
    restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) =
      f.app U (restrictScalar Y U (baseScalars p r)) := by
  rw [baseScalars_comp_actual]
  change X.presheaf.map (homOfLE le_top).op (f.appTop (baseScalars p r)) = _
  exact (CategoryTheory.congr_fun (f.naturality (homOfLE le_top).op) (baseScalars p r)).symm

variable [IsClosedImmersion f]

lemma cohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    cohomologyMap f N k (x.comp y h) =
      (cohomologyMap f M n x).comp (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  PiExponentSeshadri.ExtSectionComparison.mapFrom_comp
    (Scheme.Modules.pushforward f) (structureMap f) x y h

def typedCohomologyMap (M : X.Modules) (n : ℕ) :
    cohomology M n →+ cohomology ((Scheme.Modules.pushforward f).obj M) n :=
  cohomologyMap f M n

lemma typedCohomologyMap_comp {M N : X.Modules} {n m k : ℕ}
    (x : cohomology M n) (y : Ext.{1} M N m) (h : n + m = k) :
    typedCohomologyMap f N k (x.comp y h) =
      (typedCohomologyMap f M n x).comp
        (y.mapExactFunctor (Scheme.Modules.pushforward f)) h :=
  cohomologyMap_comp f x y h

lemma typedCohomologyMap_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective (typedCohomologyMap f M n) :=
  cohomologyMap_bijective f M n

def cohomologyLinearMap (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact { toFun := typedCohomologyMap f M n
          map_add' := (typedCohomologyMap f M n).map_add
          map_smul' := by
            intro r x
            change typedCohomologyMap f M n ((baseScalars (f ≫ p) r) • x) =
              (baseScalars p r) • (typedCohomologyMap f M n x)
            rw [Ext.smul_eq_comp_mk₀, typedCohomologyMap_comp, Ext.smul_eq_comp_mk₀,
              Ext.mapExactFunctor_mk₀]
            congr 2
            ext U m
            change Γ(M, f ⁻¹ᵁ U) at m
            change restrictScalar X (f ⁻¹ᵁ U) (baseScalars (f ≫ p) r) • m =
              f.app U (restrictScalar Y U (baseScalars p r)) • m
            rw [scalar_naturality] }

lemma cohomologyLinearMap_eq (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    ⇑(cohomologyLinearMap f p M n) = typedCohomologyMap f M n := rfl

def cohomologyLinearEquiv (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
    cohomology M n ≃ₗ[ℂ] cohomology ((Scheme.Modules.pushforward f).obj M) n := by
  exact LinearEquiv.ofBijective (cohomologyLinearMap f p M n)
    (by rw [cohomologyLinearMap_eq]; exact typedCohomologyMap_bijective f M n)

theorem finiteDimensional_of_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ)
    (hfinite : letI := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
      FiniteDimensional ℂ (cohomology ((Scheme.Modules.pushforward f).obj M) n)) :
    letI := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M n) := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  have := hfinite
  exact FiniteDimensional.of_injective (cohomologyLinearEquiv f p M n).toLinearMap
    (cohomologyLinearEquiv f p M n).injective

lemma cohomologyDimension_pushforward
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (n : ℕ) :
    cohomologyDimension p ((Scheme.Modules.pushforward f).obj M) n =
      cohomologyDimension (f ≫ p) M n := by
  let := Module.compHom (cohomology M n) (baseScalars (f ≫ p))
  let := Module.compHom (cohomology ((Scheme.Modules.pushforward f).obj M) n) (baseScalars p)
  exact (cohomologyLinearEquiv f p M n).finrank_eq.symm

theorem euler_pushforward (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) :
    eulerCharacteristic p d ((Scheme.Modules.pushforward f).obj M) =
      eulerCharacteristic (f ≫ p) d M := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [cohomologyDimension_pushforward]

end
end PiExponent.ClosedImmersionSerreTransfer

end OAI
end Source0591

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoherentExtFiniteness.lean
section Source0592
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoherentExtFiniteness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CoherentExtFiniteness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry

theorem finite_middle_of_exact {K U V W : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Module.Finite K U] [Module.Finite K W]
    (f : U →ₗ[K] V) (g : V →ₗ[K] W) (h : Function.Exact f g) :
    Module.Finite K V := by
  have he : Function.Exact f g.rangeRestrict := by
    intro x
    rw [Subtype.ext_iff]
    exact h x
  exact Module.Finite.of_exact he g.surjective_rangeRestrict

universe w v u t k
variable {K : Type k} [Field K] {C : Type u} [Category.{v} C] [Abelian C]
    [Linear K C] [HasExt.{w} C]

def extLinearEquivBiproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ) :
    Ext.{w} A c.pt q ≃ₗ[K] ∀ j, Ext.{w} A (B j) q :=
  { Ext.addEquivBiproduct A hc q with
    map_smul' := by
      intro a x
      funext j
      exact Ext.smul_comp x (Ext.mk₀ (c.π j)) (add_zero q) a }

theorem ext_finite_of_biproduct (A : C) {J : Type*} [Fintype J]
    {B : J → C} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, Module.Finite K (Ext.{w} A (B j) q)) :
    Module.Finite K (Ext.{w} A c.pt q) := by
  let (j : J) : Module.Finite K (Ext.{w} A (B j) q) := hfinite j
  exact Module.Finite.of_surjective (extLinearEquivBiproduct (K := K) A hc q).symm.toLinearMap
    (extLinearEquivBiproduct (K := K) A hc q).symm.surjective

structure FiniteCohomologyPresentation {ι : Type t} (A : C) (F : ι → C) (i : ι) where
  kernel : ι
  middle : C
  left : F kernel ⟶ middle
  right : middle ⟶ F i
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  finite : ∀ q, Module.Finite K (Ext.{w} A middle q)

theorem ext_finite_of_presentations {ι : Type t} (A : C) (F : ι → C) (l : ℕ)
    (hbound : ∀ i q, l ≤ q → ∀ x : Ext.{w} A (F i) q, x = 0)
    (presentation : ∀ i, FiniteCohomologyPresentation (K := K) A F i)
    (i : ι) (q : ℕ) : Module.Finite K (Ext.{w} A (F i) q) := by
  have hdown : ∀ k q, l ≤ q + k → ∀ i, Module.Finite K (Ext.{w} A (F i) q) := by
    intro k
    induction k with
    | zero =>
      intro q hq i
      let : Subsingleton (Ext.{w} A (F i) q) :=
        ⟨fun x y => (hbound i q (by omega) x).trans (hbound i q (by omega) y).symm⟩
      infer_instance
    | succ k ih =>
      intro q hq i
      let P := presentation i
      let S := ShortComplex.mk P.left P.right P.comp_zero
      let : Module.Finite K (Ext.{w} A S.X₂ q) := P.finite q
      let : Module.Finite K (Ext.{w} A S.X₁ (q+1)) := ih (q+1) (by omega) P.kernel
      exact finite_middle_of_exact
        (PiExponentSeshadri.Cohomology.cohomologyMap₂ (K := K) A (S := S) q)
        (PiExponentSeshadri.Cohomology.cohomologyBoundary (K := K) A P.shortExact q)
        (PiExponentSeshadri.Cohomology.cohomology_exact₃ (K := K) A P.shortExact q)
  exact hdown l q (Nat.le_add_left _ _) i

variable {X : Scheme.{0}}

theorem cohomology_finite_of_biproduct
    (p : X ⟶ Spec (CommRingCat.of ℂ)) {J : Type*} [Fintype J]
    {B : J → X.Modules} {c : Bicone B} (hc : c.IsBilimit) (q : ℕ)
    (hfinite : ∀ j, letI := Module.compHom (cohomology (B j) q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (B j) q)) :
    letI := Module.compHom (cohomology c.pt q) (baseScalars p)
    FiniteDimensional ℂ (cohomology c.pt q) := by
  let := sheafComplexLinear p
  have hfin : ∀ j, Module.Finite ℂ (Ext.{1} (structureSheaf X) (B j) q) := by
    intro j
    change @Module.Finite ℂ (cohomology (B j) q) _ _ (complexExtModule p (B j) q)
    rw [complexExtModule_eq]
    exact hfinite j
  have hf := ext_finite_of_biproduct (K := ℂ) (structureSheaf X) hc q hfin
  change @Module.Finite ℂ (cohomology c.pt q) _ _ (complexExtModule p c.pt q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

structure CoherentFinitePresentation (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) where
  kernel : X.Modules
  kernel_coherent : kernel.IsFinitePresentation
  middle : X.Modules
  left : kernel ⟶ middle
  right : middle ⟶ M
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  middle_finite : ∀ q, letI := Module.compHom (cohomology middle q) (baseScalars p)
    FiniteDimensional ℂ (cohomology middle q)

theorem coherent_cohomology_finite_of_presentations
    [IsNoetherian X] [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (l : ℕ) (hl : 0 < l) (U : Fin l → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (presentation : ∀ (M : X.Modules) [M.IsFinitePresentation],
      Nonempty (CoherentFinitePresentation p M))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  let := sheafComplexLinear p
  let F : {N : X.Modules // N.IsFinitePresentation} → X.Modules := Subtype.val
  let P (i : {N : X.Modules // N.IsFinitePresentation}) :
      FiniteCohomologyPresentation (K := ℂ) (structureSheaf X) F i := by
    letI : i.val.IsFinitePresentation := i.property
    let S := Classical.choice (presentation i.val)
    exact
      { kernel := ⟨S.kernel, S.kernel_coherent⟩
        middle := S.middle
        left := S.left
        right := S.right
        comp_zero := S.comp_zero
        shortExact := S.shortExact
        finite := fun n => by
          change @Module.Finite ℂ (cohomology S.middle n) _ _ (complexExtModule p S.middle n)
          rw [complexExtModule_eq]
          exact S.middle_finite n }
  have hbound : ∀ i n, l ≤ n → ∀ x : Ext.{1} (structureSheaf X) (F i) n, x = 0 := by
    intro i n hn x
    let : i.val.IsFinitePresentation := i.property
    let : i.val.IsQuasicoherent :=
      (SheafOfModules.IsFinitePresentation.exists_quasicoherentData i.val).choose.isQuasicoherent
    exact PiExponent.SerreVanishing.ext_eq_zero_of_affine_cover l hl U hU hcover i.val n hn x
  have hf := ext_finite_of_presentations (K := ℂ) (structureSheaf X) F l hbound P
    ⟨M, inferInstance⟩ q
  change @Module.Finite ℂ (cohomology M q) _ _ (complexExtModule p M q) at hf
  rw [complexExtModule_eq] at hf
  exact hf

end
end PiExponent.CoherentExtFiniteness

end OAI
end Source0592

-- Source: OAI/NumberTheory/PiExponent/Approximation/NegativeTwistPresentations.lean
section Source0593
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/NegativeTwistPresentations.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.NegativeTwistPresentations
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
open PiExponent.GeometrySupport.TwistPresentations
variable {X : Scheme.{0}}

def cancelIso (M : X.Modules) (L N : LineBundle X)
    (e : moduleTensor X L.sheaf N.sheaf ≅ structureSheaf X) :
    moduleTensor X (moduleTensor X M L.sheaf) N.sheaf ≅ M :=
  moduleLineTensorAssoc M L N ≪≫ moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

variable (L N : LineBundle X) {M : X.Modules} {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections)
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)

def presentationMap : moduleTensor X (SheafOfModules.free s.I) N.sheaf ⟶ M :=
  moduleTensorMap (s.π ≫ (moduleTwistPowerIso L M n).hom) (𝟙 N.sheaf) ≫
    (cancelIso M (L.pow n) N e).hom

instance presentationMap_epi : Epi (presentationMap L N s e) := by
  let g : (SheafOfModules.free s.I : X.Modules) ⟶ moduleTensor X M (L.pow n).sheaf :=
    s.π ≫ (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) s.π := s.epi
  let hg : Epi (C := X.Modules) g := epi_comp (C := X.Modules) s.π (moduleTwistPowerIso L M n).hom
  let : Epi (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf)) :=
    @moduleTensorMap_epi X _ _ g hg N
  exact epi_comp (C := X.Modules) (moduleTensorMap g (𝟙 N.sheaf))
    (cancelIso M (L.pow n) N e).hom

def middleIsoBiproduct [Fintype s.I] [HasFiniteBiproducts X.Modules] :
    moduleTensor X (SheafOfModules.free s.I) N.sheaf ≅ ⨁ (fun _ : s.I => N.sheaf) :=
  twistFreeIsoBiproduct N 1 s.I ≪≫
    biproduct.mapIso (fun _ : s.I => moduleTensorRightUnit N.sheaf)

theorem middle_isFinitePresentation [hs : s.IsFiniteType] :
    (moduleTensor X (SheafOfModules.free s.I) N.sheaf).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := PiExponent.FiniteGlobalPresentation.free_isFinitePresentation X s.I
  exact PiExponent.FiniteGlobalPresentation.moduleTwist_isFinitePresentation N 1
    (SheafOfModules.free s.I)

theorem kernel_isFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    [s.IsFiniteType] : (kernel (presentationMap L N s e)).IsFinitePresentation := by
  have := middle_isFinitePresentation L N s
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  exact PiExponent.FiniteGlobalPresentation.kernel_isFinitePresentation (presentationMap L N s e)

theorem presentation_shortExact :
    (ShortComplex.mk (kernel.ι (presentationMap L N s e)) (presentationMap L N s e)
      (kernel.condition (presentationMap L N s e))).ShortExact :=
  { exact := ShortComplex.exact_kernel (presentationMap L N s e) }

theorem middle_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ)) [hs : s.IsFiniteType]
    (q : ℕ)
    (hN : letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    letI := Module.compHom
      (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
    FiniteDimensional ℂ (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let : HasFiniteBiproducts X.Modules := Abelian.hasFiniteBiproducts
  let B := ⨁ (fun _ : s.I => N.sheaf)
  let := Module.compHom (cohomology B q) (baseScalars p)
  let := Module.compHom
    (cohomology (moduleTensor X (SheafOfModules.free s.I) N.sheaf) q) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology B q) :=
    CoherentExtFiniteness.cohomology_finite_of_biproduct p
      (biproduct.isBilimit (fun _ : s.I => N.sheaf)) q (fun _ => hN)
  exact Module.Finite.of_surjective (cohomologyIso p (middleIsoBiproduct L N s) q).symm.toLinearMap
    (cohomologyIso p (middleIsoBiproduct L N s) q).symm.surjective

def coherentFinitePresentation [IsLocallyNoetherian X] [M.IsFinitePresentation]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [s.IsFiniteType]
    (hN : ∀ q, letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    CoherentExtFiniteness.CoherentFinitePresentation p M where
  kernel := kernel (presentationMap L N s e)
  kernel_coherent := kernel_isFinitePresentation L N s e
  middle := moduleTensor X (SheafOfModules.free s.I) N.sheaf
  left := kernel.ι (presentationMap L N s e)
  right := presentationMap L N s e
  comp_zero := kernel.condition (presentationMap L N s e)
  shortExact := presentation_shortExact L N s e
  middle_finite := fun q => middle_cohomology_finite L N s p q (hN q)

end
end PiExponent.NegativeTwistPresentations

end OAI
end Source0593

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PositiveCoherentExtFiniteness.lean
section Source0594
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PositiveCoherentExtFiniteness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

namespace CoherentExtFiniteness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

structure PositiveCoherentFinitePresentation
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) where
  kernel : X.Modules
  kernel_coherent : kernel.IsFinitePresentation
  middle : X.Modules
  left : kernel ⟶ middle
  right : middle ⟶ M
  comp_zero : left ≫ right = 0
  shortExact : (ShortComplex.mk left right comp_zero).ShortExact
  middle_finite : ∀ q, 0 < q → letI := Module.compHom (cohomology middle q) (baseScalars p)
    FiniteDimensional ℂ (cohomology middle q)

end CoherentExtFiniteness

namespace NegativeTwistPresentations
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def positiveCoherentFinitePresentation [IsLocallyNoetherian X]
    (L N : LineBundle X) {M : X.Modules} [M.IsFinitePresentation] {n : ℕ}
    (s : ((moduleTwistFunctor L n).obj M).GeneratingSections) [s.IsFiniteType]
    (e : moduleTensor X (L.pow n).sheaf N.sheaf ≅ structureSheaf X)
    (p : X ⟶ Spec (CommRingCat.of ℂ))
    (hN : ∀ q, 0 < q → letI := Module.compHom (cohomology N.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology N.sheaf q)) :
    CoherentExtFiniteness.PositiveCoherentFinitePresentation p M where
  kernel := kernel (presentationMap L N s e)
  kernel_coherent := kernel_isFinitePresentation L N s e
  middle := moduleTensor X (SheafOfModules.free s.I) N.sheaf
  left := kernel.ι (presentationMap L N s e)
  right := presentationMap L N s e
  comp_zero := kernel.condition (presentationMap L N s e)
  shortExact := presentation_shortExact L N s e
  middle_finite := fun q hq => middle_cohomology_finite L N s p q (hN q hq)

end NegativeTwistPresentations

end PiExponent

end

end OAI
end Source0594

-- Source: OAI/NumberTheory/PiExponent/Geometry/CoherentProjectiveFinite.lean
section Source0595
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CoherentProjectiveFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  apply CoherentExtFiniteness.coherent_cohomology_finite_of_presentations p
    l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover _ M q
  intro A hA
  obtain ⟨n, hn⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A s hcover haffine
  obtain ⟨g, hg⟩ := hn n le_rfl
  let : g.IsFiniteType := hg
  exact ⟨NegativeTwistPresentations.coherentFinitePresentation L (N n) g (hpair n) p
    (hfinite n)⟩

end
end PiExponent.CoherentProjectiveFinite

end OAI
end Source0595

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoherentInverseFinite.lean
section Source0596
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoherentInverseFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q,
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) :=
  coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q

end
end PiExponent.CoherentProjectiveFinite

end OAI
end Source0596

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFinite.lean
section Source0597
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveCoordinateFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.ProjectiveCoordinateFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveTupleCharts
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] negativeCoordinateLaurentPresentation
  coordinateFramedTuple negativeCoordinateFrame LineBundle.inverse lineTensorInverseIso
variable {X Y : Scheme.{0}} {K σ : Type} [Field K] [Fintype σ]

theorem inversePower_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (L : LineBundle X) (s : σ → (structureSheaf X ⟶ L.sheaf)) (k : K →+* Γ(X,⊤))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade K σ)) (hf : sectionsMorphism k s hc = f.hom)
    (n q : ℕ) :
    letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) k
    Module.Finite K (cohomology (L.pow n).inverse.sheaf q) := by
  let := LineBundleCoherent.lineBundle_isFinitePresentation (L.pow n).inverse
  let : (L.pow n).inverse.sheaf.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData
      (L.pow n).inverse.sheaf).choose.isQuasicoherent
  exact ActualLaurentExtFinite.cohomology_finite k
    (negativeCoordinateLaurentPresentation L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    (negativeCoordinateLaurentPresentation_smul L.sheaf s k hc f hf n _
      (lineTensorInverseIso (L.pow n)))
    hc.ge
    (fun r t => IsAffineOpen.iInf
      (fun i => coordinateOpen_isAffine L.sheaf s k hc f hf (t i))) q

theorem coordinateBundle_cohomology_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L l hl s hc (coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf)
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end
end PiExponent.GeometrySupport.ProjectiveCoordinateFinite

end OAI
end Source0597

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CohomologyFinite.lean
section Source0598
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CohomologyFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CohomologyFiniteness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra
variable {X Y : Scheme.{0}}

def CohomologyFinite (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ) : Prop :=
  letI := Module.compHom (cohomology M q) (baseScalars p)
  FiniteDimensional ℂ (cohomology M q)

theorem finiteDimensional (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p M q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := h

theorem coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ (Fin l)))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q :=
  coordinateBundle_cohomology_finite p L l hl s hc f hf M q

theorem closedPushforward_finite (i : X ⟶ Y) [IsClosedImmersion i]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (q : ℕ)
    (h : CohomologyFinite p ((Scheme.Modules.pushforward i).obj M) q) :
    CohomologyFinite (i ≫ p) M q :=
  ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward i p M q h

end
end PiExponent.CohomologyFiniteness

end OAI
end Source0598

-- Source: OAI/NumberTheory/PiExponent/Geometry/ProjectiveFiniteCoordinates.lean
section Source0599
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/ProjectiveFiniteCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

namespace CohomologyFiniteness
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open GeometrySupport.ProjectiveCoordinateFinite
attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {σ : Type} [Fintype σ] [Nonempty σ]

theorem finiteIndex_coordinateBundle_finite [IsNoetherian X]
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : σ → (structureSheaf X ⟶ L.sheaf))
    (hc : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (f : X ≅ Proj (PolyGrade ℂ σ))
    (hf : sectionsMorphism (baseScalars p) s hc = f.hom)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) : CohomologyFinite p M q := by
  let e := Fintype.equivFin σ
  let t : Fin (Fintype.card σ) → (structureSheaf X ⟶ L.sheaf) := fun i => s (e.symm i)
  have ht : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (t i)) = ⊤ :=
    (Equiv.iSup_comp (g := fun j => PiExponentSeshadri.SectionOpens.isoOpen (s j)) e.symm).trans hc
  exact CoherentProjectiveFinite.coherent_cohomology_finite_of_inverse_powers
    p L (Fintype.card σ) Fintype.card_pos t ht
    (fun i => GeometrySupport.ProjectiveTupleCharts.coordinateOpen_isAffine L.sheaf s (baseScalars p) hc f hf (e.symm i))
    (inversePower_cohomology_finite L s (baseScalars p) hc f hf) M q

end CohomologyFiniteness

namespace ProjectiveFiniteCoordinates
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Projective
open ProjectiveO1 CohomologyFiniteness
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local irreducible] ProjectiveO1.lineBundle ProjectiveO1.coordinateCocycle
  ProjectiveO1.coordinateSection sectionsMorphism CoordinateAtlas.morphism atlasOfFramedSections
  CohomologyFinite
variable {X : Scheme.{0}} {σ : Type} [Finite σ] [Nonempty σ]

theorem projectiveSpace_cohomology_finite
    (M : (projectiveSpace ℂ σ).Modules) [M.IsFinitePresentation] (q : ℕ) :
    CohomologyFinite (polynomialProjectiveProjection ℂ σ) M q := by
  let : Fintype σ := Fintype.ofFinite σ
  have hid : sectionsMorphism
      (X := projectiveSpace ℂ σ) (K := ℂ) (σ := σ)
      (M := (lineBundle (R := ℂ) (σ := σ)).sheaf)
      (baseScalars (polynomialProjectiveProjection ℂ σ))
      (coordinateSection (R := ℂ) (σ := σ))
      (coordinateSection_cover (R := ℂ) (σ := σ)) =
      (Iso.refl (projectiveSpace ℂ σ)).hom :=
    coordinate_sectionsMorphism_identity (R := ℂ) (σ := σ)
  exact finiteIndex_coordinateBundle_finite (X := projectiveSpace ℂ σ)
    (polynomialProjectiveProjection ℂ σ)
    (lineBundle (R := ℂ) (σ := σ)) (coordinateSection (R := ℂ) (σ := σ))
    (coordinateSection_cover (R := ℂ) (σ := σ))
    (Iso.refl (projectiveSpace ℂ σ)) hid M q

theorem projectiveEmbedding_cohomology_finite
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q)
      (baseScalars (i ≫ polynomialProjectiveProjection ℂ σ))
    FiniteDimensional ℂ (cohomology M q) := by
  exact finiteDimensional (i ≫ polynomialProjectiveProjection ℂ σ) M q
    (closedPushforward_finite i (polynomialProjectiveProjection ℂ σ) M q
      (projectiveSpace_cohomology_finite ((Scheme.Modules.pushforward i).obj M) q))

theorem projectiveOver_cohomology_finite (p : X ⟶ Spec (CommRingCat.of ℂ))
    (i : X ⟶ projectiveSpace ℂ σ) [IsClosedImmersion i]
    (hi : i ≫ polynomialProjectiveProjection ℂ σ = p)
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  subst p
  exact projectiveEmbedding_cohomology_finite i M q

end ProjectiveFiniteCoordinates

end PiExponent

end

end OAI
end Source0599
