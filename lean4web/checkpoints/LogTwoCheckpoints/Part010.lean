/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part006
public import LogTwoCheckpoints.Part009
public import Batteries.Logic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.CategoryTheory.Abelian.Projective.Ext
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceResolution.lean
section Source0250
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceResolution.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [AddCommGroup W] [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

def coneDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (X × Y) →ₗ[R] (Y × Z) :=
  ((f.comp (LinearMap.fst R X Y)) + r • LinearMap.snd R X Y).prod
    (-(g.comp (LinearMap.snd R X Y)))

@[simp] theorem coneDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (x : X) (y : Y) :
    coneDifferential f g r (x, y) = (f x + r • y, -g y) := rfl

def coneBottom (g : Y →ₗ[R] Z) (r : R) : (Y × Z) →ₗ[R] Z :=
  g.comp (LinearMap.fst R Y Z) + r • LinearMap.snd R Y Z

@[simp] theorem coneBottom_apply (g : Y →ₗ[R] Z) (r : R) (y : Y) (z : Z) :
    coneBottom g r (y, z) = g y + r • z := rfl

lemma comp_zero_of_range_eq_ker (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : LinearMap.range f = LinearMap.ker g) : g.comp f = 0 := by
  apply LinearMap.ext
  intro x
  change g (f x) = 0
  apply LinearMap.mem_ker.mp
  rw [← h]
  exact LinearMap.mem_range_self f x

theorem coneDifferential_comp (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (hgf : g.comp f = 0) (hhg : h.comp g = 0) :
    (coneDifferential g h r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro x
  apply Prod.ext
  · change g (f x.1 + r • x.2) + r • (-g x.2) = 0
    have hz : g (f x.1) = 0 := LinearMap.congr_fun hgf x.1
    simp [map_add, map_smul, hz]
  · change -h (-g x.2) = 0
    have hz : h (g x.2) = 0 := LinearMap.congr_fun hhg x.2
    simp [hz]

theorem coneDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgh : LinearMap.range g = LinearMap.ker h) :
    LinearMap.range (coneDifferential f g r) =
      LinearMap.ker (coneDifferential g h r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨xy, rfl⟩
    exact LinearMap.congr_fun
      (coneDifferential_comp f g h r (comp_zero_of_range_eq_ker f g hfg)
        (comp_zero_of_range_eq_ker g h hgh)) xy
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := congrArg Prod.fst hyz
    have hsecond : h yz.2 = 0 := by
      have hn : -h yz.2 = 0 := congrArg Prod.snd hyz
      exact neg_eq_zero.mp hn
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgh]
      exact hsecond
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

theorem coneBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (π : Z →ₗ[R] Q) (r : R)
    (hfg : LinearMap.range f = LinearMap.ker g)
    (hgπ : LinearMap.range g = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (coneDifferential f g r) = LinearMap.ker (coneBottom g r) := by
  ext yz
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    have hz : g (f x) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker f g hfg) x
    change g (f x + r • y) + r • (-g y) = 0
    simp [map_add, map_smul, hz]
  · intro hyz
    have hfirst : g yz.1 + r • yz.2 = 0 := hyz
    have hπg : π (g yz.1) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hgπ) yz.1
    have hrπ : r • π yz.2 = 0 := by
      have heq := congrArg π hfirst
      simpa only [map_add, map_smul, hπg, zero_add, map_zero] using heq
    have hz : π yz.2 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hzrange : yz.2 ∈ LinearMap.range g := by
      rw [hgπ]
      exact hz
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hzrange
    have hcycle : g (yz.1 + r • t) = 0 := by
      simpa only [map_add, map_smul, ht] using hfirst
    have hyrange : yz.1 + r • t ∈ LinearMap.range f := by
      rw [hfg]
      exact hcycle
    obtain ⟨x, hx⟩ := LinearMap.mem_range.mp hyrange
    refine ⟨(x, -t), ?_⟩
    apply Prod.ext
    · change f x + r • (-t) = yz.1
      rw [hx, smul_neg]
      abel
    · change -g (-t) = yz.2
      simp [ht]

end PiExponentSiegelAux.W30

end OAI
end Source0250

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConeQuotientAugmentation.lean
section Source0251
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConeQuotientAugmentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open scoped Pointwise
variable {R Y Z Q : Type*} [CommRing R] [AddCommGroup Y] [AddCommGroup Z]
  [AddCommGroup Q] [Module R Y] [Module R Z] [Module R Q]

def coneQuotientAugmentation (π : Z →ₗ[R] Q) (r : R) : Z →ₗ[R] QuotSMulTop r Q :=
  (r • (⊤ : Submodule R Q)).mkQ.comp π

theorem coneQuotientAugmentation_exact (g : Y →ₗ[R] Z) (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) (hg : LinearMap.range g = LinearMap.ker π) :
    LinearMap.range (coneBottom g r) = LinearMap.ker (coneQuotientAugmentation π r) := by
  ext z
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨y, w⟩, rfl⟩
    have hz : π (g y) = 0 := LinearMap.congr_fun (comp_zero_of_range_eq_ker g π hg) y
    change (Submodule.Quotient.mk (π (g y + r • w)) : QuotSMulTop r Q) = 0
    apply (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mpr
    simp only [map_add, map_smul, hz, zero_add]
    exact Submodule.smul_mem_pointwise_smul (π w) r ⊤ (Submodule.mem_top)
  · intro hz
    have hmem : π z ∈ r • (⊤ : Submodule R Q) :=
      (Submodule.Quotient.mk_eq_zero (r • (⊤ : Submodule R Q))).mp hz
    obtain ⟨q, _, hq⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hmem
    obtain ⟨w, hw⟩ := hπ q
    have hcycle : π (z - r • w) = 0 := by
      simp only [map_sub, map_smul, hw, hq, sub_self]
    have hrange : z - r • w ∈ LinearMap.range g := by
      rw [hg]
      exact hcycle
    obtain ⟨y, hy⟩ := LinearMap.mem_range.mp hrange
    refine ⟨(y, w), ?_⟩
    change g y + r • w = z
    rw [hy]
    abel

theorem coneQuotientAugmentation_surjective (π : Z →ₗ[R] Q) (r : R)
    (hπ : Function.Surjective π) : Function.Surjective (coneQuotientAugmentation π r) :=
  (Submodule.mkQ_surjective _).comp hπ

end PiExponentSiegelAux.W30

end OAI
end Source0251

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ConeComplex.lean
section Source0252
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ConeComplex.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open CategoryTheory

universe u
variable {R : Type u} [CommRing R]

lemma coneBottom_comp {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y]
    [AddCommGroup Z] [Module R X] [Module R Y] [Module R Z]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (hgf : g.comp f = 0) :
    (coneBottom g r).comp (coneDifferential f g r) = 0 := by
  apply LinearMap.ext
  intro xy
  have hz : g (f xy.1) = 0 := LinearMap.congr_fun hgf xy.1
  change g (f xy.1 + r • xy.2) + r • (-g xy.2) = 0
  simp [map_add, map_smul, hz]

def scalarConeObject (C : ChainComplex (ModuleCat.{u} R) ℕ) : ℕ → ModuleCat.{u} R
  | 0 => C.X 0
  | n + 1 => ModuleCat.of R (C.X (n + 1) × C.X n)

def scalarConeMap (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ∀ n, scalarConeObject C (n + 1) ⟶ scalarConeObject C n
  | 0 => ModuleCat.ofHom (coneBottom (C.d 1 0).hom r)
  | n + 1 => ModuleCat.ofHom
      (coneDifferential (C.d (n + 2) (n + 1)).hom (C.d (n + 1) n).hom r)

lemma chain_linear_comp_zero (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (C.d (n + 1) n).hom.comp (C.d (n + 2) (n + 1)).hom = 0 := by
  simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
    congrArg (fun f => f.hom) (C.d_comp_d (n + 2) (n + 1) n)

theorem scalarConeMap_comp (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ) :
    scalarConeMap C r (n + 1) ≫ scalarConeMap C r n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    exact coneBottom_comp _ _ r (chain_linear_comp_zero C 0)
  | succ n =>
    apply ModuleCat.hom_ext
    exact coneDifferential_comp _ _ _ r
      (chain_linear_comp_zero C (n + 1)) (chain_linear_comp_zero C n)

def scalarConeComplex (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) :
    ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (scalarConeObject C) (scalarConeMap C r) (scalarConeMap_comp C r)

theorem scalarCone_interior_exact (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (n : ℕ)
    (hnext : LinearMap.range (C.d (n + 3) (n + 2)).hom =
      LinearMap.ker (C.d (n + 2) (n + 1)).hom)
    (hprev : LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom) :
    LinearMap.range (scalarConeMap C r (n + 2)).hom =
      LinearMap.ker (scalarConeMap C r (n + 1)).hom :=
  coneDifferential_exact _ _ _ r hnext hprev

end PiExponentSiegelAux.W30

end OAI
end Source0252

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulFiniteFree.lean
section Source0253
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulFiniteFree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30

universe u
variable {R : Type u} [CommRing R]

def emptyKoszulObject : ℕ → ModuleCat.{u} R
  | 0 => ModuleCat.of R R
  | _ + 1 => ModuleCat.of R (Fin 0 → R)

def emptyKoszulComplex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of emptyKoszulObject (fun _ => 0) (fun _ => by simp)

def iterateScalarCones (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    List R → ChainComplex (ModuleCat.{u} R) ℕ
  | [] => C
  | r :: rs => iterateScalarCones (scalarConeComplex C r) rs

def regularSequenceComplex (rs : List R) : ChainComplex (ModuleCat.{u} R) ℕ :=
  iterateScalarCones emptyKoszulComplex rs

lemma scalarCone_free (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfree 0
  | succ n =>
    let := hfree (n + 1)
    let := hfree n
    change Module.Free R (C.X (n + 1) × C.X n)
    infer_instance

lemma scalarCone_finite (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => exact hfinite 0
  | succ n =>
    let := hfinite (n + 1)
    let := hfinite n
    change Module.Finite R (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_free (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfree : ∀ n, Module.Free R (C.X n)) (n : ℕ) :
    Module.Free R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfree n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_free C r hfree)

lemma iterateScalarCones_finite (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (hfinite : ∀ n, Module.Finite R (C.X n)) (n : ℕ) :
    Module.Finite R ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C with
  | nil => exact hfinite n
  | cons r rs ih => exact ih (scalarConeComplex C r) (scalarCone_finite C r hfinite)

theorem regularSequenceComplex_free (rs : List R) (n : ℕ) :
    Module.Free R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_free
  intro k
  cases k with
  | zero =>
    change Module.Free R R
    exact Module.Free.self R
  | succ k =>
    change Module.Free R (Fin 0 → R)
    infer_instance

theorem regularSequenceComplex_finite (rs : List R) (n : ℕ) :
    Module.Finite R ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_finite
  intro k
  cases k with
  | zero =>
    change Module.Finite R R
    exact Module.Finite.self R
  | succ k =>
    change Module.Finite R (Fin 0 → R)
    infer_instance

end PiExponentSiegelAux.W30

end OAI
end Source0253

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulBounded.lean
section Source0254
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulBounded.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
universe u
variable {R : Type u} [CommRing R]

lemma scalarCone_bounded (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (n : ℕ) (hn : d + 1 < n) :
    Subsingleton ((scalarConeComplex C r).X n) := by
  cases n with
  | zero => omega
  | succ n =>
    let := hbound n (by omega)
    let := hbound (n + 1) (by omega)
    change Subsingleton (C.X (n + 1) × C.X n)
    infer_instance

lemma iterateScalarCones_bounded (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (n : ℕ) (hn : d + rs.length < n) :
    Subsingleton ((iterateScalarCones C rs).X n) := by
  induction rs generalizing C d with
  | nil => exact hbound n (by simpa using hn)
  | cons r rs ih =>
    apply ih (scalarConeComplex C r) (d + 1) (scalarCone_bounded C r d hbound)
    simp only [List.length_cons] at hn
    omega

theorem regularSequenceComplex_bounded (rs : List R) (n : ℕ) (hn : rs.length < n) :
    Subsingleton ((regularSequenceComplex rs).X n) := by
  apply iterateScalarCones_bounded rs emptyKoszulComplex 0 ?_ n (by simpa using hn)
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    change Subsingleton (Fin 0 → R)
    infer_instance

theorem iterateScalarCones_zero (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ) :
    (iterateScalarCones C rs).X 0 = C.X 0 := by
  induction rs generalizing C with
  | nil => rfl
  | cons r rs ih => exact (ih (scalarConeComplex C r)).trans rfl

@[simp] theorem regularSequenceComplex_zero (rs : List R) :
    (regularSequenceComplex rs).X 0 = ModuleCat.of R R :=
  iterateScalarCones_zero rs emptyKoszulComplex

end PiExponentSiegelAux.W30

end OAI
end Source0254

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IteratedKoszulExactness.lean
section Source0255
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IteratedKoszulExactness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
universe u
variable {R : Type u} [CommRing R]

theorem scalarCone_positive_exact (C : ChainComplex (ModuleCat.{u} R) ℕ)
    {Q : Type u} [AddCommGroup Q] [Module R Q] (π : C.X 0 →ₗ[R] Q) (r : R)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hr : IsSMulRegular Q r) (n : ℕ) :
    LinearMap.range ((scalarConeComplex C r).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((scalarConeComplex C r).d (n + 1) n).hom := by
  cases n with
  | zero =>
    change LinearMap.range (coneDifferential (C.d 2 1).hom (C.d 1 0).hom r) =
      LinearMap.ker (coneBottom (C.d 1 0).hom r)
    exact coneBottom_exact (C.d 2 1).hom (C.d 1 0).hom π r (hexact 0) hzero hr
  | succ n =>
    have hd₁ : (scalarConeComplex C r).d (n + 1 + 2) (n + 1 + 1) =
        scalarConeMap C r (n + 1 + 1) := ChainComplex.of_d _ _ (n + 1 + 1)
    have hd₀ : (scalarConeComplex C r).d (n + 1 + 1) (n + 1) =
        scalarConeMap C r (n + 1) := ChainComplex.of_d _ _ (n + 1)
    rw [hd₁, hd₀]
    exact scalarCone_interior_exact C r n (hexact (n + 1)) (hexact n)

theorem iterateScalarCones_exact (rs : List R) {Q : Type u}
    [AddCommGroup Q] [Module R Q] (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (π : C.X 0 →ₗ[R] Q) (hπ : Function.Surjective π)
    (hzero : LinearMap.range (C.d 1 0).hom = LinearMap.ker π)
    (hexact : ∀ n, LinearMap.range (C.d (n + 2) (n + 1)).hom =
      LinearMap.ker (C.d (n + 1) n).hom)
    (hreg : RingTheory.Sequence.IsRegular Q rs) :
    ∃ ε : (iterateScalarCones C rs).X 0 →ₗ[R]
        (Q ⧸ (Ideal.ofList rs • ⊤ : Submodule R Q)),
      Function.Surjective ε ∧
      LinearMap.range ((iterateScalarCones C rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((iterateScalarCones C rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((iterateScalarCones C rs).d (n + 1) n).hom := by
  induction rs generalizing Q C with
  | nil =>
    let e := (Ideal.ofList ([] : List R) • (⊤ : Submodule R Q)).quotEquivOfEqBot
      (by simp)
    refine ⟨e.symm.toLinearMap.comp π, e.symm.surjective.comp hπ, ?_, hexact⟩
    calc
      _ = LinearMap.ker π := hzero
      _ = _ := by
        ext x
        change π x = 0 ↔ e.symm (π x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩
  | cons r rs ih =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff Q r rs).mp hreg
    let C' := scalarConeComplex C r
    let π' : C'.X 0 →ₗ[R] QuotSMulTop r Q := coneQuotientAugmentation π r
    have hπ' : Function.Surjective π' := coneQuotientAugmentation_surjective π r hπ
    have hz' : LinearMap.range (C'.d 1 0).hom = LinearMap.ker π' := by
      change LinearMap.range (coneBottom (C.d 1 0).hom r) =
        LinearMap.ker (coneQuotientAugmentation π r)
      exact coneQuotientAugmentation_exact (C.d 1 0).hom π r hπ hzero
    have he' : ∀ n, LinearMap.range (C'.d (n + 2) (n + 1)).hom =
        LinearMap.ker (C'.d (n + 1) n).hom :=
      scalarCone_positive_exact C π r hzero hexact hr
    obtain ⟨ε, hε, hzε, heε⟩ := ih C' π' hπ' hz' he' htail
    let e := Submodule.quotOfListConsSMulTopEquivQuotSMulTopInner Q r rs
    refine ⟨e.symm.toLinearMap.comp ε, e.symm.surjective.comp hε, ?_, heε⟩
    calc
      _ = LinearMap.ker ε := hzε
      _ = _ := by
        ext x
        change ε x = 0 ↔ e.symm (ε x) = 0
        exact ⟨fun h => by rw [h, map_zero], fun h => e.symm.injective (by simpa using h)⟩

theorem regularSequenceComplex_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ∃ ε : (regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs),
      Function.Surjective ε ∧
      LinearMap.range ((regularSequenceComplex rs).d 1 0).hom = LinearMap.ker ε ∧
      ∀ n, LinearMap.range ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
        LinearMap.ker ((regularSequenceComplex rs).d (n + 1) n).hom := by
  have hzero : LinearMap.range (emptyKoszulComplex.d 1 0).hom =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R) := by
    have hd : (emptyKoszulComplex (R := R)).d 1 0 = 0 :=
      ChainComplex.of_d (emptyKoszulObject (R := R)) (fun _ => 0) 0
    rw [hd]
    change LinearMap.range (0 : (Fin 0 → R) →ₗ[R] R) =
      LinearMap.ker (LinearMap.id : R →ₗ[R] R)
    exact LinearMap.range_zero.trans LinearMap.ker_id.symm
  have hexact : ∀ n : ℕ,
      LinearMap.range ((emptyKoszulComplex (R := R)).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((emptyKoszulComplex (R := R)).d (n + 1) n).hom := by
    intro n
    let : Subsingleton ((emptyKoszulComplex (R := R)).X (n + 1)) := by
      change Subsingleton (Fin 0 → R)
      infer_instance
    exact Subsingleton.elim _ _
  have h := iterateScalarCones_exact rs emptyKoszulComplex
    (LinearMap.id : R →ₗ[R] R) Function.surjective_id hzero hexact hreg
  have hI : (Ideal.ofList rs • (⊤ : Submodule R R)) = Ideal.ofList rs := by
    change Ideal.ofList rs * ⊤ = Ideal.ofList rs
    exact Ideal.mul_top _
  rw [hI] at h
  exact h

end PiExponentSiegelAux.W30

end OAI
end Source0255

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceExt.lean
section Source0256
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

variable {R : Type u} [CommRing R]

def regularSequenceAugmentation (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    (W30.regularSequenceComplex rs).X 0 →ₗ[R] (R ⧸ Ideal.ofList rs) :=
  (W30.regularSequenceComplex_exact rs hreg).choose

theorem regularSequenceAugmentation_spec (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    Function.Surjective (regularSequenceAugmentation rs hreg) ∧
    LinearMap.range ((W30.regularSequenceComplex rs).d 1 0).hom =
      LinearMap.ker (regularSequenceAugmentation rs hreg) ∧
    ∀ n, LinearMap.range ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom =
      LinearMap.ker ((W30.regularSequenceComplex rs).d (n + 1) n).hom :=
  (W30.regularSequenceComplex_exact rs hreg).choose_spec

def regularSequenceResolution (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.ofList rs)) :=
  moduleFreeResolutionOfExact (W30.regularSequenceComplex rs)
    (ModuleCat.of R (R ⧸ Ideal.ofList rs))
    (ModuleCat.ofHom (regularSequenceAugmentation rs hreg))
    (by
      apply ModuleCat.hom_ext
      exact LinearMap.range_le_ker_iff.mp (regularSequenceAugmentation_spec rs hreg).2.1.le)
    (regularSequenceAugmentation_spec rs hreg).2.1
    (regularSequenceAugmentation_spec rs hreg).1
    (regularSequenceAugmentation_spec rs hreg).2.2
    (W30.regularSequenceComplex_free rs)

def regularSequenceQuotientExtAddEquiv (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n :=
  (regularSequenceResolution rs hreg).extAddEquivCohomologyClass

theorem regularSequenceQuotientExt_iff_boundaries (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (Y : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) Y (n + 1)) ↔
      ∀ f : (W30.regularSequenceComplex rs).X (n + 1) ⟶ Y,
        (W30.regularSequenceComplex rs).d (n + 2) (n + 1) ≫ f = 0 →
        ∃ g : (W30.regularSequenceComplex rs).X n ⟶ Y,
          (W30.regularSequenceComplex rs).d (n + 1) n ≫ g = f :=
  ext_subsingleton_iff_cocycles_are_boundaries _ Y (regularSequenceResolution rs hreg) n

theorem regularSequenceQuotientExt_of_dual_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ)
    (hdual : LinearMap.range (((W30.regularSequenceComplex rs).d (n + 1) n).hom.dualMap) =
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap)) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) := by
  apply (regularSequenceQuotientExt_iff_boundaries rs hreg (ModuleCat.of R R) n).mpr
  intro f hf
  have hfker : f.hom ∈
      LinearMap.ker (((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap) := by
    change f.hom.comp ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom = 0
    exact ModuleCat.hom_ext_iff.mp hf
  rw [← hdual] at hfker
  obtain ⟨g, hg⟩ := hfker
  refine ⟨ModuleCat.ofHom g, ?_⟩
  apply ModuleCat.hom_ext
  exact hg

def residueFieldExtAddEquiv [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (Y : ModuleCat.{u} R) (n : ℕ) :
    Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) Y n ≃+
      CochainComplex.HomComplex.CohomologyClass
        (regularSequenceResolution rs hreg).cochainComplex
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj Y) n := by
  change Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) Y n ≃+ _
  rw [← hmax]
  exact regularSequenceQuotientExtAddEquiv rs hreg Y n

end PiExponentSiegelAux.W31

end

end OAI
end Source0256

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceExtObstruction.lean
section Source0257
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceExtObstruction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponentJets.W18
open CategoryTheory CategoryTheory.Abelian
open PiExponentSiegelAux

variable {R : Type u} [CommRing R]

section RangeSequences
variable {L M N : Type u} [AddCommGroup L] [AddCommGroup M] [AddCommGroup N]
  [Module R L] [Module R M] [Module R N]

def differentialRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g.rangeRestrict (by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

theorem differentialRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) :
    (differentialRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g.rangeRestrict
    rw [Submodule.range_subtype, LinearMap.ker_rangeRestrict, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr (LinearMap.surjective_rangeRestrict g)

def augmentationRangeShortComplex (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.range f).subtype g (by
    apply LinearMap.ext
    intro x
    exact (show x.val ∈ LinearMap.ker g from hex ▸ x.property))

theorem augmentationRangeShortComplex_shortExact
    (f : L →ₗ[R] M) (g : M →ₗ[R] N)
    (hex : LinearMap.range f = LinearMap.ker g) (hg : Function.Surjective g) :
    (augmentationRangeShortComplex f g hex).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (LinearMap.range f).subtype = LinearMap.ker g
    rw [Submodule.range_subtype, hex]
  · exact (ModuleCat.mono_iff_injective _).mpr (LinearMap.range f).injective_subtype
  · exact (ModuleCat.epi_iff_surjective _).mpr hg

end RangeSequences

theorem ext_subsingleton_of_subsingleton_module
    {M : Type u} [AddCommGroup M] [Module R M] [Subsingleton M]
    (X : ModuleCat.{u} R) (n : ℕ) :
    Subsingleton (Ext X (ModuleCat.of R M) n) := by
  have hid : 𝟙 (ModuleCat.of R M) = 0 := by
    ext x
    exact Subsingleton.elim _ _
  apply subsingleton_of_forall_eq 0
  intro e
  have he := Ext.comp_mk₀_id e
  rw [hid, Ext.mk₀_zero, Ext.comp_zero] at he
  exact he.symm

def regularSequenceDifferentialRange (rs : List R) (n : ℕ) : ModuleCat.{u} R :=
  ModuleCat.of R (LinearMap.range ((W30.regularSequenceComplex rs).d (n + 1) n).hom)

theorem regularSequenceDifferentialRange_top_subsingleton (rs : List R) :
    Subsingleton (regularSequenceDifferentialRange rs rs.length) := by
  let := W30.regularSequenceComplex_bounded rs (rs.length + 1) (Nat.lt_succ_self _)
  apply subsingleton_of_forall_eq 0
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

theorem regular_sequence_ext_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (X : ModuleCat.{u} R)
    (hv : ∀ i ≤ rs.length, Subsingleton (Ext X (ModuleCat.of R R) i)) :
    Subsingleton (Ext X (ModuleCat.of R (R ⧸ Ideal.ofList rs)) 0) := by
  have hfree (n : ℕ) (hn : n ≤ rs.length) :
      Subsingleton (Ext X ((W30.regularSequenceComplex rs).X n) n) := by
    let := W30.regularSequenceComplex_free rs n
    let := W30.regularSequenceComplex_finite rs n
    exact W31.ext_subsingleton_of_finite_free X n (hv n hn)
  have hend : Subsingleton
      (Ext X (regularSequenceDifferentialRange rs rs.length) (rs.length + 1)) := by
    let : Subsingleton (LinearMap.range
        ((W30.regularSequenceComplex rs).d (rs.length + 1) rs.length).hom) :=
      regularSequenceDifferentialRange_top_subsingleton rs
    exact ext_subsingleton_of_subsingleton_module X (rs.length + 1)
  have hrange : Subsingleton (Ext X (regularSequenceDifferentialRange rs 0) 1) := by
    apply Nat.decreasingInduction
      (motive := fun n _ =>
        Subsingleton (Ext X (regularSequenceDifferentialRange rs n) (n + 1)))
      (fun n hn ih => ?_) hend (Nat.zero_le rs.length)
    let f := ((W30.regularSequenceComplex rs).d (n + 2) (n + 1)).hom
    let g := ((W30.regularSequenceComplex rs).d (n + 1) n).hom
    have hex : LinearMap.range f = LinearMap.ker g :=
      (W31.regularSequenceAugmentation_spec rs hreg).2.2 n
    exact ext_subsingleton_of_shortExact X (differentialRangeShortComplex f g hex)
      (differentialRangeShortComplex_shortExact f g hex) (n + 1)
      (hfree (n + 1) (Nat.succ_le_of_lt hn)) ih
  let f := ((W30.regularSequenceComplex rs).d 1 0).hom
  let g := W31.regularSequenceAugmentation rs hreg
  have hex : LinearMap.range f = LinearMap.ker g :=
    (W31.regularSequenceAugmentation_spec rs hreg).2.1
  exact ext_subsingleton_of_shortExact X (augmentationRangeShortComplex f g hex)
    (augmentationRangeShortComplex_shortExact f g hex
      (W31.regularSequenceAugmentation_spec rs hreg).1) 0
    (hfree 0 (Nat.zero_le _)) hrange

theorem regular_sequence_associatedPrime_ext_obstruction [IsNoetherianRing R]
    (rs : List R) (hreg : RingTheory.Sequence.IsRegular R rs)
    (P : Ideal R) (hP : IsAssociatedPrime P (R ⧸ Ideal.ofList rs)) :
    ∃ i : ℕ, i ≤ rs.length ∧
      ¬ Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
  classical
  by_contra h
  have hv (i : ℕ) (hi : i ≤ rs.length) :
      Subsingleton (Ext (ModuleCat.of R (R ⧸ P)) (ModuleCat.of R R) i) := by
    by_contra hv
    exact h ⟨i, hi, hv⟩
  exact not_isAssociatedPrime_of_ext_zero P
    (regular_sequence_ext_zero rs hreg (ModuleCat.of R (R ⧸ P)) hv) hP

end PiExponentJets.W18

end

end OAI
end Source0257

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualCone.lean
section Source0258
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualCone.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [Module R X] [Module R Y] [Module R Z] [Module R W]

def dualConeDifferential (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (Dual R Y × Dual R Z) →ₗ[R] (Dual R X × Dual R Y) :=
  (f.dualMap.comp (LinearMap.fst R _ _)).prod
    (r • LinearMap.fst R _ _ - g.dualMap.comp (LinearMap.snd R _ _))

@[simp] theorem dualConeDifferential_apply (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    dualConeDifferential f g r (α, β) = (α.comp f, r • α - β.comp g) := rfl

theorem coneDifferential_dual_precomposition (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (r : R) (α : Dual R Y) (β : Dual R Z) :
    (α.coprod β).comp (coneDifferential f g r) =
      (α.comp f).coprod (r • α - β.comp g) := by
  apply LinearMap.ext
  rintro ⟨x, y⟩
  change α (f x + r • y) + β (-g y) = α (f x) + (r • α - β.comp g) y
  change α (f x + r • y) + β (-g y) =
    α (f x) + (r • α y - β (g y))
  simp only [map_add, map_smul, map_neg, sub_eq_add_neg]
  abel

theorem coneDifferential_dual_equiv (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R X Y).toLinearMap.comp (dualConeDifferential f g r) =
      (coneDifferential f g r).dualMap.comp (dualProdDualEquivDual R Y Z).toLinearMap := by
  apply LinearMap.ext
  rintro ⟨α, β⟩
  exact (coneDifferential_dual_precomposition f g r α β).symm

theorem dualConeDifferential_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgf : LinearMap.range g.dualMap = LinearMap.ker f.dualMap) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    have hfg : f.dualMap (g.dualMap α) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hgf) α
    have hgh : g.dualMap (h.dualMap β) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker h.dualMap g.dualMap hhg) β
    apply Prod.ext
    · exact hfg
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      simp only [map_sub, map_smul, hgh, sub_zero, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgf]
      exact ha
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end PiExponentSiegelAux.W30

end OAI
end Source0258

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualTransport.lean
section Source0259
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C A' B' C' : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
variable [Module R A] [Module R B] [Module R C]
variable [Module R A'] [Module R B'] [Module R C']

theorem exact_of_equivalences (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (eA : A' ≃ₗ[R] A) (eB : B' ≃ₗ[R] B) (eC : C' ≃ₗ[R] C)
    (hf : eB.toLinearMap.comp f' = f.comp eA.toLinearMap)
    (hg : eC.toLinearMap.comp g' = g.comp eB.toLinearMap)
    (hex : LinearMap.range f' = LinearMap.ker g') :
    LinearMap.range f = LinearMap.ker g := by
  have hf_apply (a : A') : eB (f' a) = f (eA a) := LinearMap.congr_fun hf a
  have hg_apply (b : B') : eC (g' b) = g (eB b) := LinearMap.congr_fun hg b
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := eA.surjective a
    change g (f (eA a')) = 0
    rw [← hf_apply a', ← hg_apply (f' a')]
    have hz : g' (f' a') = 0 := by
      have hm : f' a' ∈ LinearMap.range f' := ⟨a', rfl⟩
      rw [hex] at hm
      exact hm
    rw [hz, map_zero]
  · intro hb
    obtain ⟨b', rfl⟩ := eB.surjective b
    have hz : g' b' = 0 := by
      apply eC.injective
      rw [map_zero, hg_apply b']
      exact hb
    have hm : b' ∈ LinearMap.range f' := by
      rw [hex]
      exact hz
    obtain ⟨a', ha'⟩ := hm
    refine ⟨eA a', ?_⟩
    rw [← hf_apply a', ha']

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_interior_exact
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hhi : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker (P.d (n + 3) (n + 2)).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual S (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual S (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual S (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) := by
      exact ChainComplex.of_d _ _ (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) := by
      exact ChainComplex.of_d _ _ (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualConeDifferential_exact _ _ _ r hlo hhi

end PiExponentSiegelAux.W30

end OAI
end Source0259

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualBottom.lean
section Source0260
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualBottom.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module R X] [Module R Y] [Module R Z]

def dualConeBottom (g : Y →ₗ[R] Z) (r : R) :
    Dual R Z →ₗ[R] (Dual R Y × Dual R Z) :=
  g.dualMap.prod (r • LinearMap.id)

@[simp] theorem dualConeBottom_apply (g : Y →ₗ[R] Z) (r : R) (α : Dual R Z) :
    dualConeBottom g r α = (α.comp g, r • α) := rfl

theorem coneBottom_dual_equiv (g : Y →ₗ[R] Z) (r : R) :
    (dualProdDualEquivDual R Y Z).toLinearMap.comp (dualConeBottom g r) =
      (coneBottom g r).dualMap := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  rintro ⟨y, z⟩
  change α (g y) + r • α z = α (g y + r • z)
  rw [map_add, map_smul]

theorem dualConeBottom_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R)
    (hex : LinearMap.range g.dualMap = LinearMap.ker f.dualMap)
    (hinj : Function.Injective g.dualMap) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap f.dualMap hex) α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have ha : f.dualMap ab.1 = 0 := congrArg Prod.fst hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hex]
      exact ha
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

theorem dualConeBottom_injective (g : Y →ₗ[R] Z) (r : R)
    (hinj : Function.Injective g.dualMap) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hinj (congrArg Prod.fst h)

theorem dualConeBottom_injective_of_regular (g : Y →ₗ[R] Z) (r : R)
    (hr : IsSMulRegular (Dual R Z) r) : Function.Injective (dualConeBottom g r) := by
  intro α β h
  exact hr (congrArg Prod.snd h)

theorem dualConeBottom_endpoint_exact {Q : Type*} [AddCommGroup Q] [Module R Q]
    (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hinj : Function.Injective g.dualMap) (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeBottom g r) = LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  constructor
  · rintro ⟨α, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α) = 0
      rw [map_smul, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hm : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := hm
    refine ⟨t, ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t = ab.2
      apply hinj
      rw [map_smul, ht]
      exact sub_eq_zero.mp hb

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_one_exact (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hex : LinearMap.range (P.d 1 0).hom.dualMap =
      LinearMap.ker (P.d 2 1).hom.dualMap)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl S (Dual S (P.X 0)))
    (dualProdDualEquivDual S (P.X 1) (P.X 0))
    (dualProdDualEquivDual S (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_exact _ _ r hex hinj

end PiExponentSiegelAux.W30

end OAI
end Source0260

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulTopTerm.lean
section Source0261
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulTopTerm.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
variable {R : Type u} [CommRing R]

def scalarConeTopEquiv (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) :
    (W30.scalarConeComplex C r).X (d + 1) ≃ₗ[R] C.X d := by
  letI := hbound (d + 1) (Nat.lt_succ_self d)
  letI : Unique (C.X (d + 1)) :=
    { default := 0, uniq := fun x => Subsingleton.elim x 0 }
  exact LinearEquiv.uniqueProd (R := R) (M := C.X d) (M₂ := C.X (d + 1))

def iterateScalarConesTopEquiv (rs : List R) (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n)) :
    (W30.iterateScalarCones C rs).X (d + rs.length) ≃ₗ[R] C.X d := by
  induction rs generalizing C d with
  | nil =>
    exact LinearEquiv.refl R (C.X d)
  | cons r rs ih =>
    have e := ih (W30.scalarConeComplex C r) (d + 1)
      (W30.scalarCone_bounded C r d hbound)
    let K := W30.iterateScalarCones (W30.scalarConeComplex C r) rs
    have hidx : d + (r :: rs).length = (d + 1) + rs.length := by
      simp only [List.length_cons]
      exact (Nat.add_assoc d rs.length 1).symm.trans (Nat.add_right_comm d rs.length 1)
    exact (K.XIsoOfEq hidx).toLinearEquiv.trans
      (e.trans (scalarConeTopEquiv C r d hbound))

def regularSequenceTopEquiv (rs : List R) :
    (W30.regularSequenceComplex rs).X rs.length ≃ₗ[R] R := by
  have hbound : ∀ n, 0 < n → Subsingleton (W30.emptyKoszulComplex (R := R) |>.X n) :=
    fun n hn => W30.regularSequenceComplex_bounded ([] : List R) n hn
  let K := W30.iterateScalarCones (W30.emptyKoszulComplex (R := R)) rs
  exact (K.XIsoOfEq (Nat.zero_add rs.length).symm).toLinearEquiv.trans
    (iterateScalarConesTopEquiv rs W30.emptyKoszulComplex 0 hbound)

def regularSequenceTopDualEquiv (rs : List R) :
    Module.Dual R ((W30.regularSequenceComplex rs).X rs.length) ≃ₗ[R] R :=
  (regularSequenceTopEquiv rs).dualMap.symm.trans (LinearMap.ringLmapEquivSelf R R R)

end PiExponentSiegelAux.W31

end

end OAI
end Source0261

-- Source: OAI/NumberTheory/PiExponent/Jets/KoszulTopDifferential.lean
section Source0262
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/KoszulTopDifferential.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
namespace PiExponentSiegelAux.W31
open Module
variable {R : Type u} [CommRing R]

def topDualCoordinate {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) : Module.Dual R T ≃ₗ[R] R :=
  e.dualMap.symm.trans (LinearMap.ringLmapEquivSelf R R R)

@[simp] theorem topDualCoordinate_apply {T : Type u} [AddCommGroup T] [Module R T]
    (e : T ≃ₗ[R] R) (φ : Module.Dual R T) :
    topDualCoordinate e φ = φ (e.symm 1) := rfl

def scalarConeTopDualCoordinate (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (d : ℕ) (hbound : ∀ n, d < n → Subsingleton (C.X n))
    (e : C.X d ≃ₗ[R] R) :
    Module.Dual R ((W30.scalarConeComplex C r).X (d + 1)) ≃ₗ[R] R :=
  topDualCoordinate ((scalarConeTopEquiv C r d hbound).trans e)

@[simp] theorem scalarConeTopDualCoordinate_apply
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (d : ℕ)
    (hbound : ∀ n, d < n → Subsingleton (C.X n)) (e : C.X d ≃ₗ[R] R)
    (φ : Module.Dual R ((W30.scalarConeComplex C r).X (d + 1))) :
    scalarConeTopDualCoordinate C r d hbound e φ = φ (0, e.symm 1) := rfl

theorem scalarConeTopBoundary_eval (C : ChainComplex (ModuleCat.{u} R) ℕ)
    (r : R) (n : ℕ) (α : Module.Dual R (C.X (n + 1)))
    (β : Module.Dual R (C.X n)) (t : C.X (n + 1)) :
    (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) (0, t) =
      r * α t - ((C.d (n + 1) n).hom.dualMap β) t := by
  have hd : (W30.scalarConeComplex C r).d (n + 2) (n + 1) =
      W30.scalarConeMap C r (n + 1) :=
    ChainComplex.of_d _ _ (n + 1)
  rw [hd]
  change α ((C.d (n + 2) (n + 1)).hom 0 + r • t) +
      β (-((C.d (n + 1) n).hom t)) = r * α t - β ((C.d (n + 1) n).hom t)
  simp only [map_zero, zero_add, map_smul, map_neg, smul_eq_mul, sub_eq_add_neg]

theorem scalarConeTopDualCoordinate_boundary
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (C.X k))
    (e : C.X (n + 1) ≃ₗ[R] R)
    (α : Module.Dual R (C.X (n + 1))) (β : Module.Dual R (C.X n)) :
    scalarConeTopDualCoordinate C r (n + 1) hbound e
      (((W30.scalarConeComplex C r).d (n + 2) (n + 1)).hom.dualMap (α.coprod β)) =
      r * topDualCoordinate e α -
        topDualCoordinate e ((C.d (n + 1) n).hom.dualMap β) := by
  rw [scalarConeTopDualCoordinate_apply]
  exact scalarConeTopBoundary_eval C r n α β (e.symm 1)

theorem scalarConeFirstTopBoundary_eval
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (α : Module.Dual R (C.X 0)) (t : C.X 0) :
    (((W30.scalarConeComplex C r).d 1 0).hom.dualMap α) (0, t) = r * α t := by
  change α ((C.d 1 0).hom 0 + r • t) = r * α t
  simp only [map_zero, zero_add, map_smul, smul_eq_mul]

end PiExponentSiegelAux.W31

end

end OAI
end Source0262

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceAugmentation.lean
section Source0263
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceAugmentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30

variable {R X Y : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [Module R X] [Module R Y]

theorem coneBottom_range_eq_sup (g : Y →ₗ[R] R) (r : R) (I : Ideal R)
    (hg : LinearMap.range g = I) :
    LinearMap.range (coneBottom g r) = I ⊔ Ideal.span {r} := by
  have heq : coneBottom g r = g.coprod (r • LinearMap.id) := rfl
  rw [heq, LinearMap.range_coprod, hg]
  congr 1
  ext z
  simp only [LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul, Ideal.mem_span_singleton, dvd_def]
  exact exists_congr (fun _ => eq_comm)

end PiExponentSiegelAux.W30

end OAI
end Source0263

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulTopAugmentation.lean
section Source0264
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulTopAugmentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B C : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [Module R A] [Module R B] [Module R C]

lemma range_comp_eq_of_surjective (f : B →ₗ[R] C) (g : A →ₗ[R] B)
    (hg : Function.Surjective g) : LinearMap.range (f.comp g) = LinearMap.range f := by
  ext c
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨g a, rfl⟩
  · rintro ⟨b, rfl⟩
    obtain ⟨a, rfl⟩ := hg b
    exact ⟨a, rfl⟩

theorem scalar_sub_range (e : A ≃ₗ[R] R) (g : B →ₗ[R] R) (r : R)
    (I : Ideal R) (hg : LinearMap.range g = I) :
    LinearMap.range
      (r • e.toLinearMap.comp (LinearMap.fst R A B) -
        g.comp (LinearMap.snd R A B)) = I ⊔ Ideal.span {r} := by
  let T : (A × B) →ₗ[R] (B × R) :=
    (-(LinearMap.snd R A B)).prod (e.toLinearMap.comp (LinearMap.fst R A B))
  have hT : Function.Surjective T := by
    rintro ⟨b, z⟩
    refine ⟨(e.symm z, -b), ?_⟩
    change (-(-b), e (e.symm z)) = (b, z)
    simp only [neg_neg, e.apply_symm_apply]
  have hmap : r • e.toLinearMap.comp (LinearMap.fst R A B) -
      g.comp (LinearMap.snd R A B) = (coneBottom g r).comp T := by
    apply LinearMap.ext
    rintro ⟨a, b⟩
    change r • e a - g b = g (-b) + r • e a
    rw [map_neg]
    abel
  rw [hmap, range_comp_eq_of_surjective _ _ hT, coneBottom_range_eq_sup g r I hg]

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (n : ℕ)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (e : P.X (n + 1) ≃ₗ[S] S) (I : Ideal S)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap) =
      I ⊔ Ideal.span {r} := by
  let E := dualProdDualEquivDual S (P.X (n + 1)) (P.X n)
  let F := (W31.scalarConeTopDualCoordinate P r (n + 1) hbound e).toLinearMap.comp
    ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap
  have hmap : F.comp E.toLinearMap =
      r • (W31.topDualCoordinate e).toLinearMap.comp
          (LinearMap.fst S (Dual S (P.X (n + 1))) (Dual S (P.X n))) -
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap).comp
          (LinearMap.snd S (Dual S (P.X (n + 1))) (Dual S (P.X n))) := by
    apply LinearMap.ext
    rintro ⟨α, β⟩
    exact W31.scalarConeTopDualCoordinate_boundary P r n hbound e α β
  change LinearMap.range F = _
  rw [← range_comp_eq_of_surjective F E.toLinearMap E.surjective, hmap]
  exact scalar_sub_range (W31.topDualCoordinate e) _ r I hI

end PiExponentSiegelAux.W30

end OAI
end Source0264

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualInitial.lean
section Source0265
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualInitial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R A B : Type*} [CommRing R]
variable [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]

theorem regular_on_dual (r : R) (hr : IsSMulRegular R r) :
    IsSMulRegular (Dual R A) r := by
  intro α β h
  apply LinearMap.ext
  intro a
  apply hr
  exact congrArg (fun φ : Dual R A => φ a) h

theorem coordinate_quotient_exact (f : A →ₗ[R] B) (e : B ≃ₗ[R] R)
    (I : Ideal R) (hI : LinearMap.range (e.toLinearMap.comp f) = I) :
    LinearMap.range f = LinearMap.ker (I.mkQ.comp e.toLinearMap) := by
  ext b
  constructor
  · rintro ⟨a, rfl⟩
    change I.mkQ (e (f a)) = 0
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    rw [← hI]
    exact ⟨a, rfl⟩
  · intro hb
    have hm : e b ∈ I := (Submodule.Quotient.mk_eq_zero I).mp hb
    rw [← hI] at hm
    obtain ⟨a, ha⟩ := hm
    exact ⟨a, e.injective ha⟩

universe u
variable {S : Type u} [CommRing S]

theorem scalarCone_dual_zero_injective_of_regular
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S) (hr : IsSMulRegular S r) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective_of_regular (P.d 1 0).hom r (regular_on_dual r hr)
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

theorem scalarCone_dual_zero_injective
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap) :
    Function.Injective ((scalarConeComplex P r).d 1 0).hom.dualMap := by
  have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
    ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
  rw [hd]
  change Function.Injective (coneBottom (P.d 1 0).hom r).dualMap
  intro α β h
  apply dualConeBottom_injective (P.d 1 0).hom r hinj
  apply (dualProdDualEquivDual S (P.X 1) (P.X 0)).injective
  have he (φ : Dual S (P.X 0)) :
      (dualProdDualEquivDual S (P.X 1) (P.X 0)) (dualConeBottom (P.d 1 0).hom r φ) =
        (coneBottom (P.d 1 0).hom r).dualMap φ :=
    LinearMap.congr_fun (coneBottom_dual_equiv (P.d 1 0).hom r) φ
  rw [he, he]
  exact h

theorem scalarCone_first_top_dual_image
    (P : ChainComplex (ModuleCat.{u} S) ℕ) (r : S)
    (hbound : ∀ k, 0 < k → Subsingleton (P.X k)) (e : P.X 0 ≃ₗ[S] S) :
    LinearMap.range
      ((W31.scalarConeTopDualCoordinate P r 0 hbound e).toLinearMap.comp
        ((scalarConeComplex P r).d 1 0).hom.dualMap) = Ideal.span {r} := by
  have he (α : Dual S (P.X 0)) :
      W31.scalarConeTopDualCoordinate P r 0 hbound e
        (((scalarConeComplex P r).d 1 0).hom.dualMap α) =
          r * W31.topDualCoordinate e α := by
    rw [W31.scalarConeTopDualCoordinate_apply]
    exact W31.scalarConeFirstTopBoundary_eval P r α (e.symm 1)
  ext z
  rw [LinearMap.mem_range, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨α, hα⟩
    refine ⟨W31.topDualCoordinate e α, ?_⟩
    exact hα.symm.trans (he α)
  · rintro ⟨a, ha⟩
    refine ⟨(W31.topDualCoordinate e).symm a, ?_⟩
    change W31.scalarConeTopDualCoordinate P r 0 hbound e
      (((scalarConeComplex P r).d 1 0).hom.dualMap ((W31.topDualCoordinate e).symm a)) = z
    rw [he, LinearEquiv.apply_symm_apply]
    exact ha.symm

end PiExponentSiegelAux.W30

end OAI
end Source0265

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualEndpoint.lean
section Source0266
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualEndpoint.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module

variable {R X Y Z W Q : Type*} [CommRing R]
variable [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z] [AddCommGroup W]
variable [AddCommGroup Q]
variable [Module R X] [Module R Y] [Module R Z] [Module R W] [Module R Q]

theorem dualCone_endpoint_exact (f : X →ₗ[R] Y) (g : Y →ₗ[R] Z)
    (h : Z →ₗ[R] W) (r : R) (π : Dual R Y →ₗ[R] Q)
    (hfg : f.dualMap.comp g.dualMap = 0)
    (hgh : g.dualMap.comp h.dualMap = 0)
    (hhg : LinearMap.range h.dualMap = LinearMap.ker g.dualMap)
    (hgπ : LinearMap.range g.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range (dualConeDifferential g h r) =
      LinearMap.ker (dualConeDifferential f g r) := by
  ext ab
  rw [LinearMap.mem_range, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨α, β⟩, rfl⟩
    apply Prod.ext
    · exact LinearMap.congr_fun hfg α
    · change r • g.dualMap α - g.dualMap (r • α - h.dualMap β) = 0
      have hz : g.dualMap (h.dualMap β) = 0 := LinearMap.congr_fun hgh β
      simp only [map_sub, map_smul, hz, sub_zero, sub_self]
  · intro hab
    have hb : r • ab.1 - g.dualMap ab.2 = 0 := congrArg Prod.snd hab
    have hπg : π (g.dualMap ab.2) = 0 :=
      LinearMap.congr_fun (comp_zero_of_range_eq_ker g.dualMap π hgπ) ab.2
    have hrπ : r • π ab.1 = 0 := by
      have h := congrArg π hb
      simpa only [map_sub, map_smul, hπg, sub_zero, map_zero] using h
    have hπa : π ab.1 = 0 := hr (by simpa only [smul_zero] using hrπ)
    have hamem : ab.1 ∈ LinearMap.range g.dualMap := by
      rw [hgπ]
      exact hπa
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hamem
    have hcycle : g.dualMap (r • t - ab.2) = 0 := by
      simpa only [map_sub, map_smul, ht] using hb
    have hbmem : r • t - ab.2 ∈ LinearMap.range h.dualMap := by
      rw [hhg]
      exact hcycle
    obtain ⟨a, ha⟩ := LinearMap.mem_range.mp hbmem
    refine ⟨(t, a), ?_⟩
    apply Prod.ext
    · exact ht
    · change r • t - h.dualMap a = ab.2
      rw [ha]
      abel

end PiExponentSiegelAux.W30

end OAI
end Source0266

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualStep.lean
section Source0267
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/KoszulDualStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
universe u
variable {R : Type u} [CommRing R]

theorem chain_dual_comp_zero (P : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (P.d (n + 2) (n + 1)).hom.dualMap.comp (P.d (n + 1) n).hom.dualMap = 0 := by
  apply LinearMap.ext
  intro α
  apply LinearMap.ext
  intro x
  change α ((P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x)) = 0
  have hz : (P.d (n + 1) n).hom ((P.d (n + 2) (n + 1)).hom x) = 0 :=
    LinearMap.congr_fun (chain_linear_comp_zero P n) x
  rw [hz, map_zero]

theorem scalarCone_dual_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 2)) →ₗ[R] Q)
    (hlo : LinearMap.range (P.d (n + 1) n).hom.dualMap =
      LinearMap.ker (P.d (n + 2) (n + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 2) (n + 1)).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d (n + 2) (n + 1)).hom.dualMap)
    (((scalarConeComplex P r).d (n + 3) (n + 2)).hom.dualMap)
    (dualConeDifferential (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r)
    (dualConeDifferential (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r)
    (dualProdDualEquivDual R (P.X (n + 1)) (P.X n))
    (dualProdDualEquivDual R (P.X (n + 2)) (P.X (n + 1)))
    (dualProdDualEquivDual R (P.X (n + 3)) (P.X (n + 2)))
  · have hd : (scalarConeComplex P r).d (n + 2) (n + 1) = scalarConeMap P r (n + 1) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 1)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 2) (n + 1)).hom (P.d (n + 1) n).hom r
  · have hd : (scalarConeComplex P r).d (n + 3) (n + 2) = scalarConeMap P r (n + 2) :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) (n + 2)
    rw [hd]
    exact coneDifferential_dual_equiv (P.d (n + 3) (n + 2)).hom (P.d (n + 2) (n + 1)).hom r
  · exact dualCone_endpoint_exact _ _ _ r π
      (chain_dual_comp_zero P (n + 1)) (chain_dual_comp_zero P n) hlo hπ hr

theorem scalarCone_dual_one_endpoint_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R)
    (π : Dual R (P.X 1) →ₗ[R] Q)
    (hπ : LinearMap.range (P.d 1 0).hom.dualMap = LinearMap.ker π)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hr : IsSMulRegular Q r) :
    LinearMap.range ((scalarConeComplex P r).d 1 0).hom.dualMap =
      LinearMap.ker ((scalarConeComplex P r).d 2 1).hom.dualMap := by
  apply exact_of_equivalences
    (((scalarConeComplex P r).d 1 0).hom.dualMap)
    (((scalarConeComplex P r).d 2 1).hom.dualMap)
    (dualConeBottom (P.d 1 0).hom r)
    (dualConeDifferential (P.d 2 1).hom (P.d 1 0).hom r)
    (LinearEquiv.refl R (Dual R (P.X 0)))
    (dualProdDualEquivDual R (P.X 1) (P.X 0))
    (dualProdDualEquivDual R (P.X 2) (P.X 1))
  · have hd : (scalarConeComplex P r).d 1 0 = scalarConeMap P r 0 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 0
    rw [hd]
    exact coneBottom_dual_equiv (P.d 1 0).hom r
  · have hd : (scalarConeComplex P r).d 2 1 = scalarConeMap P r 1 :=
      ChainComplex.of_d (scalarConeObject P) (scalarConeMap P r) 1
    rw [hd]
    exact coneDifferential_dual_equiv (P.d 2 1).hom (P.d 1 0).hom r
  · exact dualConeBottom_endpoint_exact _ _ r π (chain_dual_comp_zero P 0) hπ hinj hr

theorem scalarCone_dual_low_exact
    {Q : Type u} [AddCommGroup Q] [Module R Q]
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (r : R) (n : ℕ)
    (π : Dual R (P.X (n + 1)) →ₗ[R] Q)
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π)
    (hr : IsSMulRegular Q r) :
    ∀ k, k < n + 1 →
      LinearMap.range ((scalarConeComplex P r).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((scalarConeComplex P r).d (k + 2) (k + 1)).hom.dualMap := by
  intro k hk
  by_cases hkn : k < n
  · cases k with
    | zero => exact scalarCone_dual_one_exact P r (hlow 0 hkn) hinj
    | succ k =>
      exact scalarCone_dual_interior_exact P r k (hlow k (by omega))
        (hlow (k + 1) hkn)
  · have hkn : k = n := by omega
    subst k
    cases n with
    | zero => exact scalarCone_dual_one_endpoint_exact P r π hπ hinj hr
    | succ n =>
      exact scalarCone_dual_endpoint_exact P r n π (hlow n (by omega)) hπ hr

end PiExponentSiegelAux.W30

end OAI
end Source0267

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceQuotientTail.lean
section Source0268
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceQuotientTail.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.RegularSequenceQuotientTail
open RingTheory.Sequence
open scoped Pointwise

variable {R : Type*} [CommRing R]

theorem principal_image_eq_scalar_top (I : Ideal R) (r : R) :
    Submodule.map I.mkQ (Ideal.span ({r} : Set R)) = r • (⊤ : Submodule R (R ⧸ I)) := by
  have h : r • (⊤ : Ideal R) = Ideal.span ({r} : Set R) := by
    rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  rw [← h, Submodule.map_pointwise_smul, Submodule.map_top, Submodule.range_mkQ]

def quotientTailEquiv (I : Ideal R) (r : R) :
    QuotSMulTop r (R ⧸ I) ≃ₗ[R] R ⧸ (I ⊔ Ideal.span ({r} : Set R)) :=
  (Submodule.quotEquivOfEq _ _ (principal_image_eq_scalar_top I r).symm).trans
    (Submodule.quotientQuotientEquivQuotientSup I (Ideal.span ({r} : Set R)))

@[simp] theorem quotientTailEquiv_mk (I : Ideal R) (r a : R) :
    quotientTailEquiv I r (Submodule.Quotient.mk (Ideal.Quotient.mk I a)) =
      Ideal.Quotient.mk (I ⊔ Ideal.span ({r} : Set R)) a := rfl

theorem regular_quotient_cons_iff (I : Ideal R) (r : R) (rs : List R) :
    IsRegular (R ⧸ I) (r :: rs) ↔
      IsSMulRegular (R ⧸ I) r ∧
        IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs := by
  rw [isRegular_cons_iff]
  exact and_congr_right' ((quotientTailEquiv I r).isRegular_congr rs)

theorem regular_quotient_tail (I : Ideal R) (r : R) (rs : List R)
    (h : IsRegular (R ⧸ I) (r :: rs)) :
    IsRegular (R ⧸ (I ⊔ Ideal.span ({r} : Set R))) rs :=
  ((regular_quotient_cons_iff I r rs).mp h).2

end PiExponentJets.RegularSequenceQuotientTail

end

end OAI
end Source0268

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceDualExactness.lean
section Source0269
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceDualExactness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open Module
open scoped Pointwise
universe u
variable {R : Type u} [CommRing R]

theorem iterateScalarCones_dual_low_exact (rs : List R) (n : ℕ)
    (P : ChainComplex (ModuleCat.{u} R) ℕ) (I : Ideal R)
    (e : P.X (n + 1) ≃ₗ[R] R)
    (hbound : ∀ k, n + 1 < k → Subsingleton (P.X k))
    (hinj : Function.Injective (P.d 1 0).hom.dualMap)
    (hlow : ∀ k, k < n → LinearMap.range (P.d (k + 1) k).hom.dualMap =
      LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap)
    (hI : LinearMap.range
      ((W31.topDualCoordinate e).toLinearMap.comp (P.d (n + 1) n).hom.dualMap) = I)
    (hreg : RingTheory.Sequence.IsRegular (R ⧸ I) rs) :
    ∀ k, k + 1 < n + 1 + rs.length →
      LinearMap.range ((iterateScalarCones P rs).d (k + 1) k).hom.dualMap =
        LinearMap.ker ((iterateScalarCones P rs).d (k + 2) (k + 1)).hom.dualMap := by
  induction rs generalizing n P I with
  | nil =>
    intro k hk
    exact hlow k (by simpa using hk)
  | cons r rs ih =>
    let P' := scalarConeComplex P r
    let I' := I ⊔ Ideal.span {r}
    let e' : P'.X (n + 2) ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv P r (n + 1) hbound).trans e
    let π : Dual R (P.X (n + 1)) →ₗ[R] (R ⧸ I) :=
      I.mkQ.comp (W31.topDualCoordinate e).toLinearMap
    have hπ : LinearMap.range (P.d (n + 1) n).hom.dualMap = LinearMap.ker π :=
      coordinate_quotient_exact _ (W31.topDualCoordinate e) I hI
    have hr : IsSMulRegular (R ⧸ I) r :=
      ((RingTheory.Sequence.isRegular_cons_iff (R ⧸ I) r rs).mp hreg).1
    have htail : RingTheory.Sequence.IsRegular (R ⧸ I') rs :=
      PiExponentJets.RegularSequenceQuotientTail.regular_quotient_tail I r rs hreg
    have hbound' : ∀ k, n + 2 < k → Subsingleton (P'.X k) :=
      scalarCone_bounded P r (n + 1) hbound
    have hinj' : Function.Injective (P'.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective P r hinj
    have hlow' : ∀ k, k < n + 1 → LinearMap.range (P'.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P'.d (k + 2) (k + 1)).hom.dualMap :=
      scalarCone_dual_low_exact P r n π hinj hlow hπ hr
    have hI' : LinearMap.range
        ((W31.topDualCoordinate e').toLinearMap.comp (P'.d (n + 2) (n + 1)).hom.dualMap) = I' :=
      scalarCone_top_dual_image P r n hbound e I hI
    have h := ih (n + 1) P' I' e' hbound' hinj' hlow' hI' htail
    intro k hk
    exact h k (by simp only [List.length_cons] at hk; omega)

theorem regularSequenceComplex_dual_low_exact (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    LinearMap.range ((regularSequenceComplex rs).d (n + 1) n).hom.dualMap =
      LinearMap.ker ((regularSequenceComplex rs).d (n + 2) (n + 1)).hom.dualMap := by
  cases rs with
  | nil => simp at hn
  | cons r rs =>
    obtain ⟨hr, htail⟩ := (RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg
    have hJ : r • (⊤ : Submodule R R) = Ideal.span ({r} : Set R) := by
      rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul]
      exact Ideal.mul_top _
    change RingTheory.Sequence.IsRegular (R ⧸ (r • (⊤ : Submodule R R))) rs at htail
    rw [hJ] at htail
    let E := emptyKoszulComplex (R := R)
    have hb : ∀ k, 0 < k → Subsingleton (E.X k) :=
      fun k hk => regularSequenceComplex_bounded ([] : List R) k hk
    let P := scalarConeComplex E r
    let e : P.X 1 ≃ₗ[R] R :=
      (W31.scalarConeTopEquiv E r 0 hb).trans (LinearEquiv.refl R R)
    have hbound : ∀ k, 1 < k → Subsingleton (P.X k) :=
      scalarCone_bounded E r 0 hb
    have hinj : Function.Injective (P.d 1 0).hom.dualMap :=
      scalarCone_dual_zero_injective_of_regular E r hr
    have hlow : ∀ k, k < 0 → LinearMap.range (P.d (k + 1) k).hom.dualMap =
        LinearMap.ker (P.d (k + 2) (k + 1)).hom.dualMap := by
      intro k hk
      omega
    have hI : LinearMap.range
        ((W31.topDualCoordinate e).toLinearMap.comp (P.d 1 0).hom.dualMap) =
          Ideal.span ({r} : Set R) :=
      scalarCone_first_top_dual_image E r hb (LinearEquiv.refl R R)
    have h := iterateScalarCones_dual_low_exact rs 0 P (Ideal.span {r})
      e hbound hinj hlow hI htail
    exact h n (by simp only [List.length_cons] at hn; omega)

end PiExponentSiegelAux.W30

end

end OAI
end Source0269

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceHomZero.lean
section Source0270
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceHomZero.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegelAux.W30
open Module
variable {R : Type*} [CommRing R]

theorem quotient_dual_eq_zero_of_regular (I : Ideal R) (r : R) (hrI : r ∈ I)
    (hr : IsSMulRegular R r) (φ : Dual R (R ⧸ I)) : φ = 0 := by
  apply LinearMap.ext
  intro x
  apply hr
  change r • φ x = r • (0 : R)
  rw [smul_zero, ← φ.map_smul]
  have hx : r • x = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.mkQ_surjective I x
    change r • (Submodule.Quotient.mk a : R ⧸ I) = 0
    rw [← Submodule.Quotient.mk_smul I]
    apply (Submodule.Quotient.mk_eq_zero I).mpr
    simpa only [smul_eq_mul, mul_comm] using I.smul_mem a hrI
  rw [hx, map_zero]

theorem regularSequenceQuotient_dual_subsingleton (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Dual R (R ⧸ Ideal.ofList rs)) := by
  cases rs with
  | nil => exact (hne rfl).elim
  | cons r rs =>
    apply subsingleton_of_forall_eq 0
    intro φ
    apply quotient_dual_eq_zero_of_regular (Ideal.ofList (r :: rs)) r
    · exact Ideal.subset_span (by simp)
    · exact ((RingTheory.Sequence.isRegular_cons_iff R r rs).mp hreg).1

end PiExponentSiegelAux.W30

end OAI
end Source0270

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceLowExt.lean
section Source0271
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularSequenceLowExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u
variable {R : Type u} [CommRing R]

theorem regularSequenceQuotientExt_positive_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n + 1 < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) (n + 1)) :=
  W31.regularSequenceQuotientExt_of_dual_exact rs hreg n
    (regularSequenceComplex_dual_low_exact rs hreg n hn)

theorem regularSequenceQuotientExt_zero (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (hne : rs ≠ []) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) 0) := by
  let := regularSequenceQuotient_dual_subsingleton rs hreg hne
  refine ⟨fun a b => Ext.homEquiv₀.injective ?_⟩
  apply ModuleCat.hom_ext
  exact Subsingleton.elim _ _

theorem regularSequenceQuotientExt_below_length (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs) (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (R ⧸ Ideal.ofList rs)) (ModuleCat.of R R) n) := by
  cases n with
  | zero =>
    apply regularSequenceQuotientExt_zero rs hreg
    intro h
    simp [h] at hn
  | succ n => exact regularSequenceQuotientExt_positive_below_length rs hreg n hn

theorem residueFieldExt_below_regular_length [IsLocalRing R] (rs : List R)
    (hreg : RingTheory.Sequence.IsRegular R rs)
    (hmax : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (n : ℕ) (hn : n < rs.length) :
    Subsingleton (Ext (ModuleCat.of R (IsLocalRing.ResidueField R)) (ModuleCat.of R R) n) := by
  change Subsingleton (Ext (ModuleCat.of R (R ⧸ IsLocalRing.maximalIdeal R)) (ModuleCat.of R R) n)
  rw [← hmax]
  exact regularSequenceQuotientExt_below_length rs hreg n hn

end PiExponentSiegelAux.W30

end

end OAI
end Source0271

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialCoordinateMinpolyQuotient.lean
section Source0272
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialCoordinateMinpolyQuotient.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSiegel.W08

open Polynomial

variable {K : Type*} [Field K]

noncomputable def coordinatePolynomialSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin n) K) :=
  MvPolynomial.finSuccEquiv K n

noncomputable def coordinateCoefficientSplit (n : ℕ) :
    MvPolynomial (Fin (n + 1)) K ≃ₐ[K] MvPolynomial (Fin n) K[X] :=
  (MvPolynomial.renameEquiv K (_root_.finSuccEquiv n)).trans
    (MvPolynomial.optionEquivRight K (Fin n))

@[simp] theorem coordinateCoefficientSplit_X_zero (n : ℕ) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X 0) = MvPolynomial.C Polynomial.X := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_X_succ (n : ℕ) (i : Fin n) :
    coordinateCoefficientSplit (K := K) n (MvPolynomial.X i.succ) = MvPolynomial.X i := by
  simp [coordinateCoefficientSplit]

@[simp] theorem coordinateCoefficientSplit_C (n : ℕ) (a : K) :
    coordinateCoefficientSplit n (MvPolynomial.C a) = MvPolynomial.C (Polynomial.C a) := by
  simp [coordinateCoefficientSplit]

theorem coordinateCoefficientSplit_aeval (n : ℕ) (f : K[X]) :
    coordinateCoefficientSplit n (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f) =
      MvPolynomial.C f := by
  have h : (coordinateCoefficientSplit (K := K) n).toAlgHom.comp
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))) =
      IsScalarTower.toAlgHom K K[X] (MvPolynomial (Fin n) K[X]) := by
    apply Polynomial.algHom_ext
    change coordinateCoefficientSplit n
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) Polynomial.X) =
      MvPolynomial.C Polynomial.X
    rw [Polynomial.aeval_X, coordinateCoefficientSplit_X_zero]
  exact AlgHom.congr_fun h f

noncomputable def coordinateMinpolyIdeal (n : ℕ) (f : K[X]) :
    Ideal (MvPolynomial (Fin (n + 1)) K) :=
  Ideal.span {Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1))) f}

theorem coordinateMinpolyIdeal_map (n : ℕ) (f : K[X]) :
    (coordinateMinpolyIdeal n f).map (coordinateCoefficientSplit n).toRingEquiv.toRingHom =
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X]) := by
  simp only [coordinateMinpolyIdeal, Ideal.map_span, Set.image_singleton]
  congr 1
  exact congrArg Set.singleton (coordinateCoefficientSplit_aeval n f)

noncomputable def coefficientAdjoinRootQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin n) K[X] ⧸
      (Ideal.span {f}).map (MvPolynomial.C : K[X] →+* MvPolynomial (Fin n) K[X])) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  ((MvPolynomial.quotientEquivQuotientMvPolynomial
    (σ := Fin n) (Ideal.span {f} : Ideal K[X])).symm).restrictScalars K

@[simp] theorem coefficientAdjoinRootQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin n) K[X]) :
    coefficientAdjoinRootQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) p := by
  rw [MvPolynomial.map_eq_eval₂Hom_C_comp]
  rfl

noncomputable def coordinateMinpolyQuotientEquiv (n : ℕ) (f : K[X]) :
    (MvPolynomial (Fin (n + 1)) K ⧸ coordinateMinpolyIdeal n f) ≃ₐ[K]
      MvPolynomial (Fin n) (AdjoinRoot f) :=
  (Ideal.quotientEquivAlg (coordinateMinpolyIdeal n f) _
    (coordinateCoefficientSplit n) (coordinateMinpolyIdeal_map n f).symm).trans
      (coefficientAdjoinRootQuotientEquiv n f)

theorem coordinateMinpolyQuotientEquiv_mk (n : ℕ) (f : K[X])
    (p : MvPolynomial (Fin (n+1)) K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ p) =
      MvPolynomial.map (AdjoinRoot.mk f) (coordinateCoefficientSplit n p) := by
  change coefficientAdjoinRootQuotientEquiv n f
    (Ideal.Quotient.mk _ (coordinateCoefficientSplit n p)) = _
  exact coefficientAdjoinRootQuotientEquiv_mk n f (coordinateCoefficientSplit n p)

@[simp] theorem coordinateMinpolyQuotientEquiv_X_zero (n : ℕ) (f : K[X]) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X 0)) =
      MvPolynomial.C (AdjoinRoot.root f) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_zero]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_X_succ (n : ℕ) (f : K[X]) (i : Fin n) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.X i.succ)) =
      MvPolynomial.X i := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_X_succ]
  simp

@[simp] theorem coordinateMinpolyQuotientEquiv_C (n : ℕ) (f : K[X]) (a : K) :
    coordinateMinpolyQuotientEquiv n f (Ideal.Quotient.mk _ (MvPolynomial.C a)) =
      MvPolynomial.C (algebraMap K (AdjoinRoot f) a) := by
  rw [coordinateMinpolyQuotientEquiv_mk, coordinateCoefficientSplit_C]
  simp

theorem coordinateMinpolyIdeal_le_of_mem_contraction (n : ℕ) (f : K[X])
    (m : Ideal (MvPolynomial (Fin (n+1)) K))
    (hf : f ∈ m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n+1)))).toRingHom) :
    coordinateMinpolyIdeal n f ≤ m := by
  apply Ideal.span_le.mpr
  intro p hp
  obtain rfl := Set.mem_singleton_iff.mp hp
  exact hf

end PiExponentSiegel.W08

end OAI
end Source0272

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParameters.lean
section Source0273
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParameters.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
open scoped Pointwise

variable {R S : Type*} [CommRing R] [CommRing S]

theorem scalar_top_eq_principal (r : R) :
    r • (⊤ : Ideal R) = Ideal.span {r} := by
  rw [← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]

def principalModuleQuotientEquiv (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) : QuotSMulTop r R ≃+* S :=
  (Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm)).trans
    (RingHom.quotientKerEquivOfSurjective hπ)

@[simp] theorem principalModuleQuotientEquiv_mk (π : R →+* S)
    (hπ : Function.Surjective π) (r : R) (hker : RingHom.ker π = Ideal.span {r}) (x : R) :
    principalModuleQuotientEquiv π hπ r hker (Submodule.Quotient.mk x) = π x := by
  change (RingHom.quotientKerEquivOfSurjective hπ)
    ((Ideal.quotEquivOfEq ((scalar_top_eq_principal r).trans hker.symm))
      (Ideal.Quotient.mk (r • (⊤ : Ideal R)) x)) = π x
  rw [Ideal.quotEquivOfEq_mk, RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem regular_cons_of_principal_kernel (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (xs : List R) (hxs : IsRegular S (xs.map π)) : IsRegular R (r :: xs) := by
  let e := principalModuleQuotientEquiv π hπ r hker
  apply IsRegular.cons hr
  apply (e.toAddEquiv.isRegular_congr ?_).mpr hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    change e (Submodule.Quotient.mk (a * z)) = π a * e (Submodule.Quotient.mk z)
    calc
      e (Submodule.Quotient.mk (a * z)) = π (a * z) :=
        principalModuleQuotientEquiv_mk π hπ r hker (a * z)
      _ = π a * π z := π.map_mul a z
      _ = π a * e (Submodule.Quotient.mk z) :=
        congrArg (fun y : S => π a * y)
          (principalModuleQuotientEquiv_mk π hπ r hker z).symm

theorem ofList_cons_eq_comap (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (xs : List R) :
    Ideal.ofList (r :: xs) = Ideal.comap π (Ideal.ofList (xs.map π)) := by
  rw [← Ideal.map_ofList, Ideal.comap_map_of_surjective π hπ, Ideal.ofList_cons]
  change Ideal.span {r} ⊔ Ideal.ofList xs = Ideal.ofList xs ⊔ RingHom.ker π
  rw [hker, sup_comm]

theorem lift_parameters [IsLocalRing R] [IsLocalRing S]
    (π : R →+* S) (hπ : Function.Surjective π)
    (r : R) (hker : RingHom.ker π = Ideal.span {r}) (hr : IsSMulRegular R r)
    (ys : List S) (hys : IsRegular S ys)
    (hspan : Ideal.ofList ys = IsLocalRing.maximalIdeal S) :
    ∃ xs : List R, xs.length = ys.length + 1 ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R := by
  obtain ⟨xs, hxs⟩ := (List.map_surjective_iff.mpr hπ) ys
  refine ⟨r :: xs, ?_, ?_, ?_⟩
  · simpa using congrArg (fun zs : List S => zs.length + 1) hxs
  · apply regular_cons_of_principal_kernel π hπ r hker hr xs
    simpa [hxs] using hys
  · rw [ofList_cons_eq_comap π hπ r hker xs, hxs, hspan]
    let : IsLocalHom π := IsLocalHom.of_surjective π hπ
    exact IsLocalRing.maximalIdeal_comap π

theorem regular_element_of_ne_zero [IsDomain R] (r : R) (hr : r ≠ 0) : IsSMulRegular R r :=
  fun _ _ h => mul_left_cancel₀ hr h

section OneVariable
variable (K : Type*) [Field K] (m : Ideal (Polynomial K)) [m.IsMaximal]

def firstPolynomial : Polynomial K := Submodule.IsPrincipal.generator m

def firstLocalParameter : Localization.AtPrime m :=
  algebraMap (Polynomial K) (Localization.AtPrime m) (firstPolynomial K m)

end OneVariable

section ZeroVariables
variable (K : Type*) [Field K] (m : Ideal (MvPolynomial (Fin 0) K)) [m.IsMaximal]

theorem zeroVariable_maximal_eq_bot : m = ⊥ := by
  apply le_antisymm
  · intro p hp
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) p
    by_cases hc : c = 0
    · simp [hc]
    · have hu : IsUnit (MvPolynomial.C c : MvPolynomial (Fin 0) K) :=
        (isUnit_iff_ne_zero.mpr hc).map MvPolynomial.C
      exact False.elim ((inferInstance : m.IsMaximal).ne_top (m.eq_top_of_isUnit_mem hp hu))
  · exact bot_le

theorem zeroVariable_parameters :
    ∃ xs : List (Localization.AtPrime m), xs.length = 0 ∧
      IsRegular (Localization.AtPrime m) xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  refine ⟨[], rfl, IsRegular.nil _ _, ?_⟩
  rw [Ideal.ofList_nil, ← Localization.AtPrime.map_eq_maximalIdeal]
  simpa only [Ideal.map_bot] using
    (congrArg (Ideal.map
      (algebraMap (MvPolynomial (Fin 0) K) (Localization.AtPrime m)))
      (zeroVariable_maximal_eq_bot K m)).symm

end ZeroVariables

variable (K : Type*) [Field K] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin (n + 1)) K)) [m.IsMaximal]

theorem maximal_coefficient_contraction {A : Type*} [CommRing A] [IsJacobsonRing A]
    (j : ℕ) (q : Ideal (MvPolynomial (Fin j) A)) [q.IsMaximal] :
    (q.comap (MvPolynomial.C : A →+* MvPolynomial (Fin j) A)).IsMaximal := by
  rw [← @Ideal.mk_ker _ _ q, RingHom.ker_eq_comap_bot, Ideal.comap_comap]
  let := (Ideal.bot_quotient_isMaximal_iff _).mpr (inferInstance : q.IsMaximal)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _
    (MvPolynomial.quotient_mk_comp_C_isIntegral_of_isJacobsonRing q) ⊥

def firstCoordinateContraction : Ideal (Polynomial K) :=
  m.comap (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom

theorem firstCoordinateContraction_isMaximal : (firstCoordinateContraction K n m).IsMaximal := by
  let e := PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n
  let q := m.comap e.symm.toRingEquiv.toRingHom
  let : q.IsMaximal := Ideal.comap_isMaximal_of_surjective _ e.symm.surjective
  have he : e.symm.toRingEquiv.toRingHom.comp MvPolynomial.C =
      (Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)))).toRingHom := by
    apply RingHom.ext
    intro f
    change e.symm (MvPolynomial.C f) =
      Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    apply e.symm_apply_eq.mpr
    exact (PiExponentSiegel.W08.coordinateCoefficientSplit_aeval n f).symm
  have hq := maximal_coefficient_contraction n q
  simpa only [q, Ideal.comap_comap, he, firstCoordinateContraction] using hq

def firstCoordinatePolynomial : Polynomial K :=
  Submodule.IsPrincipal.generator (firstCoordinateContraction K n m)

theorem firstCoordinatePolynomial_irreducible : Irreducible (firstCoordinatePolynomial K n m) := by
  let := firstCoordinateContraction_isMaximal K n m
  apply (Submodule.IsPrincipal.prime_generator_of_isPrime
    (firstCoordinateContraction K n m) ?_).irreducible
  exact Ring.ne_bot_of_isMaximal_of_not_isField
    (firstCoordinateContraction_isMaximal K n m) (Polynomial.not_isField K)

omit [m.IsMaximal] in
theorem firstCoordinatePolynomial_mem :
    firstCoordinatePolynomial K n m ∈ firstCoordinateContraction K n m :=
  Submodule.IsPrincipal.generator_mem _

omit [m.IsMaximal] in
theorem firstCoordinateIdeal_le :
    PiExponentSiegel.W08.coordinateMinpolyIdeal n (firstCoordinatePolynomial K n m) ≤ m :=
  PiExponentSiegel.W08.coordinateMinpolyIdeal_le_of_mem_contraction n
    (firstCoordinatePolynomial K n m) m (firstCoordinatePolynomial_mem K n m)

theorem firstCoordinateRelation_ne_zero :
    Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) K)
      (firstCoordinatePolynomial K n m) ≠ 0 := by
  intro h
  have h' := congrArg (PiExponentSiegel.W08.coordinateCoefficientSplit (K := K) n) h
  rw [PiExponentSiegel.W08.coordinateCoefficientSplit_aeval, map_zero] at h'
  apply (firstCoordinatePolynomial_irreducible K n m).ne_zero
  simpa using h'

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end Source0273

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParametersAssembly.lean
section Source0274
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParametersAssembly.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence
universe u

theorem polynomialMaximal_regularParameters (n : ℕ) :
    ∀ (K : Type u) [Field K] (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal],
      ∃ xs : List (Localization.AtPrime m), xs.length = n ∧
        IsRegular (Localization.AtPrime m) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime m) := by
  induction n with
  | zero =>
    intro K _ m _
    exact zeroVariable_parameters K m
  | succ n ih =>
    intro K _ m _
    let A := MvPolynomial (Fin (n + 1)) K
    let f : Polynomial K := firstCoordinatePolynomial K n m
    let : Fact (Irreducible f) := ⟨firstCoordinatePolynomial_irreducible K n m⟩
    let I : Ideal A := PiExponentSiegel.W08.coordinateMinpolyIdeal n f
    have hI : I ≤ m := firstCoordinateIdeal_le K n m
    let e := (PiExponentSiegel.W08.coordinateMinpolyQuotientEquiv n f).toRingEquiv
    let qm := PiExponentSiegel.W23.quotientParameterPrime I m hI
    let p : Ideal (MvPolynomial (Fin n) (AdjoinRoot f)) := qm.map e.toRingHom
    let : p.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le
      (f := e.toRingHom) (m := qm) e.surjective (by simp)
    obtain ⟨ys, hylen, hyreg, hyspan⟩ := ih (AdjoinRoot f) p
    let J : Ideal (Localization.AtPrime m) := PiExponentSiegel.W23.parameterLocalizedIdeal I m
    let E : (Localization.AtPrime m ⧸ J) ≃+* Localization.AtPrime p :=
      PiExponentSiegel.W23.localizationQuotientParametersEquivTrans I m hI e
    let π : Localization.AtPrime m →+* Localization.AtPrime p :=
      E.toRingHom.comp (Ideal.Quotient.mk J)
    have hπ : Function.Surjective π := E.surjective.comp Ideal.Quotient.mk_surjective
    let g : A := Polynomial.aeval (MvPolynomial.X (0 : Fin (n + 1))) f
    let r : Localization.AtPrime m := algebraMap A (Localization.AtPrime m) g
    have hg : g ≠ 0 := firstCoordinateRelation_ne_zero K n m
    have hr : r ≠ 0 :=
      (FaithfulSMul.algebraMap_eq_zero_iff A (Localization.AtPrime m)).not.mpr hg
    have hker : RingHom.ker π = Ideal.span {r} := by
      rw [show π = E.toRingHom.comp (Ideal.Quotient.mk J) from rfl,
        RingHom.ker_comp_of_injective _ E.injective, Ideal.mk_ker]
      change (Ideal.span {g}).map (algebraMap A (Localization.AtPrime m)) = Ideal.span {r}
      rw [Ideal.map_span, Set.image_singleton]
    obtain ⟨xs, hxlen, hxreg, hxspan⟩ := lift_parameters π hπ r hker
      (regular_element_of_ne_zero r hr) ys hyreg hyspan
    refine ⟨xs, ?_, hxreg, hxspan⟩
    simpa [hylen] using hxlen

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end Source0274
