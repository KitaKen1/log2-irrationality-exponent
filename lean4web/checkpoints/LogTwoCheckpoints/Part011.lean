/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part003
public import LogTwoCheckpoints.Part004
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part008
public import LogTwoCheckpoints.Part009
public import LogTwoCheckpoints.Part010
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.FunctionField
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.Localization.AtPrime.Extension
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParametersTransport.lean
section Source0275
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TriangularLocalParametersTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W10.TriangularLocalParameters

open RingTheory.Sequence

variable {R S : Type*} [CommRing R] [CommRing S]

theorem regular_map_ringEquiv (e : R ≃+* S) (xs : List R)
    (hxs : IsRegular R xs) : IsRegular S (xs.map e.toRingHom) := by
  apply (e.toAddEquiv.isRegular_congr ?_).mp hxs
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro a _ z
  exact e.map_mul a z

theorem regularParameters_transport [IsLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) (n : ℕ)
    (h : ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R) :
    ∃ ys : List S, ys.length = n ∧ IsRegular S ys ∧
      Ideal.ofList ys = IsLocalRing.maximalIdeal S := by
  obtain ⟨xs, hlen, hreg, hspan⟩ := h
  refine ⟨xs.map e.toRingHom, ?_, regular_map_ringEquiv e xs hreg, ?_⟩
  · simpa using hlen
  · rw [← Ideal.map_ofList, hspan]
    exact IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective

theorem polynomialMaximal_regularParameters_of_ringEquiv (n : ℕ) (K : Type*) [Field K]
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal]
    [IsLocalRing R] (e : R ≃+* Localization.AtPrime m) :
    ∃ xs : List R, xs.length = n ∧ IsRegular R xs ∧
      Ideal.ofList xs = IsLocalRing.maximalIdeal R :=
  regularParameters_transport e.symm n (polynomialMaximal_regularParameters n K m)

end PiExponentSiegel.W10.TriangularLocalParameters

end

end OAI
end Source0275

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalRegularParameters.lean
section Source0276
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalRegularParameters.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable (K : Type*) [Field K] (n : ℕ)
variable (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]

theorem exists_regularParameters_actual_height :
    ∃ h : ℕ, Q.height = (h : ℕ∞) ∧
      ∃ xs : List (Localization.AtPrime Q),
        xs.length = h ∧ RingTheory.Sequence.IsRegular (Localization.AtPrime Q) xs ∧
        Ideal.ofList xs = IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  classical
  obtain ⟨t, j, htfinite, hj, hcoord, ht⟩ := exists_coordinate_basis_indices K n Q
  let A := RemainingCoordinate j
  let F := SplitCoefficientField K t
  let Qs := coordinateSplitPrime K Q t j hj
  let hB := coordinateSplitPrime_basis K Q t j hj hcoord ht
  let m₀ := closedPolynomialIdeal K A t Qs hB
  let : m₀.IsMaximal := closedPolynomialIdeal_isMaximal K A t Qs hB
  let e₀ : Localization.AtPrime Q ≃+* Localization.AtPrime m₀ :=
    coordinateBasisClosedPointEquiv K Q t j hj hcoord ht
  let h := Fintype.card A
  let eFin : MvPolynomial A F ≃ₐ[F] MvPolynomial (Fin h) F :=
    MvPolynomial.renameEquiv F (Fintype.equivFin A)
  let m : Ideal (MvPolynomial (Fin h) F) := m₀.map eFin.toRingHom
  let : m.IsMaximal := (inferInstance : m₀.IsMaximal).map_bijective eFin.toRingHom eFin.bijective
  let e : Localization.AtPrime Q ≃+* Localization.AtPrime m :=
    e₀.trans (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv eFin.toRingEquiv m₀)
  have hheight : Q.height = (h : ℕ∞) := by
    have he := ringKrullDim_eq_of_ringEquiv e
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q),
      IsLocalization.AtPrime.ringKrullDim_eq_height m (Localization.AtPrime m),
      PiExponentSiegelAux.W09.polynomialMaximal_height F h m] at he
    exact WithBot.coe_injective he
  refine ⟨h, hheight, ?_⟩
  exact PiExponentSiegel.W10.TriangularLocalParameters.polynomialMaximal_regularParameters_of_ringEquiv
    h F m e

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0276

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalLowExt.lean
section Source0277
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialLocalLowExt.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W30
open CategoryTheory CategoryTheory.Abelian
universe u

theorem polynomialLocal_residueExt_below_height
    (K : Type u) [Field K] (n : ℕ)
    (Q : Ideal (MvPolynomial (Fin n) K)) [Q.IsPrime]
    (i : ℕ) (hi : (i : ℕ∞) < Q.height) :
    Subsingleton (Ext
      (ModuleCat.of (Localization.AtPrime Q)
        (IsLocalRing.ResidueField (Localization.AtPrime Q)))
      (ModuleCat.of (Localization.AtPrime Q) (Localization.AtPrime Q)) i) := by
  obtain ⟨h, hh, xs, hlen, hreg, hmax⟩ :=
    PiExponentJets.PolynomialLocalResidueResolution.exists_regularParameters_actual_height K n Q
  apply residueFieldExt_below_regular_length xs hreg hmax i
  rw [hlen]
  exact ENat.natCast_lt_natCast.mp (by simpa only [hh] using hi)

end PiExponentSiegelAux.W30

end

end OAI
end Source0277

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection.lean
section Source0278
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RegularParameterSelection.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
universe u
open IsLocalRing RingTheory.Sequence CategoryTheory CategoryTheory.Abelian
namespace PiExponentSiegel.W58

variable (k : Type u) [Field k] (n : ℕ)
variable (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]

theorem polynomialLocal_regular_prefix_maximal_not_associated
    (rs : List (Localization.AtPrime P))
    (hreg : IsRegular (Localization.AtPrime P) rs)
    (hshort : (rs.length : ℕ∞) < P.height) :
    ¬ IsAssociatedPrime (maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P ⧸ Ideal.ofList rs) := by
  intro hass
  obtain ⟨i, hi, hnonzero⟩ :=
    PiExponentJets.W18.regular_sequence_associatedPrime_ext_obstruction
      rs hreg (maximalIdeal (Localization.AtPrime P)) hass
  have hile : (i : ℕ∞) ≤ rs.length := by exact_mod_cast hi
  have hvanish := PiExponentSiegelAux.W30.polynomialLocal_residueExt_below_height
    k n P i (hile.trans_lt hshort)
  change Subsingleton (Ext
    (ModuleCat.of (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ maximalIdeal (Localization.AtPrime P)))
    (ModuleCat.of (Localization.AtPrime P) (Localization.AtPrime P)) i) at hvanish
  exact hnonzero hvanish

variable [Infinite k]

theorem polynomialLocal_exists_constant_regular_parameters
    {J : Type*} (generators : J → Localization.AtPrime P)
    (hrad : (Ideal.span (Set.range generators)).radical =
      maximalIdeal (Localization.AtPrime P))
    (h : ℕ) (hheight : P.height = (h : ℕ∞)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      IsRegular (Localization.AtPrime P)
        (cs.map (Finsupp.linearCombination k generators)) ∧
      Ideal.ofList (cs.map (Finsupp.linearCombination k generators)) ≤
        Ideal.span (Set.range generators) ∧
      (Ideal.ofList (cs.map (Finsupp.linearCombination k generators))).radical =
        maximalIdeal (Localization.AtPrime P) := by
  apply exists_constant_regular_parameters_of_no_maximal_associated
    (k := k) generators hrad h
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height P (Localization.AtPrime P), hheight]
    rfl
  · intro rs hreg hshort
    apply polynomialLocal_regular_prefix_maximal_not_associated k n P rs hreg
    rw [hheight]
    exact_mod_cast hshort

theorem polynomialLocal_exists_degree_bounded_regular_parameters
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (d h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ d)
    (hheight : P.height = (h : ℕ∞))
    (hrad : ((Ideal.span (Set.range f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
        maximalIdeal (Localization.AtPrime P)) :
    ∃ cs : List (J →₀ k), cs.length = h ∧
      let gs := cs.map (Finsupp.linearCombination k f)
      gs.length = h ∧
      (∀ g ∈ gs, g.totalDegree ≤ d) ∧
      Ideal.ofList gs ≤ Ideal.span (Set.range f) ∧
      IsRegular (Localization.AtPrime P)
        (gs.map (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ∧
      ((Ideal.ofList gs).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))).radical =
          maximalIdeal (Localization.AtPrime P) := by
  let φ : MvPolynomial (Fin n) k →ₐ[k] Localization.AtPrime P :=
    IsScalarTower.toAlgHom k (MvPolynomial (Fin n) k) (Localization.AtPrime P)
  have hgen : (Ideal.span (Set.range (φ ∘ f))).radical =
      maximalIdeal (Localization.AtPrime P) := by
    change (Ideal.span (Set.range
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P) ∘ f))).radical = _
    simpa only [Ideal.map_span, ← Set.range_comp] using hrad
  obtain ⟨cs, hlen, hreg, _, hmax⟩ :=
    polynomialLocal_exists_constant_regular_parameters k n P (φ ∘ f) hgen h hheight
  have hmap : (cs.map (Finsupp.linearCombination k f)).map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P)) =
      cs.map (Finsupp.linearCombination k (φ ∘ f)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    exact Finsupp.apply_linearCombination k φ.toLinearMap f c
  refine ⟨cs, hlen, by simpa only [List.length_map] using hlen, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_totalDegree_le f c hdegree
  · apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hg
    exact PiExponentJets.W22.linearCombination_mem_ideal f c _
      (fun j => Ideal.subset_span (Set.mem_range_self j))
  · rwa [hmap]
  · rwa [Ideal.map_ofList, hmap]

end PiExponentSiegel.W58

end

end OAI
end Source0278

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean
section Source0279
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent

open PiExponentJets.W22

theorem localIsolatedBezout
    (k : Type) [Field k] [Infinite k] (n : ℕ)
    {J : Type*} (f : J → MvPolynomial (Fin n) k) (D h : ℕ)
    (hdegree : ∀ j, (f j).totalDegree ≤ D)
    (P : Ideal (MvPolynomial (Fin n) k)) [P.IsPrime]
    (hminimal : P ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (hheight : P.height = (h : ℕ∞)) (hbound : h ≤ n) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ (Ideal.span (Set.range f)).map
        (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime P))) ≤
      ((D ^ h : ℕ) : ℕ∞) := by
  have hrad := localized_radical_eq_maximal_of_mem_minimalPrimes
    (Ideal.span (Set.range f)) P hminimal
  obtain ⟨cs, _hcslength, hgslen, hgsdegree, hgscontained, hgsreg, hgsrad⟩ :=
    PiExponentSiegel.W58.polynomialLocal_exists_degree_bounded_regular_parameters
      k n P f D h hdegree hheight hrad
  let gs := cs.map (Finsupp.linearCombination k f)
  have hlen : gs.length = h := hgslen
  have hgsmin : P ∈ (Ideal.ofList gs).minimalPrimes :=
    mem_minimalPrimes_of_localized_radical (Ideal.ofList gs) P hgsrad
  have hselected := affine_local_regular_list_bezout n P gs D
    hgsdegree hgsreg (hlen.le.trans hbound) hgsmin
  have htransfer := ideal_quotient_length_le_of_bound
    (Ideal.map_mono hgscontained) hselected
  simpa only [hlen] using htransfer

end PiExponent

end OAI
end Source0279

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedLocalization.lean
section Source0280
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedLocalization.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing

theorem scalarLocalization_isAtPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    (Rₚ Sₚ : Type*) [CommRing Rₚ] [CommRing Sₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ]
    [Algebra S Sₚ] [IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) Sₚ]
    [Algebra R Sₚ] [Algebra Rₚ Sₚ]
    [IsScalarTower R S Sₚ] [IsScalarTower R Rₚ Sₚ]
    [Algebra.IsIntegral Rₚ Sₚ]
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    IsLocalization.AtPrime Sₚ P := by
  let M := Algebra.algebraMapSubmonoid S p.primeCompl
  have hmapmax : (P.map (algebraMap S Sₚ)).IsMaximal :=
    IsLocalization.isMaximal_of_isMaximal_disjoint M Sₚ P
      (Ideal.disjoint_primeCompl_of_liesOver P p)
  have huniqueMax : ∀ Q : Ideal Sₚ, Q.IsMaximal → Q = P.map (algebraMap S Sₚ) := by
    intro Q hQ
    let : Q.IsMaximal := hQ
    have hQP : Q.LiesOver (maximalIdeal Rₚ) :=
      (IsLocalization.AtPrime.mem_primesOver_of_isPrime Rₚ Sₚ).2
    let : Q.LiesOver (maximalIdeal Rₚ) := hQP
    have hQp : (Q.under S).LiesOver p :=
      IsLocalization.AtPrime.liesOver_comap_of_liesOver p Rₚ Q
    let : (Q.under S).LiesOver p := hQp
    have hEq : Q.under S = P :=
      hunique (Q.under S) inferInstance (Ideal.over_def (Q.under S) p).le
    calc
      Q = (Q.under S).map (algebraMap S Sₚ) := (IsLocalization.map_under M Sₚ Q).symm
      _ = P.map (algebraMap S Sₚ) := by rw [hEq]
  let : IsLocalRing Sₚ := IsLocalRing.of_unique_max_ideal
    ⟨P.map (algebraMap S Sₚ), hmapmax, huniqueMax⟩
  have hmax : maximalIdeal Sₚ = P.map (algebraMap S Sₚ) :=
    (IsLocalRing.eq_maximalIdeal hmapmax).symm
  have hcomap : (maximalIdeal Sₚ).under S = P := by
    rw [hmax]
    exact IsLocalization.AtPrime.under_map_of_isMaximal S p Sₚ P
  apply IsLocalization.of_le M P.primeCompl
  · intro x hx
    exact fun hmem => Set.disjoint_left.mp (Ideal.disjoint_primeCompl_of_liesOver P p) hx hmem
  · intro r hr
    by_contra hu
    have hm : algebraMap S Sₚ r ∈ maximalIdeal Sₚ := hu
    have hrmem : r ∈ P := by
      rw [← hcomap]
      exact hm
    exact hr hrmem

noncomputable def basis_atPrime_of_unique_fibre
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (P : Ideal S) [P.IsMaximal] [P.LiesOver p]
    [Algebra (Localization.AtPrime p) (Localization.AtPrime P)]
    [IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime P)]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι R S)
    (hunique : ∀ Q : Ideal S, Q.IsPrime → p ≤ Q.under R → Q = P) :
    Module.Basis ι (Localization.AtPrime p) (Localization.AtPrime P) := by
  let : Module.Finite R S := Module.Finite.of_basis b
  let T := Localization (Algebra.algebraMapSubmonoid S p.primeCompl)
  let : IsLocalization.AtPrime T P :=
    scalarLocalization_isAtPrime_of_unique_fibre p P (Localization.AtPrime p) T hunique
  let e : T ≃ₐ[Localization.AtPrime p] Localization.AtPrime P :=
    ((IsLocalization.algEquiv P.primeCompl T (Localization.AtPrime P)).restrictScalars R).extendScalarsOfIsLocalization
       (Localization.AtPrime p) p.primeCompl
  exact (b.localizationLocalization (Localization.AtPrime p) p.primeCompl T).map e.toLinearEquiv

end PiExponent.RamifiedLocalLength

end OAI
end Source0280

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedLocalLength.lean
section Source0281
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedLocalLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open IsLocalRing TensorProduct

namespace PiExponent.RamifiedLocalLength

theorem residueField_map_surjective_of_mod_surjective
    {R S : Type*} [CommRing R] [CommRing S]
    (P : Ideal R) [P.IsPrime] (Q : Ideal S) [Q.IsMaximal]
    (f : R →+* S) (hPQ : P = Q.comap f)
    (hs : ∀ y : S, ∃ x : R, y - f x ∈ Q) :
    Function.Surjective (Ideal.ResidueField.map P Q f hPQ) := by
  intro z
  obtain ⟨y, rfl⟩ := Q.algebraMap_residueField_surjective z
  obtain ⟨x, hx⟩ := hs y
  refine ⟨algebraMap R P.ResidueField x, ?_⟩
  rw [Ideal.ResidueField.map_algebraMap]
  have hz := (Ideal.algebraMap_residueField_eq_zero (I := Q)).mpr hx
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

variable {A B : Type*} [CommRing A] [CommRing B]
  [IsLocalRing A] [IsLocalRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)] [Module.Free A B] [Module.Finite A B]

theorem closed_fibre_length_eq_finrank
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B))) :
    Module.length B (B ⧸ (maximalIdeal A).map (algebraMap A B)) =
      (Module.finrank A B : ℕ∞) := by
  let I : Ideal B := (maximalIdeal A).map (algebraMap A B)
  have hreslen : Module.length (ResidueField A) (ResidueField B) = 1 := by
    rw [Module.length_eq_of_surjective hres]
    exact Module.length_eq_one _ _
  have hrestrict := IsLocalRing.length_restrictScalars A B (B ⧸ I)
  rw [hreslen, mul_one] at hrestrict
  rw [← hrestrict]
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field (maximalIdeal A)
  let : Module.Finite (A ⧸ maximalIdeal A) (B ⧸ I) :=
    Module.Finite.of_restrictScalars_finite A _ _
  calc
    Module.length A (B ⧸ I) = Module.length (A ⧸ maximalIdeal A) (B ⧸ I) :=
      Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
    _ = (Module.finrank (A ⧸ maximalIdeal A) (B ⧸ I) : ℕ∞) :=
      Module.length_eq_finrank _ _
    _ = (Module.finrank A B : ℕ∞) := by
      rw [IsLocalRing.finrank_quotient_map]

theorem length_baseChange_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (M : Type*) [AddCommGroup M] [Module A M] :
    Module.length B (B ⊗[A] M) =
      Module.length A M * (Module.finrank A B : ℕ∞) := by
  rw [IsLocalRing.length_baseChange, closed_fibre_length_eq_finrank hres]

theorem length_quotient_map_eq_finrank_mul
    (hres : Function.Surjective (algebraMap (ResidueField A) (ResidueField B)))
    (I : Ideal A) :
    Module.length B (B ⧸ I.map (algebraMap A B)) =
      Module.length A (A ⧸ I) * (Module.finrank A B : ℕ∞) := by
  rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.length_eq]
  exact length_baseChange_eq_finrank_mul hres (A ⧸ I)

end PiExponent.RamifiedLocalLength

end OAI
end Source0281

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedPointMap.lean
section Source0282
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedPointMap.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.RamifiedLocalLength

open IsLocalRing WeightedBezout

variable {k σ : Type*} [Field k]

noncomputable def translatedPowerLocalMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Localization.AtPrime (pointIdeal a) →ₐ[k]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localAlgHom (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a)
    (translatedPowerSubstitution_comap_origin w a hw).symm

instance translatedPowerLocalMap_isLocalHom (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    IsLocalHom (translatedPowerLocalMap w a hw).toRingHom :=
  Localization.isLocalHom_localRingHom _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm

@[simp] theorem translatedPowerLocalMap_algebraMap (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (p : MvPolynomial σ k) :
    translatedPowerLocalMap w a hw
      (algebraMap _ (Localization.AtPrime (pointIdeal a)) p) =
      algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))
        (translatedPowerSubstitution w a p) :=
  Localization.localRingHom_to_map _ _ _
    (translatedPowerSubstitution_comap_origin w a hw).symm p

theorem translatedPowerLocalResidue_surjective (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Function.Surjective (IsLocalRing.ResidueField.map
      (translatedPowerLocalMap w a hw).toRingHom) := by
  apply residueField_map_surjective_of_mod_surjective
    (pointIdeal a) (pointIdeal (0 : σ → k))
    (translatedPowerSubstitution w a).toRingHom
    (translatedPowerSubstitution_comap_origin w a hw).symm
  intro p
  refine ⟨MvPolynomial.C (MvPolynomial.aeval (0 : σ → k) p), ?_⟩
  simp [mem_pointIdeal]

theorem translatedPowerLocalMap_ideal_map (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    (I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))).map
        (translatedPowerLocalMap w a hw).toRingHom =
      (I.map (translatedPowerSubstitution w a).toRingHom).map
        (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k)))) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  apply RingHom.ext
  intro p
  exact translatedPowerLocalMap_algebraMap w a hw p

@[instance_reducible] noncomputable def translatedPowerLocalAlgebra (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) :
    Algebra (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) :=
  (translatedPowerLocalMap w a hw).toRingHom.toAlgebra

end PiExponent.RamifiedLocalLength

end OAI
end Source0282

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PowerCoverExponents.lean
section Source0283
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PowerCoverExponents.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ : Type*} [Fintype σ]

def scale (w : σ → ℕ) (q : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * q i)

def quotient (w : σ → ℕ) (a : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => a i / w i)

def residue (w : σ → ℕ) (hw : ∀ i, 0 < w i) (a : σ →₀ ℕ) :
    ∀ i, Fin (w i) :=
  fun i => ⟨a i % w i, Nat.mod_lt _ (hw i)⟩

def combine (w : σ → ℕ) (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => w i * p.1 i + (p.2 i).val)

@[simp] theorem scale_apply (w : σ → ℕ) (q : σ →₀ ℕ) (i : σ) :
    scale w q i = w i * q i := by simp [scale]

@[simp] theorem quotient_apply (w : σ → ℕ) (a : σ →₀ ℕ) (i : σ) :
    quotient w a i = a i / w i := by simp [quotient]

omit [Fintype σ] in
@[simp] theorem residue_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (i : σ) :
    (residue w hw a i).val = a i % w i := rfl

@[simp] theorem combine_apply (w : σ → ℕ)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) (i : σ) :
    combine w p i = w i * p.1 i + (p.2 i).val := by simp [combine]

@[simp] theorem combine_quotient_residue (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) :
    combine w (quotient w a, residue w hw a) = a := by
  ext i
  simp only [combine_apply, quotient_apply, residue_apply]
  exact Nat.div_add_mod (a i) (w i)

@[simp] theorem quotient_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    quotient w (combine w p) = p.1 := by
  ext i
  simp only [quotient_apply, combine_apply]
  rw [Nat.mul_add_div (hw i)]
  simp [Nat.div_eq_of_lt (p.2 i).isLt]

@[simp] theorem residue_combine (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    residue w hw (combine w p) = p.2 := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod, Nat.mod_eq_of_lt (p.2 i).isLt]

def exponentEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    (σ →₀ ℕ) ≃ ((σ →₀ ℕ) × (∀ i, Fin (w i))) where
  toFun a := (quotient w a, residue w hw a)
  invFun := combine w
  left_inv := combine_quotient_residue w hw
  right_inv p := by simp [quotient_combine w hw]

@[simp] theorem exponentEquiv_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) : exponentEquiv w hw a = (quotient w a, residue w hw a) := rfl

@[simp] theorem exponentEquiv_symm_apply (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p : (σ →₀ ℕ) × (∀ i, Fin (w i))) :
    (exponentEquiv w hw).symm p = combine w p := rfl

@[simp] theorem quotient_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    quotient w (a + scale w q) = quotient w a + q := by
  ext i
  simp only [quotient_apply, Finsupp.add_apply, scale_apply]
  simp [Nat.add_mul_div_left, hw i]

@[simp] theorem residue_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    residue w hw (a + scale w q) = residue w hw a := by
  funext i
  apply Fin.ext
  simp [Nat.add_mod]

@[simp] theorem exponentEquiv_add_scale (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a q : σ →₀ ℕ) :
    exponentEquiv w hw (a + scale w q) = (quotient w a + q, residue w hw a) := by
  simp [quotient_add_scale w hw]

@[simp] theorem combine_add (w : σ → ℕ) (q q' : σ →₀ ℕ)
    (r : ∀ i, Fin (w i)) :
    combine w (q + q', r) = combine w (q, r) + scale w q' := by
  ext i
  simp [Nat.mul_add, Nat.add_assoc, Nat.add_comm]

@[simp] theorem scale_zero (w : σ → ℕ) : scale w 0 = 0 := by
  ext i
  simp

@[simp] theorem scale_add (w : σ → ℕ) (q q' : σ →₀ ℕ) :
    scale w (q + q') = scale w q + scale w q' := by
  ext i
  simp [Nat.mul_add]

end
end PiExponent.PowerCover

end OAI
end Source0283

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PowerCoverSubstitution.lean
section Source0284
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PowerCoverSubstitution.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PowerCover

noncomputable section

variable {σ k : Type*} [Fintype σ] [CommSemiring k]

def scaleHom (w : σ → ℕ) : (σ →₀ ℕ) →+ (σ →₀ ℕ) where
  toFun := scale w
  map_zero' := scale_zero w
  map_add' := scale_add w

@[simp] theorem scaleHom_apply (w : σ → ℕ) (a : σ →₀ ℕ) :
    scaleHom w a = scale w a := rfl

@[simp] theorem scale_single (w : σ → ℕ) (i : σ) (n : ℕ) :
    scale w (Finsupp.single i n) = Finsupp.single i (w i * n) := by
  classical
  ext j
  by_cases h : i = j
  · subst j; simp
  · simp [h]

def powerSubstitution (w : σ → ℕ) :
    MvPolynomial σ k →ₐ[k] MvPolynomial σ k :=
  MvPolynomial.aeval (fun i => MvPolynomial.X i ^ w i)

omit [Fintype σ] in
@[simp] theorem powerSubstitution_X (w : σ → ℕ) (i : σ) :
    powerSubstitution (k := k) w (MvPolynomial.X i) = MvPolynomial.X i ^ w i := by
  simp [powerSubstitution]

theorem powerSubstitution_eq_mapDomainAlgHom (w : σ → ℕ) :
    powerSubstitution (k := k) w = AddMonoidAlgebra.mapDomainAlgHom k k (scaleHom w) := by
  apply MvPolynomial.algHom_ext
  intro i
  rw [powerSubstitution_X, MvPolynomial.X_pow_eq_monomial]
  change MvPolynomial.monomial (Finsupp.single i (w i)) (1 : k) =
    AddMonoidAlgebra.mapDomain (scaleHom w) (AddMonoidAlgebra.single (Finsupp.single i 1) 1)
  rw [AddMonoidAlgebra.mapDomain_single]
  simp [MvPolynomial.single_eq_monomial]

@[simp] theorem powerSubstitution_monomial (w : σ → ℕ) (a : σ →₀ ℕ) (c : k) :
    powerSubstitution w (MvPolynomial.monomial a c) =
      MvPolynomial.monomial (scale w a) c := by
  rw [powerSubstitution_eq_mapDomainAlgHom]
  change AddMonoidAlgebra.mapDomain (scaleHom w) (AddMonoidAlgebra.single a c) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

end
end PiExponent.PowerCover

end OAI
end Source0284

-- Source: OAI/NumberTheory/PiExponent/Polynomials/PowerCoverBasis.lean
section Source0285
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/PowerCoverBasis.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PowerCover
noncomputable section

variable {σ : Type*} [Fintype σ] {k : Type*} [CommSemiring k]

def decompositionAddEquiv (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    MvPolynomial σ k ≃+ ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (AddMonoidAlgebra.coeffAddEquiv : MvPolynomial σ k ≃+ ((σ →₀ ℕ) →₀ k)).trans <|
    (Finsupp.domCongr ((exponentEquiv w hw).trans (Equiv.prodComm _ _))).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv AddMonoidAlgebra.coeffAddEquiv.symm

@[simp] theorem decompositionAddEquiv_monomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (a : σ →₀ ℕ) (c : k) :
    decompositionAddEquiv w hw (MvPolynomial.monomial a c) =
      Finsupp.single (residue w hw a) (MvPolynomial.monomial (quotient w a) c) := by
  classical
  simp [decompositionAddEquiv, MvPolynomial.monomial, Finsupp.curry_single]

theorem decompositionAddEquiv_power_mul (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : MvPolynomial σ k) :
    decompositionAddEquiv w hw (powerSubstitution w p * q) =
      p • decompositionAddEquiv w hw q := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial a c =>
    induction q using MvPolynomial.induction_on' with
    | monomial b d =>
      simp only [powerSubstitution_monomial, MvPolynomial.monomial_mul_monomial,
        decompositionAddEquiv_monomial]
      rw [add_comm (scale w a) b, quotient_add_scale w hw, residue_add_scale]
      simp [Finsupp.smul_single, smul_eq_mul, MvPolynomial.monomial_mul_monomial, add_comm]
    | add q r hq hr =>
      simp only [mul_add, map_add, smul_add, hq, hr]
  | add p r hp hr =>
    simp only [map_add, add_mul, add_smul, hp, hr]

def PowerModule (_weights : σ → ℕ) (k : Type*) [CommSemiring k] := MvPolynomial σ k

instance (w : σ → ℕ) : CommSemiring (PowerModule w k) :=
  inferInstanceAs (CommSemiring (MvPolynomial σ k))

def toPolynomial (w : σ → ℕ) : PowerModule w k ≃+* MvPolynomial σ k :=
  RingEquiv.refl _

instance powerAlgebra (w : σ → ℕ) : Algebra (MvPolynomial σ k) (PowerModule w k) :=
  ((toPolynomial w).symm.toRingHom.comp
    (powerSubstitution w).toRingHom).toAlgebra

omit [Fintype σ] in
@[simp] theorem toPolynomial_smul (w : σ → ℕ) (p : MvPolynomial σ k)
    (q : PowerModule w k) :
    toPolynomial w (p • q) =
      powerSubstitution w p * toPolynomial w q := rfl

def decomposition (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    PowerModule w k ≃ₗ[MvPolynomial σ k] ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  ((toPolynomial w).toAddEquiv.trans (decompositionAddEquiv w hw)).toLinearEquiv <| by
    intro p q
    exact decompositionAddEquiv_power_mul w hw p (toPolynomial w q)

def basis (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    Module.Basis (∀ i, Fin (w i)) (MvPolynomial σ k) (PowerModule w k) where
  repr := decomposition w hw

theorem finrank (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    [StrongRankCondition (MvPolynomial σ k)] :
    Module.finrank (MvPolynomial σ k) (PowerModule w k) = ∏ i, w i := by
  classical
  rw [Module.finrank_eq_card_basis (basis w hw)]
  simp [Fintype.card_pi]

end

noncomputable instance {σ k : Type*} [CommRing k] (w : σ → ℕ) :
    CommRing (PowerModule w k) :=
  inferInstanceAs (CommRing (MvPolynomial σ k))

end PiExponent.PowerCover

end OAI
end Source0285

-- Source: OAI/NumberTheory/PiExponent/Polynomials/TranslatedPowerCover.lean
section Source0286
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/TranslatedPowerCover.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.TranslatedPowerCover

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

def Ring (_weights : σ → ℕ) (_center : σ → k) := MvPolynomial σ k

instance (w : σ → ℕ) (a : σ → k) : CommRing (Ring w a) :=
  inferInstanceAs (CommRing (MvPolynomial σ k))

def toPolynomial (w : σ → ℕ) (a : σ → k) : Ring w a ≃+* MvPolynomial σ k :=
  RingEquiv.refl _

instance (w : σ → ℕ) (a : σ → k) : Algebra (MvPolynomial σ k) (Ring w a) :=
  ((toPolynomial w a).symm.toRingHom.comp
    (translatedPowerSubstitution w a).toRingHom).toAlgebra

def decomposition (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Ring w a ≃ₗ[MvPolynomial σ k] ((∀ i, Fin (w i)) →₀ MvPolynomial σ k) :=
  (((toPolynomial w a).toAddEquiv.trans (PowerCover.decompositionAddEquiv w hw)).trans
    (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)).toLinearEquiv <| by
      intro p q
      have hsub : translatedPowerSubstitution w a p =
          PowerCover.powerSubstitution w (translationEquiv a p) := by
        rw [translatedPowerSubstitution_factor]
        rfl
      change (Finsupp.mapRange.addEquiv (translationEquiv a).symm.toAddEquiv)
          (PowerCover.decompositionAddEquiv w hw
            (translatedPowerSubstitution w a p * toPolynomial w a q)) = _
      rw [hsub, PowerCover.decompositionAddEquiv_power_mul]
      ext r
      simp [Finsupp.smul_apply, smul_eq_mul]

def basis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.Basis (∀ i, Fin (w i)) (MvPolynomial σ k) (Ring w a) where
  repr := decomposition w a hw

theorem finrank (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    Module.finrank (MvPolynomial σ k) (Ring w a) = ∏ i, w i := by
  classical
  rw [Module.finrank_eq_card_basis (basis w a hw)]
  simp [Fintype.card_pi]

end
end PiExponent.TranslatedPowerCover

end OAI
end Source0286

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedPowerLength.lean
section Source0287
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/RamifiedPowerLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.RamifiedLocalLength

open WeightedBezout
open scoped BigOperators

noncomputable section

variable {σ k : Type*} [Fintype σ] [Field k]

abbrev coverOriginIdeal (w : σ → ℕ) (a : σ → k) :
    Ideal (TranslatedPowerCover.Ring w a) :=
  (pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom

instance coverOriginIdeal_isMaximal (w : σ → ℕ) (a : σ → k) :
    (coverOriginIdeal w a).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective _ (TranslatedPowerCover.toPolynomial w a).surjective

omit [Fintype σ] in
theorem coverOriginIdeal_liesOver (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    (coverOriginIdeal w a).LiesOver (pointIdeal a) := by
  constructor
  change pointIdeal a =
    ((pointIdeal (0 : σ → k)).comap (TranslatedPowerCover.toPolynomial w a).toRingHom).comap
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
  rw [Ideal.comap_comap]
  exact (translatedPowerSubstitution_comap_origin w a hw).symm

omit [Fintype σ] in
theorem coverOriginIdeal_unique (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i)
    (Q : Ideal (TranslatedPowerCover.Ring w a)) (hQ : Q.IsPrime)
    (hQa : pointIdeal a ≤ Q.under (MvPolynomial σ k)) : Q = coverOriginIdeal w a := by
  let e := TranslatedPowerCover.toPolynomial w a
  let : Q.IsPrime := hQ
  have hmap : (Q.map e.toRingHom).IsPrime := Ideal.map_isPrime_of_equiv e
  let : (Q.map e.toRingHom).IsPrime := hmap
  have hcont : pointIdeal a ≤ (Q.map e.toRingHom).comap (translatedPowerSubstitution w a).toRingHom := by
    intro p hp
    exact Ideal.mem_map_of_mem e.toRingHom (hQa hp)
  have hle : pointIdeal (0 : σ → k) ≤ Q.map e.toRingHom := by
    rw [pointIdeal_eq_span]
    apply Ideal.span_le.mpr
    rintro polynomial ⟨index, rfl⟩
    have hcoordinate : MvPolynomial.X index - MvPolynomial.C (a index) ∈ pointIdeal a := by
      simp
    have hpower := hcont hcoordinate
    change translatedPowerSubstitution w a
      (MvPolynomial.X index - MvPolynomial.C (a index)) ∈ Q.map e.toRingHom at hpower
    have hvariable : MvPolynomial.X index ∈ Q.map e.toRingHom :=
      (hmap.pow_mem_iff_mem (w index) (hw index)).mp (by
        simpa only [map_sub, translatedPowerSubstitution_X, translatedPowerSubstitution_C,
          add_sub_cancel_left] using hpower)
    simpa using hvariable
  have hEq := ((inferInstance : (pointIdeal (0 : σ → k)).IsMaximal).eq_of_le
    hmap.ne_top hle).symm
  have hc := congrArg (Ideal.comap e.toRingHom) hEq
  rw [Ideal.comap_map_of_bijective e.toRingHom e.bijective] at hc
  exact hc

def coverOriginLocalEquiv (w : σ → ℕ) (a : σ → k) :
    Localization.AtPrime (coverOriginIdeal w a) ≃+*
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
  Localization.localRingEquiv (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
    (TranslatedPowerCover.toPolynomial w a) rfl

def translatedPowerLocalBasis (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.Basis (∀ i, Fin (w i)) (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) := by
  classical
  letI := translatedPowerLocalAlgebra w a hw
  let : (coverOriginIdeal w a).LiesOver (pointIdeal a) := coverOriginIdeal_liesOver w a hw
  letI := Localization.AtPrime.algebraOfLiesOver (pointIdeal a) (coverOriginIdeal w a)
  have hcomm : (coverOriginLocalEquiv w a).toRingHom.comp
        (algebraMap (Localization.AtPrime (pointIdeal a))
          (Localization.AtPrime (coverOriginIdeal w a))) =
      (translatedPowerLocalMap w a hw).toRingHom := by
    change (Localization.localRingHom (coverOriginIdeal w a) (pointIdeal (0 : σ → k))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).comp
        (Localization.localRingHom (pointIdeal a) (coverOriginIdeal w a)
          (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
          (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))) = _
    exact (Localization.localRingHom_comp (pointIdeal a) (coverOriginIdeal w a)
      (pointIdeal (0 : σ → k))
      (algebraMap (MvPolynomial σ k) (TranslatedPowerCover.Ring w a))
      (Ideal.over_def (coverOriginIdeal w a) (pointIdeal a))
      (TranslatedPowerCover.toPolynomial w a).toRingHom rfl).symm
  let e : Localization.AtPrime (coverOriginIdeal w a) ≃ₐ[Localization.AtPrime (pointIdeal a)]
      Localization.AtPrime (pointIdeal (0 : σ → k)) :=
    { __ := coverOriginLocalEquiv w a
      commutes' := fun x => RingHom.congr_fun hcomm x }
  exact (basis_atPrime_of_unique_fibre (pointIdeal a) (coverOriginIdeal w a)
    (TranslatedPowerCover.basis w a hw) (coverOriginIdeal_unique w a hw)).map e.toLinearEquiv

theorem translatedPowerLocal_finrank (w : σ → ℕ) (a : σ → k) (hw : ∀ i, 0 < w i) :
    letI := translatedPowerLocalAlgebra w a hw
    Module.finrank (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal (0 : σ → k))) = ∏ i, w i := by
  classical
  let := translatedPowerLocalAlgebra w a hw
  rw [Module.finrank_eq_card_basis (translatedPowerLocalBasis w a hw)]
  simp [Fintype.card_pi]

theorem translatedPowerLocal_quotient_length (w : σ → ℕ) (a : σ → k)
    (hw : ∀ i, 0 < w i) (I : Ideal (MvPolynomial σ k)) :
    Module.length (Localization.AtPrime (pointIdeal (0 : σ → k)))
      (Localization.AtPrime (pointIdeal (0 : σ → k)) ⧸
        (I.map (translatedPowerSubstitution w a).toRingHom).map
          (algebraMap _ (Localization.AtPrime (pointIdeal (0 : σ → k))))) =
    Module.length (Localization.AtPrime (pointIdeal a))
      (Localization.AtPrime (pointIdeal a) ⧸
        I.map (algebraMap _ (Localization.AtPrime (pointIdeal a)))) *
      ((∏ i, w i : ℕ) : ℕ∞) := by
  classical
  let A := Localization.AtPrime (pointIdeal a)
  let B := Localization.AtPrime (pointIdeal (0 : σ → k))
  let := translatedPowerLocalAlgebra w a hw
  let : IsLocalHom (algebraMap A B) := translatedPowerLocalMap_isLocalHom w a hw
  let : Module.Free A B := Module.Free.of_basis (translatedPowerLocalBasis w a hw)
  let : Module.Finite A B := Module.Finite.of_basis (translatedPowerLocalBasis w a hw)
  have hres : Function.Surjective (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField B)) := translatedPowerLocalResidue_surjective w a hw
  have h := length_quotient_map_eq_finrank_mul hres (I.map (algebraMap _ A))
  rw [translatedPowerLocal_finrank w a hw] at h
  change Module.length B (B ⧸ (I.map (algebraMap _ A)).map
    (translatedPowerLocalMap w a hw).toRingHom) = _ at h
  rw [translatedPowerLocalMap_ideal_map] at h
  exact h

end
end PiExponent.RamifiedLocalLength

end OAI
end Source0287

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedBezoutBound.lean
section Source0288
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedBezoutBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
namespace PiExponent.WeightedBezout

noncomputable def pointLength {k : Type*} [Field k] {n : ℕ}
    (a : Fin n → k) (I : Ideal (MvPolynomial (Fin n) k)) : ℕ∞ :=
  Module.length (Localization.AtPrime (pointIdeal a))
    (Localization.AtPrime (pointIdeal a) ⧸ I.map
      (algebraMap (MvPolynomial (Fin n) k) (Localization.AtPrime (pointIdeal a))))

theorem finite_length_of_rank_bound {L : ℕ∞} {r B : ℕ}
    (hr : 0 < r) (h : L * (r : ℕ∞) ≤ (B : ℕ∞)) :
    ∃ l : ℕ, L = (l : ℕ∞) ∧ l * r ≤ B := by
  have hfin : L ≠ ⊤ := by
    intro ht
    have hr0 : (r : ℕ∞) ≠ 0 := by exact_mod_cast hr.ne'
    rw [ht, ENat.top_mul hr0] at h
    exact (ENat.natCast_ne_top B) (top_le_iff.mp h)
  refine ⟨L.toNat, (ENat.natCast_toNat hfin).symm, ?_⟩
  have hn : ((L.toNat * r : ℕ) : ℕ∞) ≤ B := by
    simpa only [Nat.cast_mul, ENat.natCast_toNat hfin] using h
  exact_mod_cast hn

theorem weighted_bound_of_scaled_natural {n M L B : ℕ}
    (ρ : Fin n → ℝ) (w : Fin n → ℕ) (N : ℝ)
    (hM : 0 < M) (hρ : ∀ i, 0 < ρ i)
    (hw : ∀ i, (w i : ℝ) = (M : ℝ) * ρ i)
    (hbound : L * ∏ i, w i ≤ B ^ n)
    (hdegree : (B : ℝ) ≤ (M : ℝ) * N) :
    (L : ℝ) ≤ N ^ n / ∏ i, ρ i := by
  have hp : 0 < ∏ i, ρ i := Finset.prod_pos (fun i _ => hρ i)
  have hscale : 0 < (M : ℝ) ^ n := pow_pos (by exact_mod_cast hM) _
  have hprod : (∏ i, (w i : ℝ)) = (M : ℝ) ^ n * ∏ i, ρ i := by
    simp_rw [hw]
    rw [Finset.prod_mul_distrib]
    simp
  apply (le_div_iff₀ hp).mpr
  apply (mul_le_mul_iff_right₀ hscale).mp
  calc
    (M : ℝ) ^ n * ((L : ℝ) * ∏ i, ρ i) = (L : ℝ) * ∏ i, (w i : ℝ) := by
      rw [hprod]
      ring
    _ ≤ (B : ℝ) ^ n := by exact_mod_cast hbound
    _ ≤ ((M : ℝ) * N) ^ n := pow_le_pow_left₀ (Nat.cast_nonneg B) hdegree n
    _ = (M : ℝ) ^ n * N ^ n := by rw [mul_pow]

theorem pointLength_mul_le_of_substituted_degree
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (w : Fin n → ℕ) (hw : ∀ i, 0 < w i) (D : ℕ)
    (hdegree : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    pointLength a (Ideal.span (Set.range f)) * (∏ i, w i : ℕ) ≤ (D ^ n : ℕ) := by
  let I := Ideal.span (Set.range f)
  let g : J → MvPolynomial (Fin n) k := fun j => translatedPowerSubstitution w a (f j)
  have hmap : I.map (translatedPowerSubstitution w a).toRingHom =
      Ideal.span (Set.range g) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have hminimal0 := origin_minimalPrimes_map w a hw I hminimal
  rw [hmap] at hminimal0
  have hheight := PiExponentSiegelAux.W09.polynomialMaximal_height k n
    (pointIdeal (0 : Fin n → k))
  have hb := PiExponent.localIsolatedBezout k n g D n hdegree
    (pointIdeal (0 : Fin n → k)) hminimal0 hheight le_rfl
  rw [← hmap] at hb
  rw [RamifiedLocalLength.translatedPowerLocal_quotient_length w a hw I] at hb
  exact hb

theorem rational_pointLength_bound
    (k : Type) [Field k] [Infinite k] {n : ℕ} {J : Type*}
    (f : J → MvPolynomial (Fin n) k) (a : Fin n → k)
    (ρ : Fin n → ℚ) (hρ : ∀ i, 0 < ρ i) (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (ρ i : ℝ)) ≤ N)
    (hminimal : pointIdeal a ∈ (Ideal.span (Set.range f)).minimalPrimes) :
    ∃ L : ℕ, pointLength a (Ideal.span (Set.range f)) = (L : ℕ∞) ∧
      (L : ℝ) ≤ N ^ n / ∏ i, (ρ i : ℝ) := by
  classical
  obtain ⟨M, hM, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hM
  have hscale : ∀ i, (w i : ℝ) = (M : ℝ) * (ρ i : ℝ) := by
    intro i
    rw [hweights i]
    field_simp
  have hMN : 0 ≤ (M : ℝ) * N := mul_nonneg hMreal.le hN
  let D : ℕ := ⌊(M : ℝ) * N⌋₊
  have hD : ∀ j, (translatedPowerSubstitution w a (f j)).totalDegree ≤ D := by
    intro j
    apply (Nat.le_floor_iff hMN).mpr
    exact translatedPowerSubstitution_totalDegree_real w a
      (fun i => (ρ i : ℝ)) M N hMreal.le hMN hscale (f j) (hdegree j)
  have hbound := pointLength_mul_le_of_substituted_degree k f a w hw D hD hminimal
  have hprod : 0 < ∏ i, w i := Finset.prod_pos (fun i _ => hw i)
  obtain ⟨L, hL, hLbound⟩ := finite_length_of_rank_bound hprod hbound
  refine ⟨L, hL, ?_⟩
  exact weighted_bound_of_scaled_natural (fun i => (ρ i : ℝ)) w N hM
    (fun i => by exact_mod_cast hρ i) hscale hLbound (Nat.floor_le hMN)

end PiExponent.WeightedBezout

end OAI
end Source0288

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean
section Source0289
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeWeightedBezout.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PrimeWeightedBezout

open scoped BigOperators
open CoordinateFiniteSlice CoordinateSliceComparison NormalBasisRigidity WeightedSliceDegree

theorem weighted_prime_length_bound {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime]
    (A : Finset (Fin n))
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    {J : Type*} (f : J → MvPolynomial (Fin n) ℂ)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin n → ℚ) (hrho : ∀ i, 0 < rho i)
    (N : ℝ) (hN : 0 ≤ N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N) :
    ∃ L : ℕ, primeLength Q (Ideal.span (Set.range f)) = L ∧
      (L : ℝ) ≤ N ^ A.card / ∏ i ∈ A, (rho i : ℝ) := by
  let : Infinite Q.ResidueField := Infinite.of_injective
    (algebraMap ℂ Q.ResidueField) (algebraMap ℂ Q.ResidueField).injective
  have hminimal := sliceFamily_mem_minimalPrimes_of_normalBasis Q A hA f hQ
  have hlength := length_eq_sliceFamily_of_normalBasis Q A hA f
  have hrhoR (i : Fin n) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hsliceDegree : ∀ j, ∀ d ∈
      (enumeratedSliceMap A (residueCoordinates Q) (f j)).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho (A.equivFin.symm i) : ℝ)) ≤ N := by
    intro j
    exact supportBound_enumeratedSliceMap_sum A (residueCoordinates Q)
      (fun i => (rho i : ℝ)) (fun i => (hrhoR i).le) N (f j) (hdegree j)
  obtain ⟨L, hL, hupper⟩ := WeightedBezout.rational_pointLength_bound
    Q.ResidueField (fun j => enumeratedSliceMap A (residueCoordinates Q) (f j))
    (slicePoint Q A) (fun i => rho (A.equivFin.symm i)) (fun i => hrho _) N hN
    hsliceDegree hminimal
  refine ⟨L, hlength.trans hL, ?_⟩
  have hp : (∏ i : Fin A.card, (rho (A.equivFin.symm i) : ℝ)) =
      ∏ i ∈ A, (rho i : ℝ) := by
    calc
      _ = ∏ i : A, (rho i : ℝ) :=
        Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
      _ = _ := Finset.prod_coe_sort A (fun i => (rho i : ℝ))
  simpa only [hp] using hupper

end PiExponent.PrimeWeightedBezout
end

end OAI
end Source0289

-- Source: OAI/NumberTheory/PiExponent/Jets/TransverseSliceComparison.lean
section Source0290
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/TransverseSliceComparison.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.TransverseSliceComparison

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity
open TransverseWeightedMultiplicity WeightedSliceDegree

def residueCoordinates {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (i : Fin (m + 1)) : Q.ResidueField := primeResidueMap Q (MvPolynomial.X i)

def sliceEquations {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (A : Finset (Fin (m + 1))) {J : Type*} (f : J → FramePolynomial m) :
    J → MvPolynomial (Fin A.card) Q.ResidueField :=
  fun j => enumeratedSliceMap A (residueCoordinates Q) (f j)

def slicePoint {m : ℕ} (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (A : Finset (Fin (m + 1))) : Fin A.card → Q.ResidueField :=
  fun i => residueCoordinates Q (A.equivFin.symm i)

theorem comparison_of_normal_basis {m : ℕ}
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (A : Finset (Fin (m + 1))) (hk : 0 < A.card)
    (hA : IsNormalBasis (K := Q.ResidueField)
      (fun i => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (Pi.basisFun Q.ResidueField _ i)) A)
    (B : Fin A.card → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    {J : Type*} (f : J → FramePolynomial m)
    (hQ : Q ∈ (Ideal.span (Set.range f)).minimalPrimes)
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (epsilon N : ℝ) (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hdegree : ∀ j, ∀ d ∈ (f j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N)
    (hn : ∀ i, 2 ≤ rectangularCutoff (fun j => cost (B j)) (epsilon * N) i)
    (hvanish : ∀ p ∈ Ideal.span (Set.range f), ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ epsilon * N → polynomialFrameWord m word p ∈ Q) :
    (∏ i ∈ A, (rho i : ℝ)) ≤
      (A.card : ℝ) ^ A.card * (∏ i, cost (B i)) / epsilon ^ A.card := by
  obtain ⟨L, hL, hupper⟩ := PrimeWeightedBezout.weighted_prime_length_bound
    Q A hA f hQ rho hrho N hN.le hdegree
  have hlower := prime_frame_rectangular_length_lower m A.card Q hy B hB
    (Ideal.span (Set.range f)) cost
    (rectangularCutoff (fun j => cost (B j)) (epsilon * N)) (epsilon * N) hn
    (fun i => (hcost i).le)
    (rectangularCutoff_budget hk (fun j => cost (B j)) (fun j => hcost _)
      (epsilon * N) (mul_pos hepsilon hN)) hvanish
  change (∏ i, rectangularCutoff (fun j => cost (B j)) (epsilon * N) i : ℕ) ≤
    CoordinateSliceComparison.primeLength Q (Ideal.span (Set.range f)) at hlower
  rw [hL] at hlower
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have h := weight_comparison_of_rectangular_count hk
    (fun i => (rho (A.equivFin.symm i) : ℝ)) (fun j => cost (B j)) epsilon N L
    (fun i => hrhoR _) (fun j => hcost _) hepsilon hN (by exact_mod_cast hlower)
    (by simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using hupper)
  simpa only [NormalBasisProducts.prod_equivFin A (fun i => (rho i : ℝ))] using h

end PiExponent.TransverseSliceComparison
end

end OAI
end Source0290

-- Source: LogTwo/Geometry/NormalComparison.lean
section Source0291
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the logarithmic persistent weight comparison to log-two data.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! The logarithmic normal comparison, adapted from the logarithmic part of
Approximation/PersistentWeightComparison.lean in pinned openai/math (Apache-2.0).
This discharges EventualKernelComparison using the proved local length bounds.
The ordinary-coordinate comparison is not imported. -/
namespace LogTwo.Geometry
open scoped BigOperators
open OAI PiExponent PiExponentApprox NormalBasisRigidity NormalBasisProducts
open Filter Topology
noncomputable section

theorem logarithmic_normal_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (bound : ℝ) (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ Q)
    (hQ : Q ∈ (frameDerivativeIdeal cost bound F).minimalPrimes)
    (hvanish : ∀ p ∈ frameDerivativeIdeal cost bound F,
      ∀ word : List (Fin (m + 1)),
        frameWordCost cost word ≤ (sigma / ((m : ℝ) + 2)) * N →
          polynomialFrameWord m word p ∈ Q) :
    CurveComponentRigidity.NormalProductComparison Q hY
      (fun i => (rho i : ℝ)) cost (rigidityComparisonConstant m sigma) := by
  intro A B hA hB
  have hcard : A.card = B.card := hA.card_eq.trans hB.card_eq.symm
  by_cases hk0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp hk0
    have hB0 : B = ∅ := Finset.card_eq_zero.mp (hcard.symm.trans hk0)
    have hc := rectangular_factor_le_constant m 0 sigma hsigma (by omega)
    simpa [hA0, hB0, rigidityComparisonConstant] using hc
  have hk : 0 < A.card := Nat.pos_of_ne_zero hk0
  have hka : A.card ≤ m + 1 := by simpa using Finset.card_le_univ A
  have hepsilon : 0 < sigma / ((m : ℝ) + 2) := by positivity
  have hrhoR (i : Fin (m + 1)) : (0 : ℝ) < rho i := by exact_mod_cast hrho i
  have hdegree : ∀ j, ∀ d ∈ (FrameEquationFamily.equations cost bound F j).support,
      (∑ i ∈ d.support, (d i : ℝ) * (rho i : ℝ)) ≤ N := by
    intro j
    have h := FrameEquationFamily.equation_supportBound cost (fun i => (rho i : ℝ))
      bound N F hF (fun i => (hrhoR i).le) j
    simpa only [WeightedSliceDegree.SupportBound, Finsupp.weight_apply, Finsupp.sum,
      nsmul_eq_mul] using h
  have hcomp := TransverseSliceComparison.comparison_of_normal_basis Q
    (CurveComponentRigidity.residueY_ne_zero Q hY) A hk hA
    (enumeration A B hcard) (enumeration_linearIndependent A B hcard hB)
    (FrameEquationFamily.equations cost bound F)
    (by simpa only [FrameEquationFamily.span_equations] using hQ)
    rho hrho cost hcost (sigma / ((m : ℝ) + 2)) N hepsilon hN hdegree
    (hrect A.card hk hka (enumeration A B hcard))
    (by simpa only [FrameEquationFamily.span_equations] using hvanish)
  exact hcomp.trans (by
    have hc := rectangular_comparison_le_constant (m := m) (k := A.card)
      (by omega) (fun i => cost (enumeration A B hcard i)) sigma hsigma
      (fun i => (hcost _).le)
    simpa only [prod_enumeration A B hcard cost, rigidityComparisonConstant] using hc)

theorem logarithmic_persistent_comparison {m : ℕ}
    (rho : Fin (m + 1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m + 1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma N : ℝ) (hsigma : 0 < sigma) (hN : 0 < N)
    (hrect : UniformRectangles (m + 1) cost (sigma / ((m : ℝ) + 2)) N)
    (F : FramePolynomial m) (hF : HasWeightedDegreeLE (fun i => (rho i : ℝ)) N F)
    (P : Ideal (FramePolynomial m)) (hY : MvPolynomial.X (0 : Fin (m + 1)) ∉ P) :
    CurveComponentRigidity.PersistentNormalComparison (fun i => (rho i : ℝ)) cost
      (rigidityComparisonConstant m sigma) ((sigma / ((m : ℝ) + 2)) * N) F P hY := by
  intro r hr Q hQ hQP hQr hQnext hQlo hQhi hvanish
  let := hQ
  exact logarithmic_normal_comparison rho hrho cost hcost sigma N hsigma hN hrect
    F hF _ Q (fun h => hY (hQP h)) hQr hvanish

/-- The former geometric comparison input is supplied for all positive rational
degree weights and positive real derivative costs. The cutoff is chosen after
these data, independently of the field coordinates. -/
theorem eventualKernelComparison {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (z : Fin (m+1) → E) (rho : Fin (m+1) → ℚ) (hrho : ∀ i, 0 < rho i)
    (cost : Fin (m+1) → ℝ) (hcost : ∀ i, 0 < cost i)
    (sigma : ℝ) (hsigma : 0 < sigma) :
    EventualKernelComparison z (fun i => (rho i : ℝ)) cost
      (rigidityComparisonConstant m sigma) sigma := by
  have hepsilon : 0 < sigma/((m : ℝ)+2) := by positivity
  filter_upwards [eventually_uniformRectangles_nat (m+1) cost hcost _ hepsilon,
    eventually_gt_atTop (0 : ℕ)] with N hrect hN
  intro F _ hF hY
  exact logarithmic_persistent_comparison rho hrho cost hcost sigma N hsigma
    (by exact_mod_cast hN) hrect F hF (coordinateKernel z) hY

end
end LogTwo.Geometry
end Source0291

-- Source: LogTwo/Geometry/GlobalContactBound.lean
section Source0292
/-! Contact bounds with the normal comparison proved internally. The field and
residue hypotheses are retained explicitly; geometric interpolation is separate. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem contact_bound {m K : ℕ}
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)
    (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 < sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ))
      (rigidityComparisonConstant m sigma)) :
    (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
      (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  exact contact_bound_of_comparison hres hfinite z y hy c hz hK hinj w v hw hv
    theta htheta hratio sigma hsigma hmargin hvol _ hseparated
    (eventualKernelComparison z w hw (fun i => (v i : ℝ))
      (fun i => by exact_mod_cast hv i) sigma (by exact_mod_cast hsigma))

/-- This constant is fixed after n and m, before choosing any denominator. -/
def chosenComparisonConstant (n m : ℕ) : ℝ :=
  rigidityComparisonConstant m (curveSigma (theta (delta n)) m)

theorem chosenComparisonConstant_pos (n : ℕ) (hn : 1 ≤ n) (m : ℕ) :
    0 < chosenComparisonConstant n m := by
  apply rigidityComparisonConstant_pos
  exact_mod_cast curveSigma_pos (shape n hn).theta_pos
    ((shape n hn).theta_lt_a.trans ((shape n hn).a_lt_b.trans (shape n hn).b_lt_one)) m

/-- For the matrix weights, volume and normal comparison are no longer inputs.
The displayed prefix-growth condition can be supplied by denominator selection. -/
theorem chosenWeights_contact_bound
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (c : Fin w.K → Fin m → ℂ),
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  dsimp only
  intro y hy hinj c
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  apply chosenWeights_contact_bound_of_comparison hres hfinite n hn m q hq
    (chosenComparisonConstant n m) (chosenComparisonConstant_pos n hn m) hgrowth z hz
    y hy hinj c
  have hs : (0 : ℝ) < (curveSigma w.theta m : ℝ) := by
    exact_mod_cast curveSigma_pos w.theta_pos w.theta_lt_one m
  simpa only [cast_rationalColumnWeight, chosenComparisonConstant, w, chosenWeights] using
    eventualKernelComparison z (rationalColumnWeight w) (rationalColumnWeight_pos w)
      (fun i => (jetWeight w i : ℝ)) (fun i => by exact_mod_cast jetWeight_pos w i)
      (curveSigma w.theta m) hs

end
end LogTwo.Geometry
end Source0292

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterResidueField.lean
section Source0293
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/ParameterResidueField.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.ParameterResidueField
open scoped Polynomial nonZeroDivisors
open CurveZeroPole CurveValuationCenter

theorem residue_finite {F S : Type*} [Field F] [CommRing S] [Algebra F S]
    [Algebra.FiniteType F S] (q : Ideal S) [q.IsMaximal] : Module.Finite F q.ResidueField := by
  let : Algebra.FiniteType F q.ResidueField :=
    Algebra.FiniteType.of_surjective (IsScalarTower.toAlgHom F S q.ResidueField)
      (Ideal.algebraMap_residueField_surjective q)
  exact finite_of_finite_type_of_isJacobsonRing F q.ResidueField

abbrev parameterChartConstants
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) : Algebra F (parameterChart f hf) :=
  let := parameterPolynomialAlgebra f hf
  ((algebraMap F[X] (parameterChart f hf)).comp Polynomial.C).toAlgebra

theorem parameterChartConstants_tower
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f) :
    letI := parameterPolynomialAlgebra f hf
    letI := parameterChartConstants f hf
    IsScalarTower F F[X] (parameterChart f hf) := by
  let := parameterPolynomialAlgebra f hf
  let := parameterChartConstants f hf
  exact IsScalarTower.of_algebraMap_eq (fun _ => rfl)

theorem parameter_residue_finite
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Module.Finite F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let := parameterChartConstants f hf
  let := parameterChartConstants_tower f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let : Algebra.FiniteType F S := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType F F[X]) (inferInstance : Algebra.FiniteType F[X] S)
  let : q.1.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q.1 (zeroPrime F)
  exact residue_finite q.1

theorem parameter_residue_integral
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (q : parameterZeroPlaces f hf) :
    letI := parameterChartConstants f hf
    Algebra.IsIntegral F (IsLocalRing.ResidueField (Localization.AtPrime q.1)) := by
  let := parameterChartConstants f hf
  let := parameter_residue_finite f hf q
  exact Algebra.IsIntegral.of_finite F _

end PiExponent.ParameterResidueField

end

end OAI
end Source0293

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedLocalLattice.lean
section Source0294
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/WeightedLocalLattice.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators nonZeroDivisors
open PiExponent.WeightedCurveDegree PiExponent.CurveLocalOrder

namespace PiExponent.WeightedLocalLattice

theorem exists_local_element_iff_nonnegative_order
    {A K : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] (x : K) :
    (∃ a : A, algebraMap A K a = x) ↔ 0 ≤ fractionAddValuation A K x := by
  constructor
  · rintro ⟨a, rfl⟩
    rw [fractionAddValuation_algebraMap, localAddValuation_apply]
    have h := enatToIntegerOrder_monotone (show (0 : ℕ∞) ≤ IsDiscreteValuationRing.addVal A a from bot_le)
    simpa using h
  · intro hx
    by_cases hx0 : x = 0
    · exact ⟨0, by simp [hx0]⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective A x
    have hb0 : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hb
    have ha0 : a ≠ 0 := by
      intro ha
      apply hx0
      simp [ha]
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr ha0)
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
      (IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hb0)
    rw [AddValuation.map_div, fractionAddValuation_algebraMap,
      fractionAddValuation_algebraMap, localAddValuation_apply,
      localAddValuation_apply, ← hm, ← hn] at hx
    change (0 : WithTop ℤ) ≤ ((m : ℤ) : WithTop ℤ) - ((n : ℤ) : WithTop ℤ) at hx
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub, ← WithTop.coe_zero, WithTop.coe_le_coe] at hx
    have hnm : n ≤ m := by exact_mod_cast (sub_nonneg.mp hx)
    have hdvd : b ∣ a := IsDiscreteValuationRing.addVal_le_iff_dvd.mp (by
      rw [← hm, ← hn]
      exact_mod_cast hnm)
    obtain ⟨c, rfl⟩ := hdvd
    refine ⟨c, ?_⟩
    rw [map_mul, mul_div_cancel_left₀]
    exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr hb0

def generatedLattice
    (A : Type*) {K ι : Type*} [CommRing A] [Field K] [Algebra A K]
    (y : ι → K) (s : Finset ι) : Submodule A K :=
  Submodule.span A {z | ∃ i ∈ s, z = y i}

theorem generatedLattice_eq_span_of_minimum
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    (y : ι → K) (s : Finset ι) (a : ι) (ha : a ∈ s) (hya : y a ≠ 0)
    (hmin : ∀ b ∈ s, fractionAddValuation A K (y a) ≤ fractionAddValuation A K (y b)) :
    generatedLattice A y s = Submodule.span A {y a} := by
  have hva : fractionAddValuation A K (y a) ≠ ⊤ :=
    (AddValuation.top_iff _).not.mpr hya
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro z ⟨b, hb, rfl⟩
    have hv : 0 ≤ fractionAddValuation A K (y b / y a) := by
      rw [AddValuation.map_div]
      calc
        0 = fractionAddValuation A K (y a) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_self_eq_zero_of_ne_top hva).symm
        _ ≤ fractionAddValuation A K (y b) - fractionAddValuation A K (y a) :=
          (LinearOrderedAddCommGroupWithTop.sub_left_strictMono_of_ne_top hva).monotone (hmin b hb)
    obtain ⟨c, hc⟩ := (exists_local_element_iff_nonnegative_order _).mpr hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    exact div_mul_cancel₀ _ hya
  · apply Submodule.span_le.mpr
    intro z hz
    rcases Set.mem_singleton_iff.mp hz with rfl
    exact Submodule.subset_span ⟨a, ha, rfl⟩

def monomialLattice
    (A : Type*) {K ι : Type*} [CommRing A] [Field K] [Algebra A K]
    [Fintype ι] (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) : Submodule A K :=
  Submodule.span A {y | ∃ a ∈ monomials, y = ((∏ i, x i ^ a i : Kˣ) : K)}

theorem exists_monomialLattice_generator
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    ∃ a ∈ monomials,
      monomialLattice A x monomials =
        Submodule.span A {((∏ i, x i ^ a i : Kˣ) : K)} ∧
      integerOrder (fractionAddValuation A K) (∏ i, x i ^ a i) =
        -monomialPoleCoefficient (fractionAddValuation A K) x monomials hzero := by
  obtain ⟨a, ha, hord, hregular, _⟩ :=
    exists_regular_monomial_chart (fractionAddValuation A K) x monomials hzero
  refine ⟨a, ha, ?_, hord⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨b, hb, rfl⟩
    have hv : 0 ≤ fractionAddValuation A K
        (((∏ i, x i ^ b i) / (∏ i, x i ^ a i) : Kˣ) : K) := hregular b hb
    obtain ⟨c, hc⟩ := (exists_local_element_iff_nonnegative_order _).mpr hv
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    rw [Algebra.smul_def, hc]
    simp only [Units.val_div_eq_div_val]
    exact div_mul_cancel₀ _ (Units.ne_zero _)
  · apply Submodule.span_le.mpr
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Submodule.subset_span ⟨a, ha, rfl⟩

theorem monomialLattice_rank_one
    {A K ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Algebra A K] [IsFractionRing A K] [Fintype ι]
    (x : ι → Kˣ) (monomials : Finset (ι → ℕ)) (hzero : 0 ∈ monomials) :
    Nonempty (A ≃ₗ[A] monomialLattice A x monomials) := by
  obtain ⟨a, ha, hspan, hord⟩ := exists_monomialLattice_generator (A := A) x monomials hzero
  rw [hspan]
  exact ⟨LinearEquiv.toSpanNonzeroSingleton A K _ (Units.ne_zero _)⟩

end PiExponent.WeightedLocalLattice

end

end OAI
end Source0294

-- Source: OAI/NumberTheory/PiExponent/Geometry/PlaceParameterModel.lean
section Source0295
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PlaceParameterModel.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped Polynomial nonZeroDivisors
namespace PiExponent.PlaceParameterModel
open CurveZeroPole CurveValuationCenter WeightedCurveDegree

def parameterUnit {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : Eˣ := Classical.choose p.normalized

theorem parameterUnit_order {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : integerOrder p.valuation (parameterUnit p) = 1 :=
  Classical.choose_spec p.normalized

def parameter {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : E := parameterUnit p

theorem parameter_nonzero {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : parameter p ≠ 0 := (parameterUnit p).ne_zero

theorem parameter_value {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : p.valuation (parameter p) = 1 := by
  have h := coe_integerOrder p.valuation (parameterUnit p)
  rw [parameterUnit_order] at h
  exact h.symm

theorem parameter_positive {F E : Type*} [Field F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : 0 < p.valuation (parameter p) := by
  rw [parameter_value]
  norm_num

theorem parameter_transcendental
    {F E : Type*} [Field F] [IsAlgClosed F] [Field E] [Algebra F E]
    (p : NormalizedPlace F E) : Transcendental F (parameter p) := by
  intro ha
  have hm : parameter p ∈ algebraicClosure F E := mem_algebraicClosure_iff.mpr ha
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure F E)] at hm
  obtain ⟨c, hc⟩ := hm
  change algebraMap F E c = parameter p at hc
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact parameter_nonzero p hc.symm
  have hz := CurveProductFormula.valuation_constant_eq_zero p c hc0
  rw [hc, parameter_value] at hz
  exact one_ne_zero hz

def parameterCenterLocalRingEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃+*
      p.valuation.toValuation.valuationSubring := by
  let := parameterAlgebra f hf
  let := parameterPolynomialAlgebra f hf
  let := parameter_scalarTower f hf
  let := parameter_finite f hf
  let S := parameterChart f hf
  let : Module.IsTorsionFree F[X] S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (FunctionField.ringOfIntegers.algebraMap_injective F E)
  let q := parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le
  have hq : q ≠ ⊥ :=
    Ideal.ne_bot_of_mem_primesOver (zeroPrime_ne_bot F)
      (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).property
  let A := Localization.AtPrime q
  let := IsLocalization.localizationAlgebraOfSubmonoidLe A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsLocalization.localization_isScalarTower_of_submonoid_le A E
    q.primeCompl S⁰ q.primeCompl_le_nonZeroDivisors
  let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl A E
  let := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain S hq A
  let φ := parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
  have he : p.valuation = CurveLocalOrder.fractionAddValuation A E :=
    valuation_eq_parameterPlaceValuation f hf p.valuation p.constants_nonneg hp p.normalized
  apply RingEquiv.ofBijective φ
  constructor
  · intro a b hab
    apply IsFractionRing.injective A E
    have hh := congrArg (fun x : p.valuation.toValuation.valuationSubring => (x : E)) hab
    simpa only [φ, parameterCenterLocalHom_coe] using hh
  · intro x
    have hx : 0 ≤ CurveLocalOrder.fractionAddValuation A E (x : E) := by
      rw [← he]
      exact x.property
    obtain ⟨a, ha⟩ := (WeightedLocalLattice.exists_local_element_iff_nonnegative_order
      (A := A) (x : E)).mpr hx
    refine ⟨a, ?_⟩
    apply Subtype.ext
    exact (parameterCenterLocalHom_coe f hf p.valuation p.constants_nonneg hp.le a).trans ha

def parameterCenterLocalAlgEquiv
    {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (f : E) (hf : Transcendental F f)
    [FiniteDimensional (IntermediateField.adjoin F {f}) E]
    (p : NormalizedPlace F E) (hp : 0 < p.valuation f) :
    letI := ParameterResidueField.parameterChartConstants f hf
    Localization.AtPrime (parameterCenterPlace f hf p.valuation p.constants_nonneg hp).1 ≃ₐ[F]
      PlaceValuationRing.ring p := by
  let := ParameterResidueField.parameterChartConstants f hf
  refine { parameterCenterLocalRingEquiv f hf p hp with commutes' := ?_ }
  intro c
  apply Subtype.ext
  change (parameterCenterLocalHom f hf p.valuation p.constants_nonneg hp.le
    (algebraMap F _ c) : E) = algebraMap F E c
  rw [IsScalarTower.algebraMap_apply F (parameterChart f hf)
    (Localization.AtPrime (parameterValuationCenter f hf p.valuation p.constants_nonneg hp.le))]
  rw [parameterCenterLocalHom_algebraMap]
  let := parameterPolynomialAlgebra f hf
  change (algebraMap F[X] E (Polynomial.C c)) = algebraMap F E c
  rw [parameterPolynomialAlgebra_map f hf, Polynomial.aeval_C]

end PiExponent.PlaceParameterModel

end

end OAI
end Source0295

-- Source: OAI/NumberTheory/PiExponent/Geometry/PlaceLocalRing.lean
section Source0296
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PlaceLocalRing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PlaceLocalRing
open CurveZeroPole CurveValuationCenter PlaceParameterModel

theorem residue_integral_of_algEquiv
    {F A B : Type*} [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [IsLocalRing A] [IsLocalRing B]
    [Algebra.IsIntegral F (IsLocalRing.ResidueField A)] (e : A ≃ₐ[F] B) :
    Algebra.IsIntegral F (IsLocalRing.ResidueField B) := by
  constructor
  intro x
  obtain ⟨y,rfl⟩ := (IsLocalRing.ResidueField.mapAlgEquiv e).surjective x
  exact (Algebra.IsIntegral.isIntegral y).map (IsLocalRing.ResidueField.mapAlgEquiv e).toAlgHom

theorem residue_integral
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)) := by
  let f := parameter p
  have hf : Transcendental ℂ f := parameter_transcendental p
  let := CurveParameterFinite.finiteDimensional_adjoin_singleton ℂ E htrdeg hf
  let := ParameterResidueField.parameterChartConstants f hf
  let q := parameterCenterPlace f hf p.valuation p.constants_nonneg (parameter_positive p)
  let := ParameterResidueField.parameter_residue_integral f hf q
  exact residue_integral_of_algEquiv (A := Localization.AtPrime q.1)
    (parameterCenterLocalAlgEquiv f hf p (parameter_positive p))

def expansion
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    PlaceValuationRing.ring p →ₐ[ℂ] PowerSeries ℂ :=
  letI := residue_integral htrdeg p
  DVRBranch.expansion ℂ (PlaceValuationRing.ring p)

theorem expansion_injective
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E) :
    Function.Injective (expansion htrdeg p) := by
  let := residue_integral htrdeg p
  exact DVRBranch.expansion_injective ℂ (PlaceValuationRing.ring p)

theorem expansion_order
    {E : Type*} [Field E] [Algebra ℂ E] [Algebra.EssFiniteType ℂ E]
    (htrdeg : Algebra.trdeg ℂ E ≤ 1) (p : NormalizedPlace ℂ E)
    (a : PlaceValuationRing.ring p) :
    PowerSeries.order (expansion htrdeg p a) =
      IsDiscreteValuationRing.addVal (PlaceValuationRing.ring p) a := by
  let := residue_integral htrdeg p
  exact DVRBranch.expansion_order ℂ (PlaceValuationRing.ring p) a

end PiExponent.PlaceLocalRing

end

end OAI
end Source0296

-- Source: LogTwo/Geometry/IntrinsicContactBound.lean
section Source0297
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the nonconstant-coordinate argument and discharge the local field hypotheses.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Intrinsic function-field formulation for varying nonzero Y-centers.
The residue and finite-extension inputs follow from finite type and trdeg = 1.
This is a curve inequality, not a proof of interpolation surjectivity. -/
namespace LogTwo.Geometry
open OAI PiExponent CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem nonconstant_coordinates_of_trdeg_one {d : ℕ} (z : Fin d → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) : ∃ i, Transcendental ℂ (z i) := by
  let : Algebra.Transcendental ℂ E := trdeg_ne_zero_iff.mp (by rw [htrdeg]; exact one_ne_zero)
  exact CurveCenters.exists_transcendental_coordinate z hgen
    (Algebra.Transcendental.transcendental (R := ℂ) (A := E))

variable [Algebra.EssFiniteType ℂ E]

/-- The actual chosen matrix weights satisfy the full contact inequality on a
curve function field. No normal-comparison or local-residue hypothesis remains. -/
theorem chosenWeights_intrinsic_contact_bound
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m (chosenComparisonConstant n m)*
        (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) < (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E)
    (hgen : IntermediateField.adjoin ℂ (Set.range z) = ⊤)
    (htrdeg : Algebra.trdeg ℂ E = 1) :
    let hres := PlaceLocalRing.residue_integral htrdeg.le
    let hfinite := CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg
    let hz := nonconstant_coordinates_of_trdeg_one z hgen htrdeg
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0), Function.Injective y →
      ∀ (c : Fin w.K → Fin m → ℂ),
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  exact chosenWeights_contact_bound (PlaceLocalRing.residue_integral htrdeg.le)
    (CurveParameterFinite.finite_over_every_parameter ℂ E htrdeg)
    n hn m q hq hgrowth z (nonconstant_coordinates_of_trdeg_one z hgen htrdeg)

end
end LogTwo.Geometry
end Source0297

-- Source: LogTwo/Analysis/RealCenterIdentity.lean
section Source0298
/-! Exact analytic identity retaining the factor 2^(j*h) inside each column
function. It is a prospective input to the Taylor/collision argument, not a
determinant upper bound or a transfer of a bound for the fixed-Y matrix. -/
namespace LogTwo.Analysis
noncomputable section

/-- At a non-periodic center the exponential factor must be retained. -/
theorem scaled_log_monomial_identity (b center : ℂ) (h d : ℕ)
    {z : ℂ} (hz : 1+z ≠ 0) :
    b * Complex.exp center ^ h * (1+z)^h * (center+Complex.log (1+z))^d =
      b * Complex.exp ((h : ℂ)*(center+Complex.log (1+z))) *
        (center+Complex.log (1+z))^d := by
  rw [Complex.exp_nat_mul, Complex.exp_add, Complex.exp_log hz, mul_pow]
  ring

theorem exp_logTwo_center (j : ℕ) :
    Complex.exp ((j : ℂ)*(Real.log 2 : ℂ)) = (2 : ℂ)^j := by
  rw [Complex.exp_nat_mul, ← Complex.ofReal_exp, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

/-- The j-dependent matrix factor is exactly the exponential at j*log(2).
This preserves the common entire column function needed for cancellation. -/
theorem logTwo_scaled_log_monomial_identity (b : ℂ) (j h d : ℕ)
    {z : ℂ} (hz : 1+z ≠ 0) :
    b * (2 : ℂ)^(j*h) * (1+z)^h *
        ((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))^d =
      b * Complex.exp ((h : ℂ)*((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))) *
        ((j : ℂ)*(Real.log 2 : ℂ)+Complex.log (1+z))^d := by
  have hidentity := scaled_log_monomial_identity b ((j : ℂ)*(Real.log 2 : ℂ)) h d hz
  rw [exp_logTwo_center, ← pow_mul] at hidentity
  exact hidentity

end
end LogTwo.Analysis
end Source0298

-- Source: OAI/NumberTheory/PiExponent/Jets/BranchContactIdeal.lean
section Source0299
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/BranchContactIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.BranchContactIdeal
open IsDiscreteValuationRing

variable {A ι : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

def powerIdeal (z : ι → A) (e : ι → ℕ) : Ideal A :=
  Ideal.span (Set.range (fun i => z i ^ e i))

theorem powerIdeal_eq_singleton (z : ι → A) (e : ι → ℕ) (i : ι)
    (hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j)) :
    powerIdeal z e = Ideal.span {z i ^ e i} := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro a ⟨j,rfl⟩
    exact Ideal.mem_span_singleton.mpr (addVal_le_iff_dvd.mp (hmin j))
  · rw [Ideal.span_le]
    intro b hb
    obtain rfl := Set.mem_singleton_iff.mp hb
    exact Ideal.subset_span (Set.mem_range_self i)

theorem addVal_pow_toNat {a : A} (ha : a ≠ 0) (n : ℕ) :
    (addVal A (a ^ n)).toNat = n * (addVal A a).toNat := by
  have ht : addVal A a ≠ ⊤ := addVal_eq_top_iff.not.mpr ha
  rw [(addVal A).map_pow, ← ENat.natCast_toNat ht]
  simp [nsmul_eq_mul]

variable [Fintype ι] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def contact (v : ι → ℚ) (z : ι → A) (hne : ∃ i, z i ≠ 0) : ℚ :=
  BranchContact.contact v (fun i => DVRBranch.expansion ℂ A (z i)) (by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩)

theorem exists_generator_colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ∃ i, z i ≠ 0 ∧ powerIdeal z e = Ideal.span {z i ^ e i} ∧
      ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  classical
  let a : ι → PowerSeries ℂ := fun i => DVRBranch.expansion ℂ A (z i)
  have han : ∃ i, a i ≠ 0 := by
    obtain ⟨i,hi⟩ := hne
    exact ⟨i,(map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hi⟩
  obtain ⟨i,hi,hatt⟩ := BranchContact.exists_attains v a han
  have hzi : z i ≠ 0 := fun hz => hi (by simp [a,hz])
  have hival : (contact v z hne) * v i = ((addVal A (z i)).toNat : ℚ) := by
    have h := (eq_div_iff (ne_of_gt (hv i))).mp hatt
    simpa only [contact, a, DVRBranch.expansion_order] using h
  have hiR : ((addVal A (z i ^ e i)).toNat : ℚ) = R * contact v z hne := by
    rw [addVal_pow_toNat hzi, Nat.cast_mul, ← hival, ← he i]
    ring
  have hmin : ∀ j, addVal A (z i ^ e i) ≤ addVal A (z j ^ e j) := by
    intro j
    by_cases hzj : z j = 0
    · by_cases hej : e j = 0
      · have hR : R = 0 := by simpa [hej] using (he j).symm
        have hi0 : e i = 0 := by
          have hh := he i
          rw [hR, mul_eq_zero] at hh
          exact_mod_cast hh.resolve_left (ne_of_gt (hv i))
        simp [hej,hi0]
      · simp [hzj,zero_pow hej]
    · have haj : a j ≠ 0 := (map_ne_zero_iff _ (DVRBranch.expansion_injective ℂ A)).mpr hzj
      have hb := BranchContact.contact_bound v hv a han j (a j).order.toNat
        (PowerSeries.coe_toNat_order haj).symm
      have hb' : contact v z hne * v j ≤ ((addVal A (z j)).toNat : ℚ) := by
        simpa only [contact, a, DVRBranch.expansion_order] using hb
      have hrat : ((addVal A (z i ^ e i)).toNat : ℚ) ≤
          ((addVal A (z j ^ e j)).toNat : ℚ) := by
        rw [hiR, addVal_pow_toNat hzj, Nat.cast_mul, ← he j]
        nlinarith [mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg (e j) : (0:ℚ) ≤ e j)]
      have hnat : (addVal A (z i ^ e i)).toNat ≤ (addVal A (z j ^ e j)).toNat := by
        exact_mod_cast hrat
      rw [← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzi)),
        ← ENat.natCast_toNat (addVal_eq_top_iff.not.mpr (pow_ne_zero _ hzj))]
      exact_mod_cast hnat
  have heq := powerIdeal_eq_singleton z e i hmin
  refine ⟨i,hzi,heq,?_⟩
  rw [heq, CurveLocalOrder.length_quotient_span_eq_addVal (pow_ne_zero _ hzi)]
  exact hiR

theorem colength_eq_contact
    (v : ι → ℚ) (hv : ∀ i, 0 < v i) (z : ι → A) (hne : ∃ i, z i ≠ 0)
    (R : ℚ) (e : ι → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ powerIdeal z e)).toNat : ℚ) = R * contact v z hne := by
  obtain ⟨_,_,_,h⟩ := exists_generator_colength_eq_contact v hv z hne R e he
  exact h

end PiExponent.BranchContactIdeal

end

end OAI
end Source0299
