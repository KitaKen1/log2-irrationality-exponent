/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part012
public import LogTwoCheckpoints.Part016
public import LogTwoCheckpoints.Part019
public import LogTwoCheckpoints.Part022
public import LogTwoCheckpoints.Part026
public import LogTwoCheckpoints.Part029
public import LogTwoCheckpoints.Part030
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.RingHom.Flat
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedAlgebraEvaluation.lean
section Source0775
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedAlgebraEvaluation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.LocalizedAlgebraEvaluation
noncomputable section
variable {P A B : Type*} [CommRing P] [CommRing A] [CommRing B] [Algebra P A]
variable (S : Submonoid P) (T : Submonoid B) (f : A →+* B)
  (hf : ∀ s : S, f (algebraMap P A s.val) ∈ T)

def denominatorMap : S →* T where
  toFun s := ⟨f (algebraMap P A s.val), hf s⟩
  map_one' := Subtype.ext (by simp)
  map_mul' s t := Subtype.ext (by simp)

@[simp] theorem denominatorMap_val (s : S) :
    (denominatorMap S T f hf s).val = f (algebraMap P A s.val) := rfl

def evaluation : LocalizedModule S A →+ Localization T where
  toFun z := z.liftOn
    (fun p => IsLocalization.mk' (Localization T) (f p.1) (denominatorMap S T f hf p.2))
    (by
      rintro ⟨m,s⟩ ⟨m',s'⟩ ⟨u, hu⟩
      apply (IsLocalization.eq (M := T) (S := Localization T)).mpr
      refine ⟨denominatorMap S T f hf u, ?_⟩
      change f (algebraMap P A u.val) * (f (algebraMap P A s'.val) * f m) =
        f (algebraMap P A u.val) * (f (algebraMap P A s.val) * f m')
      simpa only [Submonoid.smul_def, Algebra.smul_def, map_mul] using congrArg f hu)
  map_zero' := by
    rw [← LocalizedModule.zero_mk (1 : S), LocalizedModule.liftOn_mk,
      map_zero, IsLocalization.mk'_zero]
  map_add' z w := by
    induction z, w using LocalizedModule.induction_on₂ with
    | h m m' s s' =>
      simp only [LocalizedModule.mk_add_mk, LocalizedModule.liftOn_mk,
        Submonoid.smul_def, Algebra.smul_def, map_add, map_mul]
      simpa only [denominatorMap_val, mul_comm] using
        (IsLocalization.mk'_add (M := T) (S := Localization T) (f m) (f m')
          (denominatorMap S T f hf s) (denominatorMap S T f hf s'))

@[simp] theorem evaluation_mk (m : A) (s : S) :
    evaluation S T f hf (LocalizedModule.mk m s) =
      IsLocalization.mk' (Localization T) (f m) (denominatorMap S T f hf s) :=
by
  simp only [evaluation, AddMonoidHom.coe_mk, ZeroHom.coe_mk, LocalizedModule.liftOn_mk]

theorem evaluation_smul (p : P) (z : LocalizedModule S A) :
    evaluation S T f hf (p • z) =
      algebraMap B (Localization T) (f (algebraMap P A p)) * evaluation S T f hf z := by
  induction z using LocalizedModule.induction_on with
  | h m s =>
    rw [LocalizedModule.smul'_mk, evaluation_mk, evaluation_mk]
    simp only [Algebra.smul_def, map_mul]
    exact (IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _).symm

end
end PiExponent.LocalizedAlgebraEvaluation

end OAI
end Source0775

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesLocalizedChart.lean
section Source0776
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesLocalizedChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesLocalizedChart
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J]
variable (I : Ideal R) (a : J → I) (j : J)

abbrev LocalizationModule :=
  letI := presentationAlgebra I a
  LocalizedModule (Submonoid.powers (MvPolynomial.X j : MvPolynomial J R)) (reesAlgebra I)

def localizationEvaluation : LocalizationModule I a j →+ Localization.Away (a j).val := by
  letI := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation (Submonoid.powers (MvPolynomial.X j))
    (Submonoid.powers (a j).val) (evaluation I) (by
      rintro ⟨_, k, rfl⟩
      refine ⟨k, ?_⟩
      change (a j).val ^ k = evaluation I (presentation I a (MvPolynomial.X j ^ k))
      simp only [map_pow, presentation_X, evaluation_generator])

omit [Fintype J] in
theorem localizationEvaluation_fraction (m : reesAlgebra I) (k : ℕ) :
    letI := presentationAlgebra I a
    localizationEvaluation I a j (fraction (MvPolynomial.X j : MvPolynomial J R) m k) =
      IsLocalization.mk' (Localization.Away (a j).val) (evaluation I m)
        (powerDenominator (a j).val k) := by
  let := presentationAlgebra I a
  unfold localizationEvaluation fraction
  rw [LocalizedAlgebraEvaluation.evaluation_mk]
  congr 1
  apply Subtype.ext
  change evaluation I (presentation I a (MvPolynomial.X j ^ k)) = (a j).val ^ k
  simp only [map_pow, presentation_X, evaluation_generator]

abbrev Piece (n : ℕ) :=
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  degreePiece (grading (J := J) (R := R)) (integerPiece I)
    (MvPolynomial.X j) 1 (variable_mem j) (n : ℤ)

def pieceEvaluation (n : ℕ) : Piece I a j n →+ Localization.Away (a j).val := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (localizationEvaluation I a j).comp (Piece I a j n).subtype

theorem pieceEvaluation_injective (n : ℕ) : Function.Injective (pieceEvaluation I a j n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k) := by
    change m ∈ integerPiece I (↑(n + k))
    simpa only [Nat.cast_add, mul_one] using hm
  have heval : evaluation I m = (m : Polynomial R).coeff (n + k) := evaluation_piece I ⟨m, hm'⟩
  change localizationEvaluation I a j z.val = 0 at hz
  rw [hrep, localizationEvaluation_fraction] at hz
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (a j).val) (S := Localization.Away (a j).val) _ _).mp hz
  obtain ⟨l, rfl⟩ := hb
  apply Subtype.ext
  change z.val = 0
  rw [hrep, fraction_eq_zero]
  refine ⟨l, ?_⟩
  change presentation I a (MvPolynomial.X j ^ l) * m = 0
  rw [map_pow, presentation_X]
  apply Subtype.ext
  change (generator I (a j) : Polynomial R) ^ l * (m : Polynomial R) = 0
  rw [(mem_piece I (n + k) m).mp hm', generator_val,
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
  rw [heval] at hbm
  simp only [hbm, map_zero]

theorem pieceEvaluation_mem_chartPower (n : ℕ) (z : Piece I a j n) :
    ∃ s : ↥((I ^ n).map (chartBase I (a j))),
      chartMap I (a j) s.val = pieceEvaluation I a j n z := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k) := by
    change m ∈ integerPiece I (↑(n + k))
    simpa only [Nat.cast_add, mul_one] using hm
  let q : chart I (a j) := HomogeneousLocalization.Away.mk (piece I)
    (generator_mem I (a j)) (n + k) m (by simpa using hm')
  have hmem : (chartBase I (a j) (a j).val) ^ n * q ∈
      (I ^ n).map (chartBase I (a j)) := by
    rw [ReesPushdown.chart_ordinaryPower_principal]
    exact Ideal.mul_mem_right q _ (Ideal.subset_span (by simp))
  refine ⟨⟨(chartBase I (a j) (a j).val) ^ n * q, hmem⟩, ?_⟩
  change chartMap I (a j) ((chartBase I (a j) (a j).val) ^ n * q) =
    localizationEvaluation I a j z.val
  have hmap : chartMap I (a j) ((chartBase I (a j) (a j).val) ^ n) =
      algebraMap R (Localization.Away (a j).val) ((a j).val ^ n) := by
    calc
      _ = (chartMap I (a j) (chartBase I (a j) (a j).val)) ^ n :=
        (chartMap I (a j)).map_pow _ n
      _ = _ := by rw [chartMap_base, map_pow]
  rw [hrep, localizationEvaluation_fraction, map_mul, hmap]
  change (algebraMap R (Localization.Away (a j).val) ((a j).val ^ n)) *
    chartMap I (a j) (HomogeneousLocalization.Away.mk (piece I)
      (generator_mem I (a j)) (n + k) m _) = _
  rw [chartMap_mk, IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_of_eq
  change (a j).val ^ (n + k) * evaluation I m =
    (a j).val ^ k * ((a j).val ^ n * evaluation I m)
  rw [pow_add]
  ring

theorem chartPower_mem_pieceEvaluation (n : ℕ)
    (s : ↥((I ^ n).map (chartBase I (a j)))) :
    ∃ z : Piece I a j n, pieceEvaluation I a j n z = chartMap I (a j) s.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, b, hb, hs⟩ := ReesPushdown.chart_ordinaryPower_fraction I (a j) n s.val s.property
  let m := ReesPushdown.ordinaryPowerEquivPiece I (n + k) ⟨b, hb⟩
  have hm : m.val ∈ integerPiece I ((n : ℤ) + (k : ℤ) * 1) := by
    have hm0 : m.val ∈ integerPiece I (↑(n + k)) := m.property
    simpa only [Nat.cast_add, mul_one] using hm0
  let z : Piece I a j n := ⟨fraction (MvPolynomial.X j : MvPolynomial J R) m.val k,
    k, m.val, hm, rfl⟩
  refine ⟨z, ?_⟩
  change localizationEvaluation I a j (fraction (MvPolynomial.X j : MvPolynomial J R) m.val k) = _
  rw [localizationEvaluation_fraction, hs]
  have heval : evaluation I m.val = b := by
    rw [evaluation_piece I m]
    exact ReesPushdown.ordinaryPowerEquivPiece_apply_coeff I (n + k) ⟨b, hb⟩
  rw [heval]
  rfl

def chartPowerMap (n : ℕ) : Piece I a j n →+ ↥((I ^ n).map (chartBase I (a j))) where
  toFun z := (pieceEvaluation_mem_chartPower I a j n z).choose
  map_zero' := by
    apply Subtype.ext
    apply chartMap_injective I (a j)
    rw [(pieceEvaluation_mem_chartPower I a j n 0).choose_spec, map_zero]
    change 0 = chartMap I (a j) 0
    exact (map_zero _).symm
  map_add' z w := by
    apply Subtype.ext
    apply chartMap_injective I (a j)
    change chartMap I (a j) _ = chartMap I (a j) (_ + _)
    rw [(pieceEvaluation_mem_chartPower I a j n (z+w)).choose_spec, map_add, map_add,
      (pieceEvaluation_mem_chartPower I a j n z).choose_spec,
      (pieceEvaluation_mem_chartPower I a j n w).choose_spec]

theorem chartPowerMap_evaluation (n : ℕ) (z : Piece I a j n) :
    chartMap I (a j) (chartPowerMap I a j n z).val = pieceEvaluation I a j n z :=
  (pieceEvaluation_mem_chartPower I a j n z).choose_spec

def chartPowerEquiv (n : ℕ) : Piece I a j n ≃+ ↥((I ^ n).map (chartBase I (a j))) :=
  AddEquiv.ofBijective (chartPowerMap I a j n) ⟨by
    intro z w hzw
    apply pieceEvaluation_injective I a j n
    rw [← chartPowerMap_evaluation, ← chartPowerMap_evaluation, hzw], by
    intro s
    obtain ⟨z, hz⟩ := chartPower_mem_pieceEvaluation I a j n s
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply chartMap_injective I (a j)
    rw [chartPowerMap_evaluation, hz]⟩

end
end PiExponent.ReesLocalizedChart

end OAI
end Source0776

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesLocalizedIntersections.lean
section Source0777
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesLocalizedIntersections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesLocalizedIntersections
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def coefficientProduct (s : Finset J) : R := ∏ j ∈ s, (a j).val

omit [Fintype J] [DecidableEq J] in
theorem evaluation_presentation_product (s : Finset J) :
    evaluation I (presentation I a (coverProduct MvPolynomial.X s)) = coefficientProduct I a s := by
  simp only [coverProduct, coefficientProduct, map_prod, presentation_X, evaluation_generator]

abbrev LocalizationModule (s : Finset J) :=
  letI := presentationAlgebra I a
  LocalizedModule (Submonoid.powers (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s))
    (reesAlgebra I)

def localizationEvaluation (s : Finset J) :
    LocalizationModule I a s →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation (Submonoid.powers (coverProduct MvPolynomial.X s))
    (Submonoid.powers (coefficientProduct I a s)) (evaluation I) (by
      rintro ⟨_, k, rfl⟩
      refine ⟨k, ?_⟩
      change coefficientProduct I a s ^ k =
        evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k))
      rw [map_pow, map_pow, evaluation_presentation_product])

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_fraction (s : Finset J) (m : reesAlgebra I) (k : ℕ) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (fraction
      (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  let := presentationAlgebra I a
  unfold localizationEvaluation fraction
  rw [LocalizedAlgebraEvaluation.evaluation_mk]
  congr 1
  apply Subtype.ext
  change evaluation I (presentation I a (coverProduct MvPolynomial.X s ^ k)) =
    coefficientProduct I a s ^ k
  rw [map_pow, map_pow, evaluation_presentation_product]

omit [Fintype J] [DecidableEq J] in
theorem localizationEvaluation_smul (s : Finset J) (p : MvPolynomial J R)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a s (p • z) =
      algebraMap R (Localization.Away (coefficientProduct I a s))
        (evaluation I (presentation I a p)) * localizationEvaluation I a s z := by
  let := presentationAlgebra I a
  exact LocalizedAlgebraEvaluation.evaluation_smul _ _ _ _ p z

def coefficientRestriction {s t : Finset J} (hst : s ⊆ t) :
    Localization.Away (coefficientProduct I a s) →+*
      Localization.Away (coefficientProduct I a t) :=
  IsLocalization.Away.lift (coefficientProduct I a s)
    (IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
      exact Finset.prod_dvd_prod_of_subset s t _ hst))

omit [Fintype J] [DecidableEq J] in
@[simp] theorem coefficientRestriction_algebraMap {s t : Finset J} (hst : s ⊆ t) (r : R) :
    coefficientRestriction I a hst (algebraMap R (Localization.Away (coefficientProduct I a s)) r) =
      algebraMap R (Localization.Away (coefficientProduct I a t)) r :=
  IsLocalization.Away.lift_eq _ _ _

omit [Fintype J] in
theorem localizationEvaluation_restriction {s t : Finset J} (hst : s ⊆ t)
    (z : LocalizationModule I a s) :
    letI := presentationAlgebra I a
    localizationEvaluation I a t
      (restriction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
        (coverProduct MvPolynomial.X t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z) =
      coefficientRestriction I a hst (localizationEvaluation I a s z) := by
  let := presentationAlgebra I a
  induction z using LocalizedModule.induction_on with
  | h m den =>
    obtain ⟨k, hk⟩ := den.property
    have hd : den = powerDenominator (coverProduct MvPolynomial.X s) k := Subtype.ext hk.symm
    subst den
    change localizationEvaluation I a t (restriction _ _ _ (fraction _ m k)) =
      coefficientRestriction I a hst (localizationEvaluation I a s (fraction _ m k))
    have hu : IsUnit (algebraMap R (Localization.Away (coefficientProduct I a t))
        (coefficientProduct I a s)) :=
      IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a t) (by
        exact Finset.prod_dvd_prod_of_subset s t _ hst)
    apply (hu.pow k).mul_right_injective
    calc
      _ = localizationEvaluation I a t
          (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s ^ k •
            restriction _ _ _ (fraction _ m k)) := by
        rw [localizationEvaluation_smul, map_pow, map_pow,
          evaluation_presentation_product, map_pow]
      _ = localizationEvaluation I a t (fraction (coverProduct MvPolynomial.X t) m 0) := by
        rw [← map_smul, power_smul_fraction, restriction_fraction_zero]
      _ = algebraMap R (Localization.Away (coefficientProduct I a t)) (evaluation I m) := by
        rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
      _ = _ := by
        have hspec := congrArg (coefficientRestriction I a hst)
          (IsLocalization.mk'_spec' (Localization.Away (coefficientProduct I a s))
            (evaluation I m) (powerDenominator (coefficientProduct I a s) k))
        rw [localizationEvaluation_fraction]
        simpa only [map_mul, coefficientRestriction_algebraMap, powerDenominator_val, map_pow]
          using hspec.symm

abbrev Piece (s : Finset J) (n : ℕ) :=
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  IntersectionPiece (grading (J := J) (R := R)) (integerPiece I)
    MvPolynomial.X variable_mem s n

def pieceEvaluation (s : Finset J) (n : ℕ) :
    Piece I a s n →+ Localization.Away (coefficientProduct I a s) := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact (localizationEvaluation I a s).comp (Piece I a s n).subtype

theorem pieceEvaluation_restriction {s t : Finset J} (hst : s ⊆ t) (n : ℕ)
    (z : Piece I a s n) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    pieceEvaluation I a t n (setRestriction (grading (J := J) (R := R)) (integerPiece I)
      MvPolynomial.X variable_mem hst n z) =
      coefficientRestriction I a hst (pieceEvaluation I a s n z) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  exact localizationEvaluation_restriction I a hst z.val

theorem pieceEvaluation_injective (s : Finset J) (n : ℕ) :
    Function.Injective (pieceEvaluation I a s n) := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply (injective_iff_map_eq_zero _).mpr
  intro z hz
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hp : presentation I a (coverProduct MvPolynomial.X s) ∈ piece I s.card :=
    presentation_integer_mem I a
      (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)
  have heval : evaluation I m = (m : Polynomial R).coeff (n + k * s.card) :=
    evaluation_piece I ⟨m, hm'⟩
  have hep : evaluation I (presentation I a (coverProduct MvPolynomial.X s)) =
      (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, hp⟩
  change localizationEvaluation I a s z.val = 0 at hz
  rw [hrep, localizationEvaluation_fraction] at hz
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hz
  obtain ⟨l, rfl⟩ := hb
  apply Subtype.ext
  change z.val = 0
  rw [hrep, fraction_eq_zero]
  refine ⟨l, ?_⟩
  change presentation I a (coverProduct MvPolynomial.X s ^ l) * m = 0
  rw [map_pow]
  apply Subtype.ext
  change (presentation I a (coverProduct MvPolynomial.X s) : Polynomial R) ^ l *
    (m : Polynomial R) = 0
  rw [(mem_piece I s.card _).mp hp, (mem_piece I (n + k * s.card) m).mp hm',
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial]
  rw [← hep, evaluation_presentation_product]
  rw [heval] at hbm
  simp only [hbm, map_zero]

end
end PiExponent.ReesLocalizedIntersections

end OAI
end Source0777

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductChart.lean
section Source0778
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesProductChart
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def productGenerator (s : Finset J) : reesAlgebra I :=
  presentation I a (coverProduct MvPolynomial.X s)

theorem productGenerator_mem (s : Finset J) : productGenerator I a s ∈ piece I s.card :=
  presentation_integer_mem I a
    (coverProduct_mem (grading (J := J) (R := R)) MvPolynomial.X variable_mem s)

omit [Fintype J] [DecidableEq J] in
theorem evaluation_productGenerator (s : Finset J) :
    evaluation I (productGenerator I a s) = coefficientProduct I a s :=
  evaluation_presentation_product I a s

omit [Fintype J] [DecidableEq J] in
theorem productGenerator_eq_prod (s : Finset J) :
    productGenerator I a s = ∏ j ∈ s, generator I (a j) := by
  simp only [productGenerator, coverProduct, map_prod, presentation_X]

abbrev Chart (s : Finset J) := HomogeneousLocalization.Away (piece I) (productGenerator I a s)

def chartMap (s : Finset J) : Chart I a s →+* Localization.Away (coefficientProduct I a s) :=
  (IsLocalization.map (M := Submonoid.powers (productGenerator I a s))
    (S := Localization.Away (productGenerator I a s))
    (T := Submonoid.powers (coefficientProduct I a s))
    (Localization.Away (coefficientProduct I a s)) (evaluation I)
    (by rintro _ ⟨k, rfl⟩; exact ⟨k, by simp only [map_pow, evaluation_productGenerator]⟩)).comp
      (algebraMap (Chart I a s) (Localization.Away (productGenerator I a s)))

theorem chartMap_mk (s : Finset J) (k : ℕ) (m : reesAlgebra I)
    (hm : m ∈ piece I (k • s.card)) :
    chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) k m hm) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s)) (evaluation I m)
        (powerDenominator (coefficientProduct I a s) k) := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp only [map_pow, evaluation_productGenerator, powerDenominator_val]

theorem chartMap_injective (s : Finset J) : Function.Injective (chartMap I a s) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro z hz
  change z = 0
  obtain ⟨k, m, hm, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) z
  have hzero := RingHom.mem_ker.mp hz
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbm⟩ := (IsLocalization.mk'_eq_zero_iff
    (M := Submonoid.powers (coefficientProduct I a s))
    (S := Localization.Away (coefficientProduct I a s)) _ _).mp hzero
  obtain ⟨l, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨productGenerator I a s ^ l, ⟨l, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have he : evaluation I m = (m : Polynomial R).coeff (k • s.card) := evaluation_piece I ⟨m, hm⟩
  have hep : evaluation I (productGenerator I a s) =
      (productGenerator I a s : Polynomial R).coeff s.card :=
    evaluation_piece I ⟨_, productGenerator_mem I a s⟩
  change (productGenerator I a s : Polynomial R) ^ l * (m : Polynomial R) = 0
  rw [(mem_piece I (k • s.card) m).mp hm,
    (mem_piece I s.card _).mp (productGenerator_mem I a s),
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    ← hep, evaluation_productGenerator]
  rw [he] at hbm
  simp only [hbm, map_zero]

def chartBase (s : Finset J) : R →+* Chart I a s :=
  (HomogeneousLocalization.fromZeroRingHom (piece I)
    (Submonoid.powers (productGenerator I a s))).comp (zeroEquiv I).toRingHom

theorem chartMap_base (s : Finset J) (r : R) :
    chartMap I a s (chartBase I a s r) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • s.card) := by
    simp [mem_piece]
  refine (chartMap_mk I a s 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he, powerDenominator_zero, IsLocalization.mk'_one]

variable {s : Finset J} {j : J} (hj : j ∈ s)
include hj

omit [Fintype J] in
theorem coefficientProduct_eq_pivot :
    coefficientProduct I a s = (a j).val * coefficientProduct I a (s.erase j) := by
  exact (Finset.mul_prod_erase s (fun i => (a i).val) hj).symm

def ratio (b : I) : Chart I a s :=
  HomogeneousLocalization.Away.mk (piece I) (productGenerator_mem I a s) 1
    (generator I b * productGenerator I a (s.erase j)) (by
      have h := SetLike.mul_mem_graded (generator_mem I b)
        (productGenerator_mem I a (s.erase j))
      simpa only [one_nsmul, Nat.add_comm 1, Finset.card_erase_add_one hj] using h)

theorem chartMap_ratio (b : I) :
    chartMap I a s (ratio I a hj b) =
      IsLocalization.mk' (Localization.Away (coefficientProduct I a s))
        (b.val * coefficientProduct I a (s.erase j))
        (powerDenominator (coefficientProduct I a s) 1) := by
  rw [ratio, chartMap_mk, map_mul, evaluation_generator, evaluation_productGenerator]

theorem base_mul_ratio (b : I) :
    chartBase I a s (a j).val * ratio I a hj b = chartBase I a s b.val := by
  apply chartMap_injective I a s
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_iff_eq_mul.mpr
  rw [← map_mul]
  congr 1
  change (a j).val * (b.val * coefficientProduct I a (s.erase j)) =
    b.val * coefficientProduct I a s ^ 1
  rw [pow_one, coefficientProduct_eq_pivot I a hj]
  ring

theorem map_ideal_principal :
    I.map (chartBase I a s) = Ideal.span {chartBase I a s (a j).val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a s b ∈ Ideal.span {chartBase I a s (a j).val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a hj ⟨b, hb⟩, (base_mul_ratio I a hj ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ (a j).property

theorem chart_ordinaryPower_principal (n : ℕ) :
    (I ^ n).map (chartBase I a s) = Ideal.span {(chartBase I a s (a j).val) ^ n} := by
  rw [Ideal.map_pow, map_ideal_principal I a hj, Ideal.span_singleton_pow]

theorem chart_generator_regular : IsRegular (chartBase I a s (a j).val) := by
  have hu : IsUnit (chartMap I a s (chartBase I a s (a j).val)) := by
    rw [chartMap_base]
    exact IsLocalization.Away.isUnit_of_dvd (coefficientProduct I a s)
      ⟨coefficientProduct I a (s.erase j), coefficientProduct_eq_pivot I a hj⟩
  constructor
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a s) h
  · intro x y h
    apply chartMap_injective I a s
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a s) h

end
end PiExponent.ReesProductChart

end OAI
end Source0778

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductSchemeChart.lean
section Source0779
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductSchemeChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem exists_chartMorphism :
    ∃ j : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I,
      j = Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  ⟨_, rfl⟩

def chartMorphism : Spec (CommRingCat.of (Chart I a s)) ⟶ affineBlowup I :=
  (exists_chartMorphism I a hs).choose

theorem chartMorphism_eq :
    chartMorphism I a hs =
      Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs) :=
  (exists_chartMorphism I a hs).choose_spec

instance chartMorphism_open : IsOpenImmersion (chartMorphism I a hs) := by
  rw [chartMorphism_eq]
  exact inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := s.card) (piece I) (productGenerator I a s)
      (productGenerator_mem I a s) (Finset.card_pos.mpr hs)))

theorem chartMorphism_projection :
    chartMorphism I a hs ≫ projection I =
      Spec.map (CommRingCat.ofHom (ReesProductChart.chartBase I a s)) := by
  rw [chartMorphism_eq]
  change Proj.awayι (piece I) (productGenerator I a s) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

local instance (q : I) : IsOpenImmersion ((chartCover I).f q) :=
  (chartCover I).map_prop q

theorem chartMorphism_opensRange :
    (chartMorphism I a hs).opensRange =
      s.inf (fun j => ((chartCover I).f (a j)).opensRange) := by
  have he : (chartMorphism I a hs).opensRange =
      (Proj.awayι (piece I) (productGenerator I a s) (productGenerator_mem I a s)
        (Finset.card_pos.mpr hs)).opensRange := by
    apply SetLike.coe_injective
    simp only [Scheme.Hom.coe_opensRange]
    rw [chartMorphism_eq]
    rfl
  rw [he]
  change (Proj.awayι (piece I) (productGenerator I a s) _ _).opensRange = _
  rw [Proj.opensRange_awayι, productGenerator_eq_prod]
  have h : ∀ t : Finset J,
      Proj.basicOpen (piece I) (∏ j ∈ t, generator I (a j)) =
      t.inf (fun j => Proj.basicOpen (piece I) (generator I (a j))) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih => rw [Finset.prod_insert hj, Proj.basicOpen_mul, ih, Finset.inf_insert]
  rw [h]
  congr 1
  funext j
  exact (Proj.opensRange_awayι (piece I) (generator I (a j))
    (generator_mem I (a j)) (by decide)).symm

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chartMorphism I a hs).opensRange, isAffineOpen_opensRange _⟩

variable {p : J} (hp : p ∈ s)

def chartEquation : Γ(Spec (CommRingCat.of (Chart I a s)), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv
    (ReesProductChart.chartBase I a s (a p).val)

include hp in
theorem exceptional_chart :
    ((exceptionalIdeal I).comap (chartMorphism I a hs)).ideal
      ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {chartEquation I a (s := s) (p := p)} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartMorphism_projection,
    PiExponentSeshadri.IdealPullback.specIdeal_comap,
    PiExponentSeshadri.IdealPullback.specIdeal_top,
    ReesProductChart.map_ideal_principal I a hp, Ideal.map_span, Set.image_singleton]
  rfl

include hp in
theorem chartEquation_regular : IsLeftRegular (chartEquation I a (s := s) (p := p)) := by
  exact PiExponentSeshadri.IdealModule.regular_map_flat _
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of (Chart I a s))).inv))
    (ReesProductChart.chart_generator_regular I a hp).left

end PiExponent.ReesProductPowerSections
end

end OAI
end Source0779

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductFrames.lean
section Source0780
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
namespace PiExponent.ReesProductPowerSections
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)
variable {p : J} (hp : p ∈ s)
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.idealChartFrame

include hp in

theorem chartFrame_nonempty :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme) := by
  rw [exceptionalLineBundle_sheaf_eq]
  exact ⟨ExceptionalAffineChart.idealChartFrame (Y := affineBlowup I) (chartMorphism I a hs) (exceptionalIdeal I)
    (chartEquation I a (s := s) (p := p))
    (exceptional_chart I a hs hp) (chartEquation_regular I a hp)⟩

def chartFrame :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end PiExponent.ReesProductPowerSections
end

end OAI
end Source0780

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFixedChart.lean
section Source0781
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedChart.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem exists_coordinateRing : ∃ C : CommRingCat, C = CommRingCat.of (Chart I a s) := ⟨_,rfl⟩
def coordinateRing : CommRingCat := (exists_coordinateRing I a s).choose
omit [Fintype J] [DecidableEq J] in
theorem coordinateRing_eq : coordinateRing I a s = CommRingCat.of (Chart I a s) :=
  (exists_coordinateRing I a s).choose_spec

def coordinateEquiv : coordinateRing I a s ≃+* Chart I a s :=
  (eqToIso (coordinateRing_eq I a s)).commRingCatIsoToRingEquiv

abbrev coordinateInv : CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s :=
  CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom

def base : R →+* coordinateRing I a s :=
  (coordinateInv I a s).hom.comp (ReesProductChart.chartBase I a s)

instance coordinateInv_isIso :
    IsIso (CommRingCat.ofHom (coordinateEquiv I a s).symm.toRingHom :
    CommRingCat.of (Chart I a s) ⟶ coordinateRing I a s) := by
  change IsIso (eqToIso (coordinateRing_eq I a s)).inv
  infer_instance

local instance coordinateSpec_isIso :
    IsIso (Spec.map (coordinateInv I a s)) :=
  inferInstanceAs (IsIso
    (Scheme.Spec.mapIso (eqToIso (coordinateRing_eq I a s)).symm.op).hom)

variable {s} (hs : s.Nonempty)
def chart : Spec (coordinateRing I a s) ⟶ affineBlowup I :=
  Spec.map (coordinateInv I a s) ≫
    ReesProductPowerSections.chartMorphism I a hs

instance : IsOpenImmersion (chart I a hs) := by
  exact IsOpenImmersion.comp _ _

theorem chart_projection :
    chart I a hs ≫ projection I = Spec.map (CommRingCat.ofHom (base I a s)) := by
  rw [chart, Category.assoc, ReesProductPowerSections.chartMorphism_projection]
  exact (Spec.map_comp
    (show CommRingCat.of R ⟶ CommRingCat.of (Chart I a s) from
      CommRingCat.ofHom (ReesProductChart.chartBase I a s))
    (coordinateInv I a s)).symm

theorem chart_opensRange :
    (chart I a hs).opensRange = (ReesProductPowerSections.chartMorphism I a hs).opensRange :=
  Scheme.Hom.opensRange_comp_of_isIso _ _

def chartOpen : (affineBlowup I).affineOpens :=
  ⟨(chart I a hs).opensRange, isAffineOpen_opensRange _⟩

theorem chartOpen_eq :
    (chartOpen I a hs).1 = (ReesProductPowerSections.chartOpen I a hs).1 :=
  chart_opensRange I a hs

end
end PiExponent.ReesFrozenChart

end OAI
end Source0781

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFixedFrames.lean
section Source0782
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesFrozenChart
noncomputable section
open CategoryTheory AlgebraicGeometry
open PiExponentSeshadri.ReesGrading PiExponent.ReesProductChart
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} (hs : s.Nonempty)

theorem frame_nonempty_congr {X : Scheme} (M : X.Modules) {U V : X.Opens}
    (h : U = V)
    (he : Nonempty (M.restrict U.ι ≅ PiExponentSeshadri.Frames.O U.toScheme)) :
    Nonempty (M.restrict V.ι ≅ PiExponentSeshadri.Frames.O V.toScheme) := by
  subst V
  exact he

theorem chartFrame_nonempty {p : J} (hp : p ∈ s) :
    Nonempty ((exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme) :=
  frame_nonempty_congr (exceptionalLineBundle I).sheaf (chartOpen_eq I a hs).symm
    (ReesProductPowerSections.chartFrame_nonempty I a hs hp)

def chartFrame {p : J} (hp : p ∈ s) :
    (exceptionalLineBundle I).sheaf.restrict (chartOpen I a hs).1.ι ≅
      PiExponentSeshadri.Frames.O (chartOpen I a hs).1.toScheme :=
  (chartFrame_nonempty I a hs hp).some

end
end PiExponent.ReesFrozenChart

end OAI
end Source0782

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductPower.lean
section Source0783
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductPower.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesProductPower
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) {s : Finset J} {j : J} (hj : j ∈ s)
include hj

theorem pieceEvaluation_mem_chartPower (n : ℕ) (z : Piece I a s n) :
    ∃ q : ↥((I ^ n).map (ReesProductChart.chartBase I a s)),
      ReesProductChart.chartMap I a s q.val = pieceEvaluation I a s n z := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  obtain ⟨k, m, hm, hrep⟩ := z.property
  have hm' : m ∈ piece I (n + k * s.card) := by
    change m ∈ integerPiece I (↑(n + k * s.card))
    simpa only [Nat.cast_add, Nat.cast_mul] using hm
  have hc : s.card = (s.erase j).card + 1 := (Finset.card_erase_add_one hj).symm
  have hdeg : (n + k * s.card) + n • (s.erase j).card = (n + k) • s.card := by
    rw [hc]
    simp only [nsmul_eq_mul, Nat.cast_id]
    ring
  have hnum : m * productGenerator I a (s.erase j) ^ n ∈ piece I ((n + k) • s.card) := by
    have h := SetLike.mul_mem_graded hm'
      (SetLike.pow_mem_graded n (productGenerator_mem I a (s.erase j)))
    simpa only [hdeg] using h
  let q : Chart I a s := HomogeneousLocalization.Away.mk (piece I)
    (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum
  have hmem : (ReesProductChart.chartBase I a s (a j).val) ^ n * q ∈
      (I ^ n).map (ReesProductChart.chartBase I a s) := by
    rw [chart_ordinaryPower_principal I a hj]
    exact Ideal.mul_mem_right q _ (Ideal.subset_span (by simp))
  refine ⟨⟨(ReesProductChart.chartBase I a s (a j).val) ^ n * q, hmem⟩, ?_⟩
  change ReesProductChart.chartMap I a s
    ((ReesProductChart.chartBase I a s (a j).val) ^ n * q) =
      localizationEvaluation I a s z.val
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [hrep, localizationEvaluation_fraction, map_mul, hmap]
  change algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) *
    ReesProductChart.chartMap I a s (HomogeneousLocalization.Away.mk (piece I)
      (productGenerator_mem I a s) (n + k) (m * productGenerator I a (s.erase j) ^ n) hnum) = _
  rw [ReesProductChart.chartMap_mk, map_mul, (evaluation I).map_pow, evaluation_productGenerator,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  apply IsLocalization.mk'_eq_of_eq
  change coefficientProduct I a s ^ (n + k) * evaluation I m =
    coefficientProduct I a s ^ k * ((a j).val ^ n *
      (evaluation I m * coefficientProduct I a (s.erase j) ^ n))
  rw [pow_add, coefficientProduct_eq_pivot I a hj, mul_pow]
  ring

theorem chartPower_mem_pieceEvaluation (n : ℕ)
    (q : ↥((I ^ n).map (ReesProductChart.chartBase I a s))) :
    ∃ z : Piece I a s n,
      pieceEvaluation I a s n z = ReesProductChart.chartMap I a s q.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  have hq : q.val ∈ Ideal.span {(ReesProductChart.chartBase I a s (a j).val) ^ n} :=
    (congrArg (fun K : Ideal (Chart I a s) => q.val ∈ K)
      (chart_ordinaryPower_principal I a hj n)).mp q.property
  rw [Ideal.mem_span_singleton] at hq
  obtain ⟨r, hr⟩ := hq
  obtain ⟨k, p, hp, hrep⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (productGenerator_mem I a s) r
  let m : reesAlgebra I := generator I (a j) ^ n * p
  have hm' : m ∈ piece I (n + k * s.card) := by
    have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n (generator_mem I (a j))) hp
    simpa only [nsmul_eq_mul, mul_one, Nat.cast_id, m] using h
  have hm : m ∈ integerPiece I ((n : ℤ) + (k : ℤ) * (s.card : ℤ)) := by
    have h : m ∈ integerPiece I (↑(n + k * s.card)) := hm'
    simpa only [Nat.cast_add, Nat.cast_mul] using h
  let z : Piece I a s n := ⟨fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k,
      k, m, hm, rfl⟩
  refine ⟨z, ?_⟩
  change localizationEvaluation I a s (fraction
    (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s) m k) = _
  have hmap : ReesProductChart.chartMap I a s
      ((ReesProductChart.chartBase I a s (a j).val) ^ n) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) ((a j).val ^ n) := by
    calc
      _ = (ReesProductChart.chartMap I a s
        (ReesProductChart.chartBase I a s (a j).val)) ^ n :=
          (ReesProductChart.chartMap I a s).map_pow _ n
      _ = _ := by rw [ReesProductChart.chartMap_base, map_pow]
  rw [localizationEvaluation_fraction, hr, (ReesProductChart.chartMap I a s).map_mul,
    hmap, ← hrep, ReesProductChart.chartMap_mk,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  congr 1
  change evaluation I (generator I (a j) ^ n * p) = (a j).val ^ n * evaluation I p
  rw [map_mul, map_pow, evaluation_generator]

def chartPowerMap (n : ℕ) : Piece I a s n →+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) where
  toFun z := (pieceEvaluation_mem_chartPower I a hj n z).choose
  map_zero' := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [(pieceEvaluation_mem_chartPower I a hj n 0).choose_spec, map_zero]
    change 0 = ReesProductChart.chartMap I a s 0
    exact (map_zero _).symm
  map_add' z w := by
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    change ReesProductChart.chartMap I a s _ = ReesProductChart.chartMap I a s (_ + _)
    rw [(pieceEvaluation_mem_chartPower I a hj n (z+w)).choose_spec, map_add, map_add,
      (pieceEvaluation_mem_chartPower I a hj n z).choose_spec,
      (pieceEvaluation_mem_chartPower I a hj n w).choose_spec]

theorem chartPowerMap_evaluation (n : ℕ) (z : Piece I a s n) :
    ReesProductChart.chartMap I a s (chartPowerMap I a hj n z).val = pieceEvaluation I a s n z :=
  (pieceEvaluation_mem_chartPower I a hj n z).choose_spec

def chartPowerEquiv (n : ℕ) : Piece I a s n ≃+
    ↥((I ^ n).map (ReesProductChart.chartBase I a s)) :=
  AddEquiv.ofBijective (chartPowerMap I a hj n) ⟨by
    intro z w hzw
    apply pieceEvaluation_injective I a s n
    rw [← chartPowerMap_evaluation I a hj n z, ← chartPowerMap_evaluation I a hj n w, hzw], by
    intro q
    obtain ⟨z, hz⟩ := chartPower_mem_pieceEvaluation I a hj n q
    refine ⟨z, ?_⟩
    apply Subtype.ext
    apply ReesProductChart.chartMap_injective I a s
    rw [chartPowerMap_evaluation I a hj n z, hz]⟩

end
end PiExponent.ReesProductPower

end OAI
end Source0783

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesFixedPower.lean
section Source0784
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedPower.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesFrozenPower
noncomputable section
open PiExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem map_power_eq (n : ℕ) :
    ((I^n).map (base I a s)).map (coordinateEquiv I a s).toRingHom =
      (I^n).map (ReesProductChart.chartBase I a s) := by
  rw [Ideal.map_map]
  have he : (coordinateEquiv I a s).toRingHom.comp (base I a s) =
      ReesProductChart.chartBase I a s := by
    apply RingHom.ext
    intro r
    exact (coordinateEquiv I a s).apply_symm_apply _
  rw [he]

omit [Fintype J] [DecidableEq J] in
theorem coordinate_mem_power (n : ℕ) (x : ((I^n).map (base I a s))) :
    coordinateEquiv I a s x.val ∈ (I^n).map (ReesProductChart.chartBase I a s) := by
  have hx := Ideal.mem_map_of_mem
    (show coordinateRing I a s →+* ReesProductChart.Chart I a s from
      (coordinateEquiv I a s).toRingHom) x.property
  exact (congrArg (fun K : Ideal (ReesProductChart.Chart I a s) =>
    coordinateEquiv I a s x.val ∈ K) (map_power_eq I a s n)).mp hx

omit [Fintype J] [DecidableEq J] in
theorem inverse_map_power_eq (n : ℕ) :
    ((I^n).map (ReesProductChart.chartBase I a s)).map (coordinateEquiv I a s).symm.toRingHom =
      (I^n).map (base I a s) := by
  rw [Ideal.map_map]
  rfl

omit [Fintype J] [DecidableEq J] in
theorem inverse_mem_power (n : ℕ)
    (y : ((I^n).map (ReesProductChart.chartBase I a s))) :
    (coordinateEquiv I a s).symm y.val ∈ (I^n).map (base I a s) := by
  have hy := Ideal.mem_map_of_mem
    (show ReesProductChart.Chart I a s →+* coordinateRing I a s from
      (coordinateEquiv I a s).symm.toRingHom) y.property
  exact (congrArg (fun K : Ideal (coordinateRing I a s) =>
    (coordinateEquiv I a s).symm y.val ∈ K) (inverse_map_power_eq I a s n)).mp hy

def powerEquiv (n : ℕ) : ((I^n).map (base I a s)) ≃+
    ((I^n).map (ReesProductChart.chartBase I a s)) where
  toFun x := ⟨coordinateEquiv I a s x.val, coordinate_mem_power I a s n x⟩
  invFun y := ⟨(coordinateEquiv I a s).symm y.val, inverse_mem_power I a s n y⟩
  left_inv x := Subtype.ext ((coordinateEquiv I a s).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((coordinateEquiv I a s).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (coordinateEquiv I a s) x.val y.val)

omit [Fintype J] [DecidableEq J] in
@[simp] theorem powerEquiv_apply (n : ℕ) (z : ((I^n).map (base I a s))) :
    (powerEquiv I a s n z).val = coordinateEquiv I a s z.val := rfl

variable {s}

def pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ) :
    ReesLocalizedIntersections.Piece I a s n ≃+ ((I^n).map (base I a s)) :=
  (ReesProductPower.chartPowerEquiv I a hp n).trans (powerEquiv I a s n).symm

theorem coordinate_pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ)
    (z : ReesLocalizedIntersections.Piece I a s n) :
    coordinateEquiv I a s (pieceEquiv I a hp n z).val =
      (ReesProductPower.chartPowerMap I a hp n z).val := by
  change (powerEquiv I a s n (pieceEquiv I a hp n z)).val = _
  exact congrArg Subtype.val ((powerEquiv I a s n).apply_symm_apply _)

end
end PiExponent.ReesFrozenPower

end OAI
end Source0784

-- Source: OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechBase.lean
section Source0785
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/ReesSheafCechBase.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesSheafCechBase
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponent.GeometrySupport
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
attribute [local irreducible] PiExponent.ExceptionalRepresentedTypes.Frame
  PiExponent.ExceptionalRepresentedTypes.Sections PiExponent.ExceptionalRepresentedTypes.representedSectionsTyped
  PiExponent.ReesFrozenPower.pieceEquiv PiExponent.ReesFrozenPower.powerEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)
local instance chartOpenImmersion (j : J) : IsOpenImmersion ((chartCover I).f (a j)) :=
  (chartCover I).map_prop (a j)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance frozenChartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

abbrev schemeFreeOpen (X : Scheme) (U : X.Opens) : X.Modules :=
  freeOpen X.ringCatSheaf U

abbrev exceptionalPower (n : ℕ) := ((exceptionalLineBundle I).pow n).sheaf

def opens (j : J) : (affineBlowup I).Opens := ((chartCover I).f (a j)).opensRange

omit [Fintype J] in
theorem tuple_mem (q : ℕ) (t : Fin (q + 1) → J) (k : Fin (q + 1)) : t k ∈ tupleSet t :=
  Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩

omit [Fintype J] in
theorem tuple_nonempty (q : ℕ) (t : Fin (q + 1) → J) : (tupleSet t).Nonempty :=
  ⟨t 0, tuple_mem q t 0⟩

def freeOpenSectionsEquiv {X : Scheme} (U : X.Opens) (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃+ Γ(M,U) :=
  { freeOpenEquiv X.ringCatSheaf M U with map_add' := fun _ _ => rfl }

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
  subst hU; subst hV
  simp [freeOpenHomCongr, freeOpenMap]
  erw [Category.id_comp]

theorem tupleOpen_eq (q : ℕ) (t : Fin (q + 1) → J) :
    (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).1 =
      CechHigher.intersection (opens I a) t := by
  change (chartMap I a (tuple_nonempty q t)).opensRange = _
  rw [ReesFrozenChart.chart_opensRange, ReesProductPowerSections.chartMorphism_opensRange]
  apply le_antisymm
  · apply le_iInf
    intro k
    exact Finset.inf_le (tuple_mem q t k)
  · apply Finset.le_inf
    intro j hj
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hj
    exact iInf_le (fun i => opens I a (t i)) k

def genericChartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s)
    (L : PiExponentSeshadri.Geometry.LineBundle (affineBlowup I))
    (ι : L.sheaf ⟶ PiExponentSeshadri.Frames.O (affineBlowup I))
    (hL : PiExponentSeshadri.Geometry.PresentsPullbackIdeal
      (PiExponentSeshadri.IdealPullback.specIdeal I) (projection I) L ι)
    (e : ExceptionalRepresentedTypes.Frame (chartMap I a hs) L)
    (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs) L n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  (ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
    (chartMap I a hs)
    (ReesFrozenChart.base I a s)
    (ReesFrozenChart.chart_projection I a hs) L ι hL e n).trans
      (ReesFrozenPower.pieceEquiv I a hp n).symm

attribute [local irreducible] genericChartHomEquiv

theorem chartFrameTyped_nonempty {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) :
    Nonempty (ExceptionalRepresentedTypes.Frame (chartMap I a hs)
      (exceptionalLineBundle I)) := by
  exact ExceptionalRepresentedTypes.frame_nonempty_of_open
    (chartMap I a hs) (exceptionalLineBundle I)
    (U := (ReesFrozenChart.chartOpen I a hs).1) rfl
    (ReesFrozenChart.chartFrame_nonempty I a hs hp)

def chartFrameTyped {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) :
    ExceptionalRepresentedTypes.Frame (chartMap I a hs) (exceptionalLineBundle I) :=
  (chartFrameTyped_nonempty I a hs hp).some

def chartHomEquiv {s : Finset J} (hs : s.Nonempty) {p : J} (hp : p ∈ s) (n : ℕ) :
    ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n ≃+
      ReesLocalizedIntersections.Piece I a s n :=
  genericChartHomEquiv I a hs hp (exceptionalLineBundle I) (exceptionalInclusion I)
    (exceptional_presents I) (chartFrameTyped I a hs hp) n

theorem chartHomEquiv_pieceEquiv {s : Finset J} (hs : s.Nonempty)
    {p : J} (hp : p ∈ s) (n : ℕ)
    (b : ExceptionalRepresentedTypes.Sections (chartMap I a hs)
      (exceptionalLineBundle I) n) :
    ReesFrozenPower.pieceEquiv I a hp n (chartHomEquiv I a hs hp n b) =
      ExceptionalRepresentedTypes.representedSectionsTyped I (projection I)
        (chartMap I a hs)
        (ReesFrozenChart.base I a s)
        (ReesFrozenChart.chart_projection I a hs)
        (exceptionalLineBundle I) (exceptionalInclusion I) (exceptional_presents I)
        (chartFrameTyped I a hs hp) n b := by
  unfold chartHomEquiv genericChartHomEquiv
  exact (ReesFrozenPower.pieceEquiv I a hp n).apply_symm_apply _

def tupleHomEquiv (n q : ℕ) (t : Fin (q + 1) → J) :
    (schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n) ≃+ ReesLocalizedIntersections.Piece I a (tupleSet t) n :=
  (ExceptionalRepresentedTypes.transportSections
    (chartMap I a (tuple_nonempty q t)) (exceptionalLineBundle I) n
    (tupleOpen_eq I a q t)).trans
      (chartHomEquiv I a (tuple_nonempty q t) (tuple_mem q t 0) n)

local instance cochainAddCommGroup (n q : ℕ) :
    AddCommGroup
      (CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q) :=
  inferInstanceAs (AddCommGroup (∀ t : Fin (q + 1) → J,
    schemeFreeOpen (affineBlowup I) (CechHigher.intersection (opens I a) t) ⟶
      exceptionalPower I n))

def cochainEquiv (n q : ℕ) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    CechHigher.Cochain (affineBlowup I).ringCatSheaf (opens I a) (exceptionalPower I n) q ≃+
      GradedCech.Cochain (grading (J := J) (R := R)) (integerPiece I)
        MvPolynomial.X variable_mem n q := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  letI (t : Fin (q + 1) → J) : AddCommGroup
      (freeOpen (affineBlowup I).ringCatSheaf (CechHigher.intersection (opens I a) t) ⟶
        exceptionalPower I n) :=
    Preadditive.homGroup (C := (affineBlowup I).Modules) _ _
  exact AddEquiv.piCongrRight (fun t => tupleHomEquiv I a n q t)

theorem tuple_isAffine (q : ℕ) (t : Fin (q + 1) → J) :
    IsAffineOpen (CechHigher.intersection (opens I a) t) := by
  rw [← tupleOpen_eq I a q t]
  exact (ReesFrozenChart.chartOpen I a (tuple_nonempty q t)).property

omit [Fintype J] [DecidableEq J] in

theorem iSup_opens (ha : Ideal.span (Set.range fun j => (a j).val) = I) :
    (⨆ j, opens I a j) = ⊤ := ReesFiniteCover.iSup_generator_opensRange I a ha

end
end PiExponent.ReesSheafCechBase

end OAI
end Source0785

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesSectionInclusion.lean
section Source0786
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesSectionInclusion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesSectionInclusion
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ReesGrading PiExponentSeshadri.ModuleFlasque
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.GeometrySupport PiExponent.ReesSheafCechBase
open PiExponent.GradedPolynomialLaurent PiExponent.GradedCech
attribute [local irreducible] affineBlowup projection exceptionalLineBundle exceptionalInclusion exceptionalIdeal
  PiExponentSeshadri.Geometry.LineBundle.pow PiExponentSeshadri.Geometry.PresentsPullbackIdeal
  PiExponent.ExceptionalAffineChart.sectionsEquiv PiExponent.ExceptionalAffineChart.representedSectionsEquiv
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

abbrev chartMap {s : Finset J} (hs : s.Nonempty) :
    Spec (CommRingCat.of (ReesFrozenChart.coordinateRing I a s)) ⟶ affineBlowup I :=
  ReesFrozenChart.chart I a hs

local instance chartOpenImmersion {s : Finset J} (hs : s.Nonempty) :
    IsOpenImmersion (chartMap I a hs) :=
  ReesFrozenChart.instIsOpenImmersionChart I a hs

private theorem transported_augmentation (n : ℕ)
    (f : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (t : Fin 1 → J) :
    ExceptionalRepresentedTypes.transportSections
      (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
      (tupleOpen_eq I a 0 t)
      (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
        (exceptionalPower I n) ⊤ (fun _ => le_top) f t) =
    freeOpenMap (affineBlowup I).ringCatSheaf (homOfLE le_top) ≫ f := by
  change (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (eqToHom (tupleOpen_eq I a 0 t)) ≫
    (PiExponentSeshadri.ModuleMayerVietoris.freeOpenFunctor (affineBlowup I).ringCatSheaf).map
      (homOfLE _) ≫ f = _
  erw [← Category.assoc, ← Functor.map_comp]
  rfl

def HasFrozenValues (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n) (r : R) : Prop :=
  ∀ t : Fin 1 → J,
    (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
      (tupleHomEquiv I a n 0 t
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top) u t))).val =
      ReesFrozenChart.base I a (tupleSet t) r

theorem section_chart_inclusion (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) (t : Fin 1 → J) :
    ExceptionalAffineChart.functionsOnOpenEquiv
      (chartMap I a (tuple_nonempty 0 t))
      ((affineBlowup I).presheaf.map (homOfLE le_top).op
        ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
          (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) =
      ReesFrozenChart.base I a (tupleSet t) r := by
  have h := hvalue t
  change (ReesFrozenPower.pieceEquiv I a (tuple_mem 0 t 0) n
    (chartHomEquiv I a (tuple_nonempty 0 t) (tuple_mem 0 t 0) n
      (ExceptionalRepresentedTypes.transportSections
        (chartMap I a (tuple_nonempty 0 t)) (exceptionalLineBundle I) n
        (tupleOpen_eq I a 0 t)
        (CechHigher.augmentation (affineBlowup I).ringCatSheaf (opens I a)
          (exceptionalPower I n) ⊤ (fun _ => le_top)
          (u) t)))).val = _ at h
  rw [chartHomEquiv_pieceEquiv] at h
  erw [ExceptionalRepresentedTypes.representedSectionsTyped_apply,
    ExceptionalAffineChart.representedSectionsEquiv_apply] at h
  erw [transported_augmentation I a n u t] at h
  erw [freeOpenEquiv_naturality] at h
  have hn := CategoryTheory.congr_fun
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).mapPresheaf.naturality
      (homOfLE (show (chartMap I a (tuple_nonempty 0 t)).opensRange ≤ ⊤ from le_top)).op)
    (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)
  change (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) =
    (affineBlowup I).presheaf.map (homOfLE le_top).op
      ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u)) at hn
  change ExceptionalAffineChart.functionsOnOpenEquiv _
    ((idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app _
      ((exceptionalPower I n).presheaf.map (homOfLE le_top).op
        (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u))) = _ at h
  rw [hn] at h
  exact h

theorem section_inclusion
    (ha : Ideal.span (Set.range fun j => (a j).val) = I) (n : ℕ)
    (u : freeOpen (affineBlowup I).ringCatSheaf ⊤ ⟶ exceptionalPower I n)
    (r : R) (hvalue : HasFrozenValues I a n u r) :
    (idealPowerInclusion (exceptionalLineBundle I) (exceptionalInclusion I) n).app ⊤
      (freeOpenSectionsEquiv ⊤ (exceptionalPower I n) u) =
    (projection I).appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
  apply (O (affineBlowup I)).isSheaf.section_ext
  intro x hx
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp ((iSup_opens I a ha).ge (Set.mem_univ x))
  let t : Fin 1 → J := fun _ => j
  have heq : (chartMap I a (tuple_nonempty 0 t)).opensRange = opens I a j := by
    change (ReesFrozenChart.chartOpen I a (tuple_nonempty 0 t)).1 = _
    rw [tupleOpen_eq]
    simp only [CechHigher.intersection, t, iInf_const]
  refine ⟨(chartMap I a (tuple_nonempty 0 t)).opensRange, le_top,
    heq.ge hj, ?_⟩
  apply (ExceptionalAffineChart.functionsOnOpenEquiv
    (chartMap I a (tuple_nonempty 0 t))).injective
  exact (section_chart_inclusion I a n u r hvalue t).trans
    (ExceptionalAffineChart.functionsOnOpenEquiv_pullback (projection I)
      (chartMap I a (tuple_nonempty 0 t))
      (ReesFrozenChart.base I a (tupleSet t))
      (ReesFrozenChart.chart_projection I a (tuple_nonempty 0 t)) r).symm

end
end PiExponent.ReesSectionInclusion

end OAI
end Source0786

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesProductAugmentation.lean
section Source0787
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesProductAugmentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ReesProductAugmentation
noncomputable section
open PiExponentSeshadri.ReesGrading
open PiExponent.ReesGradedModule PiExponent.ReesPolynomialPresentation
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact PiExponent.GradedCech
open PiExponent.ReesLocalizedIntersections PiExponent.ReesProductChart PiExponent.ReesProductPower
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type*} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I)

def ordinaryFraction (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) : Piece I a s n := by
  letI := presentationAlgebra I a
  letI := gradedScalarAction I a
  exact ⟨fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
    (ordinaryPowerEquivIntegerPiece I n b).val 0,
      0, (ordinaryPowerEquivIntegerPiece I n b).val,
      by simpa only [Nat.cast_zero, zero_mul, add_zero] using
        (ordinaryPowerEquivIntegerPiece I n b).property, rfl⟩

theorem ordinaryFraction_evaluation (s : Finset J) (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    pieceEvaluation I a s n (ordinaryFraction I a s n b) =
      algebraMap R (Localization.Away (coefficientProduct I a s)) b.val := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  change localizationEvaluation I a s
    (fraction (coverProduct (MvPolynomial.X : J → MvPolynomial J R) s)
      (ordinaryPowerEquivIntegerPiece I n b).val 0) = _
  rw [localizationEvaluation_fraction, powerDenominator_zero, IsLocalization.mk'_one]
  congr 1
  change evaluation I (ReesPushdown.ordinaryPowerEquivPiece I n b).val = b.val
  rw [evaluation_piece I (ReesPushdown.ordinaryPowerEquivPiece I n b)]
  exact ReesPushdown.ordinaryPowerEquivPiece_apply_coeff I n b

theorem chartPowerMap_ordinaryFraction {s : Finset J} {j : J} (hj : j ∈ s)
    (n : ℕ) (b : ↥(I ^ n : Ideal R)) :
    (chartPowerMap I a hj n (ordinaryFraction I a s n b)).val =
      ReesProductChart.chartBase I a s b.val := by
  apply ReesProductChart.chartMap_injective I a s
  rw [chartPowerMap_evaluation I a hj, ordinaryFraction_evaluation,
    ReesProductChart.chartMap_base]

theorem augmentation_eq_ordinaryFraction (n : ℕ) (b : ↥(I ^ n : Ideal R)) (t : Fin 1 → J) :
    letI := presentationAlgebra I a
    letI := gradedScalarAction I a
    augmentation (grading (J := J) (R := R)) (integerPiece I) MvPolynomial.X variable_mem n
      (ordinaryPowerEquivIntegerPiece I n b) t = ordinaryFraction I a (tupleSet t) n b := by
  let := presentationAlgebra I a
  let := gradedScalarAction I a
  apply Subtype.ext
  rfl

end
end PiExponent.ReesProductAugmentation

end OAI
end Source0787

-- Source: OAI/NumberTheory/PiExponent/Approximation/AdditiveKernelTransport.lean
section Source0788
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/AdditiveKernelTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.AdditiveKernelTransport

variable {A A' B B' : Type*}
  [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']

def kernelEquiv (e : A ≃+ B) (e' : A' ≃+ B')
    (d : A →+ A') (D : B →+ B') (h : ∀ x, e' (d x) = D (e x)) :
    d.ker ≃+ D.ker where
  toFun c := ⟨e c.val, by
    change D (e c.val) = 0
    rw [← h, c.property, map_zero]⟩
  invFun c := ⟨e.symm c.val, by
    change d (e.symm c.val) = 0
    apply e'.injective
    rw [h, e.apply_symm_apply, map_zero]
    exact c.property⟩
  left_inv c := Subtype.ext (e.symm_apply_apply c.val)
  right_inv c := Subtype.ext (e.apply_symm_apply c.val)
  map_add' c b := Subtype.ext (map_add e c.val b.val)

theorem transport_primitives {A₂ B₂ : Type*} [AddCommGroup A₂] [AddCommGroup B₂]
    (e₀ : A ≃+ B) (e₁ : A' ≃+ B') (e₂ : A₂ ≃+ B₂)
    (d₀ : A →+ A') (d₁ : A' →+ A₂) (D₀ : B →+ B') (D₁ : B' →+ B₂)
    (h₀ : ∀ x, e₁ (d₀ x) = D₀ (e₀ x))
    (h₁ : ∀ x, e₂ (d₁ x) = D₁ (e₁ x))
    (hp : ∀ c, D₁ c = 0 → ∃ b, D₀ b = c) :
    ∀ c, d₁ c = 0 → ∃ b, d₀ b = c := by
  intro c hc
  have hclosed : D₁ (e₁ c) = 0 := by rw [← h₁, hc, map_zero]
  obtain ⟨b, hb⟩ := hp (e₁ c) hclosed
  refine ⟨e₀.symm b, e₁.injective ?_⟩
  rw [h₀, e₀.apply_symm_apply, hb]

end PiExponent.AdditiveKernelTransport

end OAI
end Source0788

-- Source: OAI/NumberTheory/PiExponent/Cohomology/CechZeroAdditive.lean
section Source0789
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CechZeroAdditive.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GeometrySupport.CechZeroAdditive
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.ModuleFlasque
open CechOne CechHigher
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
  {J : Type u} (U : J → Opens X) (M : SheafOfModules.{u} R)

def differentialHom (q : ℕ) : Cochain R U M q →+ Cochain R U M (q + 1) where
  toFun := differential R U M
  map_zero' := differential_zero R U M
  map_add' c b := by
    funext t
    simp only [differential, Pi.add_apply, restrictHom_add, smul_add, Finset.sum_add_distrib]

def cycles (q : ℕ) : AddSubgroup (Cochain R U M q) := (differentialHom R U M q).ker

@[simp] theorem mem_cycles (q : ℕ) (c : Cochain R U M q) :
    c ∈ cycles R U M q ↔ differential R U M c = 0 := Iff.rfl

def augmentationHom (V : Opens X) (hUV : ∀ i, U i ≤ V) :
    (freeOpen R V ⟶ M) →+ cycles R U M 0 where
  toFun f := ⟨augmentation R U M V hUV f, augmentation_closed R U M V hUV f⟩
  map_zero' := by
    apply Subtype.ext
    funext t
    exact comp_zero
  map_add' f g := by
    apply Subtype.ext
    funext t
    exact restrictHom_add R _ f g

def sectionsEquiv (V : Opens X) (hUV : ∀ i, U i ≤ V) (hcover : V ≤ ⨆ i, U i) :
    (freeOpen R V ⟶ M) ≃+ cycles R U M 0 :=
  AddEquiv.ofBijective (augmentationHom R U M V hUV) ⟨by
    intro f g hfg
    exact CechZero.augmentation_injective R U M V hUV hcover (congrArg Subtype.val hfg), by
    intro c
    obtain ⟨f, hf⟩ := CechZero.augmentation_exists R U M V hUV hcover c.val c.property
    exact ⟨f, Subtype.ext hf⟩⟩

@[simp] theorem sectionsEquiv_val (V : Opens X) (hUV : ∀ i, U i ≤ V)
    (hcover : V ≤ ⨆ i, U i) (f : freeOpen R V ⟶ M) :
    (sectionsEquiv R U M V hUV hcover f).val = augmentation R U M V hUV f := rfl

end
end PiExponent.GeometrySupport.CechZeroAdditive

end OAI
end Source0789

-- Source: OAI/NumberTheory/PiExponent/Cohomology/TupleCechBound.lean
section Source0790
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/TupleCechBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.TupleCechBound
noncomputable section
open scoped BigOperators
open ProjectiveMonomialCechHigher
universe u
variable {J K A : Type*} [AddCommGroup A]

def FullSupport {q : ℕ} (c : Cochain J A q) : Prop :=
  ∀ t j, (∀ i, t i ≠ j) → c t = 0

def pullback (f : K → J) {q : ℕ} (c : Cochain J A q) : Cochain K A q :=
  fun t => c (f ∘ t)

lemma pullback_differential (f : K → J) {q : ℕ} (c : Cochain J A q) :
    pullback f (differential c) = differential (pullback f c) := rfl

lemma contraction_closed {q : ℕ} (c : Cochain J A (q + 1))
    (hc : differential c = 0) (p : J) :
    differential (fun t : Fin (q + 1) → J => c (Fin.cons p t)) = c := by
  funext t
  have h := differential_cons c p t
  rw [hc, Pi.zero_apply] at h
  exact (sub_eq_zero.mp h.symm).symm

def extend (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q) : Cochain J A q := by
  classical
  exact fun t => if h : ∀ i, t i ≠ p then c (fun i => ⟨t i, h i⟩) else 0

lemma extend_pullback (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 1) → {j : J // j ≠ p}) :
    extend p c (Subtype.val ∘ t) = c t := by
  classical
  simp only [extend, Function.comp_apply, dite_eq_left (fun i => (t i).property)]

lemma differential_extend_pullback (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q)
    (t : Fin (q + 2) → {j : J // j ≠ p}) :
    differential (extend p c) (Subtype.val ∘ t) = differential c t := by
  simp only [differential]
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun a => (-1 : ℤ) ^ i.val • a) (extend_pullback p c (t ∘ i.succAbove))

lemma extend_missing (p : J) {q : ℕ} (c : Cochain {j : J // j ≠ p} A q)
    (hc : FullSupport c) (t : Fin (q + 1) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : extend p c t = 0 := by
  classical
  unfold extend
  split_ifs with h
  · apply hc _ ⟨j, hjp⟩
    intro i he
    exact ht i (congrArg Subtype.val he)
  · rfl

lemma differential_extend_missing (p : J) {q : ℕ}
    (c : Cochain {j : J // j ≠ p} A q) (hc : FullSupport c)
    (t : Fin (q + 2) → J) (j : J) (hjp : j ≠ p)
    (ht : ∀ i, t i ≠ j) : differential (extend p c) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  rw [extend_missing p c hc (t ∘ i.succAbove) j hjp (fun k => ht (i.succAbove k)), smul_zero]

theorem fullSupport_primitives_aux (n : ℕ) :
    ∀ (J : Type u) [Fintype J], Fintype.card J = n →
    ∀ q : ℕ, n ≤ q + 1 → ∀ c : Cochain J A (q + 1),
      differential c = 0 → FullSupport c →
      ∃ b : Cochain J A q, differential b = c ∧ FullSupport b := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J _ hcard q hq c hc hsupport
    cases isEmpty_or_nonempty J with
    | inl hJ =>
      let := hJ
      refine ⟨0, ?_, ?_⟩
      · funext t
        exact isEmptyElim (t 0)
      · intro t
        exact isEmptyElim (t 0)
    | inr hJ =>
      let p : J := Classical.choice hJ
      let b : Cochain J A q := fun t => c (Fin.cons p t)
      have hb : differential b = c := contraction_closed c hc p
      cases q with
      | zero =>
        refine ⟨b, hb, ?_⟩
        let : Subsingleton J := Fintype.card_le_one_iff_subsingleton.mp (hcard ▸ hq)
        intro t j ht
        exact False.elim (ht 0 (Subsingleton.elim _ _))
      | succ q =>
        let K := {j : J // j ≠ p}
        have hKn : Fintype.card K < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := p) (by simp)
        let bK : Cochain K A (q + 1) := pullback Subtype.val b
        have hbK : differential bK = 0 := by
          rw [← pullback_differential, hb]
          funext t
          exact hsupport _ p (fun i => (t i).property)
        have hsK : FullSupport bK := by
          intro t j ht
          apply hsupport _ j.val
          intro i
          cases i using Fin.cases with
          | zero => exact Ne.symm j.property
          | succ i =>
            intro he
            exact ht i (Subtype.ext he)
        obtain ⟨a, ha, hs⟩ := ih (Fintype.card K) hKn K rfl q (by omega) bK hbK hsK
        refine ⟨b - differential (extend p a), ?_, ?_⟩
        · rw [differential_sub, hb, differential_squared, sub_zero]
        · intro t j ht
          change b t - differential (extend p a) t = 0
          by_cases hj : j = p
          · subst j
            let tK : Fin (q + 2) → K := fun i => ⟨t i, ht i⟩
            have hvalue := congrFun ha tK
            have hext := differential_extend_pullback p a tK
            change differential (extend p a) t = differential a tK at hext
            rw [hext, hvalue]
            exact sub_self _
          · have hb0 : b t = 0 := by
              apply hsupport _ j
              intro i
              cases i using Fin.cases with
              | zero => exact Ne.symm hj
              | succ i => exact ht i
            rw [hb0, differential_extend_missing p a hs t j hj ht, sub_self]

theorem fullSupport_primitives [Fintype J] {q : ℕ}
    (hq : Fintype.card J ≤ q + 1) (c : Cochain J A (q + 1))
    (hc : differential c = 0) (hs : FullSupport c) :
    ∃ b : Cochain J A q, differential b = c ∧ FullSupport b :=
  fullSupport_primitives_aux (Fintype.card J) J rfl q hq c hc hs

end
end PiExponent.TupleCechBound

end OAI
end Source0790

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedCechBound.lean
section Source0791
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedCechBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.FiniteTupleCech
noncomputable section
open scoped BigOperators
open GradedCech (tupleSet tupleSet_comp_subset tupleSet_subset)
variable {J : Type*} [DecidableEq J] (D : Finset J → Type*)
  [∀ s, AddCommGroup (D s)]
  (r : ∀ {s t : Finset J}, s ⊆ t → D s →+ D t)
  (rid : ∀ s (z : D s), r (s := s) le_rfl z = z)
  (rcomp : ∀ {s t u : Finset J} (hst : s ⊆ t) (htu : t ⊆ u) (z : D s),
    r htu (r hst z) = r (hst.trans htu) z)

abbrev Cochain (q : ℕ) := ∀ t : Fin (q + 1) → J, D (tupleSet t)

def differential {q : ℕ} (c : Cochain D q) : Cochain D (q + 1) :=
  fun t => ∑ i : Fin (q + 2), (-1 : ℤ) ^ i.val •
    r (tupleSet_comp_subset t i.succAbove) (c (t ∘ i.succAbove))

lemma differential_zero {q : ℕ} : differential D r (0 : Cochain D q) = 0 := by
  funext t
  simp [differential]

lemma differential_add {q : ℕ} (a b : Cochain D q) :
    differential D r (a + b) = differential D r a + differential D r b := by
  funext t
  simp only [differential, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]

lemma differential_sub {q : ℕ} (a b : Cochain D q) :
    differential D r (a - b) = differential D r a - differential D r b := by
  funext t
  simp only [differential, Pi.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib]

lemma mem_tupleSet {n : ℕ} (t : Fin n → J) (i : Fin n) : t i ∈ tupleSet t :=
  Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

def liftTo (s : Finset J) {n : ℕ} (t : Fin n → J) (ht : tupleSet t ⊆ s) :
    Fin n → s := fun i => ⟨t i, ht (mem_tupleSet t i)⟩

def evaluate (s : Finset J) {q : ℕ} (c : Cochain D q) :
    ProjectiveMonomialCechHigher.Cochain s (D s) q :=
  fun t => r (tupleSet_subset s Subtype.val (fun j => j.property) t) (c (Subtype.val ∘ t))

include rcomp in
lemma evaluate_differential (s : Finset J) {q : ℕ} (c : Cochain D q) :
    evaluate D r s (differential D r c) =
      ProjectiveMonomialCechHigher.differential (evaluate D r s c) := by
  funext t
  simp only [evaluate, differential, ProjectiveMonomialCechHigher.differential,
    map_sum, map_zsmul, rcomp]
  rfl

include rid rcomp in
lemma differential_squared {q : ℕ} (c : Cochain D q) :
    differential D r (differential D r c) = 0 := by
  funext t
  have h := congrFun (ProjectiveMonomialCechHigher.differential_squared
    (evaluate D r (tupleSet t) c)) (liftTo (tupleSet t) t le_rfl)
  rw [← evaluate_differential D r rcomp, ← evaluate_differential D r rcomp] at h
  change r le_rfl (differential D r (differential D r c) t) = 0 at h
  simpa only [rid, Pi.zero_apply] using h

lemma tuple_card_lt_of_missing {s : Finset J} {n : ℕ} (t : Fin n → J)
    (ht : tupleSet t ⊆ s) (j : J) (hj : j ∈ s) (hmiss : ∀ i, t i ≠ j) :
    (tupleSet t).card < s.card := by
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨ht, ?_⟩
  intro he
  have hmem : j ∈ tupleSet t := he.symm ▸ hj
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  exact hmiss i hi

def assemble {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q) :
    Cochain D q := fun t =>
  if h : (tupleSet t).card = k then B (tupleSet t) h (liftTo (tupleSet t) t le_rfl) else 0

include rid in
lemma assemble_restrict {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (hB : ∀ s hs, TupleCechBound.FullSupport (B s hs))
    (s : Finset J) (hs : s.card = k) (t : Fin (q + 1) → J) (ht : tupleSet t ⊆ s) :
    r ht (assemble D B t) = B s hs (liftTo s t ht) := by
  classical
  by_cases he : tupleSet t = s
  · subst s
    simp only [assemble, dite_eq_left hs, rid]
  · have hlt : (tupleSet t).card < k := by
      rw [← hs]
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ht, he⟩)
    rw [assemble, dite_eq_right (ne_of_lt hlt), map_zero]
    symm
    have hnot : ¬ s ⊆ tupleSet t := fun h => he (Finset.Subset.antisymm ht h)
    obtain ⟨j, hj, hjt⟩ := Finset.not_subset.mp hnot
    apply hB s hs _ ⟨j, hj⟩
    intro i hi
    have heq : t i = j := congrArg Subtype.val hi
    exact hjt (heq ▸ mem_tupleSet t i)

lemma differential_assemble_below {q k : ℕ}
    (B : ∀ s : Finset J, s.card = k → ProjectiveMonomialCechHigher.Cochain s (D s) q)
    (t : Fin (q + 2) → J) (ht : (tupleSet t).card < k) :
    differential D r (assemble D B) t = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hle := Finset.card_le_card (tupleSet_comp_subset t i.succAbove)
  have hne : (tupleSet (t ∘ i.succAbove)).card ≠ k := by omega
  simp only [assemble, dite_eq_right hne, map_zero, smul_zero]

variable [Fintype J]

include rid rcomp in

theorem level_correction {q k : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0)
    (hv : ∀ t, (tupleSet t).card < k → c t = 0) :
    ∃ b : Cochain D q,
      (∀ t, (tupleSet t).card < k → differential D r b t = 0) ∧
      (∀ t, (tupleSet t).card = k → differential D r b t = c t) := by
  classical
  have hlocal (s : Finset J) (hs : s.card = k) :
      ∃ b : ProjectiveMonomialCechHigher.Cochain s (D s) q,
        ProjectiveMonomialCechHigher.differential b = evaluate D r s c ∧
        TupleCechBound.FullSupport b := by
    apply TupleCechBound.fullSupport_primitives
    · simpa only [Fintype.card_coe] using (Finset.card_le_univ s).trans hq
    · rw [← evaluate_differential D r rcomp, hc]
      funext t
      exact map_zero _
    · intro t j hj
      have hsub := tupleSet_subset s Subtype.val (fun j => j.property) t
      have hlt : (tupleSet (Subtype.val ∘ t)).card < k := by
        rw [← hs]
        apply tuple_card_lt_of_missing (Subtype.val ∘ t) hsub j.val j.property
        intro i he
        exact hj i (Subtype.ext he)
      change r hsub (c (Subtype.val ∘ t)) = 0
      rw [hv _ hlt, map_zero]
  choose B hB hfull using hlocal
  refine ⟨assemble D B, differential_assemble_below D r B, ?_⟩
  intro t ht
  let s := tupleSet t
  calc
    differential D r (assemble D B) t =
        ProjectiveMonomialCechHigher.differential (B s ht) (liftTo s t le_rfl) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z => (-1 : ℤ) ^ i.val • z)
        (assemble_restrict D r rid B hfull s ht (t ∘ i.succAbove)
          (tupleSet_comp_subset t i.succAbove))
    _ = evaluate D r s c (liftTo s t le_rfl) := congrFun (hB s ht) _
    _ = c t := rid s (c t)

include rid rcomp in

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : Cochain D (q + 1)) (hc : differential D r c = 0) :
    ∃ b : Cochain D q, differential D r b = c := by
  classical
  have hlevels : ∀ k : ℕ, ∃ b : Cochain D q,
      ∀ t, (tupleSet t).card < k → differential D r b t = c t := by
    intro k
    induction k with
    | zero => exact ⟨0, fun _ h => False.elim (Nat.not_lt_zero _ h)⟩
    | succ k ih =>
      obtain ⟨b, hb⟩ := ih
      let a := c - differential D r b
      have ha : differential D r a = 0 := by
        rw [differential_sub, hc, differential_squared D r rid rcomp, sub_self]
      have hav : ∀ t, (tupleSet t).card < k → a t = 0 := by
        intro t ht
        change c t - differential D r b t = 0
        rw [hb t ht, sub_self]
      obtain ⟨e, helo, heeq⟩ := level_correction D r rid rcomp hq a ha hav
      refine ⟨b + e, ?_⟩
      intro t ht
      rw [differential_add, Pi.add_apply]
      by_cases hlt : (tupleSet t).card < k
      · rw [hb t hlt, helo t hlt, add_zero]
      · have heq : (tupleSet t).card = k := by omega
        rw [heeq t heq]
        change differential D r b t + (c t - differential D r b t) = c t
        abel
  obtain ⟨b, hb⟩ := hlevels (Fintype.card J + 1)
  refine ⟨b, funext (fun t => hb t ?_)⟩
  exact Nat.lt_succ_of_le (Finset.card_le_univ (tupleSet t))

end
end PiExponent.FiniteTupleCech

namespace PiExponent.GradedCechBound
noncomputable section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {σR σM : Type*} [SetLike σR R]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓜]
  {J : Type*} [Fintype J] [DecidableEq J]
  (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1) (d : ℤ)

theorem primitives {q : ℕ} (hq : Fintype.card J ≤ q + 1)
    (c : GradedCech.Cochain 𝒜 𝓜 x hx d (q + 1))
    (hc : GradedCech.differential 𝒜 𝓜 x hx d c = 0) :
    ∃ b : GradedCech.Cochain 𝒜 𝓜 x hx d q,
      GradedCech.differential 𝒜 𝓜 x hx d b = c := by
  exact FiniteTupleCech.primitives
    (fun s => GradedCech.IntersectionPiece 𝒜 𝓜 x hx s d)
    (fun {_ _} h => GradedCech.setRestriction 𝒜 𝓜 x hx h d)
    (fun s z => GradedCech.setRestriction_refl 𝒜 𝓜 x hx s d z)
    (fun {_ _ _} hst htu z => GradedCech.setRestriction_comp 𝒜 𝓜 x hx hst htu d z)
    hq c hc

end
end PiExponent.GradedCechBound

end OAI
end Source0791

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedCechRecovery.lean
section Source0792
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedCechRecovery.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedCechRecovery

theorem augmentation_surjective_on_closed
    {P M A₀ A₁ A₂ B₀ B₁ B₂ C₀ C₁ : Type*}
    [AddCommGroup P] [AddCommGroup M]
    [AddCommGroup A₀] [AddCommGroup A₁] [AddCommGroup A₂]
    [AddCommGroup B₀] [AddCommGroup B₁] [AddCommGroup B₂]
    [AddCommGroup C₀] [AddCommGroup C₁]
    (a₀ : A₀ →+ A₁) (a₁ : A₁ →+ A₂)
    (b₀ : B₀ →+ B₁) (b₁ : B₁ →+ B₂) (c₀ : C₀ →+ C₁)
    (f₀ : A₀ →+ B₀) (f₁ : A₁ →+ B₁) (f₂ : A₂ →+ B₂)
    (g₀ : B₀ →+ C₀) (g₁ : B₁ →+ C₁)
    (εB : P →+ B₀) (εC : M →+ C₀) (g : P →+ M)
    (hg₀ : Function.Surjective g₀)
    (hker : ∀ z : B₁, g₁ z = 0 → ∃ y : A₁, f₁ y = z)
    (hf₂ : Function.Injective f₂)
    (hff₀ : ∀ x, b₀ (f₀ x) = f₁ (a₀ x))
    (hff₁ : ∀ x, b₁ (f₁ x) = f₂ (a₁ x))
    (hgg : ∀ x, g₁ (b₀ x) = c₀ (g₀ x))
    (hzero : ∀ x, g₀ (f₀ x) = 0)
    (hdiff : ∀ x, b₁ (b₀ x) = 0)
    (hε : ∀ x, εC (g x) = g₀ (εB x))
    (hfree : ∀ x : B₀, b₀ x = 0 → ∃ p : P, εB p = x)
    (hkernel : ∀ x : A₁, a₁ x = 0 → ∃ y : A₀, a₀ y = x) :
    ∀ x : C₀, c₀ x = 0 → ∃ m : M, εC m = x := by
  intro x hx
  obtain ⟨b, hb⟩ := hg₀ x
  have hdb : g₁ (b₀ b) = 0 := by rw [hgg, hb, hx]
  obtain ⟨a, ha⟩ := hker (b₀ b) hdb
  have hclosed : a₁ a = 0 := by
    apply hf₂
    rw [map_zero, ← hff₁, ha, hdiff]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : b₀ (b - f₀ v) = 0 := by
    rw [map_sub, hff₀, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree (b - f₀ v) hcorrected
  refine ⟨g p, ?_⟩
  rw [hε, hp, map_sub, hzero, sub_zero, hb]

end PiExponent.GradedCechRecovery

end OAI
end Source0792

-- Source: OAI/NumberTheory/PiExponent/Polynomials/HomogeneousSubmoduleGrading.lean
section Source0793
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/HomogeneousSubmoduleGrading.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.HomogeneousSubmoduleGrading
noncomputable section
open DirectSum
variable {R M σM : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  (K : Submodule R M) (hK : K.IsHomogeneous 𝓜)

def piece (_hK : K.IsHomogeneous 𝓜) (d : ℤ) : AddSubgroup K where
  carrier := {m | (m : M) ∈ 𝓜 d}
  zero_mem' := zero_mem _
  add_mem' := fun hm hn => add_mem hm hn
  neg_mem' := fun hm => neg_mem hm

def component (m : K) (d : ℤ) : piece 𝓜 K hK d :=
  ⟨⟨DirectSum.decompose 𝓜 (m : M) d, hK d m.property⟩,
    (DirectSum.decompose 𝓜 (m : M) d).property⟩

def decompositionMap : K →+ ⨁ d, piece 𝓜 K hK d where
  toFun m := by
    classical
    exact DFinsupp.mk' (component 𝓜 K hK m) (Trunc.mk
    ⟨(DirectSum.decompose 𝓜 (m : M)).support.val, fun d => by
      classical
      by_cases hd : d ∈ (DirectSum.decompose 𝓜 (m : M)).support
      · exact Or.inl hd
      · right
        apply Subtype.ext
        apply Subtype.ext
        change (DirectSum.decompose 𝓜 (m : M) d : M) = 0
        rw [DFinsupp.notMem_support_iff.mp hd]
        rfl⟩)
  map_zero' := by
    ext d
    change (DirectSum.decompose 𝓜 (0 : M) d : M) = 0
    rw [DirectSum.decompose_zero]
    rfl
  map_add' m n := by
    ext d
    change (DirectSum.decompose 𝓜 ((m : M) + (n : M)) d : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) + (DirectSum.decompose 𝓜 (n : M) d : M)
    rw [DirectSum.decompose_add]
    rfl

@[simp] theorem decompositionMap_apply (m : K) (d : ℤ) :
    (((decompositionMap 𝓜 K hK m) d : K) : M) =
      (DirectSum.decompose 𝓜 (m : M) d : M) := rfl

theorem decompositionMap_injective : Function.Injective (decompositionMap 𝓜 K hK) := by
  intro m n h
  apply Subtype.ext
  apply (DirectSum.decompose 𝓜).injective
  ext d
  exact congrArg (fun z : ⨁ d, piece 𝓜 K hK d => ((z d : K) : M)) h

theorem decompositionMap_homogeneous (d : ℤ) (m : piece 𝓜 K hK d) :
    decompositionMap 𝓜 K hK m.val = DirectSum.of (fun d => piece 𝓜 K hK d) d m := by
  classical
  ext e
  by_cases he : d = e
  · subst e
    rw [DirectSum.of_eq_same]
    exact DirectSum.decompose_of_mem_same 𝓜 m.property
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm he)]
    exact DirectSum.decompose_of_mem_ne 𝓜 m.property he

instance decomposition : DirectSum.Decomposition (piece 𝓜 K hK) := by
  classical
  have hr : (decompositionMap 𝓜 K hK).comp (DirectSum.coeAddMonoidHom (piece 𝓜 K hK)) =
      AddMonoidHom.id _ := by
    apply DirectSum.addHom_ext
    intro d m
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
      AddMonoidHom.id_apply, decompositionMap_homogeneous]
  apply DirectSum.Decomposition.ofAddHom (piece 𝓜 K hK) (decompositionMap 𝓜 K hK) ?_ hr
  apply AddMonoidHom.ext
  intro m
  apply decompositionMap_injective 𝓜 K hK
  exact DFunLike.congr_fun hr (decompositionMap 𝓜 K hK m)

theorem subtype_degree_compatible (d : ℤ) (m : K) :
    K.subtype (DirectSum.decompose (piece 𝓜 K hK) m d : K) =
      (DirectSum.decompose 𝓜 (K.subtype m) d : M) := rfl

variable {σR : Type*} [SetLike σR R] [AddSubgroupClass σR R]
  (𝒜 : ℤ → σR) [SetLike.GradedSMul 𝒜 𝓜]

instance gradedSMul : SetLike.GradedSMul 𝒜 (piece 𝓜 K hK) where
  smul_mem := by
    intro i d a m ha hm
    change a • (m : M) ∈ 𝓜 (i + d)
    exact SetLike.GradedSMul.smul_mem ha (show (m : M) ∈ 𝓜 d from hm)

end
end PiExponent.HomogeneousSubmoduleGrading

end OAI
end Source0793

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedCechExactness.lean
section Source0794
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedCechExactness.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedCechExactness
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationExact
variable {R K F M σR σK σF σM J : Type*} [CommRing R]
  [AddCommGroup K] [Module R K] [AddCommGroup F] [Module R F]
  [AddCommGroup M] [Module R M]
  [SetLike σR R]
  [SetLike σK K] [AddSubgroupClass σK K]
  [SetLike σF F] [AddSubgroupClass σF F]
  [SetLike σM M] [AddSubgroupClass σM M]
  (𝒜 : ℤ → σR) (𝓚 : ℤ → σK) (𝓕 : ℤ → σF) (𝓜 : ℤ → σM)
  [SetLike.GradedMonoid 𝒜] [SetLike.GradedSMul 𝒜 𝓚]
  [SetLike.GradedSMul 𝒜 𝓕] [SetLike.GradedSMul 𝒜 𝓜]
  [DirectSum.Decomposition 𝓚] [DirectSum.Decomposition 𝓕] [DirectSum.Decomposition 𝓜]
  [DecidableEq J] (x : J → R) (hx : ∀ j, x j ∈ 𝒜 1)
  (f : K →ₗ[R] F) (g : F →ₗ[R] M)
  (hf : ∀ i z, f (DirectSum.decompose 𝓚 z i : K) =
    (DirectSum.decompose 𝓕 (f z) i : F))
  (hg : ∀ i z, g (DirectSum.decompose 𝓕 z i : F) =
    (DirectSum.decompose 𝓜 (g z) i : M))
  (hinj : Function.Injective f) (hex : Function.Exact f g) (hsurj : Function.Surjective g)

include hf hg hinj hex hsurj in

theorem augmentation_recovery_of_shortExact (d : ℤ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d 0,
      differential 𝒜 𝓕 x hx d c = 0 → ∃ p : 𝓕 d, augmentation 𝒜 𝓕 x hx d p = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d 1,
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d 0,
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d 0,
      differential 𝒜 𝓜 x hx d c = 0 → ∃ m : 𝓜 d, augmentation 𝒜 𝓜 x hx d m = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  apply GradedCechRecovery.augmentation_surjective_on_closed
    (differentialHom 𝒜 𝓚 x hx d 0) (differentialHom 𝒜 𝓚 x hx d 1)
    (differentialHom 𝒜 𝓕 x hx d 0) (differentialHom 𝒜 𝓕 x hx d 1)
    (differentialHom 𝒜 𝓜 x hx d 0)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 0) (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 1)
    (cochainMap 𝒜 𝓚 x hx 𝓕 f pf d 2)
    (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 0) (cochainMap 𝒜 𝓕 x hx 𝓜 g pg d 1)
    (augmentation 𝒜 𝓕 x hx d) (augmentation 𝒜 𝓜 x hx d)
    (globalPieceMap 𝓕 𝓜 g pg d)
  · exact cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d 0 g hg hsurj
  · intro c hc
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 1 f g hf hg hex c).mp hc
  · exact cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d 2 hinj
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact (cochainMap_differential 𝒜 𝓚 x hx 𝓕 f pf d c).symm
  · intro c
    exact cochainMap_differential 𝒜 𝓕 x hx 𝓜 g pg d c
  · intro c
    exact (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d 0 f g hf hg hex).apply_apply_eq_zero c
  · exact differential_squared 𝒜 𝓕 x hx d
  · intro p
    exact (augmentation_natural 𝒜 𝓕 x hx 𝓜 g pg d p).symm
  · exact hfree
  · exact hkernel

include hf hg hinj hex hsurj in

theorem primitives_of_shortExact (d : ℤ) (q : ℕ)
    (hfree : ∀ c : Cochain 𝒜 𝓕 x hx d (q + 1),
      differential 𝒜 𝓕 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓕 x hx d q,
        differential 𝒜 𝓕 x hx d b = c)
    (hkernel : ∀ c : Cochain 𝒜 𝓚 x hx d (q + 1 + 1),
      differential 𝒜 𝓚 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓚 x hx d (q + 1),
        differential 𝒜 𝓚 x hx d b = c) :
    ∀ c : Cochain 𝒜 𝓜 x hx d (q + 1),
      differential 𝒜 𝓜 x hx d c = 0 → ∃ b : Cochain 𝒜 𝓜 x hx d q,
        differential 𝒜 𝓜 x hx d b = c := by
  let pf := preserves_of_compatible 𝓚 𝓕 f hf
  let pg := preserves_of_compatible 𝓕 𝓜 g hg
  intro c hc
  obtain ⟨b, hb⟩ := cochainMap_surjective 𝒜 𝓕 x hx 𝓜 d (q + 1) g hg hsurj c
  have hdb : cochainMap 𝒜 𝓕 x hx 𝓜 g pg d (q + 1 + 1)
      (differential 𝒜 𝓕 x hx d b) = 0 := by
    rw [cochainMap_differential, hb, hc]
  obtain ⟨a, ha⟩ := (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1 + 1)
    f g hf hg hex (differential 𝒜 𝓕 x hx d b)).mp hdb
  have hclosed : differential 𝒜 𝓚 x hx d a = 0 := by
    apply cochainMap_injective 𝒜 𝓚 x hx 𝓕 f pf d (q + 1 + 1 + 1) hinj
    rw [map_zero, cochainMap_differential, ha, differential_squared]
  obtain ⟨v, hv⟩ := hkernel a hclosed
  have hcorrected : differential 𝒜 𝓕 x hx d
      (b - cochainMap 𝒜 𝓚 x hx 𝓕 f pf d (q + 1) v) = 0 := by
    rw [differential_sub, ← cochainMap_differential, hv, ha, sub_self]
  obtain ⟨p, hp⟩ := hfree _ hcorrected
  refine ⟨cochainMap 𝒜 𝓕 x hx 𝓜 g pg d q p, ?_⟩
  rw [← cochainMap_differential, hp, map_sub,
    (cochainMap_exact 𝒜 𝓚 x hx 𝓕 𝓜 d (q + 1) f g hf hg hex).apply_apply_eq_zero,
    sub_zero, hb]

end
end PiExponent.GradedCechExactness

end OAI
end Source0794

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedPolynomialCech.lean
section Source0795
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedPolynomialCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedPolynomialCech
noncomputable section
open scoped BigOperators
open PiExponent.GradedLocalizationExact PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.ProjectiveMonomialCech
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R : Type*} [Fintype J] [DecidableEq J] [CommRing R]

def intersectionToPiece (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Piece (R := R) s d where
  toFun z := ⟨z.val, z.property⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def intersectionToLaurent (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d →+ Laurent J R d :=
  (pieceToLaurent s d).comp (intersectionToPiece s d)

@[simp] theorem intersectionToLaurent_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s d) :
    intersectionToLaurent s d z = pieceToLaurent s d z := rfl

def cochainToLaurent (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q →+
      ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q where
  toFun c t := intersectionToLaurent (tupleSet t) d (c t)
  map_zero' := by funext t; exact map_zero _
  map_add' c b := by funext t; exact map_add _ _ _

@[simp] theorem cochainToLaurent_apply (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q)
    (t : Fin (q + 1) → J) :
    cochainToLaurent d q c t = pieceToLaurent (tupleSet t) d (c t) := rfl

theorem cochainToLaurent_injective (d : ℤ) (q : ℕ) :
    Function.Injective (cochainToLaurent (J := J) (R := R) d q) := by
  intro c b h
  funext t
  exact pieceToLaurent_injective (tupleSet t) d (congrFun h t)

theorem cochainToLaurent_regular (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    ProjectiveMonomialCechHigher.Regular (cochainToLaurent d q c) := by
  intro t a ha j hj
  have h := pieceToLaurent_regular (tupleSet t) d (c t) a ha j hj
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
  exact ⟨k, hk⟩

theorem cochainToLaurent_surjective_regular (d : ℤ) (q : ℕ)
    (c : ProjectiveMonomialCechHigher.Cochain J (Laurent J R d) q)
    (hc : ProjectiveMonomialCechHigher.Regular c) :
    ∃ b, cochainToLaurent d q b = c := by
  have ht (t : Fin (q + 1) → J) : ∃ b : Piece (R := R) (tupleSet t) d,
      pieceToLaurent (tupleSet t) d b = c t := by
    apply pieceToLaurent_surjective_regular
    intro a ha j hj
    obtain ⟨k, hk⟩ := hc t a ha j hj
    exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩
  choose b hb using ht
  exact ⟨b, funext hb⟩

theorem cochainToLaurent_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q) :
    cochainToLaurent d (q + 1) (differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c) =
      ProjectiveMonomialCechHigher.differential (cochainToLaurent d q c) := by
  funext t
  change intersectionToLaurent (tupleSet t) d
      (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
        setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R))
          MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  apply congrArg (fun z : Laurent J R d => (-1 : ℤ) ^ k.val • z)
  exact pieceToLaurent_restriction (R := R) (tupleSet_comp_subset t k.succAbove) d
    ⟨(c (t ∘ k.succAbove)).val, (c (t ∘ k.succAbove)).property⟩

theorem nonnegative_polynomial_cech_exact (d : ℤ) (hd : 0 ≤ d) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ b : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d b = c := by
  have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d (q + 1) c) = 0 := by
    rw [← cochainToLaurent_differential, hc, map_zero]
  obtain ⟨b, hb, hdb⟩ := ProjectiveMonomialCechHigher.nonnegative_twist_cech_exact_all_positive
    hd (cochainToLaurent d (q + 1) c) (cochainToLaurent_regular d (q + 1) c) hclosed
  obtain ⟨a, ha⟩ := cochainToLaurent_surjective_regular d q b hb
  refine ⟨a, ?_⟩
  apply cochainToLaurent_injective d (q + 1)
  rw [cochainToLaurent_differential, ha, hdb]

theorem nonnegative_polynomial_augmentation_recovery (d : ℤ) (hd : 0 ≤ d)
    (c : Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) (MvPolynomial.X : J → MvPolynomial J R)
      variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d c = 0) :
    ∃ m : (grading (J := J) (R := R)) d,
      augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem d m = c := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
      refine ⟨0, ?_⟩
      funext t
      exact isEmptyElim (t 0)
  | inr h =>
      have hclosed : ProjectiveMonomialCechHigher.differential (cochainToLaurent d 0 c) = 0 := by
        rw [← cochainToLaurent_differential, hc, map_zero]
      have hreg (j : J) : RegularOn {j} (cochainToLaurent d 0 c (fun _ => j)) := by
        simpa only [Set.range_const] using cochainToLaurent_regular d 0 c (fun _ => j)
      obtain ⟨p, hpreg, hp⟩ := GradedSerre.compatible_vertices_are_polynomial hd
        (fun j => cochainToLaurent d 0 c (fun _ => j)) hreg
        (GradedH0.zeroth_cocycle_vertices_eq _ hclosed)
      obtain ⟨z, hzL⟩ := pieceToLaurent_surjective_regular (R := R) ∅ d p (by simpa using hpreg)
      obtain ⟨n, m, hm, hz⟩ := z.property
      have hm' : m ∈ (grading (J := J) (R := R)) d := by simpa using hm
      refine ⟨⟨m, hm'⟩, ?_⟩
      funext t
      apply pieceToLaurent_injective (tupleSet t) d
      have ht : t = fun _ => t 0 := by
        funext i
        exact congrArg t (show i = 0 by omega)
      calc
        _ = pieceToLaurent ∅ d z := by
          ext a
          change (moduleToGroupAlgebra (tupleSet t) (fraction (product (tupleSet t)) m 0)).coeff a.val =
            (moduleToGroupAlgebra ∅ z.val).coeff a.val
          rw [hz]
          simp only [moduleToGroupAlgebra_fraction_coefficient, zero_smul,
            productExponent, Finset.sum_empty, smul_zero, add_zero]
        _ = p := hzL
        _ = pieceToLaurent (tupleSet t) d (c t) := by
          change p = cochainToLaurent d 0 c t
          rw [ht, hp]

end
end PiExponent.GradedPolynomialCech

end OAI
end Source0795

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GradedLocalizationFree.lean
section Source0796
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GradedLocalizationFree.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedLocalizationFree

noncomputable section
open scoped BigOperators
open GradedLocalizationExact

variable {R J σR : Type*} [CommRing R] [Fintype J]
  [SetLike σR R] [AddSubgroupClass σR R]

def coordinateMap (a : R) :
    LocalizedModule (Submonoid.powers a) (J → R) →ₗ[R]
      (J → LocalizedModule (Submonoid.powers a) R) :=
  LinearMap.pi (fun j => localizedMap a (LinearMap.proj j))

omit [Fintype J] in
@[simp] theorem coordinateMap_fraction (a : R) (v : J → R) (n : ℕ) (j : J) :
    coordinateMap a (fraction a v n) j = fraction a (v j) n := by
  change localizedMap a (LinearMap.proj (φ := fun _ : J => R) j) (fraction a v n) = _
  exact localizedMap_fraction a (LinearMap.proj (φ := fun _ : J => R) j) v n

theorem coordinateMap_injective (a : R) : Function.Injective (coordinateMap (J := J) a) := by
  classical
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm ?_ bot_le
  intro z hz
  change coordinateMap a z = 0 at hz
  change z = 0
  induction z using LocalizedModule.induction_on with
  | _ v s =>
    obtain ⟨n, hn⟩ := s.property
    have hs : s = powerDenominator a n := Subtype.ext hn.symm
    subst s
    change coordinateMap a (fraction a v n) = 0 at hz
    have hcoord : ∀ j, ∃ k : ℕ, a ^ k • v j = 0 := by
      intro j
      apply (fraction_eq_zero a (v j) n).mp
      have h := congrFun hz j
      simpa only [coordinateMap_fraction, Pi.zero_apply] using h
    choose k hk using hcoord
    let K : ℕ := ∑ j, k j
    apply (fraction_eq_zero a v n).mpr
    refine ⟨K, ?_⟩
    funext j
    have hj : k j ≤ K := Finset.single_le_sum (fun i _ => Nat.zero_le (k i))
      (Finset.mem_univ j)
    change a ^ K • v j = 0
    calc
      a ^ K • v j = (a ^ (K - k j) * a ^ k j) • v j := by
        rw [← pow_add, Nat.sub_add_cancel hj]
      _ = 0 := by rw [mul_smul, hk j, smul_zero]

variable (𝒜 : ℤ → σR) [SetLike.GradedMonoid 𝒜]
  (w : J → ℤ) (a : R) (e : ℤ) (ha : a ∈ 𝒜 e) (d : ℤ)

def coordinatePieces :
    degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d →+
      (∀ j, degreePiece 𝒜 𝒜 a e ha (d - w j)) where
  toFun z j := ⟨coordinateMap a z.val j, by
    obtain ⟨n, v, hv, hz⟩ := z.property
    refine ⟨n, v j, ?_, ?_⟩
    · have h := hv j
      change v j ∈ 𝒜 (d + (n : ℤ) * e - w j) at h
      convert h using 1
      ring_nf
    · rw [hz, coordinateMap_fraction]⟩
  map_zero' := by
    funext j
    exact Subtype.ext (congrFun (map_zero (coordinateMap a)) j)
  map_add' z z' := by
    funext j
    exact Subtype.ext (congrFun (map_add (coordinateMap a) z.val z'.val) j)

@[simp] theorem coordinatePieces_coe
    (z : degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d) (j : J) :
    (coordinatePieces 𝒜 w a e ha d z j).val = coordinateMap a z.val j := rfl

theorem coordinatePieces_injective : Function.Injective (coordinatePieces 𝒜 w a e ha d) := by
  intro z z' h
  apply Subtype.ext
  apply coordinateMap_injective a
  funext j
  exact congrArg Subtype.val (congrFun h j)

theorem coordinatePieces_surjective : Function.Surjective (coordinatePieces 𝒜 w a e ha d) := by
  classical
  intro z
  have hz : ∀ j, ∃ (n : ℕ) (m : R),
      m ∈ 𝒜 (d - w j + (n : ℤ) * e) ∧ (z j).val = fraction a m n :=
    fun j => (z j).property
  choose n m hm hzm using hz
  let N : ℕ := ∑ j, n j
  have hn (j : J) : n j ≤ N := Finset.single_le_sum
    (fun i _ => Nat.zero_le (n i)) (Finset.mem_univ j)
  let v : J → R := fun j => a ^ (N - n j) • m j
  have hv : v ∈ ShiftedFreeGrading.piece 𝒜 w (d + (N : ℤ) * e) := by
    intro j
    have h := power_smul_mem 𝒜 𝒜 a e ha (hm j) (N - n j)
    change v j ∈ 𝒜 (d + (N : ℤ) * e - w j)
    dsimp only [v]
    convert h using 1
    rw [Nat.cast_sub (hn j)]
    ring_nf
  refine ⟨⟨fraction a v N, N, v, hv, rfl⟩, ?_⟩
  funext j
  apply Subtype.ext
  change coordinateMap a (fraction a v N) j = (z j).val
  rw [coordinateMap_fraction, hzm]
  change fraction a (a ^ (N - n j) • m j) N = fraction a (m j) (n j)
  have hc := fraction_cancel a (m j) (n j) (N - n j)
  simpa only [Nat.add_sub_of_le (hn j)] using hc

def shiftedFreeEquiv :
    degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d ≃+
      (∀ j, degreePiece 𝒜 𝒜 a e ha (d - w j)) :=
  AddEquiv.ofBijective (coordinatePieces 𝒜 w a e ha d)
    ⟨coordinatePieces_injective 𝒜 w a e ha d,
      coordinatePieces_surjective 𝒜 w a e ha d⟩

@[simp] theorem shiftedFreeEquiv_apply
    (z : degreePiece 𝒜 (ShiftedFreeGrading.piece 𝒜 w) a e ha d) (j : J) :
    (shiftedFreeEquiv 𝒜 w a e ha d z j).val = coordinateMap a z.val j := rfl

end
end PiExponent.GradedLocalizationFree

end OAI
end Source0796

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedFreeCech.lean
section Source0797
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedFreeCech.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedFreeCech
noncomputable section
open PiExponent.GradedCech PiExponent.GradedLocalizationFree
open PiExponent.GradedPolynomialLaurent PiExponent.GradedLocalizationExact
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R B : Type*} [DecidableEq J] [CommRing R] [Fintype B]
  (w : B → ℤ)

def coordinateIntersection (s : Finset J) (d : ℤ) :
    IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d →+
    (∀ b, IntersectionPiece (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem s (d - w b)) where
  toFun z b := coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b
  map_zero' := by funext b; exact congrFun (map_zero _) b
  map_add' z z' := by funext b; exact congrFun (map_add _ _ _) b

@[simp] theorem coordinateIntersection_apply (s : Finset J) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinateIntersection w s d z b =
      coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem s) d z b := rfl

def coordinateCochain (d : ℤ) (q : ℕ) :
    Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q →+
    (∀ b, Cochain (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b) q) where
  toFun c b t := coordinateIntersection w (tupleSet t) d (c t) b
  map_zero' := by funext b t; exact congrFun (map_zero _) b
  map_add' c e := by funext b t; exact congrFun (map_add _ _ _) b

theorem coordinateCochain_injective (d : ℤ) (q : ℕ) :
    Function.Injective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c e h
  funext t
  apply coordinatePieces_injective (grading (J := J) (R := R)) w (product (tupleSet t)) _ (product_mem _) d
  funext b
  exact congrFun (congrFun h b) t

theorem coordinateCochain_surjective (d : ℤ) (q : ℕ) :
    Function.Surjective (coordinateCochain (J := J) (R := R) w d q) := by
  intro c
  have ht (t : Fin (q + 1) → J) := coordinatePieces_surjective (grading (J := J) (R := R)) w
    (product (R := R) (tupleSet t)) _ (product_mem _) d (fun b => c b t)
  choose e he using ht
  refine ⟨e, ?_⟩
  funext b t
  exact congrFun (he t) b

theorem coordinate_restriction {s t : Finset J} (hst : s ⊆ t) (d : ℤ)
    (z : IntersectionPiece (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem s d) (b : B) :
    coordinatePieces (grading (J := J) (R := R)) w (product t) _ (product_mem _) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem hst d z) b =
      setRestriction (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst (d - w b)
        (coordinatePieces (grading (J := J) (R := R)) w (product s) _ (product_mem _) d z b) := by
  apply Subtype.ext
  change localizedMap (product t) (LinearMap.proj b)
      (restriction (product s) (product t)
        (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) z.val) =
    restriction (product s) (product t)
      (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (localizedMap (product s) (LinearMap.proj b) z.val)
  exact DFunLike.congr_fun (restriction_localizedMap (product s) (product t)
    (coverProduct_dvd (grading (J := J) (R := R)) MvPolynomial.X variable_mem hst) (LinearMap.proj b)) z.val

theorem coordinateCochain_differential (d : ℤ) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d q) (b : B) :
    coordinateCochain w d (q + 1)
        (differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d c) b =
      differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
        (coordinateCochain w d q c b) := by
  funext t
  change (coordinateIntersection w (tupleSet t) d
    (∑ k : Fin (q + 2), (-1 : ℤ) ^ k.val •
      setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)))) b = _
  rw [map_sum]
  simp only [Finset.sum_apply, differential]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul]
  change (-1 : ℤ) ^ k.val • coordinateIntersection w (tupleSet t) d
      (setRestriction (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove))) b = _
  apply congrArg (fun z => (-1 : ℤ) ^ k.val • z)
  exact coordinate_restriction w (tupleSet_comp_subset t k.succAbove) d (c (t ∘ k.succAbove)) b

variable [Fintype J]

theorem free_cech_exact (d : ℤ) (hd : ∀ b, 0 ≤ d - w b) (q : ℕ)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      (MvPolynomial.X : J → MvPolynomial J R) variable_mem d (q + 1))
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ a : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) MvPolynomial.X variable_mem d a = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R)) MvPolynomial.X variable_mem (d - w b)
      (coordinateCochain w d (q + 1) c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hpr (b : B) := GradedPolynomialCech.nonnegative_polynomial_cech_exact
    (d - w b) (hd b) q (coordinateCochain w d (q + 1) c b) (hclosed b)
  choose p hp using hpr
  obtain ⟨a, ha⟩ := coordinateCochain_surjective (J := J) (R := R) w d q p
  refine ⟨a, ?_⟩
  apply coordinateCochain_injective w d (q + 1)
  funext b
  rw [coordinateCochain_differential, ha, hp]

omit [Fintype J] in
theorem coordinateCochain_augmentation (d : ℤ)
    (m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d) (b : B) :
    coordinateCochain w d 0
      (augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m) b =
    augmentation (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) ⟨m.val b, m.property b⟩ := by
  funext t
  apply Subtype.ext
  change coordinateMap (product (tupleSet t)) (fraction (product (tupleSet t)) m.val 0) b =
    fraction (product (tupleSet t)) (m.val b) 0
  exact coordinateMap_fraction _ m.val 0 b

theorem free_augmentation_recovery (d : ℤ) (hd : ∀ b, 0 ≤ d - w b)
    (c : Cochain (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d 0)
    (hc : differential (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
      MvPolynomial.X variable_mem d c = 0) :
    ∃ m : ShiftedFreeGrading.piece (grading (J := J) (R := R)) w d,
      augmentation (grading (J := J) (R := R)) (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w)
        MvPolynomial.X variable_mem d m = c := by
  have hclosed (b : B) : differential (grading (J := J) (R := R)) (grading (J := J) (R := R))
      MvPolynomial.X variable_mem (d - w b) (coordinateCochain w d 0 c b) = 0 := by
    rw [← coordinateCochain_differential, hc, map_zero]
    rfl
  have hrec (b : B) := GradedPolynomialCech.nonnegative_polynomial_augmentation_recovery
    (d - w b) (hd b) (coordinateCochain w d 0 c b) (hclosed b)
  choose m hm using hrec
  refine ⟨⟨fun b => (m b).val, fun b => (m b).property⟩, ?_⟩
  apply coordinateCochain_injective w d 0
  funext b
  rw [coordinateCochain_augmentation]
  exact hm b

end
end PiExponent.GradedFreeCech

end OAI
end Source0797

-- Source: OAI/NumberTheory/PiExponent/Polynomials/GradedSerreStep.lean
section Source0798
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/GradedSerreStep.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedSerreStep
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {J R M σM : Type*} [Fintype J] [DecidableEq J] [CommRing R]
  [IsNoetherianRing R] [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

def HasPrimitive (d : ℤ) (q : ℕ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d (q + 1),
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ b : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d q,
      differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d b = c

def HasRecovery (d : ℤ) : Prop :=
  ∀ c : Cochain (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d 0,
    differential (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d c = 0 →
    ∃ m : 𝓜 d, augmentation (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem d m = c

omit [IsNoetherianRing R] in
theorem exists_syzygy_eventual_step :
    ∃ (rank : ℕ) (w : Fin rank → ℤ) (g : (Fin rank → MvPolynomial J R) →ₗ[MvPolynomial J R] M),
      ∃ (hg : ∀ d z, g (DirectSum.decompose (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) z d :
          Fin rank → MvPolynomial J R) = (DirectSum.decompose 𝓜 (g z) d : M)),
        Function.Surjective g ∧
        let hK := GradedSerre.kernel_homogeneous (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) 𝓜 g hg
        let 𝓚 := HomogeneousSubmoduleGrading.piece (ShiftedFreeGrading.piece (grading (J := J) (R := R)) w) g.ker hK
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
          (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
          ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  obtain ⟨rank, w, g, hrange, hg⟩ := GradedSerre.exists_graded_free_map
    (grading (J := J) (R := R)) 𝓜 (⊤ : Submodule (MvPolynomial J R) M)
    (fun _ _ _ => trivial) Module.Finite.fg_top
  have hsurj : Function.Surjective g := LinearMap.range_eq_top.mp hrange
  refine ⟨rank, w, g, hg, hsurj, ?_⟩
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  change ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    (HasPrimitive (J := J) (R := R) 𝓚 n 0 → HasRecovery (J := J) (R := R) 𝓜 n) ∧
    ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓚 n (q + 1) → HasPrimitive (J := J) (R := R) 𝓜 n q
  refine ⟨∑ b, (w b).toNat, ?_⟩
  intro n hn
  have hdeg (b : Fin rank) : 0 ≤ (n : ℤ) - w b := by
    have hb : (w b).toNat ≤ ∑ b, (w b).toNat :=
      Finset.single_le_sum (fun b _ => Nat.zero_le ((w b).toNat)) (Finset.mem_univ b)
    have hb' : ((w b).toNat : ℤ) ≤ (n : ℤ) := by exact_mod_cast hb.trans hn
    omega
  have hf : ∀ d z, g.ker.subtype (DirectSum.decompose 𝓚 z d : g.ker) =
      (DirectSum.decompose 𝓕 (g.ker.subtype z) d : Fin rank → MvPolynomial J R) :=
    HomogeneousSubmoduleGrading.subtype_degree_compatible 𝓕 g.ker hK
  constructor
  · intro hk
    exact GradedCechExactness.augmentation_recovery_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n
      (GradedFreeCech.free_augmentation_recovery w n hdeg) hk
  · intro q hk
    exact GradedCechExactness.primitives_of_shortExact
      (grading (J := J) (R := R)) 𝓚 𝓕 𝓜 MvPolynomial.X variable_mem
      g.ker.subtype g hf hg Subtype.val_injective (LinearMap.exact_subtype_ker_map g) hsurj n q
      (GradedFreeCech.free_cech_exact w n hdeg q) hk

end
end PiExponent.GradedSerreStep

end OAI
end Source0798

-- Source: OAI/NumberTheory/PiExponent/Cohomology/GradedSerreVanishing.lean
section Source0799
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/GradedSerreVanishing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GradedSerreVanishing
noncomputable section
open PiExponent.GradedCech PiExponent.GradedPolynomialLaurent PiExponent.GradedSerreStep
attribute [local instance] MvPolynomial.weightedGradedAlgebra
universe u
variable {J R : Type u} [Fintype J] [DecidableEq J] [CommRing R] [IsNoetherianRing R]

theorem eventually_hasPrimitive_aux (depth : ℕ) :
    ∀ {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
      [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
      (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
      [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]
      (q : ℕ), Fintype.card J ≤ q + 1 + depth →
        ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q := by
  induction depth with
  | zero =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      refine ⟨0, ?_⟩
      intro n _ c hc
      exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
        n (by omega) c hc
  | succ depth ih =>
      intro M σM _ _ _ _ _ 𝓜 _ _ q hq
      obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step (J := J) (R := R) 𝓜
      let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
      let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
      let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
      obtain ⟨N₁, h₁⟩ := ih 𝓚 (q + 1) (by omega)
      refine ⟨max N N₁, ?_⟩
      intro n hn
      exact (hstep n ((le_max_left _ _).trans hn)).2 q
        (h₁ n ((le_max_right _ _).trans hn))

variable {M σM : Type u} [AddCommGroup M] [Module (MvPolynomial J R) M]
  [Module.Finite (MvPolynomial J R) M] [SetLike σM M] [AddSubgroupClass σM M]
  (𝓜 : ℤ → σM) [DirectSum.Decomposition 𝓜]
  [SetLike.GradedSMul (grading (J := J) (R := R)) 𝓜]

theorem eventually_hasPrimitive (q : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasPrimitive (J := J) (R := R) 𝓜 n q :=
  eventually_hasPrimitive_aux (Fintype.card J) 𝓜 q (by omega)

theorem eventually_all_positive :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℕ, HasPrimitive (J := J) (R := R) 𝓜 n q := by
  classical
  have hq (q : Fin (Fintype.card J)) := eventually_hasPrimitive (J := J) (R := R) 𝓜 q.val
  choose N hN using hq
  refine ⟨∑ q, N q, ?_⟩
  intro n hn q c hc
  by_cases hbound : Fintype.card J ≤ q + 1
  · exact GradedCechBound.primitives (grading (J := J) (R := R)) 𝓜 MvPolynomial.X variable_mem
      n hbound c hc
  · have hq' : q < Fintype.card J := by omega
    have hNq : N ⟨q, hq'⟩ ≤ ∑ q, N q :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (N i)) (Finset.mem_univ (⟨q, hq'⟩ : Fin (Fintype.card J)))
    exact hN ⟨q, hq'⟩ n (hNq.trans hn) c hc

theorem eventually_augmentation_recovery :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → HasRecovery (J := J) (R := R) 𝓜 n := by
  obtain ⟨rank, w, g, hg, hsurj, N, hstep⟩ := exists_syzygy_eventual_step (J := J) (R := R) 𝓜
  let 𝓕 := ShiftedFreeGrading.piece (grading (J := J) (R := R)) w
  let hK := GradedSerre.kernel_homogeneous 𝓕 𝓜 g hg
  let 𝓚 := HomogeneousSubmoduleGrading.piece 𝓕 g.ker hK
  obtain ⟨N₁, h₁⟩ := eventually_hasPrimitive (J := J) (R := R) 𝓚 0
  refine ⟨max N N₁, ?_⟩
  intro n hn
  exact (hstep n ((le_max_left _ _).trans hn)).1 (h₁ n ((le_max_right _ _).trans hn))

end
end PiExponent.GradedSerreVanishing

end OAI
end Source0799
