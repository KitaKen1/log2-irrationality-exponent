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
public import Mathlib.Algebra.Algebra.Hom.Rat
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: LogTwo/Geometry/SeparationAssembly.lean
section Source0100
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! Choose genuinely separated matrix weights, while keeping the existing
arithmetic error bound and any additional past-dependent denominator threshold.
The comparison constant is fixed after the dimension and before denominators. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section

def denominatorSeparationFactor (n m : ℕ) (M : ℝ) : ℝ :=
  weightSeparationFactor m M (horizontalWeight (b (delta n)) m)
    (verticalWeight (theta (delta n)) (b (delta n)) (c (delta n)) m)
    (theta (delta n))

theorem chosenWeights_separatedProducts (n : ℕ) (hn : 1 ≤ n) (m : ℕ)
    (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i) (M : ℝ) (hM : 0 < M)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m M * (∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) <
        (ceilLogWeight (q i) : ℝ)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    SeparatedProducts (columnWeight w) (fun i => (jetWeight w i : ℝ)) M := by
  dsimp only
  apply separatedProducts_of_growth _ M hM (normalizedLogWeights q) rfl
    (normalizedLogWeights_one_le q hq) (fun _ => rfl)
  intro i hi him
  cases i with
  | zero => omega
  | succ i =>
    change denominatorSeparationFactor n m M *
      (∏ j ∈ Finset.range (i+1), normalizedLogWeights q j) <
        (ceilLogWeight (q i) : ℝ)
    rw [normalizedLogWeights_prod]
    exact hgrowth i (by omega)

end
end LogTwo.Geometry
end Source0100

-- Source: LogTwo/Geometry/ContactBound.lean
section Source0101
/-! Component contact bounds with an explicit normal comparison input.
NormalComparison supplies this input; GlobalContactBound applies that proof. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- The comparison input, restricted to the actual coordinate kernel.
It is a proposition; NormalComparison.lean proves it for positive weights. -/
def EventualKernelComparison {m : ℕ} (z : Fin (m+1) → E)
    (w cost : Fin (m+1) → ℝ) (M sigma : ℝ) : Prop :=
  ∀ᶠ N : ℕ in atTop, ∀ F : FramePolynomial m, F ≠ 0 →
    HasWeightedDegreeLE w N F →
    ∀ hY : MvPolynomial.X (0 : Fin (m+1)) ∉ coordinateKernel z,
      CurveComponentRigidity.PersistentNormalComparison w cost M
        ((sigma/((m : ℝ)+2))*N) F (coordinateKernel z) hY

variable {m K : ℕ}
variable
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ) (hz : ∃ i, Transcendental ℂ (z i)) (hK : 0 < K)

theorem constantY_of_excess_of_comparison
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (sigma : ℚ) (hsigma : 0 < sigma)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (M : ℝ)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M)
    (hcomparison : EventualKernelComparison z (fun i => (w i : ℝ))
      (fun i => (v i : ℝ)) M sigma)
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ)) :
    ∃ a : ℂ, z 0 = algebraMap ℂ E a := by
  obtain ⟨hheight,hY,hann⟩ := rigidity_data_of_excess hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma hvol hexcess
  obtain ⟨N,hF,hcomp⟩ := (hann.and hcomparison).exists
  obtain ⟨F,hF0,hdegree,hwords⟩ := hF
  exact coordinate_constant_of_persistent_comparison z hheight hY
    (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M sigma N
    (fun i => by exact_mod_cast (hv i).le) (by exact_mod_cast hsigma.le)
    (Nat.cast_nonneg N) F hF0 hwords (hcomp F hF0 hdegree hY) hseparated

/-- The full finite contact sum obeys the desired inequality once the normal
comparison and weight separation have been supplied. -/
theorem contact_bound_of_comparison (hinj : Function.Injective y)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta*v i.succ)
    (sigma : ℚ) (hsigma : 0 < sigma) (hmargin : (1+sigma)*theta ≤ 1)
    (hvol : (K : ℝ)*(1+3*(sigma : ℝ))^(m+1)*(∏ i, (w i : ℝ))/(∏ i, (v i : ℝ)) < 1)
    (M : ℝ)
    (hseparated : SeparatedProducts (fun i => (w i : ℝ)) (fun i => (v i : ℝ)) M)
    (hcomparison : EventualKernelComparison z (fun i => (w i : ℝ))
      (fun i => (v i : ℝ)) M sigma) :
    (1+(sigma : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
      (ContactFamilyAt.contact hres hfinite z y hy c hz hK v p : ℝ) ≤
        CurveContactSum.weightedDegree hfinite z w := by
  by_contra h
  obtain ⟨a,ha⟩ := constantY_of_excess_of_comparison hres hfinite z y hy c hz hK
    w v hw hv sigma hsigma hvol M hseparated hcomparison (lt_of_not_ge h)
  exact h (ContactFamilyAt.no_excess_of_constantY hres hfinite z y hy c hz hK hinj
    w v hw hv theta htheta hratio sigma hsigma.le hmargin a ha)

end
end LogTwo.Geometry
end Source0101

-- Source: LogTwo/Geometry/ChosenContactBound.lean
section Source0102
/-! Specialize the conditional curve inequality to the actual arithmetic matrix
weights. Volume, contact margin, and product separation are discharged here.
This component exposes the normal comparison; GlobalContactBound supplies it. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox CurveValuationCenter PlaceValuationRing
open LogTwo.Interpolation LogTwo.Parameters LogTwo.Arithmetic
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem chosenWeights_contact_bound_of_comparison
    (hres : ∀ p : NormalizedPlace ℂ E,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (n : ℕ) (hn : 1 ≤ n) (m : ℕ) (q : ℕ → ℕ) (hq : ∀ i, 2 ≤ q i)
    (M : ℝ) (hM : 0 < M)
    (hgrowth : ∀ i, i < m →
      denominatorSeparationFactor n m M*(∏ j : Fin i, (ceilLogWeight (q j) : ℝ)) <
        (ceilLogWeight (q i) : ℝ))
    (z : Fin (m+1) → E) (hz : ∃ i, Transcendental ℂ (z i)) :
    let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
    let hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
    ∀ (y : Fin w.K → ℂ) (hy : ∀ j, y j ≠ 0) (hinj : Function.Injective y)
      (c : Fin w.K → Fin m → ℂ),
      EventualKernelComparison z (columnWeight w) (fun i => (jetWeight w i : ℝ))
        M (curveSigma w.theta m) →
      (1+(curveSigma w.theta m : ℝ))*∑ p ∈ ContactFamilyAt.places hfinite z y c hz,
        (ContactFamilyAt.contact hres hfinite z y hy c hz hK (jetWeight w) p : ℝ) ≤
          CurveContactSum.weightedDegree hfinite z (rationalColumnWeight w) := by
  dsimp only
  intro y hy hinj c hcomp
  let w := chosenWeights n hn m (fun i => q i) (fun i => hq i)
  have hK : 0 < w.K := centerCount_pos (shape n hn).one_lt_c.le m
  have hm := chosenWeights_geometric_margins n hn m (fun i => q i) (fun i => hq i)
  have hratio : ∀ i : Fin m, rationalColumnWeight w i.succ = w.theta*jetWeight w i.succ := by
    intro i
    dsimp [rationalColumnWeight, jetWeight]
    field_simp [w.theta_pos.ne']
  have hsep : SeparatedProducts (fun i => (rationalColumnWeight w i : ℝ))
      (fun i => (jetWeight w i : ℝ)) M := by
    simpa only [cast_rationalColumnWeight] using
      chosenWeights_separatedProducts n hn m q hq M hM hgrowth
  have hc : EventualKernelComparison z (fun i => (rationalColumnWeight w i : ℝ))
      (fun i => (jetWeight w i : ℝ)) M (curveSigma w.theta m) := by
    simpa only [cast_rationalColumnWeight] using hcomp
  exact contact_bound_of_comparison hres hfinite z y hy c hz hK hinj
    (rationalColumnWeight w) (jetWeight w) (rationalColumnWeight_pos w) (jetWeight_pos w)
    w.theta w.theta_pos.le hratio (curveSigma w.theta m) hm.1
    (curveSigma_contact_margin w.theta_pos w.theta_lt_one m).le hm.2.2 M hsep hc

end
end LogTwo.Geometry
end Source0102

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameEquationFamily.lean
section Source0103
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameEquationFamily.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.FrameEquationFamily

open scoped BigOperators
open PiExponentApprox

abbrev BoundedWords {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ) :=
  {word : List (Fin (m + 1)) // frameWordCost cost word ≤ bound}

noncomputable def equations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) : BoundedWords cost bound → FramePolynomial m :=
  fun word => polynomialFrameWord m word.1 F

theorem span_equations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) :
    Ideal.span (Set.range (equations cost bound F)) =
      frameDerivativeIdeal cost bound F := by
  unfold frameDerivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨word, rfl⟩
    exact ⟨word.1, word.2, rfl⟩
  · rintro ⟨word, hword, rfl⟩
    exact ⟨⟨word, hword⟩, rfl⟩

theorem monomialWeight_eq_weight {m : ℕ} (W : Fin (m + 1) → ℝ)
    (d : Fin (m + 1) →₀ ℕ) :
    monomialWeight W d = Finsupp.weight W d := by
  simp only [monomialWeight, Finsupp.weight_eq_sum, nsmul_eq_mul]

theorem hasWeightedDegreeLE_iff_supportBound {m : ℕ} (W : Fin (m + 1) → ℝ)
    (N : ℝ) (F : FramePolynomial m) :
    HasWeightedDegreeLE W N F ↔ WeightedSliceDegree.SupportBound W N F := by
  simp only [HasWeightedDegreeLE, WeightedSliceDegree.SupportBound, monomialWeight_eq_weight]

theorem equation_hasWeightedDegreeLE {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    HasWeightedDegreeLE W N (equations cost bound F word) :=
  hF.polynomialFrameWord hW word.1

theorem equation_supportBound {m : ℕ} (cost W : Fin (m + 1) → ℝ)
    (bound N : ℝ) (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE W N F) (hW : ∀ i, 0 ≤ W i)
    (word : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound F word) :=
  (hasWeightedDegreeLE_iff_supportBound W N _).mp
    (equation_hasWeightedDegreeLE cost W bound N F hF hW word)

variable {E : Type*} [Field E] [Algebra ℂ E]

noncomputable def sliceEquations {m : ℕ} (cost : Fin (m + 1) → ℝ) (bound : ℝ)
    (F : FramePolynomial m) (A : Finset (Fin (m + 1))) (b : Fin (m + 1) → E) :
    BoundedWords cost bound → MvPolynomial (Fin A.card) E :=
  fun word => WeightedSliceDegree.enumeratedSliceMap A b (equations cost bound F word)

end PiExponent.FrameEquationFamily

end OAI
end Source0103

-- Source: OAI/NumberTheory/PiExponent/Approximation/WeightSeparationConstant.lean
section Source0104
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/WeightSeparationConstant.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox

end PiExponentApprox

end OAI
end Source0104

-- Source: OAI/NumberTheory/PiExponent/Jets/FilteredLength.lean
section Source0105
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FilteredLength.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

section Modules

variable {R M P : Type*} [Ring R] [AddCommGroup M] [AddCommGroup P]
  [Module R M] [Module R P]

def filtrationRestriction (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ) : F n →ₗ[R] G n :=
  (f.domRestrict (F n)).codRestrict (G n) (fun x => hf n x x.property)

def filtrationLayerMap (f : M →ₗ[R] P)
    (F : ℕ → Submodule R M) (G : ℕ → Submodule R P)
    (hf : ∀ n, ∀ x ∈ F n, f x ∈ G n) (n : ℕ) :
    (F n ⧸ (F (n + 1)).comap (F n).subtype) →ₗ[R]
      (G n ⧸ (G (n + 1)).comap (G n).subtype) :=
  Submodule.mapQ _ _ (filtrationRestriction f F G hf n) (by
    intro x hx
    exact hf (n + 1) x hx)

theorem surjective_of_finite_corrections (f : M →ₗ[R] P)
    (G : ℕ → Submodule R P) (d : ℕ) (hzero : G 0 = ⊤) (hend : G d = ⊥)
    (hstep : ∀ n < d, ∀ y ∈ G n, ∃ x : M, y - f x ∈ G (n + 1)) :
    Function.Surjective f := by
  intro y
  have hlift : ∀ n, n ≤ d → ∃ x : M, y - f x ∈ G n := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨0, by simp [hzero]⟩
    | succ n ih =>
      intro hn
      obtain ⟨x, hx⟩ := ih (Nat.le_trans (Nat.le_succ n) hn)
      obtain ⟨z, hz⟩ := hstep n (Nat.lt_of_succ_le hn) (y - f x) hx
      exact ⟨x + z, by simpa only [map_add, sub_add_eq_sub_sub] using hz⟩
  obtain ⟨x, hx⟩ := hlift d le_rfl
  rw [hend, Submodule.mem_bot] at hx
  exact ⟨x, (sub_eq_zero.mp hx).symm⟩

end Modules

variable {A : Type*} [CommRing A]

end PiExponentJets.W24

end OAI
end Source0105

-- Source: OAI/NumberTheory/PiExponent/Jets/GradedGeneration.lean
section Source0106
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/GradedGeneration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

section RingHom

variable {A B : Type*} [CommRing A] [CommRing B]

theorem residue_corrections_of_surjective {K : Type*} [CommRing K]
    (f : A →+* B) (ρ : A →+* K) (π : B →+* K)
    (hρ : Function.Surjective ρ) (hcomm : π.comp f = ρ) :
    ∀ y : B, ∃ x : A, y - f x ∈ RingHom.ker π := by
  intro y
  obtain ⟨x, hx⟩ := hρ (π y)
  have hc : π (f x) = ρ x := congrArg (fun g : A →+* K => g x) hcomm
  refine ⟨x, ?_⟩
  rw [RingHom.mem_ker, map_sub, hc, hx, sub_self]

theorem ideal_power_corrections (f : A →+* B) (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap f)
    (hres : ∀ y : B, ∃ x : A, y - f x ∈ J)
    (hone : ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, y - f x ∈ J ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro y _
    obtain ⟨x, hx⟩ := hres y
    exact ⟨x, by simp, by simpa using hx⟩
  | succ n ih =>
    intro y hy
    rw [pow_succ'] at hy
    refine Submodule.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨x, hx, hex⟩ := hone a ha
      obtain ⟨z, hz, hez⟩ := ih b hb
      refine ⟨x * z, ?_, ?_⟩
      · rw [pow_succ']
        exact Ideal.mul_mem_mul hx hz
      · have hleft : (a - f x) * b ∈ J ^ (n + 1 + 1) := by
          simpa only [← pow_add, Nat.add_comm 2 n, Nat.add_assoc] using
            (Ideal.mul_mem_mul hex hb)
        have hright : f x * (b - f z) ∈ J ^ (n + 1 + 1) := by
          rw [pow_succ']
          exact Ideal.mul_mem_mul (hf hx) hez
        have heq : a * b - f (x * z) = (a - f x) * b + f x * (b - f z) := by
          rw [map_mul]
          ring
        rw [heq]
        exact (J ^ (n + 1 + 1)).add_mem hleft hright
    · intro a b ha hb
      obtain ⟨x, hx, hex⟩ := ha
      obtain ⟨z, hz, hez⟩ := hb
      refine ⟨x + z, (I ^ (n + 1)).add_mem hx hz, ?_⟩
      have heq : a + b - f (x + z) = (a - f x) + (b - f z) := by
        rw [map_add]
        ring
      rw [heq]
      exact (J ^ (n + 1 + 1)).add_mem hex hez

end RingHom

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

theorem ideal_power_preservation (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B)) :
    ∀ n, ∀ x ∈ (I ^ n : Ideal A), algebraMap A B x ∈ J ^ n := by
  intro n x hx
  exact Ideal.le_comap_pow (algebraMap A B) n (Ideal.pow_right_mono hf n hx)

def idealPowerLayerMap (I : Ideal A) (J : Ideal B)
    (hf : I ≤ J.comap (algebraMap A B)) (n : ℕ) :=
  filtrationLayerMap (Algebra.linearMap A B) (fun n => (I ^ n : Ideal A))
    (fun n => (J ^ n).restrictScalars A) (ideal_power_preservation I J hf) n

end PiExponentJets.W24

end OAI
end Source0106

-- Source: OAI/NumberTheory/PiExponent/Jets/CotangentGeneration.lean
section Source0107
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CotangentGeneration.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W24

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

theorem corrections_of_mapCotangent_surjective (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf)) :
    ∀ y ∈ J, ∃ x ∈ I, y - f x ∈ J ^ 2 := by
  intro y hy
  obtain ⟨z, hz⟩ := hs (J.toCotangent ⟨y, hy⟩)
  obtain ⟨x, rfl⟩ := I.toCotangent_surjective z
  rw [Ideal.mapCotangent_toCotangent] at hz
  have he : f x - y ∈ J ^ 2 := J.toCotangent_eq.mp hz
  exact ⟨x, x.property, by simpa only [neg_sub] using (J ^ 2).neg_mem he⟩

theorem algHom_surjective_of_residue_cotangent
    {K : Type*} [CommRing K] (I : Ideal A) (J : Ideal B)
    (f : A →ₐ[R] B) (hf : I ≤ J.comap f)
    (ρ : A →+* K) (π : B →+* K) (hρ : Function.Surjective ρ)
    (hcomm : π.comp f.toRingHom = ρ) (hJ : J = RingHom.ker π)
    (hs : Function.Surjective (Ideal.mapCotangent I J f hf))
    (d : ℕ) (hd : J ^ d = ⊥) : Function.Surjective f := by
  have hres : ∀ y : B, ∃ x : A, y - f x ∈ J := by
    rw [hJ]
    exact residue_corrections_of_surjective f.toRingHom ρ π hρ hcomm
  have hcor := ideal_power_corrections f.toRingHom I J hf hres
    (corrections_of_mapCotangent_surjective I J f hf hs)
  let : Algebra A B := f.toRingHom.toAlgebra
  apply surjective_of_finite_corrections (Algebra.linearMap A B)
    (fun n => (J ^ n).restrictScalars A) d
  · simp
  · simp [hd]
  · intro n _ y hy
    obtain ⟨x, _, hx⟩ := hcor n y hy
    exact ⟨x, hx⟩

end PiExponentJets.W24

end OAI
end Source0107

-- Source: OAI/NumberTheory/PiExponent/Jets/TransverseMultiplicity.lean
section Source0108
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/TransverseMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentApprox.TransverseMultiplicity

noncomputable section

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

def RectIndex (n : σ → ℕ) := {d : σ →₀ ℕ // ∀ i, d i < n i}

def rectangularIdeal (n : σ → ℕ) : Ideal (MvPowerSeries σ K) where
  carrier := {f | ∀ d, (∀ i, d i < n i) → coeff d f = 0}
  zero_mem' := by intro d hd; exact map_zero _
  add_mem' := by
    intro f g hf hg d hd
    rw [map_add, hf d hd, hg d hd, zero_add]
  smul_mem' := by
    intro a f hf d hd
    change coeff d (a * f) = 0
    rw [coeff_mul]
    apply Finset.sum_eq_zero
    intro ab hab
    have heq : ab.1 + ab.2 = d := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
    have hb : ∀ i, ab.2 i < n i := by
      intro i
      have hdi := hd i
      rw [← heq, Finsupp.add_apply] at hdi
      omega
    rw [hf ab.2 hb, mul_zero]

def rectangularPacket (n : σ → ℕ) :
    MvPowerSeries σ K →ₗ[K] (RectIndex n → K) where
  toFun f d := coeff d.val f
  map_add' f g := by ext d; exact map_add _ _ _
  map_smul' a f := by ext d; exact map_smul _ _ _

omit [DecidableEq σ] in
theorem rectangularPacket_surjective (n : σ → ℕ) :
    Function.Surjective (rectangularPacket (K := K) n) := by
  classical
  intro packet
  let f : MvPowerSeries σ K := fun d =>
    if hd : ∀ i, d i < n i then packet ⟨d, hd⟩ else 0
  refine ⟨f, ?_⟩
  funext d
  change (if hd : ∀ i, d.val i < n i then packet ⟨d.val, hd⟩ else 0) = packet d
  simp only [dite_eq_left d.property]
  exact congrArg packet (Subtype.ext rfl)

def rectangularQuotientCoefficients (n : σ → ℕ) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) →ₗ[K] (RectIndex n → K) :=
  Submodule.liftQ ((rectangularIdeal (K := K) n).restrictScalars K)
    (rectangularPacket n) (by
      intro f hf
      change rectangularPacket n f = 0
      funext d
      exact hf d.val d.property)

omit [Fintype σ] in
@[simp] theorem rectangularQuotientCoefficients_mk (n : σ → ℕ)
    (f : MvPowerSeries σ K) (d : RectIndex n) :
    rectangularQuotientCoefficients (K := K) n (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) d =
      coeff d.val f := rfl

theorem rectangularQuotientCoefficients_bijective (n : σ → ℕ) :
    Function.Bijective (rectangularQuotientCoefficients (K := K) n) := by
  constructor
  · intro a b hab
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
    apply Ideal.Quotient.eq.mpr
    intro d hd
    have hc := congrFun hab (⟨d, hd⟩ : RectIndex n)
    change coeff d f = coeff d g at hc
    rw [map_sub, hc, sub_self]
  · intro packet
    obtain ⟨f, hf⟩ := rectangularPacket_surjective (K := K) n packet
    exact ⟨Ideal.Quotient.mk (rectangularIdeal (K := K) n) f, hf⟩

def rectangularQuotientEquiv (n : σ → ℕ) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) ≃ₗ[K] (RectIndex n → K) :=
  LinearEquiv.ofBijective (rectangularQuotientCoefficients n)
    (rectangularQuotientCoefficients_bijective n)

def rectIndexEquiv (n : σ → ℕ) : RectIndex n ≃ (∀ i, Fin (n i)) where
  toFun d i := ⟨d.val i, d.property i⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val), by
    intro i
    exact (a i).isLt⟩
  left_inv d := by
    apply Subtype.ext
    exact Finsupp.ext fun i => rfl
  right_inv a := by
    funext i
    apply Fin.ext
    rfl

instance rectIndexFintype (n : σ → ℕ) : Fintype (RectIndex n) :=
  Fintype.ofEquiv (∀ i, Fin (n i)) (rectIndexEquiv n).symm

theorem card_rectIndex (n : σ → ℕ) : Fintype.card (RectIndex n) = ∏ i, n i := by
  rw [Fintype.card_congr (rectIndexEquiv n), Fintype.card_pi]
  simp only [Fintype.card_fin]

instance rectangularQuotientFinite (n : σ → ℕ) :
    Module.Finite K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  Module.Finite.equiv (rectangularQuotientEquiv n).symm

theorem finrank_rectangularQuotient (n : σ → ℕ) :
    Module.finrank K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = ∏ i, n i := by
  rw [(rectangularQuotientEquiv (K := K) n).finrank_eq,
    Module.finrank_fintype_fun_eq_card, card_rectIndex]

def rectangularAugmentation (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) →+* K :=
  Ideal.Quotient.lift (rectangularIdeal (K := K) n)
    (constantCoeff : MvPowerSeries σ K →+* K) (by
    intro f hf
    change coeff 0 f = 0
    exact hf 0 hn)

omit [Fintype σ] in
@[simp] theorem rectangularAugmentation_mk (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    (f : MvPowerSeries σ K) :
    rectangularAugmentation (K := K) n hn
      (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) = constantCoeff f := rfl

omit [Fintype σ] in
@[simp] theorem rectangularAugmentation_algebraMap (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    (a : K) : rectangularAugmentation (K := K) n hn
      (algebraMap K (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) a) = a := by
  change constantCoeff (C a : MvPowerSeries σ K) = a
  exact constantCoeff_C a

omit [Fintype σ] in
theorem rectangularQuotient_isLocal (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    IsLocalRing (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
    Ideal.Quotient.mk_surjective

theorem ordinaryIdeal_le_rectangularIdeal (n : σ → ℕ) :
    PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i) ≤
      rectangularIdeal (K := K) n := by
  intro f hf d hd
  apply (PiExponent.JetGeometry.mem_weightedIdeal_iff _ _ f).mp hf d
  rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_sum]
  have hsum : (∑ i, d i) ≤ ∑ i, n i :=
    Finset.sum_le_sum fun i _ => Nat.le_of_lt (hd i)
  omega

omit [Fintype σ] [DecidableEq σ] in
theorem ordinaryOneIdeal_eq_constantKernel :
    (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1 :
      Ideal (MvPowerSeries σ K)) = RingHom.ker constantCoeff := by
  ext f
  change (1 : ℕ∞) ≤ f.order ↔ constantCoeff f = 0
  exact one_le_order_iff_constCoeff_eq_zero

omit [Fintype σ] in
theorem rectangularAugmentation_ker_eq_map (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    RingHom.ker (rectangularAugmentation (K := K) n hn) =
      Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
        (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) := by
  rw [ordinaryOneIdeal_eq_constantKernel]
  let q := Ideal.Quotient.mk (rectangularIdeal (K := K) n)
  have hker : Ideal.comap q (RingHom.ker (rectangularAugmentation (K := K) n hn)) =
      RingHom.ker (constantCoeff : MvPowerSeries σ K →+* K) := by
    ext f
    rfl
  rw [← hker, Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective]

theorem rectangularAugmentation_ker_pow (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    (RingHom.ker (rectangularAugmentation (K := K) n hn)) ^ (1 + ∑ i, n i) = ⊥ := by
  rw [rectangularAugmentation_ker_eq_map, ← Ideal.map_pow]
  apply le_antisymm _ bot_le
  calc
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) (1 + ∑ i, n i)) := by
      apply Ideal.map_mono
      simpa only [Nat.mul_one] using
        PiExponent.JetGeometry.ideal_pow_le_weightedIdeal (R := K) (fun _ : σ => 1)
          (PiExponent.JetGeometry.weightedIdeal (fun _ : σ => 1) 1) 1 le_rfl (1 + ∑ i, n i)
    _ ≤ Ideal.map (Ideal.Quotient.mk (rectangularIdeal (K := K) n))
          (rectangularIdeal (K := K) n) :=
      Ideal.map_mono (ordinaryIdeal_le_rectangularIdeal n)
    _ = ⊥ := Ideal.map_quotient_self _

theorem length_rectangularQuotient (n : σ → ℕ) (hn : ∀ i, 0 < n i) :
    Module.length (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)
      (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) = (∏ i, n i : ℕ) := by
  let := (rectangularAugmentation (K := K) n hn).domain_nontrivial
  let := rectangularQuotient_isLocal (K := K) n hn
  rw [PiExponentJets.W24.ring_length_eq_finrank_of_augmentation
    (rectangularAugmentation (K := K) n hn)
    (rectangularAugmentation_algebraMap n hn), finrank_rectangularQuotient]

def rectangularTaylorFactor {A : Type*} [CommRing A] (n : σ → ℕ)
    (I : Ideal A) (tau : A →+* MvPowerSeries σ K)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (A ⧸ I) →+* (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (rectangularIdeal (K := K) n)).comp tau)
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hvanish a ha))

omit [Fintype σ] in
@[simp] theorem rectangularTaylorFactor_mk {A : Type*} [CommRing A]
    (n : σ → ℕ) (I : Ideal A) (tau : A →+* MvPowerSeries σ K)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0)
    (a : A) : rectangularTaylorFactor n I tau hvanish (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := rfl

theorem rectangular_quotient_length_le_of_residue_cotangent
    {A C : Type*} [CommRing A] [CommRing C] [Algebra C A]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i)
    [Algebra C (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n)]
    (P I : Ideal A)
    (f : A →ₐ[C] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n))
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hcomm : (rectangularAugmentation (K := K) n hn).comp f.toRingHom = rho)
    (hf : P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap f)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf))
    (hI : I ≤ RingHom.ker f.toRingHom) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  let B := MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n
  have hs := PiExponentJets.W24.algHom_surjective_of_residue_cotangent
    P (RingHom.ker (rectangularAugmentation (K := K) n hn)) f hf
    rho (rectangularAugmentation (K := K) n hn) hrho hcomm rfl hCot
    (1 + ∑ i, n i) (rectangularAugmentation_ker_pow n hn)
  let g : (A ⧸ I) →+* B := Ideal.Quotient.lift I f.toRingHom hI
  have hg : Function.Surjective g :=
    Ideal.Quotient.lift_surjective_of_surjective I hI hs
  let : Algebra (A ⧸ I) B := g.toAlgebra
  have hg' : Function.Surjective (algebraMap (A ⧸ I) B) := hg
  have hlength : Module.length B B ≤ Module.length (A ⧸ I) (A ⧸ I) := by
    rw [← Module.length_eq_of_surjective (M := B) hg']
    exact Module.length_le_of_surjective (Algebra.linearMap (A ⧸ I) B) hg'
  rw [Module.length_eq_of_surjective (R := A ⧸ I) (M := A ⧸ I)
    (Ideal.Quotient.mk_surjective : Function.Surjective (algebraMap A (A ⧸ I)))]
  rw [length_rectangularQuotient n hn] at hlength
  exact hlength

def rectangularTaylorAlgHom {A : Type*} [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (tau : A →+* MvPowerSeries σ K) :
    A →ₐ[ℚ] (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  ((Ideal.Quotient.mk (rectangularIdeal (K := K) n)).comp tau).toRatAlgHom

omit [Fintype σ] in
@[simp] theorem rectangularTaylorAlgHom_apply {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (tau : A →+* MvPowerSeries σ K) (a : A) :
    rectangularTaylorAlgHom n tau a =
      Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := rfl

omit [Fintype σ] in
theorem rectangularTaylorAlgHom_augmentation {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hconstant : ∀ a, constantCoeff (tau a) = rho a) :
    (rectangularAugmentation (K := K) n hn).comp
      (rectangularTaylorAlgHom n tau).toRingHom = rho := by
  ext a
  exact hconstant a

omit [Fintype σ] in
theorem rectangularTaylorAlgHom_maps_residueIdeal {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hconstant : ∀ a, constantCoeff (tau a) = rho a)
    (P : Ideal A) (hP : P ≤ RingHom.ker rho) :
    P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap
      (rectangularTaylorAlgHom n tau) := by
  intro a ha
  change constantCoeff (tau a) = 0
  rw [hconstant]
  exact hP ha

theorem rectangularTaylor_length_lower {A : Type*}
    [CommRing A] [Algebra ℚ A] [Algebra ℚ K]
    (n : σ → ℕ) (hn : ∀ i, 0 < n i) (tau : A →+* MvPowerSeries σ K)
    (rho : A →+* K) (hrho : Function.Surjective rho)
    (hconstant : ∀ a, constantCoeff (tau a) = rho a)
    (P I : Ideal A) (hP : P ≤ RingHom.ker rho)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn))
        (rectangularTaylorAlgHom n tau)
        (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP)))
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (∏ i, n i : ℕ) ≤ Module.length A (A ⧸ I) := by
  apply rectangular_quotient_length_le_of_residue_cotangent n hn P I
    (rectangularTaylorAlgHom n tau) rho hrho
    (rectangularTaylorAlgHom_augmentation n hn tau rho hconstant)
    (rectangularTaylorAlgHom_maps_residueIdeal n hn tau rho hconstant P hP) hCot
  intro a ha
  change Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hvanish a ha)

def localizedTaylorMap {A L : Type*} [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    L →+* MvPowerSeries σ K :=
  IsLocalization.lift (M := M) (S := L) (g := tau) (fun s : M => by
    apply MvPowerSeries.isUnit_iff_constantCoeff.mpr
    rw [hconstant]
    exact (IsLocalization.map_units L s).map rho)

omit [Fintype σ] [DecidableEq σ] in
@[simp] theorem localizedTaylorMap_algebraMap {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) (a : A) :
    localizedTaylorMap M tau rho hconstant (algebraMap A L a) = tau a := by
  simp only [localizedTaylorMap, IsLocalization.lift_eq]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_constant {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a)) :
    (constantCoeff : MvPowerSeries σ K →+* K).comp
      (localizedTaylorMap M tau rho hconstant) = rho := by
  apply IsLocalization.ringHom_ext M
  ext a
  simp only [RingHom.comp_apply, localizedTaylorMap_algebraMap]
  exact hconstant a

omit [Fintype σ] [DecidableEq σ] in
theorem linearCoefficient_mul (i : σ) (f g : MvPowerSeries σ K) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
      constantCoeff g * coeff (Finsupp.single i 1) f := by
  have h (p : MvPowerSeries σ K) :
      constantCoeff (MvPowerSeries.pderiv i p) = coeff (Finsupp.single i 1) p := by
    rw [← coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp
  rw [← h, (MvPowerSeries.pderiv i).leibniz]
  simp only [smul_eq_mul, map_add, map_mul, h]

omit [Fintype σ] [DecidableEq σ] in
theorem localizedTaylorMap_linearCoefficient {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (i : σ) (d : L → K)
    (hd : ∀ x y, d (x * y) = rho x * d y + rho y * d x)
    (ha : ∀ a, coeff (Finsupp.single i 1) (tau a) = d (algebraMap A L a))
    (x : L) :
    coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) = d x := by
  obtain ⟨a, s, hs⟩ := IsLocalization.exists_mk'_eq M x
  have heq : x * algebraMap A L s = algebraMap A L a :=
    (IsLocalization.mk'_eq_iff_eq_mul.mp hs).symm
  have hc0 (y : L) :
      constantCoeff (localizedTaylorMap M tau rho hconstant y) = rho y :=
    RingHom.congr_fun (localizedTaylorMap_constant M tau rho hconstant) y
  have hc := congrArg
    (fun y => coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant y)) heq
  rw [map_mul, linearCoefficient_mul, hc0, hc0,
    localizedTaylorMap_algebraMap, localizedTaylorMap_algebraMap, ha, ha] at hc
  have hd' := hd x (algebraMap A L s)
  rw [heq] at hd'
  have he : rho (algebraMap A L s) *
      coeff (Finsupp.single i 1) (localizedTaylorMap M tau rho hconstant x) =
        rho (algebraMap A L s) * d x := by
    exact add_left_cancel (hc.trans hd')
  exact mul_left_cancel₀ ((IsLocalization.map_units L s).map rho).ne_zero he

omit [Fintype σ] in
theorem localizedTaylorMap_ideal_le {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    I.map (algebraMap A L) ≤
      (rectangularIdeal (K := K) n).comap (localizedTaylorMap M tau rho hconstant) := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha
  change localizedTaylorMap M tau rho hconstant (algebraMap A L a) ∈ rectangularIdeal n
  rw [localizedTaylorMap_algebraMap]
  exact hvanish a ha

def localizedRectangularTaylorFactor {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) :
    (L ⧸ I.map (algebraMap A L)) →+*
      (MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n) :=
  rectangularTaylorFactor n (I.map (algebraMap A L))
    (localizedTaylorMap M tau rho hconstant)
    (localizedTaylorMap_ideal_le M tau rho hconstant n I hvanish)

omit [Fintype σ] in
@[simp] theorem localizedRectangularTaylorFactor_mk {A L : Type*}
    [CommRing A] [CommRing L] [Algebra A L]
    (M : Submonoid A) [IsLocalization M L]
    (tau : A →+* MvPowerSeries σ K) (rho : L →+* K)
    (hconstant : ∀ a, constantCoeff (tau a) = rho (algebraMap A L a))
    (n : σ → ℕ) (I : Ideal A)
    (hvanish : ∀ a ∈ I, ∀ d, (∀ i, d i < n i) → coeff d (tau a) = 0) (a : A) :
    localizedRectangularTaylorFactor M tau rho hconstant n I hvanish
      (Ideal.Quotient.mk (I.map (algebraMap A L)) (algebraMap A L a)) =
        Ideal.Quotient.mk (rectangularIdeal (K := K) n) (tau a) := by
  change Ideal.Quotient.mk (rectangularIdeal (K := K) n)
    (localizedTaylorMap M tau rho hconstant (algebraMap A L a)) = _
  rw [localizedTaylorMap_algebraMap]

end
end PiExponentApprox.TransverseMultiplicity

end OAI
end Source0108

-- Source: OAI/NumberTheory/PiExponent/Jets/TransverseWeightedMultiplicity.lean
section Source0109
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/TransverseWeightedMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.TransverseWeightedMultiplicity

open scoped BigOperators

theorem rectangularCutoff_budget {k : ℕ} (hk : 0 < k)
    (kappa : Fin k → ℝ) (hkappa : ∀ i, 0 < kappa i)
    (T : ℝ) (hT : 0 < T) :
    ∑ i, ((rectangularCutoff kappa T i - 1 : ℕ) : ℝ) * kappa i ≤ T := by
  have hpos := rectangularCutoff_pos hk kappa hkappa hT
  have hlt : ∀ i, rectangularCutoff kappa T i - 1 < rectangularCutoff kappa T i := by
    intro i
    exact Nat.sub_lt (hpos i) (by norm_num)
  have h := rectangularCutoff_weight_lt hk kappa hkappa
    (fun i => rectangularCutoff kappa T i - 1) hlt
  simpa only [mul_comm] using h.le

theorem rectangular_weight_product_comparison {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N L : ℝ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (epsilon * N) ^ k / ((k : ℝ) ^ k * ∏ i, kappa i) ≤ L)
    (hupper : L ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  have hA : 0 < ∏ i, rho i := Finset.prod_pos (fun i _ => hrho i)
  have hB : 0 < (k : ℝ) ^ k * ∏ i, kappa i :=
    mul_pos (pow_pos (by exact_mod_cast hk) _) (Finset.prod_pos (fun i _ => hkappa i))
  have h := (div_le_div_iff₀ hB hA).mp (hlower.trans hupper)
  rw [mul_pow] at h
  apply (le_div_iff₀ (pow_pos hepsilon k)).mpr
  apply (mul_le_mul_iff_right₀ (pow_pos hN k)).mp
  calc
    N ^ k * ((∏ i, rho i) * epsilon ^ k) =
        epsilon ^ k * N ^ k * ∏ i, rho i := by ring
    _ ≤ N ^ k * ((k : ℝ) ^ k * ∏ i, kappa i) := h

theorem weight_comparison_of_rectangular_count {k : ℕ} (hk : 0 < k)
    (rho kappa : Fin k → ℝ) (epsilon N : ℝ) (L : ℕ)
    (hrho : ∀ i, 0 < rho i) (hkappa : ∀ i, 0 < kappa i)
    (hepsilon : 0 < epsilon) (hN : 0 < N)
    (hlower : (∏ i, rectangularCutoff kappa (epsilon * N) i : ℕ) ≤ L)
    (hupper : (L : ℝ) ≤ N ^ k / ∏ i, rho i) :
    (∏ i, rho i) ≤ (k : ℝ) ^ k * (∏ i, kappa i) / epsilon ^ k := by
  apply rectangular_weight_product_comparison hk rho kappa epsilon N L
    hrho hkappa hepsilon hN _ hupper
  have hv := rectangularCutoff_product_lower hk kappa hkappa (mul_pos hepsilon hN)
  apply hv.trans
  exact_mod_cast hlower

end PiExponent.TransverseWeightedMultiplicity
end

end OAI
end Source0109

-- Source: OAI/NumberTheory/PiExponent/Jets/NormalBasisProducts.lean
section Source0110
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/NormalBasisProducts.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.NormalBasisProducts

open scoped BigOperators
open NormalBasisRigidity TransverseWeightedMultiplicity

variable {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def enumeration (A B : Finset ι) (hcard : A.card = B.card) : Fin A.card → ι :=
  fun i => (B.equivFin.symm (Fin.cast hcard i)).val

theorem enumeration_linearIndependent {v : ι → V} (A B : Finset ι)
    (hcard : A.card = B.card) (hB : IsNormalBasis (K := K) v B) :
    LinearIndependent K (fun i => v (enumeration A B hcard i)) := by
  have hli : LinearIndependent K (fun i : B => v i) := hB.1
  exact hli.comp (fun i => B.equivFin.symm (Fin.cast hcard i))
    (B.equivFin.symm.injective.comp (Fin.cast_injective hcard))

theorem prod_equivFin {M : Type*} [CommMonoid M] (A : Finset ι) (f : ι → M) :
    (∏ i : Fin A.card, f (A.equivFin.symm i)) = ∏ i ∈ A, f i := by
  calc
    _ = ∏ i : A, f i := Fintype.prod_equiv A.equivFin.symm _ _ (fun _ => rfl)
    _ = _ := Finset.prod_coe_sort A f

theorem prod_enumeration {M : Type*} [CommMonoid M]
    (A B : Finset ι) (hcard : A.card = B.card) (f : ι → M) :
    (∏ i : Fin A.card, f (enumeration A B hcard i)) = ∏ i ∈ B, f i := by
  calc
    _ = ∏ i : Fin B.card, f (B.equivFin.symm i) :=
      Fintype.prod_equiv (finCongr hcard) _ _ (fun _ => rfl)
    _ = _ := prod_equivFin B f

theorem rectangular_factor_le_constant (m k : ℕ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkm : k ≤ m + 2) :
    (k : ℝ) ^ k * (((m : ℝ) + 2) / sigma) ^ k ≤
      2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
  have hbase : 0 ≤ ((m : ℝ) + 2) / sigma := by positivity
  have hdim : (k : ℝ) ≤ (m : ℝ) + 2 := by exact_mod_cast hkm
  have hp : (k : ℝ) ^ k ≤ ((m : ℝ) + 2) ^ (m + 2) := by
    calc
      _ ≤ ((m : ℝ) + 2) ^ k := pow_le_pow_left₀ (Nat.cast_nonneg k) hdim k
      _ ≤ _ := pow_le_pow_right₀ (by have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith) hkm
  have hfactor : (k : ℝ) ^ k ≤ 2 * ((m : ℝ) + 2) ^ (m + 2) := hp.trans (by
    have h : 0 ≤ ((m : ℝ) + 2) ^ (m + 2) := by positivity
    linarith)
  have hpow : (((m : ℝ) + 2) / sigma) ^ k ≤
      (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2) := by
    calc
      _ ≤ (1 + ((m : ℝ) + 2) / sigma) ^ k :=
        pow_le_pow_left₀ hbase (le_add_of_nonneg_left zero_le_one) k
      _ ≤ _ := pow_le_pow_right₀ (le_add_of_nonneg_right hbase) hkm
  exact mul_le_mul hfactor hpow (pow_nonneg hbase _) (by positivity)

theorem rectangular_comparison_le_constant {m k : ℕ}
    (hkm : k ≤ m + 2) (kappa : Fin k → ℝ) (sigma : ℝ)
    (hsigma : 0 < sigma) (hkappa : ∀ i, 0 ≤ kappa i) :
    (k : ℝ) ^ k * (∏ i, kappa i) / (sigma / ((m : ℝ) + 2)) ^ k ≤
      (2 * ((m : ℝ) + 2) ^ (m + 2) *
        (1 + ((m : ℝ) + 2) / sigma) ^ (m + 2)) * ∏ i, kappa i := by
  have h := rectangular_factor_le_constant m k sigma hsigma hkm
  have hp : 0 ≤ ∏ i, kappa i := Finset.prod_nonneg (fun i _ => hkappa i)
  have hh := mul_le_mul_of_nonneg_right h hp
  convert hh using 1
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow, inv_inv]
  ring

end PiExponent.NormalBasisProducts
end

end OAI
end Source0110

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameResidueDirections.lean
section Source0111
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameResidueDirections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent

open scoped BigOperators
open PiExponentApprox NormalBasisRigidity

theorem residue_polynomialFrame_eq_frameBasis_dot {E : Type*} [Field E]
    (m : ℕ) (phi : FramePolynomial m →+* E)
    (hy : phi (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (j : Fin (m + 1)) (p : FramePolynomial m) :
    phi (polynomialFrame m j p) =
      ∑ i, frameBasis m (phi (MvPolynomial.X 0)) hy j i *
        phi (MvPolynomial.pderiv i p) := by
  refine Fin.cases ?_ (fun l => ?_) j
  · rw [polynomialFrame_zero, logarithmicDerivation_apply, map_add, map_mul,
      map_sum, Fin.sum_univ_succ]
    simp only [frameBasis_zero_zero, frameBasis_zero_succ, one_mul]
  · rw [polynomialFrame_pos m l.succ (Fin.succ_ne_zero l), frameBasis_succ]
    simp [Pi.basisFun_apply, Pi.single_apply]

end PiExponent
end

end OAI
end Source0111

-- Source: OAI/NumberTheory/PiExponent/Jets/CommutingTaylor.lean
section Source0112
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CommutingTaylor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CommutingTaylor

open Finset Nat
variable {R : Type*} [CommRing R] [Algebra ℚ R]

def iter (D : Derivation ℚ R R) (n : ℕ) : R →ₗ[ℚ] R := D.toLinearMap ^ n

@[simp] theorem iter_zero (D : Derivation ℚ R R) (a : R) : iter D 0 a = a := rfl
@[simp] theorem iter_succ (D : Derivation ℚ R R) (n : ℕ) (a : R) :
    iter D (n+1) a = D (iter D n a) := by
  change (D.toLinearMap ^ (n + 1)) a = D ((D.toLinearMap ^ n) a)
  calc
    (D.toLinearMap ^ (n + 1)) a = (D.toLinearMap * D.toLinearMap ^ n) a :=
      congrArg (fun f : Module.End ℚ R => f a) (_root_.pow_succ' D.toLinearMap n)
    _ = D.toLinearMap ((D.toLinearMap ^ n) a) :=
      Module.End.mul_apply D.toLinearMap (D.toLinearMap ^ n) a
    _ = D ((D.toLinearMap ^ n) a) :=
      congrFun (Derivation.coeFn_coe D) ((D.toLinearMap ^ n) a)

theorem iter_mul (D : Derivation ℚ R R) (n : ℕ) (a b : R) :
    iter D n (a*b) = ∑ ij ∈ antidiagonal n,
      n.choose ij.1 • (iter D ij.1 a * iter D ij.2 b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_antidiagonal_choose_succ_nsmul
      (fun i j => iter D i a * iter D j b) n]
    simp only [iter_succ, ih, map_sum, map_nsmul, Derivation.leibniz,
      smul_eq_mul, nsmul_add, Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro ij hij
    rw [n.choose_symm_of_eq_add (mem_antidiagonal.mp hij).symm]
    rw [mul_comm]

private theorem factorial_normalize (i j : ℕ) :
    (1 / ((i+j).factorial : ℚ)) * ((i+j).choose i : ℚ) =
      (1 / (i.factorial : ℚ)) * (1 / (j.factorial : ℚ)) := by
  have h : (((i+j).choose i : ℚ) * (i.factorial : ℚ) * (j.factorial : ℚ)) =
      ((i+j).factorial : ℚ) := by
    exact_mod_cast (by
      simpa using Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right i j) :
        (i+j).choose i * i.factorial * j.factorial = (i+j).factorial)
  have hi : (i.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i
  have hj : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hn : ((i+j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (i+j)
  field_simp
  nlinarith [h]

def taylorSeries (D : Derivation ℚ R R) (a : R) : PowerSeries R :=
  PowerSeries.mk fun n => (1 / (n.factorial : ℚ)) • iter D n a

@[simp] theorem coeff_taylorSeries (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorSeries D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact PowerSeries.coeff_mk n _

theorem taylorSeries_mul (D : Derivation ℚ R R) (a b : R) :
    taylorSeries D (a*b) = taylorSeries D a * taylorSeries D b := by
  ext n
  rw [PowerSeries.coeff_mul, coeff_taylorSeries, iter_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  have hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
  rw [coeff_taylorSeries, coeff_taylorSeries]
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_mul_smul_comm]
  rw [← hn, factorial_normalize]

def taylorHom (D : Derivation ℚ R R) : R →+* PowerSeries R where
  toFun := taylorSeries D
  map_zero' := by ext n; simp [taylorSeries]
  map_one' := by
    ext n
    cases n with
    | zero => simp [taylorSeries]
    | succ n =>
      have h : iter D (n+1) (1:R) = 0 := by
        induction n with
        | zero => simp
        | succ n ih => simp [ih]
      simp [taylorSeries, h]
  map_add' a b := by ext n; simp [taylorSeries, smul_add]
  map_mul' := taylorSeries_mul D

@[simp] theorem coeff_taylorHom (D : Derivation ℚ R R) (a : R) (n : ℕ) :
    PowerSeries.coeff n (taylorHom D a) = (1 / (n.factorial : ℚ)) • iter D n a := by
  exact coeff_taylorSeries D a n

@[simp] theorem constantCoeff_taylorHom (D : Derivation ℚ R R) (a : R) :
    PowerSeries.constantCoeff (taylorHom D a) = a := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_taylorHom]
  simp

def mixedIter : (m : ℕ) → (Fin m → Derivation ℚ R R) → (Fin m →₀ ℕ) → R →ₗ[ℚ] R
  | 0, _, _ => LinearMap.id
  | m+1, D, α => (mixedIter m (fun i => D i.succ) α.tail).comp (iter (D 0) (α 0))

def taylorHomFin : (m : ℕ) → (Fin m → Derivation ℚ R R) → R →+* MvPowerSeries (Fin m) R
  | 0, _ => MvPowerSeries.C
  | m+1, D => (MvPowerSeries.finSuccEquiv R m).symm.toRingHom.comp
      ((PowerSeries.map (taylorHomFin m (fun i => D i.succ))).comp (taylorHom (D 0)))

theorem coeff_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (taylorHomFin m D a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • mixedIter m D α a := by
  induction m generalizing a with
  | zero =>
    have hα : α = 0 := Subsingleton.elim _ _
    simp [taylorHomFin, mixedIter, hα]
  | succ m ih =>
    have hcoeff := MvPowerSeries.coeff_coeff_finSuccEquiv
      ((MvPowerSeries.finSuccEquiv R m).symm
        (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a)))
      (k := α 0) (x := α.tail)
    simp only [AlgEquiv.apply_symm_apply] at hcoeff
    rw [show α.tail.cons (α 0) = α by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp] at hcoeff
    rw [taylorHomFin, RingHom.comp_apply, RingHom.comp_apply]
    change MvPowerSeries.coeff α ((MvPowerSeries.finSuccEquiv R m).symm
      (PowerSeries.map (taylorHomFin m (fun i => D i.succ)) (taylorHom (D 0) a))) = _
    rw [← hcoeff, PowerSeries.coeff_map, coeff_taylorHom, ih]
    simp only [map_smul, mixedIter, LinearMap.comp_apply, Fin.prod_univ_succ,
      Finsupp.tail_apply, smul_smul]
    rw [mul_comm]

@[simp] theorem mixedIter_zero (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    mixedIter m D 0 a = a := by
  induction m generalizing a with
  | zero => rfl
  | succ m ih =>
    have ht : (0 : Fin (m+1) →₀ ℕ).tail = 0 := by ext i; rfl
    simp [mixedIter, ht, ih]

@[simp] theorem mixedIter_single (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) : mixedIter m D (Finsupp.single i 1) a = D i a := by
  induction m generalizing a with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [← Finsupp.cons_zero_eq_single_zero]
      simp [mixedIter, iter]
    · rw [← Finsupp.cons_zero_single_eq_single_succ]
      simp [mixedIter, ih]

@[simp] theorem coeff_zero_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R) (a : R) :
    MvPowerSeries.coeff 0 (taylorHomFin m D a) = a := by
  simp [coeff_taylorHomFin]

@[simp] theorem coeff_single_taylorHomFin (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorHomFin m D a) = D i a := by
  rw [coeff_taylorHomFin, mixedIter_single]
  have h : (∏ j : Fin m, (1 / ((Finsupp.single i 1 j).factorial : ℚ))) = 1 := by
    apply Finset.prod_eq_one
    intro j hj
    by_cases he : i = j <;> simp [he]
  rw [h, one_smul]

def residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) :
    R →+* MvPowerSeries (Fin m) K :=
  (MvPowerSeries.map ρ).comp (taylorHomFin m D)

theorem coeff_residueTaylorFin {K : Type*} [CommRing K] [Algebra ℚ K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K)
    (α : Fin m →₀ ℕ) (a : R) :
    MvPowerSeries.coeff α (residueTaylorFin m D ρ a) =
      (∏ i, (1 / ((α i).factorial : ℚ))) • ρ (mixedIter m D α a) := by
  simp [residueTaylorFin, coeff_taylorHomFin, map_rat_smul]

@[simp] theorem coeff_zero_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.coeff 0 (residueTaylorFin m D ρ a) = ρ a := by
  simp [residueTaylorFin]

@[simp] theorem coeff_single_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (i : Fin m) (a : R) :
    MvPowerSeries.coeff (Finsupp.single i 1) (residueTaylorFin m D ρ a) = ρ (D i a) := by
  simp [residueTaylorFin]

@[simp] theorem constantCoeff_residueTaylorFin {K : Type*} [CommRing K]
    (m : ℕ) (D : Fin m → Derivation ℚ R R) (ρ : R →+* K) (a : R) :
    MvPowerSeries.constantCoeff (residueTaylorFin m D ρ a) = ρ a := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_residueTaylorFin m D ρ a

end PiExponent.CommutingTaylor

end

end OAI
end Source0112

-- Source: OAI/NumberTheory/PiExponent/Jets/TaylorRectangular.lean
section Source0113
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/TaylorRectangular.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.TaylorRectangular

open scoped BigOperators
open CommutingTaylor
open PiExponentApprox

section General
variable {R K : Type*} [CommRing R] [Algebra ℚ R] [Field K] [Algebra ℚ K]

theorem residueTaylor_mem_rectangular (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (ρ : R →+* K) (n : Fin m → ℕ) (a : R)
    (ha : ∀ α : Fin m →₀ ℕ, (∀ i, α i < n i) → ρ (mixedIter m D α a) = 0) :
    residueTaylorFin m D ρ a ∈ TransverseMultiplicity.rectangularIdeal n := by
  intro α hα
  rw [coeff_residueTaylorFin, ha α hα]
  rw [Algebra.smul_def]
  exact mul_zero _

end General

def rationalFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℚ (FramePolynomial m) (FramePolynomial m) :=
  (polynomialFrame m i).restrictScalars ℚ

@[simp] theorem rationalFrame_apply (m : ℕ) (i : Fin (m + 1)) (a : FramePolynomial m) :
    rationalFrame m i a = polynomialFrame m i a := rfl

def derivativeWord {ι : Type*} : (k : ℕ) → (Fin k → ι) → (Fin k →₀ ℕ) → List ι
  | 0, _, _ => []
  | k+1, B, α => derivativeWord k (fun i => B i.succ) α.tail ++ List.replicate (α 0) (B 0)

theorem frameWord_append (m : ℕ) (u v : List (Fin (m + 1))) (a : FramePolynomial m) :
    polynomialFrameWord m (u ++ v) a = polynomialFrameWord m u (polynomialFrameWord m v a) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [polynomialFrameWord_cons, ih]

theorem frameWord_replicate (m : ℕ) (i : Fin (m + 1)) (n : ℕ) (a : FramePolynomial m) :
    polynomialFrameWord m (List.replicate n i) a = iter (rationalFrame m i) n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem mixedIter_eq_frameWord (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (a : FramePolynomial m) :
    mixedIter k (fun i => rationalFrame m (B i)) α a =
      polynomialFrameWord m (derivativeWord k B α) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord, frameWord_append,
      frameWord_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_cost (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost (derivativeWord k B α) = ∑ i, (α i : ℝ) * cost (B i) := by
  induction k with
  | zero => simp [derivativeWord, frameWordCost]
  | succ k ih =>
    simp only [derivativeWord, frameWordCost, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate]
    change frameWordCost cost (derivativeWord k (fun i => B i.succ) α.tail) +
      (α 0) • cost (B 0) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_cost_le (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hα : ∀ i, α i < n i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ) :
    frameWordCost cost (derivativeWord k B α) ≤ δ := by
  rw [derivativeWord_cost]
  apply le_trans _ hn
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα i; omega : α i ≤ n i - 1)

theorem frame_residueTaylor_ideal_le {K : Type*} [Field K] [Algebra ℚ K]
    (m k : ℕ) (B : Fin k → Fin (m + 1)) (ρ : FramePolynomial m →+* K)
    (I : Ideal (FramePolynomial m)) (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      ρ (polynomialFrameWord m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap
      (residueTaylorFin k (fun i => rationalFrame m (B i)) ρ) := by
  intro a ha
  apply residueTaylor_mem_rectangular
  intro α hα
  rw [mixedIter_eq_frameWord]
  exact hvanish a ha _ (derivativeWord_cost_le m k B α cost n δ hcost hα hn)

def costRectangle (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ) (i : Fin k) : ℕ :=
  ⌊δ / ((k : ℝ) * cost (B i))⌋₊ + 1

@[simp] theorem costRectangle_pos (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ) (i : Fin k) :
    0 < costRectangle m k B cost δ i := Nat.zero_lt_succ _

end PiExponent.TaylorRectangular

end

end OAI
end Source0113

-- Source: OAI/NumberTheory/PiExponent/Jets/FrameTransverseMultiplicity.lean
section Source0114
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FrameTransverseMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FrameTransverseMultiplicity

open scoped BigOperators
open PiExponentApprox
open CommutingTaylor TaylorRectangular
open TransverseMultiplicity

variable {L K : Type*} [CommRing L] [Field K]

def frameTaylor (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) :
    FramePolynomial m →+* MvPowerSeries (Fin k) K :=
  residueTaylorFin k (fun i => rationalFrame m (B i))
    (rho.comp (algebraMap (FramePolynomial m) L))

@[simp] theorem frameTaylor_constant (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) (a : FramePolynomial m) :
    MvPowerSeries.constantCoeff (frameTaylor m k B rho a) =
      rho (algebraMap (FramePolynomial m) L a) := by
  exact constantCoeff_residueTaylorFin _ _ _ _

def localizedFrameTaylor (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) : L →+* MvPowerSeries (Fin k) K :=
  localizedTaylorMap M (frameTaylor m k B rho) rho (frameTaylor_constant m k B rho)

@[simp] theorem localizedFrameTaylor_algebraMap (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (a : FramePolynomial m) :
    localizedFrameTaylor m k B M rho (algebraMap (FramePolynomial m) L a) =
      frameTaylor m k B rho a := by
  exact localizedTaylorMap_algebraMap M _ rho _ a

@[simp] theorem localizedFrameTaylor_constant (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (a : L) :
    MvPowerSeries.constantCoeff (localizedFrameTaylor m k B M rho a) = rho a := by
  exact RingHom.congr_fun (localizedTaylorMap_constant M (frameTaylor m k B rho) rho
    (frameTaylor_constant m k B rho)) a

@[simp] theorem frameTaylor_firstCoefficient (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (rho : L →+* K) (i : Fin k) (a : FramePolynomial m) :
    MvPowerSeries.coeff (Finsupp.single i 1) (frameTaylor m k B rho a) =
      rho (algebraMap (FramePolynomial m) L (polynomialFrame m (B i) a)) := by
  exact coeff_single_residueTaylorFin _ _ _ i a

variable [Algebra ℚ K]

theorem localizedFrameTaylor_ideal_le (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra (FramePolynomial m) L] (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (I : Ideal (FramePolynomial m))
    (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      rho (algebraMap (FramePolynomial m) L (polynomialFrameWord m word a)) = 0) :
    I.map (algebraMap (FramePolynomial m) L) ≤
      (rectangularIdeal (K := K) n).comap (localizedFrameTaylor m k B M rho) := by
  apply localizedTaylorMap_ideal_le M (frameTaylor m k B rho) rho (frameTaylor_constant m k B rho)
  exact frame_residueTaylor_ideal_le m k B (rho.comp (algebraMap (FramePolynomial m) L))
    I cost n δ hcost hn hvanish

def frameRectangularHom (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (n : Fin k → ℕ) :
    L →ₐ[ℚ] (MvPowerSeries (Fin k) K ⧸ rectangularIdeal (K := K) n) :=
  rectangularTaylorAlgHom n (localizedFrameTaylor m k B M rho)

theorem frameRectangularHom_maps_residueIdeal (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (P : Ideal L) (hP : P ≤ RingHom.ker rho) :
    P ≤ (RingHom.ker (rectangularAugmentation (K := K) n hn)).comap
      (frameRectangularHom m k B M rho n) :=
  rectangularTaylorAlgHom_maps_residueIdeal n hn _ rho
    (localizedFrameTaylor_constant m k B M rho) P hP

theorem frame_rectangular_length_lower (m k : ℕ) (B : Fin k → Fin (m + 1))
    [Algebra ℚ L] [Algebra (FramePolynomial m) L]
    (M : Submonoid (FramePolynomial m)) [IsLocalization M L]
    (rho : L →+* K) (hrho : Function.Surjective rho)
    (P : Ideal L) (hP : P ≤ RingHom.ker rho) (I : Ideal (FramePolynomial m))
    (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hn : ∀ i, 0 < n i) (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hCot : Function.Surjective
      (Ideal.mapCotangent P (RingHom.ker (rectangularAugmentation (K := K) n hn))
        (frameRectangularHom m k B M rho n)
        (frameRectangularHom_maps_residueIdeal m k B M rho n hn P hP)))
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      rho (algebraMap (FramePolynomial m) L (polynomialFrameWord m word a)) = 0) :
    (∏ i, n i : ℕ) ≤
      Module.length L (L ⧸ I.map (algebraMap (FramePolynomial m) L)) := by
  apply rectangularTaylor_length_lower n hn (localizedFrameTaylor m k B M rho) rho hrho
    (localizedFrameTaylor_constant m k B M rho) P _ hP hCot
  exact localizedFrameTaylor_ideal_le m k B M rho I cost n δ hcost hbudget hvanish

end PiExponent.FrameTransverseMultiplicity

end

end OAI
end Source0114

-- Source: OAI/NumberTheory/PiExponent/Jets/RectangularCotangent.lean
section Source0115
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/RectangularCotangent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentApprox.TransverseMultiplicity

open MvPowerSeries

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

abbrev RectangularRing (n : σ → ℕ) :=
  MvPowerSeries σ K ⧸ rectangularIdeal (K := K) n

omit [Fintype σ] [DecidableEq σ] in
theorem rectangularPositive (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) : ∀ i, 0 < n i :=
  fun i => lt_of_lt_of_le (by norm_num) (hn i)

def rectangularAugmentationIdeal (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Ideal (RectangularRing (K := K) n) :=
  RingHom.ker (rectangularAugmentation (K := K) n (rectangularPositive n hn))

def unitRectIndex (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) (i : σ) : RectIndex n :=
  ⟨Finsupp.single i 1, by
    intro j
    by_cases h : j = i
    · subst j
      simpa using (show 1 < n i by have := hn i; omega)
    · simpa [Finsupp.single_eq_of_ne h] using rectangularPositive n hn j⟩

def rectangularFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    RectangularRing (K := K) n →ₗ[K] (σ → K) where
  toFun f i := rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i)
  map_add' f g := by ext i; exact congrFun (map_add (rectangularQuotientCoefficients (K := K) n) f g) _
  map_smul' a f := by ext i; exact congrFun (map_smul (rectangularQuotientCoefficients (K := K) n) a f) _

omit [Fintype σ] in
@[simp] theorem rectangularFirstCoefficients_mk (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : MvPowerSeries σ K) (i : σ) :
    rectangularFirstCoefficients (K := K) n hn (Ideal.Quotient.mk (rectangularIdeal (K := K) n) f) i =
      coeff (Finsupp.single i 1) f := rfl

omit [Fintype σ] [DecidableEq σ] in

theorem firstCoeff_mul (f g : MvPowerSeries σ K) (i : σ) :
    coeff (Finsupp.single i 1) (f * g) =
      constantCoeff f * coeff (Finsupp.single i 1) g +
        constantCoeff g * coeff (Finsupp.single i 1) f := by
  have hh := congrArg (constantCoeff : MvPowerSeries σ K →+* K)
    ((MvPowerSeries.pderiv i).leibniz f g)
  simpa only [smul_eq_mul, map_add, map_mul,
    ← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add,
    Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one] using hh

theorem rectangular_reconstruct (n : σ → ℕ) (f : RectangularRing (K := K) n) :
    f = ∑ d : RectIndex n,
      Ideal.Quotient.mk (rectangularIdeal (K := K) n)
        (monomial d.val (rectangularQuotientCoefficients (K := K) n f d)) := by
  apply (rectangularQuotientCoefficients_bijective (K := K) n).1
  rw [map_sum]
  funext e
  simp only [Finset.sum_apply, rectangularQuotientCoefficients_mk]
  change rectangularQuotientCoefficients (K := K) n f e =
    ∑ d : RectIndex n, coeff e.val
      (monomial d.val (rectangularQuotientCoefficients (K := K) n f d))
  symm
  rw [Finset.sum_eq_single e]
  · simp only [coeff_monomial_same]
  · intro d _ hde
    have hne : e.val ≠ d.val := by
      intro he
      exact hde (Subtype.ext he.symm)
    simp only [coeff_monomial, ite_eq_right hne]
  · intro h
    exact (h (Finset.mem_univ e)).elim

theorem rectangular_monomial_mem_square (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (d : σ →₀ ℕ) (a : K) (hd : d ≠ 0)
    (hunit : ∀ i, d ≠ Finsupp.single i 1) :
    Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial d a) ∈
      (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  have hex : ∃ i, d i ≠ 0 := by
    by_contra! hh
    exact hd (by ext i; exact hh i)
  obtain ⟨i, hi⟩ := hex
  let e : σ →₀ ℕ := d - Finsupp.single i 1
  have he : e + Finsupp.single i 1 = d := Finsupp.sub_add_single_one_cancel hi
  have he0 : e ≠ 0 := by
    intro h
    apply hunit i
    simpa [h] using he.symm
  have hleft : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial (Finsupp.single i 1) (1 : K)) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial (Finsupp.single i 1) (1 : K)) = 0
    have hsingle : (0 : σ →₀ ℕ) ≠ Finsupp.single i 1 := by
      intro h
      have hh := congrArg (fun d : σ →₀ ℕ => d i) h
      simp at hh
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, hsingle]
  have hright : Ideal.Quotient.mk (rectangularIdeal (K := K) n) (monomial e a) ∈
      rectangularAugmentationIdeal (K := K) n hn := by
    change constantCoeff (monomial e a) = 0
    simp [← coeff_zero_eq_constantCoeff, coeff_monomial, Ne.symm he0]
  rw [pow_two]
  have hh := Ideal.mul_mem_mul hleft hright
  convert hh using 1
  rw [← map_mul, monomial_mul_monomial, one_mul, add_comm, he]

theorem rectangular_mem_square_of_first_zero (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : RectangularRing (K := K) n)
    (hf : f ∈ rectangularAugmentationIdeal (K := K) n hn)
    (hfirst : rectangularFirstCoefficients (K := K) n hn f = 0) :
    f ∈ (rectangularAugmentationIdeal (K := K) n hn) ^ 2 := by
  rw [rectangular_reconstruct n f]
  apply Ideal.sum_mem
  intro d hd
  by_cases hd0 : d.val = 0
  · have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
      obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
      change coeff d.val F = 0
      rw [hd0]
      exact hf
    simp [hc]
  · by_cases hu : ∃ i, d.val = Finsupp.single i 1
    · obtain ⟨i, hi⟩ := hu
      have hc : rectangularQuotientCoefficients (K := K) n f d = 0 := by
        have hh := congrFun hfirst i
        change rectangularQuotientCoefficients (K := K) n f (unitRectIndex n hn i) = 0 at hh
        have he : d = unitRectIndex n hn i := Subtype.ext hi
        simpa only [he] using hh
      simp [hc]
    · exact rectangular_monomial_mem_square n hn d.val _ hd0 (by simpa using hu)

def rectangularIdealFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    rectangularAugmentationIdeal (K := K) n hn →ₗ[K] (σ → K) :=
  (rectangularFirstCoefficients (K := K) n hn).comp
    ((rectangularAugmentationIdeal (K := K) n hn).subtype.restrictScalars K)

omit [Fintype σ] in
theorem rectangularIdealFirstCoefficients_mul (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f g : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularIdealFirstCoefficients (K := K) n hn (f * g) = 0 := by
  obtain ⟨F, hF⟩ := Ideal.Quotient.mk_surjective f.val
  obtain ⟨G, hG⟩ := Ideal.Quotient.mk_surjective g.val
  have hFc : constantCoeff F = 0 := by
    have hf := f.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) f.val = 0 at hf
    simpa only [← hF, rectangularAugmentation_mk] using hf
  have hGc : constantCoeff G = 0 := by
    have hg := g.property
    change rectangularAugmentation (K := K) n (rectangularPositive n hn) g.val = 0 at hg
    simpa only [← hG, rectangularAugmentation_mk] using hg
  ext i
  change rectangularFirstCoefficients (K := K) n hn (f.val * g.val) i = 0
  rw [← hF, ← hG, ← map_mul, rectangularFirstCoefficients_mk, firstCoeff_mul, hFc, hGc]
  simp

def rectangularCotangentFirstCoefficients (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    (rectangularAugmentationIdeal (K := K) n hn).Cotangent →ₗ[K] (σ → K) :=
  Ideal.Cotangent.lift (rectangularIdealFirstCoefficients (K := K) n hn)
    (rectangularIdealFirstCoefficients_mul n hn)

omit [Fintype σ] in
@[simp] theorem rectangularCotangentFirstCoefficients_toCotangent
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i)
    (f : rectangularAugmentationIdeal (K := K) n hn) :
    rectangularCotangentFirstCoefficients (K := K) n hn
      ((rectangularAugmentationIdeal (K := K) n hn).toCotangent f) =
        rectangularFirstCoefficients (K := K) n hn f.val := rfl

theorem rectangularCotangentFirstCoefficients_injective
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Injective (rectangularCotangentFirstCoefficients (K := K) n hn) := by
  have hz : ∀ z, rectangularCotangentFirstCoefficients (K := K) n hn z = 0 → z = 0 := by
    intro z hz
    obtain ⟨f, rfl⟩ := (rectangularAugmentationIdeal (K := K) n hn).toCotangent_surjective z
    apply ((rectangularAugmentationIdeal (K := K) n hn).toCotangent_eq_zero f).mpr
    exact rectangular_mem_square_of_first_zero n hn f.val f.property hz
  intro x y h
  apply sub_eq_zero.mp
  apply hz
  rw [map_sub, h, sub_self]

end PiExponentApprox.TransverseMultiplicity

end

end OAI
end Source0115

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalKernel.lean
section Source0116
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeNormalKernel.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

variable {C ι : Type*} [Field C] [Fintype ι]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

theorem primeLocalDirectional_polynomial (v : ι → Q.ResidueField) (p : MvPolynomial ι C) :
    primeLocalDirectional Q v
      (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) =
      ∑ i, v i * primeResidueMap Q (MvPolynomial.pderiv i p) := by
  calc
    _ = ∑ i, v i * primeLocalPartial Q i
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p) := by
      change (Derivation.coeFnAddMonoidHom (∑ i, v i • primeLocalPartial Q i)) _ = _
      rw [map_sum, Finset.sum_apply]
      rfl
    _ = _ := by simp only [primeLocalPartial_polynomial]; rfl

end PiExponent

end

end OAI
end Source0116

-- Source: OAI/NumberTheory/PiExponent/Jets/PrimeTaylorCotangent.lean
section Source0117
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PrimeTaylorCotangent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent

open PiExponentApprox.TransverseMultiplicity MvPowerSeries

variable {C ι σ : Type*} [Field C] [CharZero C] [Fintype ι]
variable [Fintype σ] [DecidableEq σ]
variable (Q : Ideal (MvPolynomial ι C)) [Q.IsPrime]

omit [Fintype ι] [Fintype σ] in
theorem primeRectangular_maps_maximal
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤
      (rectangularAugmentationIdeal (K := Q.ResidueField) n hn).comap
        (rectangularTaylorAlgHom n tau) := by
  apply rectangularTaylorAlgHom_maps_residueIdeal n (rectangularPositive n hn)
    tau (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero
  exact le_of_eq (IsLocalRing.ker_residue (R := Localization.AtPrime Q)).symm

theorem prime_rectangular_mapCotangent_surjective
    (tau : Localization.AtPrime Q →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ x, constantCoeff (tau x) = algebraMap (Localization.AtPrime Q) Q.ResidueField x)
    (v : σ → ι → Q.ResidueField)
    (hv : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ (v j)))
    (hfirst : ∀ j x, coeff (Finsupp.single j 1) (tau x) = primeLocalDirectional Q (v j) x)
    (n : σ → ℕ) (hn : ∀ i, 2 ≤ n i) :
    Function.Surjective
      (Ideal.mapCotangent (IsLocalRing.maximalIdeal (Localization.AtPrime Q))
        (rectangularAugmentationIdeal (K := Q.ResidueField) n hn)
        (rectangularTaylorAlgHom n tau) (primeRectangular_maps_maximal Q tau hzero n hn)) := by
  intro z
  obtain ⟨x, hx⟩ := prime_cotangent_evaluation_surjective Q v hv
    (rectangularCotangentFirstCoefficients n hn z)
  refine ⟨x, ?_⟩
  apply rectangularCotangentFirstCoefficients_injective n hn
  rw [← hx]
  obtain ⟨a, rfl⟩ :=
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).toCotangent_surjective x
  funext j
  rw [Ideal.mapCotangent_toCotangent, rectangularCotangentFirstCoefficients_toCotangent]
  change rectangularFirstCoefficients n hn
    (Ideal.Quotient.mk (rectangularIdeal (K := Q.ResidueField) n) (tau a.1)) j = _
  rw [rectangularFirstCoefficients_mk, hfirst]
  exact (primeNormalPairing_toCotangent Q (v j) a).symm

omit [CharZero C] [Fintype σ] [DecidableEq σ] in

theorem prime_localizedTaylor_firstCoefficient
    (tau : MvPolynomial ι C →+* MvPowerSeries σ Q.ResidueField)
    (hzero : ∀ p, constantCoeff (tau p) =
      algebraMap (Localization.AtPrime Q) Q.ResidueField
        (algebraMap (MvPolynomial ι C) (Localization.AtPrime Q) p))
    (v : σ → ι → Q.ResidueField)
    (hfirst : ∀ j p, coeff (Finsupp.single j 1) (tau p) =
      ∑ i, v j i * primeResidueMap Q (MvPolynomial.pderiv i p))
    (j : σ) (x : Localization.AtPrime Q) :
    coeff (Finsupp.single j 1)
      (localizedTaylorMap Q.primeCompl tau
        (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero x) =
      primeLocalDirectional Q (v j) x := by
  apply localizedTaylorMap_linearCoefficient Q.primeCompl tau
    (algebraMap (Localization.AtPrime Q) Q.ResidueField) hzero j
      (primeLocalDirectional Q (v j))
  · intro a b
    simp only [Derivation.leibniz, Algebra.smul_def]
  · intro p
    rw [hfirst, primeLocalDirectional_polynomial]

end PiExponent

end

end OAI
end Source0117

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeFrameMultiplicity.lean
section Source0118
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeFrameMultiplicity.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent

open scoped BigOperators
open PiExponentApprox PiExponentApprox.TransverseMultiplicity
open FrameTransverseMultiplicity NormalBasisRigidity

theorem prime_frame_rectangular_length_lower (m k : ℕ)
    (Q : Ideal (FramePolynomial m)) [Q.IsPrime]
    (hy : primeResidueMap Q (MvPolynomial.X (0 : Fin (m + 1))) ≠ 0)
    (B : Fin k → Fin (m + 1))
    (hB : LinearIndependent Q.ResidueField
      (fun j => (polynomialTangent (primeResidueMap Q) Q).mkQ
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))))
    (I : Ideal (FramePolynomial m)) (cost : Fin (m + 1) → ℝ)
    (n : Fin k → ℕ) (delta : ℝ) (hn : ∀ i, 2 ≤ n i)
    (hcost : ∀ i, 0 ≤ cost i)
    (hbudget : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ delta)
    (hvanish : ∀ p ∈ I, ∀ word : List (Fin (m + 1)),
      frameWordCost cost word ≤ delta → polynomialFrameWord m word p ∈ Q) :
    (∏ i, n i : ℕ) ≤
      Module.length (Localization.AtPrime Q)
        (Localization.AtPrime Q ⧸ I.map
          (algebraMap (FramePolynomial m) (Localization.AtPrime Q))) := by
  let rho := algebraMap (Localization.AtPrime Q) Q.ResidueField
  let tau := localizedFrameTaylor m k B Q.primeCompl rho
  have hzero : ∀ x, MvPowerSeries.constantCoeff (tau x) = rho x :=
    localizedFrameTaylor_constant m k B Q.primeCompl rho
  have hfirst : ∀ j x, MvPowerSeries.coeff (Finsupp.single j 1) (tau x) =
      primeLocalDirectional Q
        (frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j)) x := by
    intro j x
    apply prime_localizedTaylor_firstCoefficient Q
      (frameTaylor m k B rho) (frameTaylor_constant m k B rho)
      (fun j => frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j))
    intro l p
    rw [frameTaylor_firstCoefficient]
    dsimp only [rho]
    rw [← IsScalarTower.algebraMap_apply]
    exact residue_polynomialFrame_eq_frameBasis_dot m (primeResidueMap Q).toRingHom hy (B l) p
  have hCot := prime_rectangular_mapCotangent_surjective Q tau hzero
    (fun j => frameBasis m (primeResidueMap Q (MvPolynomial.X 0)) hy (B j)) hB hfirst n hn
  have hP : IsLocalRing.maximalIdeal (Localization.AtPrime Q) ≤ RingHom.ker rho := by
    rw [show RingHom.ker rho = IsLocalRing.maximalIdeal (Localization.AtPrime Q)
      from IsLocalRing.ker_residue]
  apply frame_rectangular_length_lower m k B Q.primeCompl rho
    IsLocalRing.residue_surjective (IsLocalRing.maximalIdeal (Localization.AtPrime Q)) hP
    I cost n delta (rectangularPositive n hn) hcost hbudget hCot
  intro p hp word hword
  dsimp only [rho]
  rw [← IsScalarTower.algebraMap_apply]
  exact Ideal.algebraMap_residueField_eq_zero.mpr (hvanish p hp word hword)

end PiExponent
end

end OAI
end Source0118

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLengthEquivalence.lean
section Source0119
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/QuotientLengthEquivalence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

theorem length_eq_of_semilinear_bijective
    {R S M N : Type*} [Ring R] [Ring S] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R →+* S) [RingHomSurjective σ]
    (f : M →ₛₗ[σ] N) (hf : Function.Bijective f) :
    Module.length R M = Module.length S N := by
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

theorem quotient_length_eq_of_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : J = I.map e.toRingHom) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ J) := by
  let eQ : R ⧸ I ≃+* S ⧸ J := Ideal.quotientEquiv I J e hIJ
  let f : (R ⧸ I) →ₛₗ[e.toRingHom] (S ⧸ J) :=
    { toFun := eQ
      map_add' := eQ.map_add
      map_smul' := by
        intro r x
        change eQ ((Ideal.Quotient.mk I r) * x) =
          Ideal.Quotient.mk J (e r) * eQ x
        rw [map_mul]
        change Ideal.quotientEquiv I J e hIJ (Ideal.Quotient.mk I r) * eQ x = _
        rfl }
  let : RingHomSurjective e.toRingHom := ⟨e.surjective⟩
  exact length_eq_of_semilinear_bijective e.toRingHom f eQ.bijective

end PiExponentJets.W22

end OAI
end Source0119

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedLengthEquivalence.lean
section Source0120
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizedLengthEquivalence.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentJets.W22

variable {R S : Type*} [CommRing R] [CommRing S]

theorem primeCompl_map_eq_of_comap
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    P.primeCompl.map e.toMonoidHom = Q.primeCompl := by
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    change e r ∉ Q
    intro h
    apply hr
    rw [hPQ]
    exact h
  · intro hx
    change x ∉ Q at hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    change e.symm x ∉ P
    rw [hPQ]
    change e (e.symm x) ∉ Q
    simpa only [e.apply_symm_apply] using hx

noncomputable def primeLocalizationEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) :
    Localization.AtPrime P ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime P) (Localization.AtPrime Q)
    e (primeCompl_map_eq_of_comap e P Q hPQ)

theorem primeLocalizationEquiv_map_ideal
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    (I.map (algebraMap R (Localization.AtPrime P))).map
      (primeLocalizationEquiv e P Q hPQ).toRingHom =
    (I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)) := by
  rw [Ideal.map_map, Ideal.map_map]
  congr 1
  ext r
  exact IsLocalization.ringEquivOfRingEquiv_eq
    (primeCompl_map_eq_of_comap e P Q hPQ) r

theorem localized_quotient_length_eq_of_ringEquiv
    (e : R ≃+* S) (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]
    (hPQ : P = Q.comap e.toRingHom) (I : Ideal R) :
    Module.length (Localization.AtPrime P)
      (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P))) =
    Module.length (Localization.AtPrime Q)
      (Localization.AtPrime Q ⧸ (I.map e.toRingHom).map
        (algebraMap S (Localization.AtPrime Q))) :=
  quotient_length_eq_of_ringEquiv (primeLocalizationEquiv e P Q hPQ)
    (I.map (algebraMap R (Localization.AtPrime P)))
    ((I.map e.toRingHom).map (algebraMap S (Localization.AtPrime Q)))
    (primeLocalizationEquiv_map_ideal e P Q hPQ I).symm

end PiExponentJets.W22

end OAI
end Source0120

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizationQuotientParameters.lean
section Source0121
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalizationQuotientParameters.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentSiegel.W23

variable {A : Type*} [CommRing A]

def quotientParameterPrime (I m : Ideal A) (_hI : I ≤ m) : Ideal (A ⧸ I) :=
  m.map (Ideal.Quotient.mk I)

instance quotientParameterPrime_isPrime (I m : Ideal A) [m.IsPrime] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsPrime :=
  Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk I) (I := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

instance quotientParameterPrime_isMaximal (I m : Ideal A) [m.IsMaximal] (hI : I ≤ m) :
    (quotientParameterPrime I m hI).IsMaximal :=
  Ideal.IsMaximal.map_of_surjective_of_ker_le (f := Ideal.Quotient.mk I) (m := m)
    Ideal.Quotient.mk_surjective
    (by simpa only [Ideal.mk_ker] using hI)

@[simp] theorem mem_quotientParameterPrime_mk (I m : Ideal A) (hI : I ≤ m) (a : A) :
    Ideal.Quotient.mk I a ∈ quotientParameterPrime I m hI ↔ a ∈ m :=
  Ideal.mem_quotient_iff_mem hI

def parameterLocalizedIdeal (I m : Ideal A) [m.IsPrime] :
    Ideal (Localization.AtPrime m) :=
  I.map (algebraMap A (Localization.AtPrime m))

variable (I m : Ideal A) [m.IsPrime] (hI : I ≤ m)

def parameterLocalizationMap :
    Localization.AtPrime m →+* Localization.AtPrime (quotientParameterPrime I m hI) :=
  IsLocalization.map (Localization.AtPrime (quotientParameterPrime I m hI))
    (Ideal.Quotient.mk I) (M := m.primeCompl)
    (S := Localization.AtPrime m)
    (T := (quotientParameterPrime I m hI).primeCompl) (by
      intro a ha
      change Ideal.Quotient.mk I a ∉ quotientParameterPrime I m hI
      exact fun h => ha ((mem_quotientParameterPrime_mk I m hI a).mp h))

@[simp] theorem parameterLocalizationMap_algebraMap (a : A) :
    parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) =
      algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
        (Ideal.Quotient.mk I a) :=
  IsLocalization.map_eq _ a

theorem parameterLocalizedIdeal_le_ker :
    parameterLocalizedIdeal I m ≤ RingHom.ker (parameterLocalizationMap I m hI) := by
  rw [parameterLocalizedIdeal, Ideal.map_le_iff_le_comap]
  intro a ha
  change parameterLocalizationMap I m hI (algebraMap A (Localization.AtPrime m) a) = 0
  rw [parameterLocalizationMap_algebraMap,
    (Ideal.Quotient.eq_zero_iff_mem).mpr ha, map_zero]

def parameterLocalQuotientForward :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) →+*
      Localization.AtPrime (quotientParameterPrime I m hI) :=
  Ideal.Quotient.lift _ (parameterLocalizationMap I m hI)
    (fun x hx => (RingHom.mem_ker (f := parameterLocalizationMap I m hI) (r := x)).mp
      (parameterLocalizedIdeal_le_ker I m hI hx))

@[simp] theorem parameterLocalQuotientForward_mk (x : Localization.AtPrime m) :
    parameterLocalQuotientForward I m hI (Ideal.Quotient.mk _ x) =
      parameterLocalizationMap I m hI x := rfl

def parameterQuotientToLocalQuotient :
    (A ⧸ I) →+* (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  Ideal.Quotient.lift I
    ((Ideal.Quotient.mk (parameterLocalizedIdeal I m)).comp
      (algebraMap A (Localization.AtPrime m)))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))

@[simp] theorem parameterQuotientToLocalQuotient_mk (a : A) :
    parameterQuotientToLocalQuotient I m (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (parameterLocalizedIdeal I m)
        (algebraMap A (Localization.AtPrime m) a) := rfl

theorem parameterQuotientToLocalQuotient_units
    (s : (quotientParameterPrime I m hI).primeCompl) :
    IsUnit (parameterQuotientToLocalQuotient I m (s : A ⧸ I)) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (s : A ⧸ I)
  have ham : a ∉ m := by
    intro ham
    apply s.property
    change (s : A ⧸ I) ∈ m.map (Ideal.Quotient.mk I)
    rw [← ha]
    exact Ideal.mem_map_of_mem _ ham
  rw [← ha, parameterQuotientToLocalQuotient_mk]
  exact (IsLocalization.map_units (Localization.AtPrime m) (⟨a, ham⟩ : m.primeCompl)).map
    (Ideal.Quotient.mk (parameterLocalizedIdeal I m))

def parameterLocalQuotientReverse :
    Localization.AtPrime (quotientParameterPrime I m hI) →+*
      (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  IsLocalization.lift (M := (quotientParameterPrime I m hI).primeCompl)
    (S := Localization.AtPrime (quotientParameterPrime I m hI))
    (parameterQuotientToLocalQuotient_units I m hI)

@[simp] theorem parameterLocalQuotientReverse_algebraMap (x : A ⧸ I) :
    parameterLocalQuotientReverse I m hI
      (algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI)) x) =
      parameterQuotientToLocalQuotient I m x :=
  IsLocalization.lift_eq _ x

theorem parameterLocalQuotient_reverse_forward :
    (parameterLocalQuotientReverse I m hI).comp (parameterLocalQuotientForward I m hI) =
      RingHom.id (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) := by
  apply Ideal.Quotient.ringHom_ext
  apply IsLocalization.ringHom_ext m.primeCompl
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk]

theorem parameterLocalQuotient_forward_reverse :
    (parameterLocalQuotientForward I m hI).comp (parameterLocalQuotientReverse I m hI) =
      RingHom.id (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  apply IsLocalization.ringHom_ext (quotientParameterPrime I m hI).primeCompl
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro a
  simp only [RingHom.comp_apply, RingHom.id_apply, parameterLocalQuotientReverse_algebraMap,
    parameterQuotientToLocalQuotient_mk, parameterLocalQuotientForward_mk,
    parameterLocalizationMap_algebraMap]

def localizationQuotientParametersEquiv :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime (quotientParameterPrime I m hI) where
  toFun := parameterLocalQuotientForward I m hI
  invFun := parameterLocalQuotientReverse I m hI
  left_inv x := RingHom.congr_fun (parameterLocalQuotient_reverse_forward I m hI) x
  right_inv x := RingHom.congr_fun (parameterLocalQuotient_forward_reverse I m hI) x
  map_mul' := (parameterLocalQuotientForward I m hI).map_mul
  map_add' := (parameterLocalQuotientForward I m hI).map_add

@[simp] theorem localizationQuotientParametersEquiv_mk_algebraMap (a : A) :
    localizationQuotientParametersEquiv I m hI
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
    algebraMap (A ⧸ I) (Localization.AtPrime (quotientParameterPrime I m hI))
      (Ideal.Quotient.mk I a) :=
  parameterLocalizationMap_algebraMap I m hI a

include hI in

theorem parameterLocalQuotient_isLocalRing :
    IsLocalRing (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) :=
  (localizationQuotientParametersEquiv I m hI).symm.isLocalRing

def localizationQuotientParametersResidueEquiv :
    letI := parameterLocalQuotient_isLocalRing I m hI
    IsLocalRing.ResidueField (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      IsLocalRing.ResidueField (Localization.AtPrime (quotientParameterPrime I m hI)) := by
  letI := parameterLocalQuotient_isLocalRing I m hI
  exact IsLocalRing.ResidueField.mapEquiv (localizationQuotientParametersEquiv I m hI)

variable {B : Type*} [CommRing B]

local instance parameterEquivImage_isPrime (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

theorem atPrimeImage_comap (e : A ≃+* B) (P : Ideal A) :
    P = (P.map e.toRingHom).comap e.toRingHom := by
  ext a
  change a ∈ P ↔ e a ∈ P.map e.toRingHom
  exact Ideal.apply_mem_of_equiv_iff.symm

def atPrimeEquivOfRingEquiv (e : A ≃+* B) (P : Ideal A) [P.IsPrime] :
    Localization.AtPrime P ≃+* Localization.AtPrime (P.map e.toRingHom) :=
  PiExponentJets.W22.primeLocalizationEquiv e P (P.map e.toRingHom)
    (atPrimeImage_comap e P)

@[simp] theorem atPrimeEquivOfRingEquiv_algebraMap
    (e : A ≃+* B) (P : Ideal A) [P.IsPrime] (a : A) :
    atPrimeEquivOfRingEquiv e P (algebraMap A (Localization.AtPrime P) a) =
      algebraMap B (Localization.AtPrime (P.map e.toRingHom)) (e a) :=
  IsLocalization.ringEquivOfRingEquiv_eq
    (PiExponentJets.W22.primeCompl_map_eq_of_comap e P (P.map e.toRingHom)
      (atPrimeImage_comap e P)) a

def localizationQuotientParametersEquivTrans (e : (A ⧸ I) ≃+* B) :
    (Localization.AtPrime m ⧸ parameterLocalizedIdeal I m) ≃+*
      Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom) :=
  (localizationQuotientParametersEquiv I m hI).trans
    (atPrimeEquivOfRingEquiv e (quotientParameterPrime I m hI))

@[simp] theorem localizationQuotientParametersEquivTrans_mk_algebraMap
    (e : (A ⧸ I) ≃+* B) (a : A) :
    localizationQuotientParametersEquivTrans I m hI e
      (Ideal.Quotient.mk _ (algebraMap A (Localization.AtPrime m) a)) =
      algebraMap B
        (Localization.AtPrime ((quotientParameterPrime I m hI).map e.toRingHom))
        (e (Ideal.Quotient.mk I a)) := by
  simp only [localizationQuotientParametersEquivTrans, RingEquiv.trans_apply,
    localizationQuotientParametersEquiv_mk_algebraMap, atPrimeEquivOfRingEquiv_algebraMap]

end PiExponentSiegel.W23

end

end OAI
end Source0121

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeResidueAlgebraEquiv.lean
section Source0122
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/PrimeResidueAlgebraEquiv.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponentJets.PolynomialLocalResidueResolution

variable {K R S : Type*} [CommRing K] [CommRing R] [CommRing S]
variable [Algebra K R] [Algebra K S]
variable (e : R ≃ₐ[K] S) (P : Ideal R) [P.IsPrime]

instance primeResidueImage_isPrime : (P.map e.toRingHom).IsPrime :=
  Ideal.map_isPrime_of_equiv e

def primeResidueRingEquiv : P.ResidueField ≃+* (P.map e.toRingHom).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P)

@[simp] theorem primeResidueRingEquiv_algebraMap (r : R) :
    primeResidueRingEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) := by
  change IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv e.toRingEquiv P
        (algebraMap R (Localization.AtPrime P) r)) =
    IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom))
      (algebraMap S (Localization.AtPrime (P.map e.toRingHom)) (e r))
  exact congrArg (IsLocalRing.residue (Localization.AtPrime (P.map e.toRingHom)))
    (PiExponentSiegel.W23.atPrimeEquivOfRingEquiv_algebraMap e.toRingEquiv P r)

def primeResidueAlgEquiv : P.ResidueField ≃ₐ[K] (P.map e.toRingHom).ResidueField where
  __ := primeResidueRingEquiv e P
  commutes' a := by
    change primeResidueRingEquiv e P (algebraMap K P.ResidueField a) = _
    rw [IsScalarTower.algebraMap_apply K R P.ResidueField,
      primeResidueRingEquiv_algebraMap, e.commutes]
    exact (IsScalarTower.algebraMap_apply K S (P.map e.toRingHom).ResidueField a).symm

@[simp] theorem primeResidueAlgEquiv_algebraMap (r : R) :
    primeResidueAlgEquiv e P (algebraMap R P.ResidueField r) =
      algebraMap S (P.map e.toRingHom).ResidueField (e r) :=
  primeResidueRingEquiv_algebraMap e P r

theorem primeResidueAlgEquiv_transcendenceBasis {ι : Type*} (x : ι → P.ResidueField)
    (hx : IsTranscendenceBasis K x) :
    IsTranscendenceBasis K (fun i => primeResidueAlgEquiv e P (x i)) :=
  (primeResidueAlgEquiv e P).isTranscendenceBasis hx

end PiExponentJets.PolynomialLocalResidueResolution

end

end OAI
end Source0122

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateFiniteSlice.lean
section Source0123
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateFiniteSlice.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.CoordinateFiniteSlice

open PiExponentJets.PolynomialLocalResidueResolution

variable {K ι : Type*} [Field K]

def coordinateEquiv (A : Finset ι) :
    Fin A.card ⊕ {i // i ∉ A} ≃ ι := by
  classical
  exact (Equiv.sumCongr A.equivFin.symm (Equiv.refl _)).trans (Equiv.sumCompl (· ∈ A))

@[simp] theorem coordinateEquiv_inl (A : Finset ι) (i : Fin A.card) :
    coordinateEquiv A (Sum.inl i) = (A.equivFin.symm i).val := rfl

@[simp] theorem coordinateEquiv_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateEquiv A (Sum.inr i) = i.val := rfl

def coordinateRenaming (A : Finset ι) :
    MvPolynomial ι K ≃ₐ[K] MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K :=
  MvPolynomial.renameEquiv K (coordinateEquiv A).symm

@[simp] theorem coordinateRenaming_X_inl (A : Finset ι) (i : Fin A.card) :
    coordinateRenaming (K := K) A (MvPolynomial.X (A.equivFin.symm i).val) =
      MvPolynomial.X (Sum.inl i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inl i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

@[simp] theorem coordinateRenaming_X_inr (A : Finset ι) (i : {i // i ∉ A}) :
    coordinateRenaming (K := K) A (MvPolynomial.X i.val) =
      MvPolynomial.X (Sum.inr i) := by
  change MvPolynomial.rename (coordinateEquiv A).symm
    (MvPolynomial.X (coordinateEquiv A (Sum.inr i))) = _
  rw [MvPolynomial.rename_X, Equiv.symm_apply_apply]

abbrev splitPrime (Q : Ideal (MvPolynomial ι K)) (A : Finset ι) :
    Ideal (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) :=
  Q.map (coordinateRenaming (K := K) A).toRingHom

instance splitPrime_isPrime (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    (splitPrime Q A).IsPrime := Ideal.map_isPrime_of_equiv (coordinateRenaming A)

def residueEquiv (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) :
    Q.ResidueField ≃ₐ[K] (splitPrime Q A).ResidueField :=
  primeResidueAlgEquiv (coordinateRenaming A) Q

@[simp] theorem residueEquiv_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X (A.equivFin.symm i).val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inl] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q
      (MvPolynomial.X (A.equivFin.symm i).val)

@[simp] theorem residueEquiv_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    residueEquiv Q A
      (algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val)) =
    algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i)) := by
  simpa only [residueEquiv, splitPrime, coordinateRenaming_X_inr] using
    primeResidueAlgEquiv_algebraMap (coordinateRenaming (K := K) A) Q (MvPolynomial.X i.val)

theorem complementary_transcendenceBasis
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hB : IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i.val))) :
    IsTranscendenceBasis K (fun i : {i // i ∉ A} =>
      algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) := by
  simpa only [Function.comp_def, residueEquiv_coordinate_inr] using (residueEquiv Q A).isTranscendenceBasis hB

theorem splitPrime_mem_minimalPrimes
    (Q I : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (hQ : Q ∈ I.minimalPrimes) :
    splitPrime Q A ∈ (I.map (coordinateRenaming (K := K) A).toRingHom).minimalPrimes := by
  rw [Ideal.minimalPrimes_map_of_surjective (f := (coordinateRenaming (K := K) A).toRingHom)
    (coordinateRenaming (K := K) A).surjective]
  have hk : RingHom.ker (coordinateRenaming (K := K) A).toRingHom = ⊥ := by
    ext p
    change coordinateRenaming (K := K) A p = 0 ↔ p = 0
    exact (coordinateRenaming (K := K) A).map_eq_zero_iff
  rw [hk, sup_bot_eq]
  exact ⟨Q, hQ, rfl⟩

def residueCoordinates (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (i : ι) : Q.ResidueField :=
  algebraMap (MvPolynomial ι K) Q.ResidueField (MvPolynomial.X i)

def slicePoint (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι)
    (i : Fin A.card) : Q.ResidueField := residueCoordinates Q (A.equivFin.symm i)

@[simp] theorem enumeratedSliceMap_X_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X (A.equivFin.symm i).val) = MvPolynomial.X i := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_mem (C := K) A (residueCoordinates Q)
      (A.equivFin.symm i).val (A.equivFin.symm i).property]

@[simp] theorem enumeratedSliceMap_X_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    WeightedSliceDegree.enumeratedSliceMap (C := K) A (residueCoordinates Q)
      (MvPolynomial.X i.val) = MvPolynomial.C (residueCoordinates Q i.val) := by
  simp [WeightedSliceDegree.enumeratedSliceMap,
    WeightedSliceDegree.sliceMap_X_notMem (C := K) A (residueCoordinates Q) i.val i.property]

theorem residueEquiv_symm_coordinate_inl
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : Fin A.card) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inl i))) =
      slicePoint Q A i := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inl Q A i).symm

theorem residueEquiv_symm_coordinate_inr
    (Q : Ideal (MvPolynomial ι K)) [Q.IsPrime] (A : Finset ι) (i : {i // i ∉ A}) :
    (residueEquiv Q A).symm
      (algebraMap (MvPolynomial (Fin A.card ⊕ {i // i ∉ A}) K) (splitPrime Q A).ResidueField (MvPolynomial.X (Sum.inr i))) =
      residueCoordinates Q i.val := by
  apply (residueEquiv Q A).injective
  rw [AlgEquiv.apply_symm_apply]
  exact (residueEquiv_coordinate_inr Q A i).symm

end PiExponent.CoordinateFiniteSlice

end

end OAI
end Source0123

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/LocalLengthTransport.lean
section Source0124
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/LocalLengthTransport.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.LocalLengthTransport

abbrev localLength {R : Type*} [CommRing R]
    (P : Ideal R) [P.IsPrime] (I : Ideal R) : ℕ∞ :=
  Module.length (Localization.AtPrime P)
    (Localization.AtPrime P ⧸ I.map (algebraMap R (Localization.AtPrime P)))

variable {R S : Type*} [CommRing R] [CommRing S]
variable (P : Ideal R) (Q : Ideal S) [P.IsPrime] [Q.IsPrime]

theorem localLength_eq_of_localizedIdeal_map
    (e : Localization.AtPrime P ≃+* Localization.AtPrime Q)
    (I : Ideal R) (J : Ideal S)
    (hIJ : (I.map (algebraMap R (Localization.AtPrime P))).map e.toRingHom =
      J.map (algebraMap S (Localization.AtPrime Q))) :
    localLength P I = localLength Q J :=
  PiExponentJets.W22.quotient_length_eq_of_ringEquiv e _ _ hIJ.symm

end PiExponent.LocalLengthTransport

end

end OAI
end Source0124
