/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt jet-ideal radical, support and packet-vanishing arguments using inverse Y-scaling.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import LogTwo.Geometry.JetTruncation
public import LogTwo.Geometry.NormalizedContact
public import LogTwo.Geometry.Centers
public import OAI.NumberTheory.PiExponent.Jets.CompactJetPolynomial

@[expose] public section

/-! Polynomial jet ideals at varying Y-centers. Their powers annihilate full
formal packets; their radicals and support are the actual matrix centers.
These facts do not assert bounded-degree interpolation surjectivity. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox MvPolynomial
open CompactJetPolynomial JetGeometry
noncomputable section

variable {m : ℕ}

theorem scaleY_comp (y z : ℂ) :
    (scaleY (m := m) y).comp (scaleY z) = scaleY (y * z) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [mul_comm, mul_left_comm]
  | succ i => simp

@[simp] theorem scaleY_one : scaleY (m := m) 1 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp

def scaleYEquiv (y : ℂ) (hy : y ≠ 0) : FramePolynomial m ≃ₐ[ℂ] FramePolynomial m :=
  AlgEquiv.ofAlgHom (scaleY y) (scaleY y⁻¹)
    (by rw [scaleY_comp, mul_inv_cancel₀ hy, scaleY_one])
    (by rw [scaleY_comp, inv_mul_cancel₀ hy, scaleY_one])

theorem aeval_comp_scaleY {A : Type*} [CommRing A] [Algebra ℂ A]
    (y : ℂ) (z : Fin (m+1) → A) :
    (MvPolynomial.aeval z).comp (scaleY y) =
      MvPolynomial.aeval (Fin.cases (algebraMap ℂ A y * z 0) (fun i => z i.succ)) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases <;> simp

def jetIdealAt (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    Ideal (FramePolynomial m) :=
  (powerIdeal c (logPolynomials T) e).comap (scaleY y).toRingHom

theorem jetIdealAt_eq_map_inverse (y : ℂ) (hy : y ≠ 0)
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    jetIdealAt y c T e =
      (powerIdeal c (logPolynomials T) e).map (scaleY y⁻¹).toRingHom := by
  exact (Ideal.map_comap_of_equiv (scaleYEquiv (m := m) y hy).symm.toRingEquiv).symm

theorem radical_jetIdealAt (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (jetIdealAt y c T e).radical = WeightedBezout.pointIdeal (centerPoint y c) := by
  rw [jetIdealAt, ← Ideal.comap_radical,
    radical_powerIdeal c (logPolynomials T) (logPolynomials_eval_zero T) e he]
  ext P
  change MvPolynomial.aeval (center c) (scaleY y P) = 0 ↔
    MvPolynomial.aeval (centerPoint y c) P = 0
  rw [← AlgHom.comp_apply, aeval_comp_scaleY]
  simp only [center, Fin.cases_zero, Fin.cases_succ, Algebra.algebraMap_self, mul_one]
  rfl

def centerPrime (y : ℂ) (c : Fin m → ℂ) : PrimeSpectrum (FramePolynomial m) :=
  ⟨WeightedBezout.pointIdeal (centerPoint y c), inferInstance⟩

theorem zeroLocus_jetIdealAt (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (jetIdealAt y c T e : Set _) = {centerPrime y c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_jetIdealAt y c T e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem centerPrime_injective_of_Y {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ) :
    Function.Injective (fun j => centerPrime (y j) (c j)) := by
  intro j k h
  apply hy
  have hi := congrArg PrimeSpectrum.asIdeal h
  have hm : X 0 - C (y j) ∈ WeightedBezout.pointIdeal (centerPoint (y j) (c j)) := by
    simp [centerPoint]
  change WeightedBezout.pointIdeal (centerPoint (y j) (c j)) =
    WeightedBezout.pointIdeal (centerPoint (y k) (c k)) at hi
  rw [hi] at hm
  have hz : y k - y j = 0 := by simpa [centerPoint] using hm
  exact (sub_eq_zero.mp hz).symm

theorem logTwo_centerPrime_injective (K : ℕ) (r : Fin m → ℚ) :
    Function.Injective (fun j : Fin K =>
      centerPrime ((2 : ℂ)^j.val) (fun i => (j.val : ℂ) * (r i : ℂ))) :=
  centerPrime_injective_of_Y _ (complex_centerY_injective.comp Fin.val_injective) _

def jetProductIdeal {J : Type*} [Fintype J] (y : J → ℂ) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (FramePolynomial m) :=
  ∏ j, jetIdealAt (y j) (c j) T e

theorem zeroLocus_finset_prod_jetIdealAt {J : Type*} (s : Finset J)
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus
      (((∏ j ∈ s, jetIdealAt (y j) (c j) T e) : Ideal (FramePolynomial m)) : Set _) =
      (fun j => centerPrime (y j) (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_jetIdealAt (y j) (c j) T e he, ih]
    simp

theorem zeroLocus_jetProductIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (jetProductIdeal y c T e : Set _) =
      Set.range (fun j => centerPrime (y j) (c j)) := by
  simpa [jetProductIdeal] using zeroLocus_finset_prod_jetIdealAt Finset.univ y c T e he

theorem formalJetAt_mem_weighted_of_mem_pow (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : FramePolynomial m) (hP : P ∈ jetIdealAt y c T e ^ n) :
    formalJetAt y c P ∈ rationalWeightedIdeal v hv (n * R) := by
  exact formalJet_mem_weighted_of_mem_pow c T e v hv hT R he n (scaleY y P)
    (Ideal.le_comap_pow (scaleY y).toRingHom n hP)

theorem jetProductIdeal_pow_le {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (n : ℕ) (j : J) :
    jetProductIdeal y c T e ^ n ≤ jetIdealAt (y j) (c j) T e ^ n := by
  classical
  apply pow_le_pow_left'
  exact Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))

theorem formalJetAt_packet_zero_of_mem_product_pow {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : FramePolynomial m) (hP : P ∈ jetProductIdeal y c T e ^ n) (j : J) :
    rationalCoefficientPacket v (n * R) (formalJetAt (y j) (c j) P) =
      (fun _ => (0 : ℂ)) := by
  funext d
  exact formalJetAt_mem_weighted_of_mem_pow (y j) (c j) T e v hv hT R he n P
    (jetProductIdeal_pow_le y c T e n j hP) d.val d.property

theorem map_jetIdealAt_aeval {A : Type*} [CommRing A] [Algebra ℂ A]
    (y : ℂ) (hy : y ≠ 0) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (z : Fin (m+1) → A) :
    (jetIdealAt y c T e).map (MvPolynomial.aeval z).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c
        (algebraMap ℂ A y⁻¹ * z 0) (fun i => z i.succ) T e := by
  rw [jetIdealAt_eq_map_inverse y hy, Ideal.map_map]
  change (powerIdeal c (logPolynomials T) e).map
    ((MvPolynomial.aeval z).comp (scaleY y⁻¹)).toRingHom = _
  rw [aeval_comp_scaleY]
  exact map_powerIdeal_aeval c T e _ _

end
end LogTwo.Geometry
