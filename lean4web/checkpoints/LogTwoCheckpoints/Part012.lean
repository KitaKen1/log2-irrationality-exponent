/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import LogTwoCheckpoints.Part002
public import LogTwoCheckpoints.Part005
public import LogTwoCheckpoints.Part011
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.FiveLemma
public import Mathlib.Algebra.GroupWithZero.Action.Regular
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Data.Opposite
public import Mathlib.Data.SetLike.Basic
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.MayerVietoris
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Analysis/FormalLogTailOrder.lean
section Source0300
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/FormalLogTailOrder.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalLogTruncation

theorem logTail_order_ge (T : ℕ) : (T : ℕ∞) ≤ (logTail T).order :=
  PowerSeries.nat_le_order (logTail T) T (coeff_logTail_eq_zero T)

theorem composed_logTail_order_ge (T : ℕ) (t : PowerSeries ℂ)
    (ht : PowerSeries.constantCoeff t = 0) :
    (T : ℕ∞) * t.order ≤ PowerSeries.order (PowerSeries.subst t (logTail T)) := by
  calc
    (T : ℕ∞) * t.order = MvPowerSeries.order t * T := by
      rw [PowerSeries.order_eq_order, mul_comm]
    _ ≤ MvPowerSeries.order t * (logTail T).order :=
      mul_le_mul_right (logTail_order_ge T) _
    _ ≤ MvPowerSeries.order (PowerSeries.subst t (logTail T)) :=
      PowerSeries.le_order_subst t (PowerSeries.HasSubst.of_constantCoeff_zero' ht) _
    _ = PowerSeries.order (PowerSeries.subst t (logTail T)) := PowerSeries.order_eq_order.symm

theorem composed_logTail_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (i : Fin m) (k : ℕ)
    (hk : PowerSeries.order (PowerSeries.subst (a 0) (logTail (T i))) = (k : ℕ∞)) :
    BranchContact.contact v a hne * v i.succ < (k : ℚ) := by
  have hTi : 0 < T i := by
    by_contra h
    have hz : T i = 0 := by omega
    have hh := hT i
    rw [hz, Nat.cast_zero, zero_mul] at hh
    exact (not_lt_of_ge (hv i.succ).le) hh
  have hb := composed_logTail_order_ge (T i) (a 0) (ha 0)
  rw [hk] at hb
  have hfinite : (a 0).order ≠ ⊤ := by
    intro htop
    have hTi0 : (T i : ℕ∞) ≠ 0 := by exact_mod_cast hTi.ne'
    simp only [htop, ENat.mul_top hTi0] at hb
    simp at hb
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  rw [← hn] at hb
  have hnat : T i * n ≤ k := by exact_mod_cast hb
  have hcontact := BranchContact.contact_bound v hv a hne 0 n hn.symm
  have hμ := BranchContact.contact_pos v hv a hne ha
  calc
    BranchContact.contact v a hne * v i.succ <
        BranchContact.contact v a hne * ((T i : ℚ) * v 0) :=
      mul_lt_mul_of_pos_left (hT i) hμ
    _ = (T i : ℚ) * (BranchContact.contact v a hne * v 0) := by ring
    _ ≤ (T i : ℚ) * (n : ℚ) := mul_le_mul_of_nonneg_left hcontact (by positivity)
    _ ≤ (k : ℚ) := by exact_mod_cast hnat

end PiExponent.FormalBranchContact

end

end OAI
end Source0300

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalBranchCoordinates.lean
section Source0301
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchCoordinates.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation FormalLogTruncation

def composedLogTails {m : ℕ} (a : Fin (m+1) → PowerSeries ℂ) (T : Fin m → ℕ) :
    Fin (m+1) → PowerSeries ℂ :=
  Fin.cases 0 (fun i => PowerSeries.subst (a 0) (logTail (T i)))

def truncatedBranchCoordinates {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (T : Fin m → ℕ) : Fin (m+1) → PowerSeries ℂ :=
  Fin.cases (y-1) (fun i => x i - PowerSeries.C (c i) -
    PowerSeries.subst (y-1)
      (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ))

theorem branchCoordinates_constantCoeff {m : ℕ} (c : Fin m → ℂ) (y : PowerSeries ℂ)
    (x : Fin m → PowerSeries ℂ) (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (branchCoordinates c y x i) = 0 := by
  intro i
  have hh := (branchCoordinates_hasSubst c y x hy hx).const_coeff i
  have hz := isNilpotent_iff_eq_zero.mp hh
  simpa only [PowerSeries.constantCoeff_eq] using hz

theorem truncatedBranchCoordinates_eq_add_tail {m : ℕ}
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (T : Fin m → ℕ) (hy : PowerSeries.constantCoeff y = 1) :
    truncatedBranchCoordinates c y x T =
      fun i => branchCoordinates c y x i + composedLogTails (branchCoordinates c y x) T i := by
  have ht : PowerSeries.constantCoeff (y-1) = 0 := by simp [hy]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedBranchCoordinates, branchCoordinates, composedLogTails]
  | succ i =>
    simp only [truncatedBranchCoordinates, branchCoordinates, composedLogTails,
      Fin.cases_succ, Fin.cases_zero, logTail, PowerSeries.subst_sub hs]
    ring

end PiExponent.FormalBranchContact

end

end OAI
end Source0301

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalBranchContact.lean
section Source0302
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalBranchContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalBranchContact

open FormalBranchEvaluation

theorem composedLogTails_strict_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (a : Fin (m+1) → PowerSeries ℂ) (hne : ∃ i, a i ≠ 0)
    (ha : ∀ i, PowerSeries.constantCoeff (a i) = 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∀ i (k : ℕ), (composedLogTails a T i).order = (k : ℕ∞) →
      BranchContact.contact v a hne * v i < (k : ℚ) := by
  intro i k hk
  cases i using Fin.cases with
  | zero => simp [composedLogTails] at hk
  | succ i => exact composed_logTail_strict_contact v hv a hne ha T hT i k hk

theorem truncatedBranchCoordinates_not_all_zero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedBranchCoordinates c y x T i ≠ 0 := by
  rw [truncatedBranchCoordinates_eq_add_tail c y x T hy]
  exact BranchContact.add_not_all_zero v hv _ _ hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)

theorem contact_truncatedBranchCoordinates_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : PowerSeries ℂ) (x : Fin m → PowerSeries ℂ)
    (hy : PowerSeries.constantCoeff y = 1)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (hne : ∃ i, branchCoordinates c y x i ≠ 0)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContact.contact v (truncatedBranchCoordinates c y x T)
      (truncatedBranchCoordinates_not_all_zero v hv c y x hy hx hne T hT) =
        BranchContact.contact v (branchCoordinates c y x) hne := by
  have hh := BranchContact.contact_add_high_tail v hv
    (branchCoordinates c y x) (composedLogTails (branchCoordinates c y x) T) hne
    (composedLogTails_strict_contact v hv _ hne
      (branchCoordinates_constantCoeff c y x hy hx) T hT)
  simpa only [← truncatedBranchCoordinates_eq_add_tail c y x T hy] using hh

end PiExponent.FormalBranchContact

end

end OAI
end Source0302

-- Source: OAI/NumberTheory/PiExponent/Analysis/LogarithmicContactIdeal.lean
section Source0303
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Analysis/LogarithmicContactIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.LogarithmicContactIdeal

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

def truncatedCoordinates {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) : Fin (m+1) → A :=
  Fin.cases (y-1) (fun i => x i - algebraMap ℂ A (c i) -
    Polynomial.aeval (y-1) (PowerSeries.trunc (T i) (PowerSeries.log ℂ)))

def logarithmicIdeal {m : ℕ} (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal A :=
  BranchContactIdeal.powerIdeal (truncatedCoordinates c y x T) e

theorem expansion_polynomial_aeval (z : A) (p : Polynomial ℂ) :
    DVRBranch.expansion ℂ A (Polynomial.aeval z p) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) p := by
  have hh : (DVRBranch.expansion ℂ A).comp (Polynomial.aeval z) =
      Polynomial.aeval (DVRBranch.expansion ℂ A z) := by
    apply Polynomial.algHom_ext
    simp
  exact AlgHom.congr_fun hh p

theorem expansion_truncatedCoordinates {m : ℕ}
    (c : Fin m → ℂ) (y : A) (x : Fin m → A) (T : Fin m → ℕ)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1) :
    (fun i => DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i)) =
      FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
        (fun i => DVRBranch.expansion ℂ A (x i)) T := by
  have ht : PowerSeries.constantCoeff (DVRBranch.expansion ℂ A y - 1) = 0 := by
    simp [hy]
  have hs := PowerSeries.HasSubst.of_constantCoeff_zero' ht
  funext i
  cases i using Fin.cases with
  | zero => simp [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates]
  | succ i =>
    simp only [truncatedCoordinates, FormalBranchContact.truncatedBranchCoordinates,
      Fin.cases_succ, map_sub, map_one, AlgHom.commutes, expansion_polynomial_aeval]
    rw [PowerSeries.subst_coe hs]
    rfl

theorem truncatedCoordinates_nonzero {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    ∃ i, truncatedCoordinates c y x T i ≠ 0 := by
  have hn := FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c
    (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
    (by simpa using hy) (fun i => by simpa using hx i)
    (DVRBranchJet.coordinates_nonzero c y x hnc) T hT
  rw [← expansion_truncatedCoordinates c y x T hy] at hn
  obtain ⟨i, hi⟩ := hn
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  change DVRBranch.expansion ℂ A (truncatedCoordinates c y x T i) = 0
  rw [hz, map_zero]

theorem branchContact_congr {ι : Type*} [Fintype ι]
    (v : ι → ℚ) (a b : ι → PowerSeries ℂ)
    (ha : ∃ i, a i ≠ 0) (hb : ∃ i, b i ≠ 0) (hab : a = b) :
    BranchContact.contact v a ha = BranchContact.contact v b hb := by
  subst b
  rfl

theorem truncated_contact_eq {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0) :
    BranchContactIdeal.contact v (truncatedCoordinates c y x T)
      (truncatedCoordinates_nonzero v hv c y x hy hx hnc T hT) =
        DVRBranchJet.contact v c y x hnc := by
  unfold BranchContactIdeal.contact DVRBranchJet.contact
  trans BranchContact.contact v
    (FormalBranchContact.truncatedBranchCoordinates c (DVRBranch.expansion ℂ A y)
      (fun i => DVRBranch.expansion ℂ A (x i)) T)
    (FormalBranchContact.truncatedBranchCoordinates_not_all_zero v hv c
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT)
  · apply branchContact_congr
    exact expansion_truncatedCoordinates c y x T hy
  · exact FormalBranchContact.contact_truncatedBranchCoordinates_eq v hv c
      (DVRBranch.expansion ℂ A y) (fun i => DVRBranch.expansion ℂ A (x i))
      (by simpa using hy) (fun i => by simpa using hx i)
      (DVRBranchJet.coordinates_nonzero c y x hnc) T hT

theorem logarithmicIdeal_colength_eq_contact {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length A (A ⧸ logarithmicIdeal c y x T e)).toNat : ℚ) =
      R * DVRBranchJet.contact v c y x hnc := by
  change ((Module.length A (A ⧸ BranchContactIdeal.powerIdeal
    (truncatedCoordinates c y x T) e)).toNat : ℚ) = _
  rw [BranchContactIdeal.colength_eq_contact v hv _
    (truncatedCoordinates_nonzero v hv c y x hy hx hnc T hT) R e he,
    truncated_contact_eq v hv c y x hy hx hnc T hT]

theorem logarithmicIdeal_colength_ne_top {m : ℕ}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin m → ℂ) (y : A) (x : Fin m → A)
    (hy : CurveLocalOrder.residueAugmentation ℂ A y = 1)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : y ≠ 1 ∨ ∃ i, x i ≠ algebraMap ℂ A (c i))
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    Module.length A (A ⧸ logarithmicIdeal c y x T e) ≠ ⊤ := by
  obtain ⟨i, hi, heq, _⟩ := BranchContactIdeal.exists_generator_colength_eq_contact
    v hv (truncatedCoordinates c y x T)
    (truncatedCoordinates_nonzero v hv c y x hy hx hnc T hT) R e he
  change Module.length A (A ⧸ BranchContactIdeal.powerIdeal
    (truncatedCoordinates c y x T) e) ≠ ⊤
  rw [heq]
  exact CurveLocalOrder.principal_colength_ne_top (pow_ne_zero _ hi)

end PiExponent.LogarithmicContactIdeal

end

end OAI
end Source0303

-- Source: OAI/NumberTheory/PiExponent/Jets/PolynomialJetPackets.lean
section Source0304
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/PolynomialJetPackets.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PolynomialJetPackets
open MvPowerSeries JetGeometry

theorem polynomial_packet_surjective {R : Type*} [CommRing R] {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun p : MvPolynomial (Fin n) R =>
      rationalCoefficientPacket v H (p : MvPowerSeries (Fin n) R)) := by
  classical
  let I := {d : Fin n →₀ ℕ // Finsupp.weight v d < H}
  let : Fintype I := Fintype.ofEquiv _ (FormalMatrixBridge.rationalJetIndexEquiv v hv H).symm
  intro packet
  change I → R at packet
  let p : MvPolynomial (Fin n) R := ∑ d : I, MvPolynomial.monomial d.val (packet d)
  refine ⟨p, ?_⟩
  funext d
  change coeff d.val (p : MvPowerSeries (Fin n) R) = packet d
  simp only [p, MvPolynomial.coeff_coe, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_monomial, Subtype.val_inj]
  change (∑ x : I, if x = (d : I) then packet x else 0) = packet d
  exact Fintype.sum_ite_eq' (d : I) packet

end PiExponent.PolynomialJetPackets

end

end OAI
end Source0304

-- Source: OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean
section Source0305
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/AlgebraicJetPackets.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.AlgebraicJetPackets

open MvPolynomial
variable {R : Type*} [CommRing R] {m : ℕ}

def triangularMap (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (1 + X 0)
    (fun i => C (c i) + X i.succ + Polynomial.aeval (X 0) (G i)))

def inverseTriangularMap (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R →ₐ[R] MvPolynomial (Fin (m+1)) R :=
  MvPolynomial.aeval (Fin.cases (X 0 - 1)
    (fun i => X i.succ - C (c i) - Polynomial.aeval (X 0 - 1) (G i)))

@[simp] theorem triangularMap_X_zero (c : Fin m → R) (G : Fin m → Polynomial R) :
    triangularMap c G (X 0) = 1 + X 0 := by simp [triangularMap]

@[simp] theorem triangularMap_X_succ (c : Fin m → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    triangularMap c G (X i.succ) = C (c i) + X i.succ + Polynomial.aeval (X 0) (G i) := by
  simp [triangularMap]

@[simp] theorem inverseTriangularMap_X_zero (c : Fin m → R) (G : Fin m → Polynomial R) :
    inverseTriangularMap c G (X 0) = X 0 - 1 := by simp [inverseTriangularMap]

@[simp] theorem inverseTriangularMap_X_succ (c : Fin m → R) (G : Fin m → Polynomial R)
    (i : Fin m) :
    inverseTriangularMap c G (X i.succ) =
      X i.succ - C (c i) - Polynomial.aeval (X 0 - 1) (G i) := by
  simp [inverseTriangularMap]

theorem triangularMap_comp_inverse (c : Fin m → R) (G : Fin m → Polynomial R) :
    (triangularMap c G).comp (inverseTriangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      triangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, triangularMap_X_zero, map_one, AlgHom.id_apply]
    rw [show (1 + X (0 : Fin (m+1)) - 1 : MvPolynomial (Fin (m+1)) R) = X 0 by ring]
    ring

theorem inverseTriangularMap_comp (c : Fin m → R) (G : Fin m → Polynomial R) :
    (inverseTriangularMap c G).comp (triangularMap c G) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp
  | succ i =>
    simp only [AlgHom.comp_apply, triangularMap_X_succ, map_add,
      inverseTriangularMap_X_succ, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq,
      ← Polynomial.aeval_algHom_apply, inverseTriangularMap_X_zero, AlgHom.id_apply]
    ring

def triangularEquiv (c : Fin m → R) (G : Fin m → Polynomial R) :
    MvPolynomial (Fin (m+1)) R ≃ₐ[R] MvPolynomial (Fin (m+1)) R :=
  AlgEquiv.ofAlgHom (triangularMap c G) (inverseTriangularMap c G)
    (triangularMap_comp_inverse c G) (inverseTriangularMap_comp c G)

theorem liftSeries_polynomial (p : Polynomial R) :
    FormalLogJet.liftSeries m (p : PowerSeries R) =
      Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1))) p := by
  have h : (FormalLogJet.liftSeries (R := R) m).comp Polynomial.coeToPowerSeries.ringHom =
      (Polynomial.aeval (MvPowerSeries.X (0 : Fin (m+1)))).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro r
      simp [MvPowerSeries.algebraMap_apply]
    · simp
  exact RingHom.congr_fun h p

theorem truncatedFormalJet_eq_polynomial (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : PiExponentApprox.FramePolynomial m) :
    FormalLogTruncation.truncatedFormalJet c T P =
      ((triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) :
        MvPowerSeries (Fin (m+1)) ℂ) := by
  have h : FormalLogTruncation.truncatedFormalJet c T =
      (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
        (triangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) := by
    apply MvPolynomial.algHom_ext
    intro i
    cases i using Fin.cases with
    | zero =>
      simp [FormalLogTruncation.truncatedFormalJet]
    | succ i =>
      simp only [FormalLogTruncation.truncatedFormalJet, MvPolynomial.aeval_X,
        Fin.cases_succ, AlgHom.comp_apply, triangularMap_X_succ, map_add]
      rw [liftSeries_polynomial, ← Polynomial.aeval_algHom_apply]
      simp [MvPowerSeries.algebraMap_apply]
  simpa using AlgHom.congr_fun h P

theorem truncatedFormalJet_inverse (c : Fin m → ℂ) (T : Fin m → ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) :
    FormalLogTruncation.truncatedFormalJet c T
      (inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P) =
      (P : MvPowerSeries (Fin (m+1)) ℂ) := by
  rw [truncatedFormalJet_eq_polynomial]
  have h := AlgHom.congr_fun
    (triangularMap_comp_inverse c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ))) P
  simpa using congrArg (fun Q : MvPolynomial (Fin (m+1)) ℂ =>
    (Q : MvPowerSeries (Fin (m+1)) ℂ)) h

theorem quotient_surjective_of_packet {A : Type*} [CommRing A] [Algebra R A]
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (f : A →ₐ[R] MvPowerSeries (Fin (m+1)) R)
    (hf : Function.Surjective (fun p => JetGeometry.rationalCoefficientPacket v H (f p))) :
    Function.Surjective ((Ideal.Quotient.mkₐ R (JetGeometry.rationalWeightedIdeal v hv H)).comp f) := by
  intro q
  obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨p, hp⟩ := hf (JetGeometry.rationalCoefficientPacket v H F)
  refine ⟨p, ?_⟩
  change Ideal.Quotient.mk _ (f p) = Ideal.Quotient.mk _ F
  apply Ideal.Quotient.eq.mpr
  exact (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv H _ _).mp hp

def algebraicJetMap (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    PiExponentApprox.FramePolynomial m →ₐ[ℂ]
      MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H :=
  (Ideal.Quotient.mkₐ ℂ (JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H)).comp
    (FormalLogTruncation.truncatedFormalJet c T)

def algebraicJetIdeal (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ) :
    Ideal (PiExponentApprox.FramePolynomial m) :=
  RingHom.ker (algebraicJetMap c T v hv H)

@[simp] theorem mem_algebraicJetIdeal (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (P : PiExponentApprox.FramePolynomial m) :
    P ∈ algebraicJetIdeal c T v hv H ↔
      FormalLogTruncation.truncatedFormalJet c T P ∈ JetGeometry.rationalWeightedIdeal (R := ℂ) v hv H := by
  change Ideal.Quotient.mk _ _ = 0 ↔ _
  exact Ideal.Quotient.eq_zero_iff_mem

theorem truncatedFormalJet_packet_surjective (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogTruncation.truncatedFormalJet c T P)) := by
  intro packet
  obtain ⟨P, hP⟩ := PolynomialJetPackets.polynomial_packet_surjective v hv H packet
  refine ⟨inverseTriangularMap c (fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)) P, ?_⟩
  simpa only [truncatedFormalJet_inverse] using hP

theorem algebraicJetMap_surjective (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (algebraicJetMap c T v (fun i => (hv i).le) H) :=
  quotient_surjective_of_packet v (fun i => (hv i).le) H _
    (truncatedFormalJet_packet_surjective c T v hv H)

def algebraicJetQuotientEquiv (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    (PiExponentApprox.FramePolynomial m ⧸ algebraicJetIdeal c T v (fun i => (hv i).le) H) ≃ₐ[ℂ]
      (MvPowerSeries (Fin (m+1)) ℂ ⧸ JetGeometry.rationalWeightedIdeal (R := ℂ) v (fun i => (hv i).le) H) :=
  Ideal.quotientKerAlgEquivOfSurjective (algebraicJetMap_surjective c T v hv H)

@[simp] theorem algebraicJetQuotientEquiv_mk (c : Fin m → ℂ) (T : Fin m → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (P : PiExponentApprox.FramePolynomial m) :
    algebraicJetQuotientEquiv c T v hv H (Ideal.Quotient.mk _ P) =
      Ideal.Quotient.mk _ (FormalLogTruncation.truncatedFormalJet c T P) :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ P

theorem formalJet_packet_surjective (c : Fin m → ℂ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) :
    Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      JetGeometry.rationalCoefficientPacket v H (FormalLogJet.formalJet c P)) := by
  let T : Fin m → ℕ := fun i => Nat.ceil (v i.succ / v 0)
  have hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0 := by
    intro i
    exact (div_le_iff₀ (hv 0)).mp (Nat.le_ceil _)
  have ht : Function.Surjective (fun P : PiExponentApprox.FramePolynomial m =>
      fun _ : Unit => JetGeometry.rationalCoefficientPacket v H
        (FormalLogTruncation.truncatedFormalJet c T P)) := by
    intro packets
    obtain ⟨P, hP⟩ := truncatedFormalJet_packet_surjective c T v hv H (packets ())
    refine ⟨P, ?_⟩
    funext j
    cases j
    exact hP
  have hs := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    v (fun i => (hv i).le) H T hT (fun _ : Unit => c) (fun P => P)).mpr ht
  intro packet
  obtain ⟨P, hP⟩ := hs (fun _ => packet)
  exact ⟨P, congrFun hP ()⟩

end PiExponent.AlgebraicJetPackets

end

end OAI
end Source0305

-- Source: OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean
section Source0306
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/CompactJetPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.CompactJetPolynomial

open MvPolynomial AlgebraicJetPackets
open scoped BigOperators

variable {k : Type*} [Field k] {m : ℕ}

def center (c : Fin m → k) : Fin (m+1) → k := Fin.cases 1 c

def coordinates (c : Fin m → k) (G : Fin m → Polynomial k) (i : Fin (m+1)) :
    MvPolynomial (Fin (m+1)) k := inverseTriangularMap c G (X i)

def powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k) (e : Fin (m+1) → ℕ) :
    Ideal (MvPolynomial (Fin (m+1)) k) :=
  Ideal.span (Set.range (fun i => coordinates c G i ^ e i))

theorem eval_center_inverse (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    (MvPolynomial.aeval (center c)).comp (inverseTriangularMap c G) =
      MvPolynomial.aeval (0 : Fin (m+1) → k) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i using Fin.cases with
  | zero => simp [center]
  | succ i =>
    simp only [AlgHom.comp_apply, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, ← Polynomial.aeval_algHom_apply]
    simp [center, Polynomial.coe_aeval_eq_eval, hG i]

theorem span_coordinates (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) :
    Ideal.span (Set.range (coordinates c G)) = WeightedBezout.pointIdeal (center c) := by
  let φ := (inverseTriangularMap c G).toRingHom
  have hs : Function.Surjective φ := (triangularEquiv c G).symm.surjective
  have hc : (WeightedBezout.pointIdeal (center c)).comap φ =
      WeightedBezout.pointIdeal (0 : Fin (m+1) → k) := by
    ext P
    change MvPolynomial.aeval (center c) (inverseTriangularMap c G P) = 0 ↔
      MvPolynomial.aeval (0 : Fin (m+1) → k) P = 0
    rw [← AlgHom.comp_apply, eval_center_inverse c G hG]
  calc
    Ideal.span (Set.range (coordinates c G)) =
        (Ideal.span (Set.range (X (R := k) : Fin (m+1) → _))).map φ := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    _ = (WeightedBezout.pointIdeal (0 : Fin (m+1) → k)).map φ := by
      congr 1
      rw [WeightedBezout.pointIdeal_eq_span]
      simp
    _ = WeightedBezout.pointIdeal (center c) := by
      rw [← hc, Ideal.map_comap_of_surjective φ hs]

theorem radical_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    (powerIdeal c G e).radical = WeightedBezout.pointIdeal (center c) := by
  apply le_antisymm
  · apply (Ideal.IsPrime.radical_le_iff
      (inferInstance : (WeightedBezout.pointIdeal (center c)).IsPrime)).mpr
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    have hz : coordinates c G i ∈ WeightedBezout.pointIdeal (center c) := by
      rw [← span_coordinates c G hG]
      exact Ideal.subset_span ⟨i,rfl⟩
    change MvPolynomial.aeval (center c) (coordinates c G i ^ e i) = 0
    rw [map_pow, (WeightedBezout.mem_pointIdeal _ _).mp hz, zero_pow (he i).ne']
  · rw [← span_coordinates c G hG]
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact ⟨e i, Ideal.subset_span ⟨i,rfl⟩⟩

def centerPoint (c : Fin m → k) : PrimeSpectrum (MvPolynomial (Fin (m+1)) k) :=
  ⟨WeightedBezout.pointIdeal (center c), inferInstance⟩

theorem zeroLocus_powerIdeal (c : Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (powerIdeal c G e : Set _) = {centerPoint c} := by
  rw [← PrimeSpectrum.zeroLocus_radical, radical_powerIdeal c G hG e he]
  exact PrimeSpectrum.zeroLocus_eq_singleton _

theorem zeroLocus_finset_prod_powerIdeal {J : Type*} (s : Finset J)
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j ∈ s, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      (fun j => centerPoint (c j)) '' (s : Set J) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, PrimeSpectrum.zeroLocus_mul,
      zeroLocus_powerIdeal (c j) G hG e he, ih]
    simp

theorem zeroLocus_prod_powerIdeal {J : Type*} [Fintype J]
    (c : J → Fin m → k) (G : Fin m → Polynomial k)
    (hG : ∀ i, (G i).eval 0 = 0) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    PrimeSpectrum.zeroLocus (((∏ j, powerIdeal (c j) G e) : Ideal (MvPolynomial (Fin (m+1)) k)) : Set _) =
      Set.range (fun j => centerPoint (c j)) := by
  simpa using zeroLocus_finset_prod_powerIdeal Finset.univ c G hG e he

def logPolynomials (T : Fin m → ℕ) : Fin m → Polynomial ℂ :=
  fun i => PowerSeries.trunc (T i) (PowerSeries.log ℂ)

@[simp] theorem logPolynomials_eval_zero (T : Fin m → ℕ) (i : Fin m) :
    (logPolynomials T i).eval 0 = 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simp [logPolynomials, PowerSeries.coeff_trunc, PowerSeries.coeff_log]

theorem truncatedFormalJet_coordinates (c : Fin m → ℂ) (T : Fin m → ℕ)
    (i : Fin (m+1)) :
    FormalLogTruncation.truncatedFormalJet c T (coordinates c (logPolynomials T) i) =
      MvPowerSeries.X i := by
  change FormalLogTruncation.truncatedFormalJet c T
    (inverseTriangularMap c (fun j => PowerSeries.trunc (T j) (PowerSeries.log ℂ)) (X i)) = _
  rw [truncatedFormalJet_inverse]
  simp

theorem map_powerIdeal_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) :
    (powerIdeal c (logPolynomials T) e).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change FormalLogTruncation.truncatedFormalJet c T
    (coordinates c (logPolynomials T) i ^ e i) = MvPowerSeries.X i ^ e i
  rw [map_pow, truncatedFormalJet_coordinates]

theorem map_powerIdeal_pow_truncatedFormalJet (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (n : ℕ) :
    (powerIdeal c (logPolynomials T) e ^ n).map
      (FormalLogTruncation.truncatedFormalJet c T).toRingHom =
        JetGeometry.coordinatePowerIdeal (R := ℂ) e ^ n := by
  rw [Ideal.map_pow, map_powerIdeal_truncatedFormalJet]

theorem truncatedFormalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogTruncation.truncatedFormalJet c T P ∈
      JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  apply JetGeometry.coordinatePowerIdeal_pow_le_rational v hv e R he n
  rw [← map_powerIdeal_pow_truncatedFormalJet c T e n]
  exact Ideal.mem_map_of_mem _ hP

theorem formalJet_mem_weighted_of_mem_pow (c : Fin m → ℂ) (T : Fin m → ℕ)
    (e : Fin (m+1) → ℕ) (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P : MvPolynomial (Fin (m+1)) ℂ) (hP : P ∈ powerIdeal c (logPolynomials T) e ^ n) :
    FormalLogJet.formalJet c P ∈ JetGeometry.rationalWeightedIdeal v hv (n * R) := by
  rw [← FormalLogTruncation.shiftMap_truncatedFormalJet c T P]
  exact FormalLogTruncation.shiftMap_mem_rationalWeightedIdeal
    (fun i => FormalLogTruncation.logTail (T i))
    (fun i => FormalLogTruncation.logTail_constantCoeff (T i)) v hv
    (fun i => FormalLogTruncation.logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i))
    (n * R) _ (truncatedFormalJet_mem_weighted_of_mem_pow c T e v hv R he n P hP)

theorem aeval_coordinates {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (y : A) (x : Fin m → A) (i : Fin (m+1)) :
    MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i) =
      LogarithmicContactIdeal.truncatedCoordinates c y x T i := by
  cases i using Fin.cases with
  | zero => simp [coordinates, LogarithmicContactIdeal.truncatedCoordinates]
  | succ i =>
    simp only [coordinates, inverseTriangularMap_X_succ, map_sub,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, Fin.cases_succ,
      ← Polynomial.aeval_algHom_apply, Fin.cases_zero, map_one,
      LogarithmicContactIdeal.truncatedCoordinates]
    rfl

theorem map_powerIdeal_aeval {A : Type*} [CommRing A] [Algebra ℂ A]
    (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (y : A) (x : Fin m → A) :
    (powerIdeal c (logPolynomials T) e).map (MvPolynomial.aeval (Fin.cases y x)).toRingHom =
      LogarithmicContactIdeal.logarithmicIdeal c y x T e := by
  rw [powerIdeal, Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext i
  change MvPolynomial.aeval (Fin.cases y x) (coordinates c (logPolynomials T) i ^ e i) =
    LogarithmicContactIdeal.truncatedCoordinates c y x T i ^ e i
  rw [map_pow, aeval_coordinates]

end PiExponent.CompactJetPolynomial

end

end OAI
end Source0306

-- Source: LogTwo/Geometry/JetIdealAt.lean
section Source0307
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt jet-ideal radical, support and packet-vanishing arguments using inverse Y-scaling.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

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
end Source0307

-- Source: LogTwo/Geometry/JetIdealContact.lean
section Source0308
/-! The polynomial ideal at a varying center, evaluated in a branch DVR,
has colength equal to the normalized logarithmic contact. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E) {m : ℕ}

theorem lift_normalizeY (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E)
    (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p) :
    lift p (normalizeY y z) (centerPoint 1 c) ((normalized_centered_iff p y hy z c).mpr hc) =
      Fin.cases (algebraMap ℂ (ring p) y⁻¹ * lift p z (centerPoint y c) hc 0)
        (fun i => lift p z (centerPoint y c) hc i.succ) := by
  funext i
  cases i using Fin.cases with
  | zero =>
    apply Subtype.ext
    change z 0 / algebraMap ℂ E y = algebraMap ℂ E y⁻¹ * z 0
    rw [map_inv₀, div_eq_mul_inv, mul_comm]
  | succ i => rfl

def localJetIdealAt (y : ℂ) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (centerPoint y c) p) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    Ideal (ring p) :=
  (jetIdealAt y c T e).map (MvPolynomial.aeval (lift p z (centerPoint y c) hc)).toRingHom

theorem localJetIdealAt_eq (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E)
    (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) :
    localJetIdealAt p y z c hc T e =
      LogarithmicContactIdeal.logarithmicIdeal c
        (lift p (normalizeY y z) (centerPoint 1 c)
          ((normalized_centered_iff p y hy z c).mpr hc) 0)
        (fun i => lift p (normalizeY y z) (centerPoint 1 c)
          ((normalized_centered_iff p y hy z c).mpr hc) i.succ) T e := by
  rw [localJetIdealAt, map_jetIdealAt_aeval y hy, lift_normalizeY p y hy]
  rfl

variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem localJetIdealAt_colength_eq_contact (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ localJetIdealAt p y z c hc T e)).toNat : ℚ) =
      R * logContactAt p y hy z c hc hnc v := by
  rw [localJetIdealAt_eq p y hy]
  let hc' : Centered (normalizeY y z) (Fin.cases 1 c) p :=
    (normalized_centered_iff p y hy z c).mpr hc
  let hnc' := normalized_nonconstant y hy z c hnc
  let u : Fin (m+1) → ring p := lift p (normalizeY y z) (Fin.cases 1 c) hc'
  have hzero : CurveLocalOrder.residueAugmentation ℂ (ring p) (u 0) = 1 :=
    lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' 0
  have hsucc : ∀ i : Fin m, CurveLocalOrder.residueAugmentation ℂ (ring p) (u i.succ) = c i :=
    fun i => lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' i.succ
  have hn : u 0 ≠ 1 ∨ ∃ i, u i.succ ≠ algebraMap ℂ (ring p) (c i) :=
    logLift_nonconstant p (normalizeY y z) c hc' hnc'
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_eq_contact v hv c
    (u 0) (fun i => u i.succ) hzero hsucc hn T hT R e he

theorem localJetIdealAt_colength_ne_top (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, v i * (e i : ℚ) = R) :
    Module.length (ring p) ((ring p) ⧸ localJetIdealAt p y z c hc T e) ≠ ⊤ := by
  rw [localJetIdealAt_eq p y hy]
  let hc' : Centered (normalizeY y z) (Fin.cases 1 c) p :=
    (normalized_centered_iff p y hy z c).mpr hc
  let hnc' := normalized_nonconstant y hy z c hnc
  let u : Fin (m+1) → ring p := lift p (normalizeY y z) (Fin.cases 1 c) hc'
  have hzero : CurveLocalOrder.residueAugmentation ℂ (ring p) (u 0) = 1 :=
    lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' 0
  have hsucc : ∀ i : Fin m, CurveLocalOrder.residueAugmentation ℂ (ring p) (u i.succ) = c i :=
    fun i => lift_residue p (normalizeY y z) (Fin.cases 1 c) hc' i.succ
  have hn : u 0 ≠ 1 ∨ ∃ i, u i.succ ≠ algebraMap ℂ (ring p) (c i) :=
    logLift_nonconstant p (normalizeY y z) c hc' hnc'
  exact LogarithmicContactIdeal.logarithmicIdeal_colength_ne_top v hv c
    (u 0) (fun i => u i.succ) hzero hsucc hn T hT R e he

end
end LogTwo.Geometry
end Source0308

-- Source: LogTwo/Geometry/JetIdealCRT.lean
section Source0309
/-! Chinese remainder interpolation at the distinct centers. There is no
weighted-degree bound here, so this does not imply FullRowMinor. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox
noncomputable section

theorem jetIdealAt_pairwise_coprime {m : ℕ} {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun j k => IsCoprime (jetIdealAt (y j) (c j) T e)
      (jetIdealAt (y k) (c k) T e)) := by
  intro j k hjk
  have hne : WeightedBezout.pointIdeal (centerPoint (y j) (c j)) ≠
      WeightedBezout.pointIdeal (centerPoint (y k) (c k)) := by
    intro h
    apply hjk
    apply centerPrime_injective_of_Y y hy c
    exact PrimeSpectrum.ext h
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_jetIdealAt (y j) (c j) T e he,
    radical_jetIdealAt (y k) (c k) T e he,
    (Ideal.isCoprime_of_isMaximal hne).sup_eq, Ideal.radical_top]

/-- Every finite set of polynomial residue classes can be simultaneously
realized, with no bound asserted on the degree of the realizing polynomial. -/
theorem jetIdealAt_residue_surjective {m : ℕ} {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) (n : ℕ) :
    Function.Surjective (fun P : FramePolynomial m =>
      fun j => Ideal.Quotient.mk (jetIdealAt (y j) (c j) T e ^ n) P) := by
  intro b
  have hpair : Pairwise (fun j k => IsCoprime (jetIdealAt (y j) (c j) T e ^ n)
      (jetIdealAt (y k) (c k) T e ^ n)) := by
    intro j k hjk
    exact (jetIdealAt_pairwise_coprime y hy c T e he hjk).pow
  obtain ⟨P, hP⟩ := Ideal.pi_quotient_surjective hpair b
  exact ⟨P, funext hP⟩

end
end LogTwo.Geometry
end Source0309

-- Source: LogTwo/Geometry/JetProductContact.lean
section Source0310
/-! At a branch centered at one of the distinct Y-centers, all other factors
of the product jet ideal become the unit ideal. Thus the local colength of the
full product is the already verified logarithmic contact at this center. -/
namespace LogTwo.Geometry
open OAI PiExponent PiExponentApprox MvPolynomial
open CurveValuationCenter CurveCenters PlaceValuationRing PlaceCenteredBranch
noncomputable section

variable {m : ℕ}

theorem isUnit_of_residueAugmentation_ne_zero {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (x : A) (hx : CurveLocalOrder.residueAugmentation ℂ A x ≠ 0) : IsUnit x := by
  apply (IsLocalRing.residue_ne_zero_iff_isUnit x).mp
  intro h
  apply hx
  change (CurveLocalOrder.residueCoefficientEquiv ℂ A).symm
    (IsLocalRing.residue A x) = 0
  rw [h, map_zero]

/-- A different residue of the Y-coordinate makes the whole jet ideal a unit.
Only the radical is needed; explicit logarithmic generators are unnecessary. -/
theorem map_jetIdealAt_eq_top_of_residue_ne {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (he : ∀ i, 0 < e i) (u : Fin (m+1) → A)
    (hne : CurveLocalOrder.residueAugmentation ℂ A (u 0) ≠ y) :
    (jetIdealAt y c T e).map (MvPolynomial.aeval u).toRingHom = ⊤ := by
  have hg : X 0 - C y ∈ (jetIdealAt y c T e).radical := by
    rw [radical_jetIdealAt y c T e he]
    simp [centerPoint]
  obtain ⟨n, hn⟩ := hg
  have hu : IsUnit (MvPolynomial.aeval u (X 0 - C y)) := by
    apply isUnit_of_residueAugmentation_ne_zero
    simpa only [map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C,
      CurveLocalOrder.residueAugmentation_algebraMap, sub_ne_zero] using hne
  apply Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (MvPolynomial.aeval u).toRingHom hn)
  change IsUnit (MvPolynomial.aeval u ((X 0 - C y) ^ n))
  rw [map_pow]
  exact hu.pow n

theorem map_jetProductIdeal_eq_factor {A : Type*} [CommRing A]
    [IsLocalRing A] [Algebra ℂ A]
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]
    {J : Type*} [Fintype J] (y : J → ℂ) (hy : Function.Injective y)
    (c : J → Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (he : ∀ i, 0 < e i) (u : Fin (m+1) → A) (j : J)
    (hu : CurveLocalOrder.residueAugmentation ℂ A (u 0) = y j) :
    (jetProductIdeal y c T e).map (MvPolynomial.aeval u).toRingHom =
      (jetIdealAt (y j) (c j) T e).map (MvPolynomial.aeval u).toRingHom := by
  classical
  change Ideal.mapHom (MvPolynomial.aeval u).toRingHom
    (∏ k, jetIdealAt (y k) (c k) T e) = _
  rw [map_prod]
  apply Finset.prod_eq_single j
  · intro k _ hkj
    have hne : CurveLocalOrder.residueAugmentation ℂ A (u 0) ≠ y k := by
      rw [hu]
      exact fun h => hkj (hy h).symm
    exact (map_jetIdealAt_eq_top_of_residue_ne (y k) (c k) T e he u hne).trans
      Ideal.one_eq_top.symm
  · simp

variable {E : Type*} [Field E] [Algebra ℂ E]
variable (p : NormalizedPlace ℂ E)
variable [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def localJetProductIdeal {J : Type*} [Fintype J]
    (y : J → ℂ) (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) : Ideal (ring p) :=
  (jetProductIdeal y c T e).map
    (MvPolynomial.aeval (lift p z (centerPoint (y j) (c j)) hc)).toRingHom

theorem localJetProductIdeal_eq {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (j : J) (hc : Centered z (centerPoint (y j) (c j)) p)
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    localJetProductIdeal p y c z j hc T e = localJetIdealAt p (y j) z (c j) hc T e := by
  exact map_jetProductIdeal_eq_factor y hy c T e he
    (lift p z (centerPoint (y j) (c j)) hc) j
    (lift_residue p z (centerPoint (y j) (c j)) hc 0)

theorem localJetProductIdeal_colength_eq_contact {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (hbalance : ∀ i, v i * (e i : ℚ) = R) :
    ((Module.length (ring p) ((ring p) ⧸ localJetProductIdeal p y c z j hc T e)).toNat : ℚ) =
      R * logContactAt p (y j) (hy0 j) z (c j) hc hnc v := by
  rw [localJetProductIdeal_eq p y hy c z j hc T e he]
  exact localJetIdealAt_colength_eq_contact p (y j) (hy0 j) z (c j) hc hnc
    v hv T hT R e hbalance

theorem localJetProductIdeal_colength_ne_top {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : Function.Injective y) (hy0 : ∀ j, y j ≠ 0)
    (c : J → Fin m → ℂ) (z : Fin (m+1) → E) (j : J)
    (hc : Centered z (centerPoint (y j) (c j)) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ < (T i : ℚ) * v 0)
    (R : ℚ) (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i)
    (hbalance : ∀ i, v i * (e i : ℚ) = R) :
    Module.length (ring p) ((ring p) ⧸ localJetProductIdeal p y c z j hc T e) ≠ ⊤ := by
  rw [localJetProductIdeal_eq p y hy c z j hc T e he]
  exact localJetIdealAt_colength_ne_top p (y j) (hy0 j) z (c j) hc hnc
    v hv T hT R e hbalance

end
end LogTwo.Geometry
end Source0310

-- Source: OAI/NumberTheory/PiExponent/Cohomology/FiniteCoverCohomology.lean
section Source0311
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteCoverCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

abbrev schemeUnit (X : AlgebraicGeometry.Scheme) : X.Modules :=
  SheafOfModules.unit X.ringCatSheaf

namespace AdicInjective
universe u v
variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

def adicTorsion : Submodule R M :=
  ⨆ n : ℕ, Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)

lemma torsion_mono : Monotone (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) :=
  fun a b hab => Submodule.torsionBySet_le_torsionBySet_pow a b hab I

lemma mem_adicTorsion (x : M) : x ∈ adicTorsion I M ↔
    ∃ n : ℕ, ∀ a ∈ I ^ n, a • x = 0 := by
  rw [adicTorsion, Submodule.mem_iSup_of_directed _ (torsion_mono I M).directed_le]
  simp only [Submodule.mem_torsionBySet_iff, Subtype.forall, SetLike.mem_coe]

lemma fg_uniform_exponent (N : Submodule R M) (hN : N.FG)
    (h : N ≤ adicTorsion I M) :
    ∃ n : ℕ, N ≤ Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R) := by
  classical
  obtain ⟨s, hs⟩ := IsCompactElement.exists_finset_of_le_iSup
    ((Submodule.fg_iff_compact N).mp hN)
    (fun n : ℕ => Submodule.torsionBySet R M ((I ^ n : Ideal R) : Set R)) h
  refine ⟨s.sup id, hs.trans (iSup_le fun n => iSup_le fun hn => ?_)⟩
  exact torsion_mono I M (Finset.le_sup (f := id) hn)

lemma exists_power_inf_le [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    ∃ m : ℕ, I ^ m ⊓ J ≤ I ^ n * J := by
  obtain ⟨k, hk⟩ := I.exists_pow_inf_eq_pow_smul (M := R) J
  refine ⟨k+n, ?_⟩
  have h := hk (k+n) (Nat.le_add_right _ _)
  simp only [Ideal.smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left] at h
  rw [h]
  exact Ideal.mul_mono le_rfl inf_le_right

theorem adicTorsion_injective [IsNoetherianRing R] [Small.{v} R]
    [Module.Injective R M] : Module.Injective R (adicTorsion I M) := by
  apply Module.Baer.injective
  intro J g
  let g₀ : J →ₗ[R] M := (adicTorsion I M).subtype.comp g
  have hg₀ : g₀.range ≤ adicTorsion I M := by
    rintro x ⟨y, rfl⟩
    exact (g y).property
  obtain ⟨n, hn⟩ := fg_uniform_exponent I M g₀.range (Submodule.fg_range g₀) hg₀
  obtain ⟨h, hh⟩ := Module.Injective.extension_property R M J R
    J.subtype Subtype.val_injective g₀
  have hj : ∀ x : J, h x = g₀ x := fun x => LinearMap.congr_fun hh x
  have hzero : I ^ n * J ≤ h.ker := by
    apply Ideal.mul_le.mpr
    intro a ha b hb
    change h (a * b) = 0
    rw [← smul_eq_mul, h.map_smul, hj ⟨b, hb⟩]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hn (LinearMap.mem_range_self g₀ ⟨b,hb⟩)) ⟨a,ha⟩
  obtain ⟨m, hm⟩ := exists_power_inf_le I J n
  let f : R →ₗ.[R] M := ⟨J, g₀⟩
  let z : R →ₗ.[R] M := ⟨I ^ m, 0⟩
  have hz : ∀ (x : f.domain) (y : z.domain), (x : R) = y → f x = z y := by
    intro x y hxy
    change g₀ x = 0
    rw [← hj x]
    exact hzero (hm ⟨hxy ▸ y.property, x.property⟩)
  let F := f.sup z hz
  obtain ⟨H, hH⟩ := Module.Injective.extension_property R M F.domain R
    F.domain.subtype Subtype.val_injective F.toFun
  have HF : ∀ x : F.domain, H x = F x := fun x => LinearMap.congr_fun hH x
  have HJ : ∀ x : J, H x = g₀ x := by
    intro x
    rw [HF ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩]
    exact ((f.left_le_sup z hz).2 (x := x) (y := ⟨x, (show J ≤ J ⊔ I ^ m from le_sup_left) x.property⟩) rfl).symm
  have HI : ∀ a ∈ I ^ m, H a = 0 := by
    intro a ha
    rw [HF ⟨a, (show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩]
    exact ((f.right_le_sup z hz).2 (x := ⟨a,ha⟩) (y := ⟨a,(show I ^ m ≤ J ⊔ I ^ m from le_sup_right) ha⟩) rfl).symm
  have Hmem : ∀ a, H a ∈ adicTorsion I M := by
    intro a
    apply (mem_adicTorsion I M _).mpr
    refine ⟨m, fun b hb => ?_⟩
    rw [← H.map_smul]
    exact HI (b * a) ((I ^ m).mul_mem_right a hb)
  refine ⟨H.codRestrict (adicTorsion I M) Hmem, ?_⟩
  intro x hx
  apply Subtype.ext
  exact HJ ⟨x,hx⟩

end AdicInjective

namespace InjectiveRange
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Small.{v} R]
variable {N : Type w} [AddCommGroup N] [Module R N] [Small.{w} R]

omit [Small.{w} R] in

lemma injective_of_retract [Module.Injective R M]
    (i : N →ₗ[R] M) (p : M →ₗ[R] N) (h : p.comp i = LinearMap.id) :
    Module.Injective R N := by
  apply Module.Baer.injective
  intro J g
  obtain ⟨f, hf⟩ := Module.Baer.of_injective (R := R) (Q := M) inferInstance J (i.comp g)
  refine ⟨p.comp f, fun x hx => ?_⟩
  change p (f x) = g ⟨x,hx⟩
  rw [hf x hx]
  exact LinearMap.congr_fun h (g ⟨x,hx⟩)

omit [Small.{w} R] in
lemma range_injective (r : M →ₗ[R] N) [Module.Injective R M]
    [Module.Injective R r.ker] : Module.Injective R r.range := by
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.ker r.ker M
    r.ker.subtype Subtype.val_injective LinearMap.id
  let f : M →ₗ[R] M := LinearMap.id - r.ker.subtype.comp p
  have hf : r.ker ≤ f.ker := by
    intro x hx
    change x - (p x : M) = 0
    have hpx := LinearMap.congr_fun hp ⟨x,hx⟩
    exact sub_eq_zero.mpr (congrArg Subtype.val hpx).symm
  let i : r.range →ₗ[R] M := (r.ker.liftQ f hf).comp r.quotKerEquivRange.symm.toLinearMap
  apply injective_of_retract i r.rangeRestrict
  ext y
  rcases y with ⟨y,hy⟩
  obtain ⟨x,rfl⟩ := hy
  change r ((r.ker.liftQ f hf) (r.quotKerEquivRange.symm ⟨r x, LinearMap.mem_range_self r x⟩)) = r x
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  change r (x - (p x : M)) = r x
  rw [map_sub, (p x).property, sub_zero]

lemma surjective_of_torsion_cokernel (I : Ideal R) (r : M →ₗ[R] N)
    [Module.Injective R M] [Module.Injective R r.ker]
    (hc : ∀ y : N, ∃ n : ℕ, ∀ a ∈ I ^ n, a • y ∈ r.range)
    (ht : ∀ y : N, (∃ n : ℕ, ∀ a ∈ I ^ n, a • y = 0) → y = 0) :
    Function.Surjective r := by
  let : Module.Injective R r.range := range_injective r
  obtain ⟨p, hp⟩ := Module.Injective.extension_property R r.range r.range N
    r.range.subtype Subtype.val_injective LinearMap.id
  intro y
  suffices h : y = (p y : N) from h ▸ (p y).property
  apply sub_eq_zero.mp
  apply ht
  obtain ⟨n, hn⟩ := hc y
  refine ⟨n, fun a ha => ?_⟩
  rw [smul_sub]
  have h := congrArg Subtype.val (LinearMap.congr_fun hp ⟨a • y, hn a ha⟩)
  change (p (a • y) : N) = a • y at h
  rw [map_smul] at h
  exact sub_eq_zero.mpr h.symm

end InjectiveRange

section
universe u
open TopCat AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
open PrimeSpectrum
namespace AffineDenominators
variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

abbrev schemeBasicOpen (f : R) : (Spec R).Opens := PrimeSpectrum.basicOpen f

private lemma schemeBasicOpen_mul (f g : R) :
    schemeBasicOpen (f * g) = schemeBasicOpen f ⊓ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul f g

private lemma schemeBasicOpen_mul_le_left (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen f :=
  PrimeSpectrum.basicOpen_mul_le_left f g

private lemma schemeBasicOpen_mul_le_right (f g : R) :
    schemeBasicOpen (f * g) ≤ schemeBasicOpen g :=
  PrimeSpectrum.basicOpen_mul_le_right f g

private lemma schemeIsSMulRegular {f : R} {U : (Spec R).Opens}
    (hle : U ≤ schemeBasicOpen f) : IsSMulRegular Γ(M, U) f :=
  M.isSMulRegular_of_le_basicOpen (U := U) hle

structure Aux (V : (Spec R).Opens) where
  existence (f : R) (hf : schemeBasicOpen f ≤ V) (s : Γ(M, schemeBasicOpen f)) :
    ∃ (n : ℕ) (t : Γ(M, V)), M.presheaf.map (homOfLE hf).op t = f ^ n • s
  uniqueness (f : R) (hf : schemeBasicOpen f ≤ V) (t : Γ(M, V)) :
    M.presheaf.map (.op <| homOfLE hf) t = (0 : Γ(M, schemeBasicOpen f)) →
    ∃ (n : ℕ), f ^ n • t = 0

lemma Aux.of_le {M : (Spec R).Modules} {V : (Spec R).Opens} (g : R) (hg : schemeBasicOpen g ≤ V)
    (hV : Aux M V) :
    Aux M (schemeBasicOpen g) where
  existence f hfg s := by
    obtain ⟨n, t, ht⟩ := hV.existence f (le_trans hfg hg) s
    use n, M.presheaf.map (homOfLE hg).op t
    simp [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, ht]
  uniqueness f hfg t ht := by
    obtain ⟨n, t', ht'⟩ := hV.existence g hg t
    obtain ⟨m, hm⟩ := hV.uniqueness _ (le_trans hfg hg) t' <| by
      rw [← homOfLE_comp hfg hg, op_comp, M.presheaf.map_comp_apply, ht', M.map_smul_Spec, ht]
      simp
    refine ⟨m, ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul ?_⟩
    simp [smul_comm, ← ht', ← M.map_smul_Spec, hm]

lemma Aux.of_eq_iSup_basicOpen {M : (Spec R).Modules} (V : (Spec R).Opens)
    {ι : Type*} [Finite ι] (g : ι → R) (hg : V = ⨆ i, schemeBasicOpen (g i))
    (h₁ : ∀ (i : ι), Aux M (schemeBasicOpen (g i))) :
    Aux M V := by
  have h₂ (i j : ι) : Aux M (schemeBasicOpen (g i * g j)) :=
    .of_le _ (schemeBasicOpen_mul_le_left _ _) (h₁ i)
  have hgle (i : ι) : schemeBasicOpen (g i) ≤ V := by rw [hg]; exact le_iSup_of_le _ le_rfl
  have hug (i : ι) (m : ℕ) :
      IsUnit (algebraMap R (Module.End R Γ(M, schemeBasicOpen (g i))) (g i ^ m)) := by
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (g i) le_rfl).pow m

  refine ⟨fun f hf s ↦ ?_, fun f hf t hs ↦ ?_⟩
  · have hfgi (i : ι) : schemeBasicOpen (f * g i) ≤ schemeBasicOpen (g i) := schemeBasicOpen_mul_le_right f (g i)
    let s' (i : ι) : Γ(M, schemeBasicOpen (f * g i)) :=
      M.presheaf.map (homOfLE <| schemeBasicOpen_mul_le_left f (g i)).op s

    obtain ⟨N, t, ht⟩ : ∃ (N : ℕ) (t : ∀ i, Γ(M, schemeBasicOpen (g i))),
        ∀ i, f ^ N • s' i = M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right f (g i))).op (t i) := by
      have (i : ι) : ∃ (n : ℕ) (t : Γ(M, schemeBasicOpen (g i))),
          f ^ n • s' i = M.presheaf.map (homOfLE (hfgi i)).op t := by
        obtain ⟨n, t', ht'⟩ := (h₁ i).existence (f * g i) (hfgi i) (s' i)
        rw [mul_pow, mul_smul, smul_comm] at ht'
        obtain ⟨ψ, hψ⟩ := IsUnit.exists_right_inv (hug i n)
        use n, ψ t'
        apply (schemeIsSMulRegular M (schemeBasicOpen_mul_le_right f (g i))).pow n
        dsimp
        rw [← ht', ← Scheme.Modules.map_smul_Spec]
        congr 1
        exact congr($hψ t').symm
      choose n t' ht' using this
      have (i : ι) : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have hN (i : ι) : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by grind
      refine ⟨⨆ i, n i, fun i ↦ f ^ ((⨆ i, n i) - n i) • t' i, fun i ↦ ?_⟩
      conv_lhs => rw [hN i]
      rw [pow_add, mul_smul, ht', M.map_smul_Spec]

    obtain ⟨K, hK⟩ : ∃ (K : ℕ), ∀ (i j : ι),
        M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ K • t i) =
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ K • t j) := by
      have (i j : ι) : ∃ (m : ℕ),
          M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (f ^ m • t i) =
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (f ^ m • t j) := by
        have := (h₂ i j).uniqueness (f * (g i * g j)) (schemeBasicOpen_mul_le_right _ _)
          (M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_left (g i) (g j))).op (t i) -
            M.presheaf.map (homOfLE (schemeBasicOpen_mul_le_right (g i) (g j))).op (t j)) ?_
        · obtain ⟨m, hm⟩ := this
          use m
          apply (schemeIsSMulRegular M le_rfl).pow m
          simpa [M.map_smul_Spec _ (f ^ m), ← mul_smul, ← mul_smul, ← mul_pow, ← mul_comm f,
            smul_sub, sub_eq_zero] using hm
        · have hfgigi : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g i) := by
            rw [← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          have hfgigj : schemeBasicOpen (f * (g i * g j)) ≤ schemeBasicOpen (f * g j) := by
            rw [mul_comm (g i) (g j), ← mul_assoc]
            exact schemeBasicOpen_mul_le_left _ _
          rw [map_sub, ← M.presheaf.map_comp_apply, ← op_comp, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp, homOfLE_comp, ← homOfLE_comp hfgigi (hfgi i),
            ← homOfLE_comp hfgigj (hfgi j), op_comp, M.presheaf.map_comp_apply, ← ht i,
            M.map_smul_Spec, ← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp, op_comp,
            M.presheaf.map_comp_apply, ← ht j, M.map_smul_Spec, ← M.presheaf.map_comp_apply,
            ← op_comp, homOfLE_comp]
          simp
      choose m hm using this
      let K := ⨆ i, ⨆ j, m i j
      refine ⟨K, fun i j ↦ ?_⟩
      have : m i j ≤ K :=
        le_ciSup_of_le (Finite.bddAbove_range _) i (le_ciSup (Finite.bddAbove_range _) _)
      have : K = (K - m i j) + m i j := by lia
      rw [this, pow_add, mul_smul, mul_smul, M.map_smul_Spec, M.map_smul_Spec _ (f ^ (K - m i j)),
        hm i j]

    refine ⟨N + K, ?_⟩
    have := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) V
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl)) (by simp [hg])
      (fun i ↦ f ^ K • t i) ?_
    · obtain ⟨a, ha, -⟩ := this
      use a
      refine TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (f * g i)) _
          (fun i ↦ homOfLE (schemeBasicOpen_mul_le_left f (g i))) ?_ _ _ ?_
      · rw [left_eq_inf.mpr hf, hg, inf_iSup_eq]
        simp_rw [schemeBasicOpen_mul]
        exact le_rfl
      · intro i
        rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp (schemeBasicOpen_mul_le_right _ _) (hgle i), op_comp, M.presheaf.map_comp_apply,
          M.map_smul_Spec, ha, M.map_smul_Spec, pow_add, mul_smul, smul_comm, ht i]
    · intro i j
      have : Function.Injective (M.presheaf.map (eqToHom <| (schemeBasicOpen_mul (g i) (g j))).op) :=
        ConcreteCategory.injective_of_mono_of_preservesPullback _
      apply this
      dsimp [Opens.infLELeft, Opens.infLERight]
      simp_rw [← M.presheaf.map_comp_apply, ← op_comp, eqToHom_comp_homOfLE]
      exact hK i j
  · have (i : ι) : ∃ (n : ℕ), M.presheaf.map (homOfLE (hgle i)).op (f ^ n • t) = 0 := by
      have := (h₁ i).uniqueness (f * g i) (schemeBasicOpen_mul_le_right f (g i))
        (M.presheaf.map (homOfLE (hgle i)).op t) ?_
      · obtain ⟨n, hn⟩ := this
        use n
        rw [mul_pow, mul_comm, mul_smul, ← Scheme.Modules.map_smul_Spec] at hn
        exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul hn
      · rw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp,
          ← homOfLE_comp ((schemeBasicOpen_mul_le_left f (g i))) hf, op_comp, M.presheaf.map_comp_apply]
        simp [hs]
    choose n hn using this
    use ⨆ i, n i
    apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i ↦ schemeBasicOpen (g i)) _
      (fun i ↦ homOfLE (by rw [hg]; exact le_iSup_of_le _ le_rfl))
    · simp [hg]
    · intro i
      have : n i ≤ ⨆ i, n i := le_ciSup (Finite.bddAbove_range _) _
      have : ⨆ i, n i = ((⨆ i, n i) - n i) + n i := by lia
      rw [this, pow_add, mul_smul, Scheme.Modules.map_smul_Spec, hn i]
      simp

lemma isLocalizing_iff_aux (M : (Spec R).Modules) :
    IsLocalizing (modulesSpecToSheaf.obj M) ↔ Aux M ⊤ := by
  let φ (f : R) := ((modulesSpecToSheaf.obj M).obj.map (schemeBasicOpen f).leTop.op).hom
  refine ⟨fun h ↦ ?_, fun h f ↦ IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_⟩
  · have hf (f : R) : IsLocalizedModule.Away f (φ f) := h f
    refine ⟨fun f hle s ↦ ?_, fun f hle s hs ↦ ?_⟩
    · obtain ⟨n, y, hy⟩ := (hf f).surj _ _ s
      use n, y, hy.symm
    · obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers f) (φ f)).mp hs
      use n, hn
  · exact Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen f le_rfl
  · intro x
    obtain ⟨n, t, ht⟩ := h.existence _ _ x
    use n, t, ht.symm
  · intro x hx
    obtain ⟨n, hn⟩ := h.uniqueness _ _ _ hx
    use n, hn

theorem aux_of_isCompact (V : (Spec R).Opens) (hV : IsCompact (V : Set (Spec R)))
    (h : IsLocalizing (modulesSpecToSheaf.obj M)) : Aux M V := by
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact V hV
  let := hι
  exact Aux.of_eq_iSup_basicOpen V g hg (fun i =>
    Aux.of_le (g i) le_top ((isLocalizing_iff_aux M).mp h))

variable {M}

def res (U V : (Spec R).Opens) (h : U ≤ V) : Γ(M,V) →ₗ[R] Γ(M,U) :=
  ((modulesSpecToSheaf.obj M).obj.map (homOfLE h).op).hom

lemma res_comp {U V W : (Spec R).Opens} (h : U ≤ V) (k : V ≤ W) (s : Γ(M,W)) :
    res U V h (M := M) (res V W k s) = res U W (h.trans k) s := by
  exact (M.presheaf.map_comp_apply (homOfLE k).op (homOfLE h).op s).symm

lemma eq_zero_of_cover {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (h : ∀ i, res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl) s = 0) : s = 0 := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => schemeBasicOpen (g i)) U
    (fun i => homOfLE (hU ▸ le_iSup_of_le i le_rfl)) (by rw [hU])
  intro i
  change res (schemeBasicOpen (g i)) U _ s = res (schemeBasicOpen (g i)) U _ 0
  rw [map_zero]
  exact h i

lemma power_in_ideal_of_generator_powers {ι : Type*} [Finite ι]
    (g : ι → R) (J : Ideal R) (h : ∀ i, ∃ n : ℕ, g i ^ n ∈ J) :
    ∃ n : ℕ, Ideal.span (Set.range g) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg
  · apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact h i
  · exact Submodule.fg_span (Set.finite_range g)

lemma kernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,⊤))
    (hs : res U ⊤ le_top s = 0) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0 := by
  let J : Ideal R := (LinearMap.toSpanSingleton R Γ(M,⊤) s).ker
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    apply ((isLocalizing_iff_aux M).mp hloc).uniqueness (g i) le_top s
    change res (schemeBasicOpen (g i)) ⊤ le_top s = 0
    rw [← res_comp (hU ▸ le_iSup_of_le i le_rfl) le_top, hs, map_zero]
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

lemma torsion_free {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,U))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) : s = 0 := by
  obtain ⟨n,hn⟩ := hs
  apply eq_zero_of_cover g U hU s
  intro i
  have hm : g i ^ n ∈ Ideal.span (Set.range g) ^ n :=
    Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) n
  have h := congrArg (res (schemeBasicOpen (g i)) U (hU ▸ le_iSup_of_le i le_rfl)) (hn _ hm)
  rw [map_smul, map_zero] at h
  exact ((schemeIsSMulRegular M le_rfl).pow n).right_eq_zero_of_smul h

lemma torsion_in_kernel {ι : Type*} (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (s : Γ(M,⊤))
    (hs : ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n, a • s = 0) :
    res U ⊤ le_top s = 0 := by
  apply torsion_free g U hU
  obtain ⟨n,hn⟩ := hs
  refine ⟨n,fun a ha => ?_⟩
  rw [← map_smul, hn a ha, map_zero]

lemma cokernel_is_torsion {ι : Type*} [Finite ι] (g : ι → R) (U : (Spec R).Opens)
    (hU : U = ⨆ i, schemeBasicOpen (g i)) (hU' : IsCompact (U : Set (Spec R)))
    (hloc : IsLocalizing (modulesSpecToSheaf.obj M)) (s : Γ(M,U)) :
    ∃ n : ℕ, ∀ a ∈ Ideal.span (Set.range g) ^ n,
      a • s ∈ (res U ⊤ le_top (M := M)).range := by
  let J : Ideal R := (res U ⊤ le_top (M := M)).range.comap
    (LinearMap.toSpanSingleton R Γ(M,U) s)
  have hgen : ∀ i, ∃ n : ℕ, g i ^ n ∈ J := by
    intro i
    let hgi : schemeBasicOpen (g i) ≤ U := hU ▸ le_iSup_of_le i le_rfl
    obtain ⟨m,t,ht⟩ := ((isLocalizing_iff_aux M).mp hloc).existence (g i) le_top
      (res (schemeBasicOpen (g i)) U hgi s)
    have hzero : res (schemeBasicOpen (g i)) U hgi (res U ⊤ le_top t - g i ^ m • s) = 0 := by
      rw [map_sub, map_smul, res_comp]
      exact sub_eq_zero.mpr ht
    obtain ⟨n,hn⟩ := (aux_of_isCompact M U hU' hloc).uniqueness (g i) hgi _ hzero
    refine ⟨n+m, ?_⟩
    change g i ^ (n+m) • s ∈ (res U ⊤ le_top (M := M)).range
    refine ⟨g i ^ n • t, ?_⟩
    rw [map_smul, pow_add, mul_smul]
    exact sub_eq_zero.mp (by simpa only [smul_sub] using hn)
  obtain ⟨n,hn⟩ := power_in_ideal_of_generator_powers g J hgen
  exact ⟨n,fun a ha => hn ha⟩

end AffineDenominators

end

namespace TildeFlasque
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open AffineDenominators AdicInjective InjectiveRange
universe u
variable {R : CommRingCat.{u}} [IsNoetherianRing R]
variable (M : (Spec R).Modules)

theorem top_surjective (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] (U : (Spec R).Opens) :
    Function.Surjective (res U ⊤ le_top (M := M)) := by
  have hU : IsCompact (U : Set (Spec R)) := NoetherianSpace.isCompact _
  obtain ⟨ι, hι, g, hg⟩ := PrimeSpectrum.isBasis_basic_opens.exists_iSup_eq_of_isCompact U hU
  let := hι
  let I : Ideal R := Ideal.span (Set.range g)
  let r := res U ⊤ le_top (M := M)
  have hk : r.ker = adicTorsion I Γ(M,⊤) := by
    ext s
    change r s = 0 ↔ s ∈ adicTorsion I Γ(M,⊤)
    rw [mem_adicTorsion]
    exact ⟨kernel_is_torsion g U hg hloc s, torsion_in_kernel g U hg s⟩
  have hi : Module.Injective R (adicTorsion I Γ(M,⊤)) := adicTorsion_injective I Γ(M,⊤)
  let : Module.Injective R r.ker := Module.Baer.injective
    (Module.Baer.of_equiv (LinearEquiv.ofEq _ _ hk.symm) (Module.Baer.of_injective hi))
  apply surjective_of_torsion_cokernel I r
  · exact fun s => cokernel_is_torsion g U hg hU hloc s
  · exact fun s => torsion_free g U hg s

theorem flasque_of_injective_global (hloc : IsLocalizing (modulesSpecToSheaf.obj M))
    [Module.Injective R Γ(M,⊤)] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    intro s
    obtain ⟨t,ht⟩ := top_surjective M hloc V.unop s
    refine ⟨res U.unop ⊤ le_top t, ?_⟩
    change res V.unop U.unop (leOfHom i.unop) (res U.unop ⊤ le_top t) = s
    rw [res_comp]
    exact ht

instance tilde_injective_isFlasque (N : ModuleCat.{u} R) [Module.Injective R N] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (Spec R).ringCatSheaf).obj (tilde N)) := by
  let : Module.Injective R Γ(tilde N,⊤) := Module.Baer.injective
    (Module.Baer.of_equiv (asIso (tilde.toOpen N ⊤)).toLinearEquiv
      (Module.Baer.of_injective inferInstance))
  exact flasque_of_injective_global (tilde N) (isLocalizing_tilde N)

end TildeFlasque

namespace TildeExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {R : CommRingCat.{u}}

instance map_mono {M N : ModuleCat.{u} R} (f : M ⟶ N) [Mono f] : Mono (tilde.map f) := by
  apply (SheafOfModules.forget _).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U s t h
  apply Subtype.ext
  funext x
  apply LocalizedModule.map_injective x.1.asIdeal.primeCompl f.hom
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
  exact congrFun (congrArg Subtype.val h) x

instance preservesMonomorphisms : (tilde.functor R).PreservesMonomorphisms where
  preserves f _ := map_mono f

instance preservesHomology : (tilde.functor R).PreservesHomology :=
  (tilde.functor R).preservesHomology_of_preservesMonos_and_cokernels

instance preservesFiniteLimits : PreservesFiniteLimits (tilde.functor R) :=
  (tilde.functor R).preservesFiniteLimits_of_preservesHomology

end TildeExact

namespace ModuleGrothendieck
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] (R₀ : Cᵒᵖ ⥤ RingCat.{u})

instance presheafAB5 : AB5 (PresheafOfModules.{u} R₀) where
  ofShape J _ _ := HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf R₀)

instance presheafHasSeparator : HasSeparator (PresheafOfModules.{u} R₀) :=
  ⟨⟨∐ (yoneda ⋙ PresheafOfModules.free R₀).obj,
    (PresheafOfModules.freeYoneda.isSeparating R₀).isSeparator_coproduct⟩⟩

instance presheafGrothendieck : IsGrothendieckAbelian.{u} (PresheafOfModules.{u} R₀) where

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{u}]

instance sheafAB5 : AB5 (SheafOfModules.{u} R) where
  ofShape K _ _ :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K

lemma freeSheafSeparating :
    ObjectProperty.IsSeparating (.ofObj (fun U : C =>
      (PresheafOfModules.sheafification (𝟙 R.obj)).obj
        ((PresheafOfModules.free R.obj).obj (yoneda.obj U)))) := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  intro M N f g h
  apply (SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map_injective
  apply PresheafOfModules.freeYoneda.isSeparating R.obj
  intro P hP a
  obtain ⟨U⟩ := hP
  obtain ⟨b, rfl⟩ := (adj.homEquiv _ _).surjective a
  rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_right]
  exact congrArg (adj.homEquiv _ _) (h _ ⟨U⟩ b)

instance sheafHasSeparator : HasSeparator (SheafOfModules.{u} R) :=
  ⟨⟨∐ (fun U : C => (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))),
    (freeSheafSeparating R).isSeparator_coproduct⟩⟩

instance sheafGrothendieck : IsGrothendieckAbelian.{u} (SheafOfModules.{u} R) where

theorem enoughInjectives : EnoughInjectives (SheafOfModules.{u} R) := inferInstance

end ModuleGrothendieck

namespace ModuleFlasque
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

abbrev freeOpen (U : Opens X) : SheafOfModules.{u} R :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).obj
    ((PresheafOfModules.free R.obj).obj (yoneda.obj U))

abbrev freeOpenMap {U V : Opens X} (i : U ⟶ V) : freeOpen R U ⟶ freeOpen R V :=
  (PresheafOfModules.sheafification (𝟙 R.obj)).map
    ((PresheafOfModules.free R.obj).map (yoneda.map i))

lemma freeMap_mono {F G : (Opens X)ᵒᵖ ⥤ Type u} (f : F ⟶ G) [Mono f] :
    Mono ((PresheafOfModules.free R.obj).map f) := by
  apply PresheafOfModules.mono_of_injective
  intro W
  change Function.Injective (Finsupp.mapDomain (f.app W))
  exact Finsupp.mapDomain_injective ((CategoryTheory.mono_iff_injective (f.app W)).mp
    inferInstance)

instance freeOpenMap_mono {U V : Opens X} (i : U ⟶ V) : Mono (freeOpenMap R i) := by
  let := freeMap_mono R (yoneda.map i)
  dsimp [freeOpenMap]
  infer_instance

def freeOpenEquiv (M : SheafOfModules.{u} R) (U : Opens X) :
    (freeOpen R U ⟶ M) ≃ M.val.obj (op U) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).trans
    PresheafOfModules.freeYonedaEquiv

lemma freeYoneda_naturality {M : PresheafOfModules.{u} R.obj} {U V : Opens X}
    (i : U ⟶ V) (f : (PresheafOfModules.free R.obj).obj (yoneda.obj V) ⟶ M) :
    PresheafOfModules.freeYonedaEquiv
      ((PresheafOfModules.free R.obj).map (yoneda.map i) ≫ f) =
      M.map i.op (PresheafOfModules.freeYonedaEquiv f) := by
  have h := (PresheafOfModules.freeAdjunction R.obj).homEquiv_naturality_left
    (yoneda.map i) f
  simp only [PresheafOfModules.freeAdjunction_homEquiv] at h
  exact (congrArg yonedaEquiv h).trans
    (yonedaEquiv_naturality (PresheafOfModules.freeHomEquiv f) i).symm

lemma freeOpenEquiv_naturality (M : SheafOfModules.{u} R) {U V : Opens X}
    (i : U ⟶ V) (f : freeOpen R V ⟶ M) :
    freeOpenEquiv R M U (freeOpenMap R i ≫ f) =
      M.val.map i.op (freeOpenEquiv R M V f) := by
  unfold freeOpenEquiv
  dsimp only [Equiv.trans_apply]
  change PresheafOfModules.freeYonedaEquiv
    ((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).homEquiv _ _ (_ ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact freeYoneda_naturality R i
    ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)) f)

theorem restriction_surjective (M : SheafOfModules.{u} R) [Injective M]
    {U V : Opens X} (i : U ⟶ V) : Function.Surjective (M.val.map i.op) := by
  intro s
  let f := (freeOpenEquiv R M U).symm s
  obtain ⟨g, hg⟩ := Injective.factors f (freeOpenMap R i)
  refine ⟨freeOpenEquiv R M V g, ?_⟩
  rw [← freeOpenEquiv_naturality, hg]
  exact (freeOpenEquiv R M U).apply_symm_apply s

instance injective_isFlasque (M : SheafOfModules.{u} R) [Injective M] :
    TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective R M i.unop

end ModuleFlasque

abbrev schemeFreeOpen (X : AlgebraicGeometry.Scheme) (U : X.Opens) : X.Modules :=
  ModuleFlasque.freeOpen X.ringCatSheaf U

namespace ModuleSheafExact
open CategoryTheory CategoryTheory.Limits
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]

instance toSheafPreservesColimit {K : Type u} [Category.{u} K]
    (D : K ⥤ SheafOfModules.{u} R) : PreservesColimit D (SheafOfModules.toSheaf R) := by
  let F := PresheafOfModules.sheafification (𝟙 R.obj)
  let G := SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
  let H := SheafOfModules.toSheaf R
  let adj : F ⊣ G := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
  have : PreservesColimitsOfSize.{u,u} (F ⋙ H) :=
    inferInstanceAs (PreservesColimitsOfSize.{u,u}
      (PresheafOfModules.toPresheaf R.obj ⋙ presheafToSheaf J AddCommGrpCat))
  have : PreservesColimit (D ⋙ G ⋙ F) H :=
    preservesColimit_of_preserves_colimit_cocone
      (isColimitOfPreserves F (colimit.isColimit (D ⋙ G)))
      (isColimitOfPreserves (F ⋙ H) (colimit.isColimit (D ⋙ G)))
  exact preservesColimit_of_iso_diagram H
    ((Functor.isoWhiskerLeft D (asIso adj.counit)) ≪≫ D.rightUnitor)

instance toSheafPreservesColimits :
    PreservesColimitsOfSize.{u,u} (SheafOfModules.toSheaf.{u} R) where
  preservesColimitsOfShape := ⟨fun {_} => inferInstance⟩

theorem shortExact_map {S : ShortComplex (SheafOfModules.{u} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := hS.map_of_exact _

end ModuleSheafExact

namespace FlasqueCohomology
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Abelian
universe u
variable {X : TopCat.{u}}
  (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def sectionsTopEquiv (M : SheafOfModules.{u} R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def globalHomEquiv (M : SheafOfModules.{u} R) :
    (SheafOfModules.unit R ⟶ M) ≃ M.val.obj (op ⊤) :=
  M.unitHomEquiv.trans (sectionsTopEquiv R M)

lemma globalHomEquiv_comp {M N : SheafOfModules.{u} R}
    (f : SheafOfModules.unit R ⟶ M) (g : M ⟶ N) :
    globalHomEquiv R N (f ≫ g) = g.val.app (op ⊤) (globalHomEquiv R M f) := rfl

theorem globalHom_surjective {S : ShortComplex (SheafOfModules.{u} R)}
    (hS : S.ShortExact)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)] :
    Function.Surjective (fun f : SheafOfModules.unit R ⟶ S.X₂ => f ≫ S.g) := by
  have h := ModuleSheafExact.shortExact_map R hS
  let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
    ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₁)›
  have he := TopCat.Sheaf.IsFlasque.epi_of_shortExact (U := ⊤) h
  have hs := (AddCommGrpCat.epi_iff_surjective
    (((SheafOfModules.toSheaf R).map S.g).hom.app (op ⊤))).mp he
  intro f
  obtain ⟨t, ht⟩ := hs (globalHomEquiv R S.X₃ f)
  let t' : S.X₂.val.obj (op ⊤) := t
  have ht' : S.g.val.app (op ⊤) t' = globalHomEquiv R S.X₃ f := ht
  refine ⟨(globalHomEquiv R S.X₂).symm t', ?_⟩
  apply (globalHomEquiv R S.X₃).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  exact ht'

instance moduleSheafHasExt : HasExt.{u+1} (SheafOfModules.{u} R) :=
  HasExt.standard _

theorem flasque_ext_zero (n : ℕ) (M : SheafOfModules.{u} R)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)]
    (x : Ext.{u+1} (SheafOfModules.unit R) M (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g, rfl⟩ := globalHom_surjective R hS f
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      hS.comp_extClass, Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₁) :=
      ‹TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj M)›
    let : TopCat.Sheaf.IsFlasque ((S.map (SheafOfModules.toSheaf R)).X₂) :=
      ModuleFlasque.injective_isFlasque R (Injective.under M)
    have : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj S.X₃) :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂
        (ModuleSheafExact.shortExact_map R hS)
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (SheafOfModules.unit R) hS x
      (Ext.eq_zero_of_injective _) rfl
    rw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

end FlasqueCohomology

namespace AffineCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open FlasqueCohomology
universe u
variable {R : CommRingCat.{u}}

lemma globalHom_tilde_surjective {M N : ModuleCat.{u} R} (g : M ⟶ N) [Epi g] :
    Function.Surjective (fun f : schemeUnit (Spec R) ⟶ tilde M =>
      f ≫ tilde.map g) := by
  intro f
  obtain ⟨q,hq⟩ := (ConcreteCategory.bijective_of_isIso (tilde.toOpen N ⊤)).surjective
    (globalHomEquiv (Spec R).ringCatSheaf (tilde N) f)
  obtain ⟨p,hp⟩ := (ModuleCat.epi_iff_surjective g).mp inferInstance q
  refine ⟨(globalHomEquiv (Spec R).ringCatSheaf (tilde M)).symm (tilde.toOpen M ⊤ p), ?_⟩
  apply (globalHomEquiv (Spec R).ringCatSheaf (tilde N)).injective
  erw [globalHomEquiv_comp, Equiv.apply_symm_apply]
  change ((modulesSpecToSheaf.map (tilde.map g)).hom.app (op ⊤)) (tilde.toOpen M ⊤ p) = _
  have h := CategoryTheory.congr_fun (tilde.toOpen_map_app g ⊤) p
  exact h.trans (by change tilde.toOpen N ⊤ (g p) = _; rw [hp, hq])

local instance affineHasExt : HasExt.{u+1} (Spec R).Modules := HasExt.standard _

theorem tilde_ext_zero [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    (x : Ext.{u+1} (C := (Spec R).Modules) (schemeUnit (Spec R)) (tilde M) (n+1)) : x = 0 := by
  induction n generalizing M with
  | zero =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T := S.map (tilde.functor R)
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf 0 (tilde S.X₂) _) rfl
    obtain ⟨f,rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
    obtain ⟨g,rfl⟩ := globalHom_tilde_surjective S.g f
    erw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      show (Ext.mk₀ (tilde.map S.g)).comp hT.extClass rfl = 0 from hT.comp_extClass,
      Ext.comp_zero] at hy
    exact hy.symm
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι M))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    let T := S.map (tilde.functor R)
    have hT : T.ShortExact := hS.map (tilde.functor R)
    let : Injective S.X₂ := (inferInstance : Injective (Injective.under M))
    let : Module.Injective R S.X₂ := Module.injective_module_of_injective_object R S.X₂
    obtain ⟨y,hy⟩ := Ext.covariant_sequence_exact₁ _ hT x
      (flasque_ext_zero (Spec R).ringCatSheaf (n+1) (tilde S.X₂) _) rfl
    erw [ih S.X₃ y, Ext.zero_comp] at hy
    exact hy.symm

theorem quasicoherent_ext_zero [IsNoetherianRing R] (n : ℕ) (M : (Spec R).Modules)
    [M.IsQuasicoherent]
    (x : Ext.{u+1} (C := (Spec R).Modules) (schemeUnit (Spec R)) M (n+1)) : x = 0 := by
  let e := asIso M.fromTildeΓ
  have hx := tilde_ext_zero n _ (x.comp (Ext.mk₀ e.inv) (add_zero _))
  have h := congrArg (fun y => y.comp (Ext.mk₀ e.hom) (add_zero (n+1))) hx
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
    e.inv_hom_id, Ext.comp_mk₀_id, Ext.zero_comp] using h

end AffineCohomology

namespace RestrictionExact
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

instance restriction_mono {M N : Y.Modules} (g : M ⟶ N) [Mono g] :
    Mono ((Scheme.Modules.restrictFunctor f).map g) := by
  apply (Scheme.Modules.toPresheafOfModules X).mono_of_mono_map
  apply PresheafOfModules.mono_of_injective
  intro U
  let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules Y).map g))
  exact PresheafOfModules.injective_of_mono g.val (op (f ''ᵁ U.unop))

instance restriction_preservesMonomorphisms :
    (Scheme.Modules.restrictFunctor f).PreservesMonomorphisms where
  preserves g _ := restriction_mono f g

instance restriction_additive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext; rfl

instance restriction_preservesHomology :
    (Scheme.Modules.restrictFunctor f).PreservesHomology :=
  (Scheme.Modules.restrictFunctor f).preservesHomology_of_preservesMonos_and_cokernels

instance restriction_preservesFiniteLimits :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor f) :=
  (Scheme.Modules.restrictFunctor f).preservesFiniteLimits_of_preservesHomology

instance restriction_flasque (M : Y.Modules)
    [TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf Y.ringCatSheaf).obj M)] :
    TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj (M.restrict f)) where
  epi {U V} i := by
    change Epi (((SheafOfModules.toSheaf Y.ringCatSheaf).obj M).obj.map
      (f.opensFunctor.map i.unop).op)
    exact TopCat.Presheaf.IsFlasque.epi _

end RestrictionExact

namespace AffineSchemeCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open Scheme.Modules
universe u

def restrictionEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (restrictFunctor e.hom) (restrictFunctor e.inv)
    ((restrictFunctorId (X := Y)).symm ≪≫ (restrictFunctorCongr e.inv_hom_id).symm ≪≫
      restrictFunctorComp e.inv e.hom)
    ((restrictFunctorComp e.hom e.inv).symm ≪≫ restrictFunctorCongr e.hom_inv_id ≪≫
      restrictFunctorId (X := X))

local instance hasExtScheme (X : Scheme.{u}) : HasExt.{u+1} X.Modules := HasExt.standard _

theorem affine_ext_zero (X : Scheme.{u}) [IsAffine X] [IsNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+1)) : x = 0 := by
  let : IsNoetherianRing Γ(X, ⊤) := IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  let E := restrictionEquivalence X.isoSpec.symm
  let F := E.functor
  let : F.Additive := RestrictionExact.restriction_additive _
  let : EnoughInjectives X.Modules := ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  let e := restrictUnitIso X.isoSpec.inv
  let z : Ext.{u+1} (F.obj (schemeUnit X)) (F.obj M) (n+1) :=
    x.mapExactFunctor F
  have hz : z = 0 := by
    have hw := AffineCohomology.quasicoherent_ext_zero n (M.restrict X.isoSpec.inv)
      ((Ext.mk₀ e.inv).comp z (zero_add _))
    have h := congrArg (fun y => (Ext.mk₀ e.hom).comp y (zero_add (n+1))) hw
    erw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp,
      Ext.comp_zero] at h
    exact h
  have hb : Function.Injective (F.mapExtAddHom (schemeUnit X) M (n+1) :
      Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+1) →
      Ext.{u+1} (F.obj (schemeUnit X)) (F.obj M) (n+1)) :=
    (F.mapExt_bijective_of_preservesInjectiveObjects _ _ (n+1)).injective
  apply hb
  simpa only [Functor.mapExtAddHom_apply, Ext.mapExactFunctor_zero] using hz

end AffineSchemeCohomology

namespace ExtSectionComparison
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
universe w w' v v' u u'
variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [HasExt.{w} C] [HasExt.{w'} D] {A : C} {B : D} (e : B ⟶ F.obj A)

def mapFrom (Y : C) (n : ℕ) : Ext.{w} A Y n →+ Ext.{w'} B (F.obj Y) n :=
  ((Ext.mk₀ e).precomp (F.obj Y) (zero_add n)).comp (F.mapExtAddHom A Y n)

lemma mapFrom_apply (Y : C) (n : ℕ) (x : Ext.{w} A Y n) :
    mapFrom F e Y n x = (Ext.mk₀ e).comp (x.mapExactFunctor F) (zero_add n) := rfl

@[simp] lemma mapFrom_mk₀ {Y : C} (f : A ⟶ Y) :
    mapFrom F e Y 0 (Ext.mk₀ f) = Ext.mk₀ (e ≫ F.map f) := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

lemma mapFrom_comp {Y Z : C} {n m k : ℕ} (x : Ext.{w} A Y n)
    (y : Ext.{w} Y Z m) (h : n+m=k) :
    mapFrom F e Z k (x.comp y h) =
      (mapFrom F e Y n x).comp (y.mapExactFunctor F) h := by
  simp only [mapFrom_apply, Ext.mapExactFunctor_comp]
  exact (Ext.comp_assoc _ _ _ (zero_add _) h (by omega)).symm

theorem mapFrom_bijective [EnoughInjectives C]
    (hhom : ∀ Y : C, Function.Bijective (fun f : A ⟶ Y => e ≫ F.map f))
    (hacyclic : ∀ (I : C) [Injective I] (n : ℕ)
      (x : Ext.{w'} B (F.obj I) (n+1)), x = 0)
    (Y : C) (n : ℕ) : Function.Bijective (mapFrom F e Y n) := by
  induction n generalizing Y with
  | zero =>
    constructor
    · intro x y h
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective _ _).surjective y
      rw [mapFrom_mk₀, mapFrom_mk₀] at h
      exact congrArg Ext.mk₀ ((hhom Y).injective ((Ext.mk₀_bijective _ _).injective h))
    · intro x
      obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective _ _).surjective x
      obtain ⟨g, rfl⟩ := (hhom Y).surjective f
      exact ⟨Ext.mk₀ g, mapFrom_mk₀ F e g⟩
  | succ n ih =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    let : Injective S.X₂ := I.injective
    refine AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (mapFrom F e S.X₂ n) (mapFrom F e S.X₃ n) (mapFrom F e S.X₁ (n+1))
      ?_ ?_
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A hS n (n+1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' B (hS.map F) n (n+1) rfl))
      (ih _).surjective (ih _)
      (fun x => Ext.covariant_sequence_exact₁ A hS x (Ext.eq_zero_of_injective _) rfl)
      (fun x => Ext.covariant_sequence_exact₁ B (hS.map F) x (hacyclic S.X₂ n _) rfl)
    · ext x
      symm
      change mapFrom F e _ _ (x.comp (Ext.mk₀ S.g) (add_zero n)) =
        (mapFrom F e _ _ x).comp (Ext.mk₀ (F.map S.g)) (add_zero n)
      rw [mapFrom_comp, Ext.mapExactFunctor_mk₀]
    · ext x
      symm
      change mapFrom F e _ _ (x.comp hS.extClass rfl) =
        (mapFrom F e _ _ x).comp (hS.map F).extClass rfl
      rw [mapFrom_comp, Ext.mapExactFunctor_extClass]

end ExtSectionComparison

namespace RestrictionCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Abelian
open ModuleFlasque FlasqueCohomology
universe u
variable {X : Scheme.{u}} (U : X.Opens)

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

lemma freeOpenEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    freeOpenEquiv X.ringCatSheaf N U (f ≫ g) =
      g.val.app (op U) (freeOpenEquiv X.ringCatSheaf M U f) := rfl

def restrictionSectionsIso (M : X.Modules) : Γ(M.restrict U.ι,⊤) ≅ Γ(M,U) :=
  M.restrictAppIso U.ι ⊤ ≪≫ M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op

def restrictionHomEquiv (M : X.Modules) :
    (schemeFreeOpen X U ⟶ M) ≃
      (schemeUnit U.toScheme ⟶ M.restrict U.ι) :=
  (freeOpenEquiv X.ringCatSheaf M U).trans
    ((restrictionSectionsIso U M).addCommGroupIsoToAddEquiv.toEquiv.symm.trans
      (globalHomEquiv U.toScheme.ringCatSheaf (M.restrict U.ι)).symm)

lemma restrictionHomEquiv_comp {M N : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) (g : M ⟶ N) :
    restrictionHomEquiv U N (f ≫ g) =
      restrictionHomEquiv U M f ≫ (Scheme.Modules.restrictFunctor U.ι).map g := by
  have hsection (P : X.Modules) (h : schemeFreeOpen X U ⟶ P) :
      globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι) (restrictionHomEquiv U P h) =
        (restrictionSectionsIso U P).inv (freeOpenEquiv X.ringCatSheaf P U h) := by
    simp only [restrictionHomEquiv]
    exact (globalHomEquiv U.toScheme.ringCatSheaf (P.restrict U.ι)).apply_symm_apply _
  apply (globalHomEquiv U.toScheme.ringCatSheaf (N.restrict U.ι)).injective
  erw [globalHomEquiv_comp, hsection, hsection, freeOpenEquiv_comp]
  change (restrictionSectionsIso U N).inv (g.val.app (op U)
    (freeOpenEquiv X.ringCatSheaf M U f)) =
    ((Scheme.Modules.restrictFunctor U.ι).map g).val.app (op ⊤)
      ((restrictionSectionsIso U M).inv (freeOpenEquiv X.ringCatSheaf M U f))
  exact (CategoryTheory.congr_fun (g.mapPresheaf.naturality
    (eqToHom U.ι_image_top).op) _).symm

def restrictionGenerator : schemeUnit U.toScheme ⟶
    (Scheme.Modules.restrictFunctor U.ι).obj (schemeFreeOpen X U) :=
  restrictionHomEquiv U _ (𝟙 _)

lemma restrictionGenerator_comp {M : X.Modules}
    (f : schemeFreeOpen X U ⟶ M) :
    restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f =
      restrictionHomEquiv U M f := by
  simpa only [restrictionGenerator, Category.id_comp] using
    (restrictionHomEquiv_comp U (𝟙 _) f).symm

theorem restriction_ext_bijective (M : X.Modules) (n : ℕ) :
    Function.Bijective
      (ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
        (restrictionGenerator U) M n :
        Ext.{u+1} (C := X.Modules) (schemeFreeOpen X U) M n →+
          Ext.{u+1} (C := U.toScheme.Modules) (schemeUnit U.toScheme) (M.restrict U.ι) n) := by
  let : EnoughInjectives X.Modules :=
    ModuleGrothendieck.enoughInjectives X.ringCatSheaf
  apply ExtSectionComparison.mapFrom_bijective
  · intro N
    have heq : (fun f : schemeFreeOpen X U ⟶ N =>
        restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f) =
        restrictionHomEquiv U N := funext (restrictionGenerator_comp U)
    change Function.Bijective (fun f : schemeFreeOpen X U ⟶ N =>
      restrictionGenerator U ≫ (Scheme.Modules.restrictFunctor U.ι).map f)
    rw [heq]
    exact (restrictionHomEquiv U N).bijective
  · intro I hI n x
    let : Injective (C := SheafOfModules X.ringCatSheaf) I := hI
    let : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj I) :=
      ModuleFlasque.injective_isFlasque X.ringCatSheaf I
    exact flasque_ext_zero U.toScheme.ringCatSheaf n (I.restrict U.ι) x

end RestrictionCohomology

namespace ModuleMayerVietoris
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque
universe u w
variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeOpenFunctor : Opens X ⥤ SheafOfModules.{u} R :=
  yoneda ⋙ PresheafOfModules.free R.obj ⋙ PresheafOfModules.sheafification (𝟙 R.obj)

lemma freeOpen_isPushout (U V : Opens X) :
    ((Opens.mayerVietorisSquare U V).toSquare.map (freeOpenFunctor R)).IsPushout := by
  rw [Square.isPushout_iff_op_map_yoneda_isPullback]
  intro M
  have h := (Opens.mayerVietorisSquare U V).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology X) (forget AddCommGrpCat)).obj
      ((SheafOfModules.toSheaf R).obj M))
  apply (Square.IsPullback.iff_of_equiv _ _
    (freeOpenEquiv R M (U ⊔ V)) (freeOpenEquiv R M U)
    (freeOpenEquiv R M V) (freeOpenEquiv R M (U ⊓ V))
    ?_ ?_ ?_ ?_).mpr h
  all_goals
    ext f
    exact freeOpenEquiv_naturality R M _ f

def shortComplex (U V : Opens X) : ShortComplex (SheafOfModules.{u} R) where
  X₁ := freeOpen R (U ⊓ V)
  X₂ := freeOpen R U ⊞ freeOpen R V
  X₃ := freeOpen R (U ⊔ V)
  f := biprod.lift (freeOpenMap R (homOfLE inf_le_left))
    (-(freeOpenMap R (homOfLE inf_le_right)))
  g := biprod.desc (freeOpenMap R (homOfLE le_sup_left))
    (freeOpenMap R (homOfLE le_sup_right))
  zero := ((Opens.mayerVietorisSquare U V).toSquare.map
    (freeOpenFunctor R)).cokernelCofork.condition

instance shortComplex_mono (U V : Opens X) : Mono (shortComplex R U V).f := by
  have : Mono ((shortComplex R U V).f ≫ biprod.snd) := by
    dsimp [shortComplex]
    simp only [biprod.lift_snd]
    infer_instance
  exact mono_of_mono _ biprod.snd

lemma shortComplex_shortExact (U V : Opens X) : (shortComplex R U V).ShortExact := by
  have h := (freeOpen_isPushout R U V).isColimitCokernelCofork
  have he : (shortComplex R U V).Exact ∧ Epi (shortComplex R U V).g :=
    (shortComplex R U V).exact_and_epi_g_iff_g_is_cokernel.mpr ⟨h⟩
  let := he.2
  exact ⟨he.1⟩

variable [HasExt.{w} (SheafOfModules.{u} R)]

lemma union_ext_zero (U V : Opens X) (M : SheafOfModules.{u} R) (n : ℕ)
    (hU : ∀ x : Ext (freeOpen R U) M (n+1), x = 0)
    (hV : ∀ x : Ext (freeOpen R V) M (n+1), x = 0)
    (hUV : ∀ x : Ext (freeOpen R (U ⊓ V)) M n, x = 0)
    (x : Ext (freeOpen R (U ⊔ V)) M (n+1)) : x = 0 := by
  have hS := shortComplex_shortExact R U V
  have hmid (y : Ext (freeOpen R U ⊞ freeOpen R V) M (n+1)) : y = 0 := by
    apply Ext.biprodAddEquiv.injective
    apply Prod.ext
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_fst, Prod.fst_zero] using
        hU ((Ext.mk₀ biprod.inl).comp y (zero_add _))
    · simpa only [map_zero, Ext.biprodAddEquiv_apply_snd, Prod.snd_zero] using
        hV ((Ext.mk₀ biprod.inr).comp y (zero_add _))
  obtain ⟨z, hz⟩ := Ext.contravariant_sequence_exact₃ hS M x (hmid _) (n₀ := n) (by omega)
  have hz0 : z = 0 := hUV z
  rw [hz0, Ext.comp_zero] at hz
  exact hz.symm

end ModuleMayerVietoris

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]

local instance hasExtScheme (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

theorem affine_open_ext_zero (U : X.Opens) (hU : IsAffineOpen U)
    (M : X.Modules) [M.IsQuasicoherent] (n : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X U) M (n+1)) : x = 0 := by
  let : IsAffine U := hU
  let : IsNoetherian U := ⟨⟩
  let f := ExtSectionComparison.mapFrom (Scheme.Modules.restrictFunctor U.ι)
    (RestrictionCohomology.restrictionGenerator U) M (n+1)
  apply (RestrictionCohomology.restriction_ext_bijective U M (n+1)).injective
  change f x = f 0
  rw [map_zero]
  exact AffineSchemeCohomology.affine_ext_zero U (M.restrict U.ι) n (f x)

variable [IsAffineHom (pullback.diagonal (terminal.from X))]

theorem affine_union_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X (⨆ i, U i)) M (n+k+1)) : x = 0 := by
  induction n generalizing k with
  | zero =>
    have hsup : (⨆ i, U i) = U 0 := by
      apply le_antisymm
      · apply iSup_le
        intro i
        have hi : i = 0 := Fin.ext (by omega)
        subst i
        exact le_rfl
      · exact le_iSup U 0
    revert x
    rw [hsup]
    exact affine_open_ext_zero (U 0) (hU 0) M (0+k)
  | succ n ih =>
    have hsup : (⨆ i, U i) = U 0 ⊔ ⨆ i : Fin (n+1), U i.succ :=
      le_antisymm (iSup_le (Fin.cases le_sup_left (fun i =>
        (le_iSup (fun i : Fin (n+1) => U i.succ) i).trans le_sup_right)))
        (sup_le (le_iSup U 0) (iSup_le (fun i => le_iSup U i.succ)))
    have hinf : U 0 ⊓ (⨆ i : Fin (n+1), U i.succ) =
        ⨆ i : Fin (n+1), U 0 ⊓ U i.succ := inf_iSup_eq _ _
    revert x
    rw [hsup, show n+1+k+1 = n+k+1+1 from by omega]
    intro x
    apply ModuleMayerVietoris.union_ext_zero X.ringCatSheaf (U 0)
      (⨆ i : Fin (n+1), U i.succ) M (n+k+1) ?_ ?_ ?_ x
    · intro y
      exact affine_open_ext_zero (U 0) (hU 0) M (n+k+1) y
    · intro y
      exact ih (fun i => U i.succ) (fun i => hU i.succ) (k+1) y
    · rw [hinf]
      intro y
      exact ih (fun i => U 0 ⊓ U i.succ) (fun i => (hU 0).inf (hU i.succ)) k y

end FiniteCoverCohomology

namespace FreeOpenUnit
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Abelian
open ModuleFlasque FlasqueCohomology
universe u v

def isoFromHomEquiv {C : Type u} [Category.{v} C] {A B : C}
    (e : ∀ M, (A ⟶ M) ≃ (B ⟶ M))
    (hnat : ∀ {M N} (f : A ⟶ M) (g : M ⟶ N), e N (f ≫ g) = e M f ≫ g) :
    A ≅ B where
  hom := (e B).symm (𝟙 B)
  inv := e A (𝟙 A)
  hom_inv_id := by
    apply (e A).injective
    rw [hnat, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    rw [← hnat, Category.id_comp, Equiv.apply_symm_apply]

variable {X : TopCat.{u}} (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

def freeTopIso : freeOpen R ⊤ ≅ SheafOfModules.unit R :=
  isoFromHomEquiv
    (fun M => (freeOpenEquiv R M ⊤).trans (globalHomEquiv R M).symm)
    (by
      intro M N f g
      apply (globalHomEquiv R N).injective
      simp only [Equiv.trans_apply, Equiv.apply_symm_apply, globalHomEquiv_comp]
      rfl)

end FreeOpenUnit

namespace FiniteCoverCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Abelian
open ModuleFlasque
universe u
variable {X : Scheme.{u}} [IsNoetherian X]
  [IsAffineHom (pullback.diagonal (terminal.from X))]

local instance hasExtScheme' (Y : Scheme.{u}) : HasExt.{u+1} Y.Modules := HasExt.standard _

theorem cover_ext_zero (n : ℕ) (U : Fin (n+1) → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (hcover : (⨆ i, U i) = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (k : ℕ)
    (x : Ext.{u+1} (C := X.Modules) (schemeUnit X) M (n+k+1)) : x = 0 := by
  let e := FreeOpenUnit.freeTopIso X.ringCatSheaf
  have hz : ∀ z : Ext.{u+1} (C := X.Modules) (schemeFreeOpen X ⊤) M (n+k+1), z = 0 := by
    rw [← hcover]
    exact affine_union_ext_zero n U hU M k
  have h := congrArg (fun y => (Ext.mk₀ e.inv).comp y (zero_add (n+k+1)))
    (hz ((Ext.mk₀ e.hom).comp x (zero_add _)))
  erw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp,
    Ext.comp_zero] at h
  exact h

end FiniteCoverCohomology

end PiExponentSeshadri

end

end OAI
end Source0311

-- Source: OAI/NumberTheory/PiExponent/Geometry/LineBundleTensor.lean
section Source0312
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable (X : Scheme)

structure LineBundle where
  sheaf : X.Modules
  locallyRankOne : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    Nonempty (sheaf.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

def moduleTensor (M N : X.Modules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val)

def modulePow (M : X.Modules) : ℕ → X.Modules
  | 0 => SheafOfModules.unit X.ringCatSheaf
  | n + 1 => moduleTensor X M (modulePow M n)

def structureSheaf : X.Modules := SheafOfModules.unit X.ringCatSheaf

abbrev GlobalSections (M : X.Modules) := structureSheaf X ⟶ M

def sectionOpen {M : X.Modules} (s : GlobalSections X M) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)), U

def LineBundle.IsAmple (L : LineBundle X) : Prop :=
  ∀ (x : X) (V : X.Opens), x ∈ V → ∃ n : ℕ, 0 < n ∧
    ∃ s : GlobalSections X (modulePow X L.sheaf n),
      x ∈ sectionOpen X s ∧ sectionOpen X s ≤ V ∧ IsAffineOpen (sectionOpen X s)

end Geometry

open CategoryTheory
open CategoryTheory.Category CategoryTheory.Functor
universe v u v₁ v₂ u₁ u₂
namespace ModulePresheaf
open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {F G : C ⥤ D} {T : Cᵒᵖ ⥤ RingCat.{u}} {S : Dᵒᵖ ⥤ RingCat.{u}}

def pushforwardCongr {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ) :
    pushforward.{v} φ ≅ pushforward.{v} ψ :=
  NatIso.ofComponents (fun M ↦
    PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsCongr (by subst h; rfl)).app _)
      (fun _ _ _ ↦ by subst h; rfl)) (fun _ ↦ by subst h; rfl)

@[simp] lemma pushforwardCongr_hom_app {φ ψ : T ⟶ F.op ⋙ S} (h : φ = ψ)
    (M : PresheafOfModules.{v} S) (U) (x) :
    ((pushforwardCongr h).hom.app M).app U x = x := by
  subst h
  rfl

def pushforwardNatTrans (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) :
    pushforward.{v} φ ⟶
      pushforward.{v} (φ ≫ whiskerRight (NatTrans.op α) S) where
  app M := {
    app U := (ModuleCat.restrictScalars (φ.app U).hom).map (M.map (α.app U.unop).op)
    naturality {U V} i := by
      ext x
      change (M.presheaf.map (G.map i.unop).op ≫ M.presheaf.map (α.app V.unop).op) _ =
        (M.presheaf.map (α.app U.unop).op ≫ M.presheaf.map (F.map i.unop).op) _
      simp only [← Functor.map_comp, ← op_comp, α.naturality] }
  naturality {M N} f := by
    ext U x
    exact congr($(f.naturality (α.app U.unop).op) x).symm

@[simp] lemma pushforwardNatTrans_app_app
    (φ : T ⟶ G.op ⋙ S) (α : F ⟶ G) (M U x) :
    ((pushforwardNatTrans φ α).app M).app U x = M.map (α.app U.unop).op x := rfl

variable {F : C ⥤ D} {G : D ⥤ C}
  (adj : F ⊣ G) (φ : T ⟶ F.op ⋙ S) (ψ : S ⟶ G.op ⋙ T)
  (H₁ : whiskerRight (NatTrans.op adj.counit) S = ψ ≫ G.op.whiskerLeft φ)
  (H₂ : φ ≫ F.op.whiskerLeft ψ ≫
    whiskerRight (NatTrans.op adj.unit) T = 𝟙 T)

def pushforwardPushforwardAdj : pushforward.{v} φ ⊣ pushforward.{v} ψ where
  unit := (pushforwardId _).inv ≫ pushforwardNatTrans (𝟙 _) adj.counit ≫
    (pushforwardCongr (by simpa using H₁)).hom ≫ (pushforwardComp _ _).inv
  counit := (pushforwardComp _ _).hom ≫ pushforwardNatTrans _ adj.unit ≫
    (pushforwardCongr (by simpa using H₂)).hom ≫ (pushforwardId _).hom
  left_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (F.map (adj.unit.app U.unop)).op
      (M.map (adj.counit.app (F.obj U.unop)).op x) = x
    change M.obj (Opposite.op (F.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.left_triangle_components, op_id, M.map_id]
    rfl
  right_triangle_components M := by
    ext U x
    simp only [comp_app, ModuleCat.comp_apply,
      pushforwardId, pushforwardComp, Iso.refl_hom, Iso.refl_inv]
    change M.map (adj.unit.app (G.obj U.unop)).op
      (M.map (G.map (adj.counit.app U.unop)).op x) = x
    change M.obj (Opposite.op (G.obj U.unop)) at x
    erw [← M.map_comp_apply, ← op_comp, adj.right_triangle_components, op_id, M.map_id]
    rfl

end ModulePresheaf

namespace Geometry

section
open AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f]

def modulePresheafRestrict : PresheafOfModules Y.ringCatSheaf.obj ⥤
    PresheafOfModules X.ringCatSheaf.obj :=
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  PresheafOfModules.pushforward (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

def modulePresheafRestrictAdjunction : modulePresheafRestrict f ⊣
    PresheafOfModules.pushforward f.toRingCatSheafHom.hom := by
  refine ModulePresheaf.pushforwardPushforwardAdj
    (by exact f.isOpenEmbedding.isOpenMap.adjunction) _ _ ?_ ?_
  · ext U x
    exact congr($((f.app_appIso_inv _).symm).hom x)
  · ext U x
    have h : (f.appIso U.unop).inv ≫ f.app _ ≫
        X.presheaf.map (eqToHom (f.preimage_image_eq U.unop).symm).op = 𝟙 _ := by
      rw [Scheme.Hom.appIso_inv_app_assoc, ← Functor.map_comp, ← X.presheaf.map_id]
      rfl
    exact congr($h x)

def moduleSheafificationRestrict :
    PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj) ⋙
      Scheme.Modules.restrictFunctor f ≅
    modulePresheafRestrict f ⋙
      PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) :=
  Adjunction.leftAdjointUniq
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).comp
      (Scheme.Modules.restrictAdjunction f))
    ((modulePresheafRestrictAdjunction f).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)))

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open MonoidalCategory
variable {X : Scheme}

def modulePresheafRestrictOpensIso (U : X.Opens) :
    modulePresheafRestrict U.ι ≅
      PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf := by
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app V := (U.ι.appIso V.unop).inv }
  have h : Functor.whiskerRight α (forget₂ CommRingCat RingCat) = 𝟙 _ := by
    ext V x
    simp only [Functor.whiskerRight_app, α, Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  exact ModulePresheaf.pushforwardCongr (F := U.ι.opensFunctor)
    (T := U.toScheme.ringCatSheaf.obj) (S := X.ringCatSheaf.obj) h

def modulePresheafTensorRestrict (U : X.Opens)
    (M N : PresheafOfModules X.ringCatSheaf.obj) :
    (modulePresheafRestrict U.ι).obj
        (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M N) ≅
      PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).obj M)
        ((modulePresheafRestrict U.ι).obj N) := by
  letI : MonoidalCategory (PresheafOfModules U.toScheme.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := U.toScheme.presheaf)
  exact (modulePresheafRestrictOpensIso U).app _ ≪≫
    (Functor.Monoidal.μIso
      (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf) M N).symm ≪≫
    tensorIso ((modulePresheafRestrictOpensIso U).symm.app M)
      ((modulePresheafRestrictOpensIso U).symm.app N)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleTensorRestrict (U : X.Opens) (M N : X.Modules) :
    (moduleTensor X M N).restrict U.ι ≅
      moduleTensor U.toScheme (M.restrict U.ι) (N.restrict U.ι) :=
  (moduleSheafificationRestrict U.ι).app _ ≪≫
    (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).mapIso
      (modulePresheafTensorRestrict U M.val N.val)

def moduleTensorIso {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    moduleTensor X M P ≅ moduleTensor X N Q := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (tensorIso ((SheafOfModules.forget _).mapIso e) ((SheafOfModules.forget _).mapIso f))

def moduleTensorUnit (M : X.Modules) :
    moduleTensor X (structureSheaf X) M ≅ M := by
  letI : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (λ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

def modulePowFrame {M : X.Modules} (U : X.Opens)
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
    moduleTensorIso e (modulePowFrame U e n) ≪≫ moduleTensorUnit _

def LineBundle.pow (L : LineBundle X) (n : ℕ) : LineBundle X where
  sheaf := modulePow X L.sheaf n
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨frame⟩⟩ := L.locallyRankOne x
    exact ⟨U, hx, ⟨modulePowFrame U frame n⟩⟩

def moduleTensorMap {M N P Q : X.Modules} (f : M ⟶ N) (g : P ⟶ Q) :
    moduleTensor X M P ⟶ moduleTensor X N Q :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)

@[simp] lemma moduleTensorMap_id (M N : X.Modules) :
    moduleTensorMap (𝟙 M) (𝟙 N) = 𝟙 (moduleTensor X M N) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((𝟙 M.val) ⊗ₘ (𝟙 N.val)) = _
  rw [id_tensorHom_id]
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map_id _

@[reassoc] lemma moduleTensorMap_comp {M N P Q R T : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (h : Q ⟶ R) (k : R ⟶ T) :
    moduleTensorMap (f ≫ g) (h ≫ k) = moduleTensorMap f h ≫ moduleTensorMap g k := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  change (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    ((f.val ≫ g.val) ⊗ₘ (h.val ≫ k.val)) = _
  rw [← tensorHom_comp_tensorHom]
  exact Functor.map_comp _ _ _

instance moduleTensorMap_isIso {M N P Q : X.Modules} (f : M ⟶ N)
    (g : P ⟶ Q) [IsIso f] [IsIso g] : IsIso (moduleTensorMap f g) := by
  refine ⟨⟨moduleTensorMap (inv f) (inv g), ?_, ?_⟩⟩ <;>
    rw [← moduleTensorMap_comp] <;> simp

def modulePowMap {M N : X.Modules} (f : M ⟶ N) :
    ∀ n, modulePow X M n ⟶ modulePow X N n
  | 0 => 𝟙 _
  | n + 1 => moduleTensorMap f (modulePowMap f n)

@[simp] lemma modulePowMap_id (M : X.Modules) (n : ℕ) :
    modulePowMap (𝟙 M) n = 𝟙 (modulePow X M n) := by
  induction n with
  | zero => rfl
  | succ n hn =>
    change moduleTensorMap (𝟙 M) (modulePowMap (𝟙 M) n) = 𝟙 (moduleTensor X M (modulePow X M n))
    rw [hn, moduleTensorMap_id]

@[reassoc] lemma modulePowMap_comp {M N P : X.Modules}
    (f : M ⟶ N) (g : N ⟶ P) (n : ℕ) :
    modulePowMap (f ≫ g) n = modulePowMap f n ≫ modulePowMap g n := by
  induction n with
  | zero => exact (Category.id_comp _).symm
  | succ n hn =>
    change moduleTensorMap (f ≫ g) (modulePowMap (f ≫ g) n) =
      moduleTensorMap f (modulePowMap f n) ≫ moduleTensorMap g (modulePowMap g n)
    rw [hn, moduleTensorMap_comp]

instance modulePowMap_isIso {M N : X.Modules} (f : M ⟶ N) [IsIso f] (n : ℕ) :
    IsIso (modulePowMap f n) := by
  induction n with
  | zero => change IsIso (𝟙 (structureSheaf X)); infer_instance
  | succ n hn => change IsIso (moduleTensorMap f (modulePowMap f n)); infer_instance

def modulePowFunctor (n : ℕ) : X.Modules ⥤ X.Modules where
  obj M := modulePow X M n
  map f := modulePowMap f n
  map_id := fun _ => modulePowMap_id _ n
  map_comp := fun _ _ => modulePowMap_comp _ _ n

def unitPowerIso : ∀ n, modulePow X (structureSheaf X) n ≅ structureSheaf X
  | 0 => Iso.refl _
  | n + 1 => moduleTensorUnit _ ≪≫ unitPowerIso n

def powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    structureSheaf X ⟶ modulePow X M n :=
  (unitPowerIso n).inv ≫ modulePowMap s n

@[simp] lemma powerSection_zero {M : X.Modules} (s : structureSheaf X ⟶ M) :
    powerSection s 0 = 𝟙 (structureSheaf X) := by
  change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X)
  exact Category.id_comp _

instance powerSection_isIso {M : X.Modules} (s : structureSheaf X ⟶ M) [IsIso s] (n : ℕ) :
    IsIso (powerSection s n) := by unfold powerSection; infer_instance

def moduleTensorRightUnit (M : X.Modules) :
    moduleTensor X M (structureSheaf X) ≅ M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (ρ_ M.val) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
      (𝟙 X.ringCatSheaf.obj)).counit).app M

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0312

-- Source: OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficients.lean
section Source0313
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficients.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

universe u

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y Z : Scheme.{u}}
def O (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def endValue (f : O X ⟶ O X) : Γ(X, ⊤) := f.app ⊤ (1 : Γ(X, ⊤))

lemma end_apply (f : O X ⟶ O X) (U : X.Opens) (a : Γ(X, U)) :
    f.app U a = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) := by
  have h := f.app_smul (r := a) (x := (1 : Γ(X, U)))
  change f.app U (a * 1 : Γ(X, U)) = a * (show Γ(X, U) from f.app U (1 : Γ(X, U))) at h
  simpa only [mul_one] using h

@[simp] lemma endValue_id : endValue (𝟙 (O X)) = 1 := rfl

lemma endValue_comp (f g : O X ⟶ O X) :
    endValue (f ≫ g) = endValue f * endValue g := by
  exact end_apply g ⊤ (endValue f)

def frameChange {M : X.Modules} (e f : M ≅ O X) : Γ(X, ⊤)ˣ where
  val := endValue (e.inv ≫ f.hom)
  inv := endValue (f.inv ≫ e.hom)
  val_inv := by rw [← endValue_comp]; simp
  inv_val := by rw [← endValue_comp]; simp

def coefficient {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) : Γ(X, ⊤) :=
  endValue (s ≫ e.hom)

lemma coefficient_change {M : X.Modules} (e f : M ≅ O X) (s : O X ⟶ M) :
    coefficient f s = (frameChange e f : Γ(X, ⊤)) * coefficient e s := by
  change endValue (s ≫ f.hom) = endValue (e.inv ≫ f.hom) * endValue (s ≫ e.hom)
  rw [mul_comm, ← endValue_comp]
  simp

lemma coefficient_frame {M : X.Modules} (e : M ≅ O X) : coefficient e e.inv = 1 := by
  simp [coefficient]

def restrictSection (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (s : O X ⟶ M) : O Y ⟶ M.restrict φ :=
  (Scheme.Modules.restrictUnitIso φ).inv ≫ (Scheme.Modules.restrictFunctor φ).map s

def restrictFrame (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) : M.restrict φ ≅ O Y :=
  (Scheme.Modules.restrictFunctor φ).mapIso e ≪≫ Scheme.Modules.restrictUnitIso φ

lemma end_naturality (f : O X ⟶ O X) (U : X.Opens) :
    f.app U (1 : Γ(X, U)) =
      X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) := by
  have h := CategoryTheory.congr_fun (f.mapPresheaf.naturality
    (homOfLE (show U ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
  change f.app U (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (1 : Γ(X, ⊤))) =
    X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op (endValue f) at h
  simpa only [map_one] using h

lemma endValue_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] (f : O X ⟶ O X) :
    endValue (restrictSection φ f ≫ (Scheme.Modules.restrictUnitIso φ).hom) =
      φ.appTop (endValue f) := by
  change (φ.appIso ⊤).hom (f.app (φ ''ᵁ ⊤) ((φ.appIso ⊤).inv 1)) = _
  rw [map_one, end_naturality]
  change (X.presheaf.map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op ≫
    (φ.appIso ⊤).hom) (endValue f) = _
  rw [Scheme.Hom.appIso_hom']
  simp only [Scheme.Hom.appTop, Scheme.Hom.appLE,
    Scheme.Hom.naturality_assoc, ← Functor.map_comp]
  congr 1
  rw [show ((Opens.map φ.base).map (homOfLE (show φ ''ᵁ ⊤ ≤ ⊤ from le_top)).op.unop).op ≫
      (homOfLE (show (⊤ : Y.Opens) ≤ φ ⁻¹ᵁ (φ ''ᵁ ⊤) from by intro x _; exact ⟨x, Set.mem_univ _, rfl⟩)).op = 𝟙 _ from Subsingleton.elim _ _]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

lemma coefficient_restrict (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules}
    (e : M ≅ O X) (s : O X ⟶ M) :
    coefficient (restrictFrame φ e) (restrictSection φ s) = φ.appTop (coefficient e s) := by
  change endValue ((Scheme.Modules.restrictUnitIso φ).inv ≫
    (Scheme.Modules.restrictFunctor φ).map s ≫
    (Scheme.Modules.restrictFunctor φ).map e.hom ≫
    (Scheme.Modules.restrictUnitIso φ).hom) = _
  erw [← Functor.map_comp_assoc]
  exact endValue_restrict φ (s ≫ e.hom)

lemma restrictUnit_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] :
    (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv ≫
      (Scheme.Modules.restrictFunctorComp φ ψ).hom.app (O Z) =
    (Scheme.Modules.restrictUnitIso φ).inv ≫
      (Scheme.Modules.restrictFunctor φ).map (Scheme.Modules.restrictUnitIso ψ).inv := by
  ext U a
  change Z.presheaf.map (eqToHom (show ψ ''ᵁ (φ ''ᵁ U) = (φ ≫ ψ) ''ᵁ U from by simp)).op
    ((φ ≫ ψ).appIso U |>.inv |>.hom |>.toFun <| a) =
      (ψ.appIso (φ ''ᵁ U)).inv ((φ.appIso U).inv a)
  rw [Scheme.Hom.comp_appIso]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.op_inv, eqToIso.inv]
  change ( (φ.appIso U).inv ≫ (ψ.appIso (φ ''ᵁ U)).inv ≫
    Z.presheaf.map _ ≫ Z.presheaf.map _) a = _
  rw [← CategoryTheory.Functor.map_comp]
  simp
  rfl

lemma restrictSection_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules} (s : O Z ⟶ M) :
    restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M =
      restrictSection φ (restrictSection ψ s) := by
  let F := Scheme.Modules.restrictFunctor φ
  let G := Scheme.Modules.restrictFunctor ψ
  let H := Scheme.Modules.restrictFunctor (φ ≫ ψ)
  let e := Scheme.Modules.restrictFunctorComp φ ψ
  let a : O Y ⟶ H.obj (O Z) := (Scheme.Modules.restrictUnitIso (φ ≫ ψ)).inv
  let b : O Y ⟶ F.obj (O X) := (Scheme.Modules.restrictUnitIso φ).inv
  let c : O X ⟶ G.obj (O Z) := (Scheme.Modules.restrictUnitIso ψ).inv
  change (a ≫ H.map s) ≫ e.hom.app M = b ≫ F.map (c ≫ G.map s)
  calc
    _ = a ≫ (H.map s ≫ e.hom.app M) := Category.assoc _ _ _
    _ = a ≫ (e.hom.app (O Z) ≫ F.map (G.map s)) :=
      congrArg (fun t => a ≫ t) (e.hom.naturality s)
    _ = (a ≫ e.hom.app (O Z)) ≫ F.map (G.map s) := (Category.assoc _ _ _).symm
    _ = (b ≫ F.map c) ≫ F.map (G.map s) :=
      congrArg (fun t => t ≫ F.map (G.map s)) (restrictUnit_comp φ ψ)
    _ = b ≫ (F.map c ≫ F.map (G.map s)) := Category.assoc _ _ _
    _ = _ := congrArg (fun t => b ≫ t) (F.map_comp c (G.map s)).symm

lemma coefficient_transport {M N : X.Modules} (e : M ≅ N) (f : N ≅ O X)
    (s : O X ⟶ M) : coefficient (e ≪≫ f) s = coefficient f (s ≫ e.hom) := by
  simp only [coefficient, Iso.trans_hom, Category.assoc]

lemma coefficient_restrict_comp (φ : Y ⟶ X) (ψ : X ⟶ Z)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : Z.Modules}
    (e : M.restrict ψ ≅ O X) (s : O Z ⟶ M) :
    coefficient ((Scheme.Modules.restrictFunctorComp φ ψ).app M ≪≫ restrictFrame φ e)
      (restrictSection (φ ≫ ψ) s) = φ.appTop (coefficient e (restrictSection ψ s)) := by
  rw [coefficient_transport]
  change coefficient (restrictFrame φ e)
    (restrictSection (φ ≫ ψ) s ≫ (Scheme.Modules.restrictFunctorComp φ ψ).hom.app M) = _
  rw [restrictSection_comp, coefficient_restrict]

lemma restrictSection_congr {φ ψ : Y ⟶ X} (h : φ = ψ)
    [IsOpenImmersion φ] [IsOpenImmersion ψ] {M : X.Modules} (s : O X ⟶ M) :
    restrictSection φ s ≫ (Scheme.Modules.restrictFunctorCongr h).hom.app M =
      restrictSection ψ s := by
  subst ψ
  have H : (Scheme.Modules.restrictFunctorCongr (show φ = φ from rfl)).hom.app M = 𝟙 _ := by
    ext U a
    simp
    rfl
  rw [H, Category.comp_id]

lemma overlap_coefficients {W : Scheme.{u}} (φ : Y ⟶ X) (ψ : Z ⟶ X)
    (a : W ⟶ Y) (b : W ⟶ Z) [IsOpenImmersion φ] [IsOpenImmersion ψ]
    [IsOpenImmersion a] [IsOpenImmersion b] (h : a ≫ φ = b ≫ ψ)
    {M : X.Modules} (e : M.restrict φ ≅ O Y) (f : M.restrict ψ ≅ O Z) :
    ∃ c : Γ(W, ⊤)ˣ, ∀ s : O X ⟶ M,
      b.appTop (coefficient f (restrictSection ψ s)) =
      (c : Γ(W, ⊤)) * a.appTop (coefficient e (restrictSection φ s)) := by
  let E : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorComp a φ).app M ≪≫ restrictFrame a e
  let F : M.restrict (a ≫ φ) ≅ O W :=
    (Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      (Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f
  refine ⟨frameChange E F, fun s => ?_⟩
  have H := coefficient_change E F (restrictSection (a ≫ φ) s)
  have hE : coefficient E (restrictSection (a ≫ φ) s) =
      a.appTop (coefficient e (restrictSection φ s)) := coefficient_restrict_comp a φ e s
  have hF : coefficient F (restrictSection (a ≫ φ) s) =
      b.appTop (coefficient f (restrictSection ψ s)) := by
    change coefficient ((Scheme.Modules.restrictFunctorCongr h).app M ≪≫
      ((Scheme.Modules.restrictFunctorComp b ψ).app M ≪≫ restrictFrame b f)) _ = _
    rw [coefficient_transport]
    change coefficient _ (restrictSection (a ≫ φ) s ≫
      (Scheme.Modules.restrictFunctorCongr h).hom.app M) = _
    rw [restrictSection_congr]
    exact coefficient_restrict_comp b ψ f s
  rwa [hE, hF] at H

end
end PiExponentSeshadri.Frames

end OAI
end Source0313

-- Source: OAI/NumberTheory/PiExponent/Approximation/FrameSections.lean
section Source0314
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

universe u

namespace PiExponentSeshadri.Frames

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

def scalarEnd (r : Γ(X, ⊤)) : O X ⟶ O X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma endValue_scalarEnd (r : Γ(X, ⊤)) : endValue (scalarEnd r) = r := by
  change X.presheaf.map (𝟙 _) r * 1 = r
  simp

lemma endValue_injective : Function.Injective (endValue (X := X)) := by
  intro f g h
  ext U a
  change Γ(X, U) at a
  change f.app U a = g.app U a
  rw [end_apply f U a, end_apply g U a]
  rw [end_naturality f U, end_naturality g U, h]

lemma end_isIso_iff (f : O X ⟶ O X) : IsIso f ↔ IsUnit (endValue f) := by
  constructor
  · intro h
    let := h
    refine isUnit_iff_exists_inv.mpr ⟨endValue (inv f), ?_⟩
    rw [← endValue_comp]
    simp
  · rintro ⟨u, hu⟩
    refine ⟨⟨scalarEnd ↑u⁻¹, ?_, ?_⟩⟩
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.val_inv u
    · apply endValue_injective
      rw [endValue_comp, ← hu, endValue_scalarEnd, endValue_id]
      exact Units.inv_val u

lemma coefficient_isUnit_iff {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    IsUnit (coefficient e s) ↔ IsIso s := by
  change IsUnit (endValue (s ≫ e.hom)) ↔ _
  rw [← end_isIso_iff]
  exact isIso_comp_right_iff s e.hom

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open scoped AlgebraicGeometry
variable {X : Scheme}

def moduleSectionsTopEquiv {T : TopCat} (R : Sheaf (Opens.grothendieckTopology T) RingCat)
    (M : SheafOfModules R) : M.sections ≃ M.val.obj (op ⊤) where
  toFun s := s.val (op ⊤)
  invFun t := PresheafOfModules.sectionsMk
    (fun U => M.val.map (homOfLE le_top).op t)
    (by
      intro U V i
      rw [← M.val.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) t)
  left_inv s := by
    apply PresheafOfModules.sections_ext
    intro U
    exact s.property (homOfLE le_top).op
  right_inv t := by
    change M.val.map (𝟙 (op ⊤)) t = t
    rw [M.val.map_id]
    rfl

def moduleSectionEquiv (M : X.Modules) : (O X ⟶ M) ≃ Γ(M, ⊤) :=
  M.unitHomEquiv.trans (moduleSectionsTopEquiv X.ringCatSheaf M)

@[simp] lemma moduleSectionEquiv_apply (M : X.Modules) (s : O X ⟶ M) :
    moduleSectionEquiv M s = s.app ⊤ (1 : Γ(X, ⊤)) := rfl

def openSectionEquiv (M : X.Modules) (U : X.Opens) :
    (O U.toScheme ⟶ M.restrict U.ι) ≃ Γ(M, U) :=
  (moduleSectionEquiv (M.restrict U.ι)).trans
    (let e := M.presheaf.mapIso (eqToIso U.ι_image_top.symm).op
     { toFun := e.hom
       invFun := e.inv
       left_inv := fun t => Iso.hom_inv_id_apply e t
       right_inv := fun t => Iso.inv_hom_id_apply e t })

lemma section_value_natural {M : X.Modules} (s : O X ⟶ M) {U V : X.Opens} (i : U ⟶ V) :
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) = s.app U (1 : Γ(X, U)) := by
  have h := CategoryTheory.congr_fun (s.mapPresheaf.naturality i.op) (1 : Γ(X, V))
  change s.app U (X.presheaf.map i.op (1 : Γ(X, V))) =
    M.presheaf.map i.op (s.app V (1 : Γ(X, V))) at h
  simpa only [map_one] using h.symm

@[simp] lemma openSectionEquiv_restrict {M : X.Modules} (s : O X ⟶ M) (U : X.Opens) :
    openSectionEquiv M U (restrictSection U.ι s) = s.app U (1 : Γ(X, U)) := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (s.app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme, ⊤)))) = _
  rw [map_one]
  exact section_value_natural s (eqToHom U.ι_image_top.symm)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma moduleSectionEquiv_scalar {M : X.Modules} (f : Γ(X, ⊤)) (s : O X ⟶ M) :
    moduleSectionEquiv M (scalarEnd f ≫ s) = f • moduleSectionEquiv M s := by
  change s.app ⊤ (endValue (scalarEnd f)) = f • s.app ⊤ (1 : Γ(X, ⊤))
  rw [endValue_scalarEnd]
  have h := s.app_smul (r := f) (x := (1 : Γ(X, ⊤)))
  change s.app ⊤ (f * 1 : Γ(X, ⊤)) = f • s.app ⊤ (1 : Γ(X, ⊤)) at h
  simpa only [mul_one] using h

lemma openSectionEquiv_scalar (M : X.Modules) (U : X.Opens)
    (f : Γ(U.toScheme, ⊤)) (s : O U.toScheme ⟶ M.restrict U.ι) :
    openSectionEquiv M U (scalarEnd f ≫ s) = U.topIso.hom f • openSectionEquiv M U s := by
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    (moduleSectionEquiv (M.restrict U.ι) (scalarEnd f ≫ s)) = _
  rw [moduleSectionEquiv_scalar]
  change M.presheaf.map (eqToHom U.ι_image_top.symm).op
    ((U.ι.appIso ⊤).inv f • (show Γ(M, U.ι ''ᵁ ⊤) from moduleSectionEquiv (M.restrict U.ι) s)) = _
  rw [M.map_smul, U.ι_appIso]
  rfl

lemma openSectionEquiv_restrict_value (M : X.Modules) (U : X.Opens)
    (s : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U s) =
      s.app W (1 : Γ(U.toScheme, W)) := by
  have h := section_value_natural s (homOfLE (show W ≤ ⊤ from le_top))
  change M.presheaf.map (U.ι.opensFunctor.map (homOfLE (show W ≤ ⊤ from le_top))).op
    (s.app ⊤ (1 : Γ(U.toScheme, ⊤))) = _ at h
  change M.presheaf.map (homOfLE (U.ι_image_le W)).op
    (M.presheaf.map (eqToHom U.ι_image_top.symm).op (s.app ⊤ (1 : Γ(U.toScheme, ⊤)))) = _
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  exact h

lemma image_section_extension (M : X.Modules) (U : X.Opens)
    (s t : O U.toScheme ⟶ M.restrict U.ι) (W : U.toScheme.Opens)
    (f : Γ(W.toScheme, ⊤))
    (h : restrictSection W.ι t = scalarEnd f ≫ restrictSection W.ι s) :
    M.presheaf.map (homOfLE (U.ι_image_le W)).op (openSectionEquiv M U t) =
      (U.ι.appIso W).inv (W.topIso.hom f) • M.presheaf.map (homOfLE (U.ι_image_le W)).op
        (openSectionEquiv M U s) := by
  have hh := congrArg (openSectionEquiv (M.restrict U.ι) W) h
  rw [openSectionEquiv_restrict, openSectionEquiv_scalar, openSectionEquiv_restrict] at hh
  rw [openSectionEquiv_restrict_value, openSectionEquiv_restrict_value]
  exact hh

end PiExponentSeshadri.Frames

end

end OAI
end Source0314

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/IdealModule.lean
section Source0315
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/IdealModule.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

def unit (X : Scheme.{u}) : X.Modules := SheafOfModules.unit X.ringCatSheaf

def structureMap : unit Y ⟶
    (Scheme.Modules.pushforward f).obj (unit X) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

@[simp] lemma structureMap_app (U : Y.Opens) (x : Γ(Y, U)) :
    ((structureMap f).val.app (op U)) x = (f.app U) x := rfl

def idealModule : Y.Modules := kernel (structureMap f)

def inclusion : idealModule f ⟶ unit Y :=
  kernel.ι (structureMap f)

instance : Mono (inclusion f) := inferInstanceAs (Mono (kernel.ι (structureMap f)))

def sectionsKernelIso (U : Y.Opens) :
    (idealModule f).val.obj (op U) ≅
      ModuleCat.of (Y.ringCatSheaf.obj.obj (op U))
        ((structureMap f).val.app (op U)).hom.ker :=
  PreservesKernel.iso
    (Scheme.Modules.toPresheafOfModules Y ⋙
      PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)) (structureMap f) ≪≫
    ModuleCat.kernelIsoKer _

lemma sectionsKernelIso_inclusion (U : Y.Opens) :
    (sectionsKernelIso f U).hom ≫
      ModuleCat.ofHom ((structureMap f).val.app (op U)).hom.ker.subtype =
        (inclusion f).val.app (op U) := by
  let E := Scheme.Modules.toPresheafOfModules Y ⋙
    PresheafOfModules.evaluation Y.ringCatSheaf.obj (op U)
  change ((PreservesKernel.iso E (structureMap f)).hom ≫
    (ModuleCat.kernelIsoKer (E.map (structureMap f))).hom) ≫
      ModuleCat.ofHom (E.map (structureMap f)).hom.ker.subtype =
        E.map (kernel.ι (structureMap f))
  rw [Category.assoc, ModuleCat.kernelIsoKer_hom_ker_subtype,
    PreservesKernel.iso_hom, kernelComparison_comp_ι]

lemma image_eq_kernel (U : Y.Opens) :
    ((inclusion f).val.app (op U)).hom.range = RingHom.ker (f.app U).hom := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change (f.app U) (((inclusion f).val.app (op U)) y) = 0
    have h := congrArg (fun g => (g.val.app (op U)) y)
      (kernel.condition (structureMap f))
    exact h
  · intro hx
    let y : ((structureMap f).val.app (op U)).hom.ker := ⟨x, hx⟩
    refine ⟨(sectionsKernelIso f U).inv y, ?_⟩
    have h := congrArg (fun g => g ((sectionsKernelIso f U).inv y))
      (sectionsKernelIso_inclusion f U)
    simpa using h.symm

lemma image_eq_ideal [QuasiCompact f] (U : Y.affineOpens) :
    ((inclusion f).val.app (op U.1)).hom.range = f.ker.ideal U := by
  rw [image_eq_kernel, Scheme.Hom.ker_apply]

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def closedModule (I : X.IdealSheafData) : X.Modules := idealModule I.subschemeι

def closedInclusion (I : X.IdealSheafData) : closedModule I ⟶ unit X :=
  inclusion I.subschemeι

lemma closed_image (I : X.IdealSheafData) (U : X.affineOpens) :
    ((closedInclusion I).val.app (op U.1)).hom.range = I.ideal U := by
  exact (image_eq_ideal I.subschemeι U).trans (congrArg (fun J => J.ideal U) I.ker_subschemeι)

lemma isIso_of_affine_app {M N : X.Modules} (g : M ⟶ N)
    (h : ∀ U : X.affineOpens, IsIso (g.app U.1)) : IsIso g := by
  let F := SheafOfModules.toSheaf X.ringCatSheaf
  have hb : TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => U.val) := by
    simpa using X.isBasis_affineOpens
  have hg : IsIso (F.map g) := TopCat.Sheaf.isIso_iff_isIso_basis hb h
  let : IsIso ((Scheme.Modules.toPresheaf X).map g) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ AddCommGrpCat).map (F.map g)))
  exact isIso_of_reflects_iso g (Scheme.Modules.toPresheaf X)

def multiply (r : Γ(X, ⊤)) : unit X ⟶ unit X where
  val.app U := by
    let S := X.ringCatSheaf.obj.obj U
    letI : CommRing S := inferInstanceAs (CommRing Γ(X, U.unop))
    exact ModuleCat.ofHom (LinearMap.mulLeft S
      ((X.presheaf.map (homOfLE le_top).op) r))
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change Γ(X, U.unop) at a
    change (X.presheaf.map (homOfLE le_top).op r) * (X.presheaf.map i a) =
      X.presheaf.map i (X.presheaf.map (homOfLE le_top).op r * a)
    rw [map_mul, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl

@[simp] lemma multiply_app (r : Γ(X, ⊤)) (U : X.Opens) (a : Γ(X, U)) :
    (multiply r).val.app (op U) a = X.presheaf.map (homOfLE le_top).op r * a := rfl

lemma multiply_structure_zero (f : Y ⟶ X) (r : Γ(X, ⊤))
    (hr : (f.app ⊤) r = 0) : multiply r ≫ structureMap f = 0 := by
  ext U a
  change Γ(X, U) at a
  change (f.app U) ((X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op r) *
    (a : Γ(X, U))) = 0
  rw [map_mul]
  have he : (f.app U) (X.presheaf.map (homOfLE le_top).op r) = 0 := by
    rw [← CommRingCat.comp_apply, f.naturality, CommRingCat.comp_apply, hr, map_zero]
  rw [he, zero_mul]

def equationToIdeal (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    unit X ⟶ idealModule f :=
  kernel.lift (structureMap f) (multiply r) (multiply_structure_zero f r hr)

@[reassoc (attr := simp)] lemma equationToIdeal_inclusion
    (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0) :
    equationToIdeal f r hr ≫ inclusion f = multiply r := kernel.lift_ι _ _ _

lemma equationToIdeal_app (f : Y ⟶ X) (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (U : X.Opens) (a : Γ(X, U)) :
    (inclusion f).val.app (op U) ((equationToIdeal f r hr).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a :=
  congrArg (fun g => g.val.app (op U) a) (equationToIdeal_inclusion f r hr)

lemma isIso_equationToIdeal (f : Y ⟶ X) [QuasiCompact f]
    (r : Γ(X, ⊤)) (hr : (f.app ⊤) r = 0)
    (hprincipal : ∀ U : X.affineOpens,
      f.ker.ideal U = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (equationToIdeal f r hr) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective ((inclusion f).val.app (op U.1)) := by
    let : Mono (inclusion f).val :=
      inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map (inclusion f)))
    exact PresheafOfModules.injective_of_mono (inclusion f).val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg ((inclusion f).val.app (op U.1)) hab
    change (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) a) =
      (inclusion f).val.app (op U.1) ((equationToIdeal f r hr).val.app (op U.1) b) at he
    exact (equationToIdeal_app f r hr U.1 a).symm.trans
      (he.trans (equationToIdeal_app f r hr U.1 b))
  · intro y
    have hy : (inclusion f).val.app (op U.1) y ∈ f.ker.ideal U := by
      rw [← image_eq_ideal f U]
      exact ⟨y, rfl⟩
    rw [hprincipal U] at hy
    have hd : X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r ∣
        (show Γ(X, U.1) from (inclusion f).val.app (op U.1) y) :=
      Ideal.mem_span_singleton.mp hy
    obtain ⟨a, ha⟩ := hd
    refine ⟨a, hinj ?_⟩
    exact (equationToIdeal_app f r hr U.1 a).trans ha.symm

end

section
open CategoryTheory AlgebraicGeometry
variable {X : Scheme}
lemma regular_map_flat {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) {r : R} (hr : IsLeftRegular r) :
    IsLeftRegular (f r) := by
  let := f.toAlgebra
  let : Module.Flat R S := hf
  have hh : IsSMulRegular S r := Module.Flat.isSMulRegular_of_isRegular
    ⟨hr, hr.right_of_commute (fun a => mul_comm r a)⟩
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra] using hh

lemma restriction_regular [IsAffine X] (r : Γ(X, ⊤)) (hr : IsLeftRegular r)
    (U : X.affineOpens) :
    IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r) := by
  apply regular_map_flat _ _ hr
  simpa [Scheme.Hom.appLE] using
    Scheme.Hom.flat_appLE (𝟙 X) (isAffineOpen_top X) U.2 (show U.1 ≤ (𝟙 X) ⁻¹ᵁ ⊤ from le_top)

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}}

lemma structureMap_epi (f : X ⟶ Y) [IsClosedImmersion f] : Epi (structureMap f) := by
  let F := SheafOfModules.toSheaf Y.ringCatSheaf
  have hloc : TopCat.Presheaf.IsLocallySurjective (F.map (structureMap f)).hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
    intro U t y hy
    obtain ⟨_,⟨V,hA,rfl⟩,hyV,hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    obtain ⟨s,hs⟩ := f.app_surjective V hA
      (((F.obj ((Scheme.Modules.pushforward f).obj (unit X))).obj.map
        (homOfLE hVU).op) t)
    exact ⟨V,hVU,⟨s,hs⟩,hyV⟩
  let : Epi (F.map (structureMap f)) :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc
  exact F.epi_of_epi_map inferInstance

theorem closedSequence_exact (f : X ⟶ Y) [IsClosedImmersion f] :
    (ShortComplex.mk (inclusion f) (structureMap f) (kernel.condition _)).ShortExact := by
  let := structureMap_epi f
  exact { exact := ShortComplex.exact_kernel _ }

end PiExponentSeshadri.IdealModule

end

end OAI
end Source0315

-- Source: OAI/NumberTheory/PiExponent/Ampleness/BlowupIdeal.lean
section Source0316
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/BlowupIdeal.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry

def sectionImageIdeal {X : Scheme} (J : LineBundle X)
    (ι : J.sheaf ⟶ structureSheaf X) (U : X.Opens) : Ideal Γ(X, U) := by
  letI : Module Γ(X, U) (J.sheaf.val.obj (Opposite.op U)) :=
    (J.sheaf.val.obj (Opposite.op U)).isModule
  let φ : J.sheaf.val.obj (Opposite.op U) →ₗ[Γ(X, U)] Γ(X, U) :=
    (ι.val.app (Opposite.op U)).hom
  exact φ.range

def PresentsPullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X)
    (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y) : Prop :=
  Mono ι ∧ ∀ (U : Y.affineOpens) (V : X.affineOpens)
    (e : U.1 ≤ f ⁻¹ᵁ V.1),
    sectionImageIdeal J ι U.1 = (I.ideal V).map (f.appLE V.1 U.1 e).hom

def InvertiblePullbackIdeal {X Y : Scheme} (I : X.IdealSheafData) (f : Y ⟶ X) : Prop :=
  ∃ (J : LineBundle Y) (ι : J.sheaf ⟶ structureSheaf Y), PresentsPullbackIdeal I f J ι

def IsBlowup {X B : Scheme} (I : X.IdealSheafData) (π : B ⟶ X) : Prop :=
  InvertiblePullbackIdeal I π ∧ ∀ (Y : Scheme) (f : Y ⟶ X),
    InvertiblePullbackIdeal I f → ∃! h : Y ⟶ B, h ≫ π = f

end Geometry

namespace IdealModule

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X : Scheme.{u}}

def sectionFamily {M : X.Modules} (s : Γ(M, ⊤)) : M.sections where
  val U := M.presheaf.map (homOfLE (show U.unop ≤ ⊤ from le_top)).op s
  property {U V} i := by
    change (M.presheaf.map (homOfLE le_top).op ≫ M.presheaf.map i) s = _
    rw [← Functor.map_comp]
    rfl

def fromSection {M : X.Modules} (s : Γ(M, ⊤)) : unit X ⟶ M :=
  M.unitHomEquiv.symm (sectionFamily s)

@[simp] lemma fromSection_app {M : X.Modules} (s : Γ(M, ⊤))
    (U : X.Opens) (a : Γ(X, U)) :
    (fromSection s).val.app (op U) a = a • M.presheaf.map (homOfLE le_top).op s := rfl

lemma fromSection_inclusion_app {M : X.Modules} (g : M ⟶ unit X)
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (U : X.Opens) (a : Γ(X, U)) :
    g.val.app (op U) ((fromSection s).val.app (op U) a) =
      X.presheaf.map (homOfLE le_top).op r * a := by
  rw [fromSection_app]
  have hn := PresheafOfModules.naturality_apply g.val (homOfLE (show U ≤ ⊤ from le_top)).op s
  change g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s) =
    X.presheaf.map (homOfLE le_top).op (g.val.app (op ⊤) s) at hn
  have he := ((g.val.app (op U)).hom).map_smul a (M.presheaf.map (homOfLE le_top).op s)
  change _ = a * (show Γ(X, U) from g.val.app (op U) (M.presheaf.map (homOfLE le_top).op s)) at he
  exact he.trans ((congrArg (fun b : Γ(X, U) => a * b)
    (hn.trans (congrArg (fun b : Γ(X, ⊤) => X.presheaf.map (homOfLE le_top).op b) hs))).trans
      (mul_comm _ _))

lemma isIso_fromSection {M : X.Modules} (g : M ⟶ unit X) [Mono g]
    (s : Γ(M, ⊤)) (r : Γ(X, ⊤)) (hs : g.val.app (op ⊤) s = r)
    (hprincipal : ∀ U : X.affineOpens,
      (g.val.app (op U.1)).hom.range = Ideal.span {X.presheaf.map (homOfLE le_top).op r})
    (hregular : ∀ U : X.affineOpens,
      IsLeftRegular (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op r)) :
    IsIso (fromSection s) := by
  apply isIso_of_affine_app
  intro U
  have hinj : Function.Injective (g.val.app (op U.1)) := by
    let : Mono g.val := inferInstanceAs (Mono ((Scheme.Modules.toPresheafOfModules X).map g))
    exact PresheafOfModules.injective_of_mono g.val (op U.1)
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  constructor
  · intro a b hab
    apply hregular U
    have he := congrArg (g.val.app (op U.1)) hab
    change g.val.app (op U.1) ((fromSection s).val.app (op U.1) a) =
      g.val.app (op U.1) ((fromSection s).val.app (op U.1) b) at he
    exact (fromSection_inclusion_app g s r hs U.1 a).symm.trans
      (he.trans (fromSection_inclusion_app g s r hs U.1 b))
  · intro y
    have hy : (show Γ(X, U.1) from g.val.app (op U.1) y) ∈
        Ideal.span {X.presheaf.map (homOfLE le_top).op r} := by
      rw [← hprincipal U]
      exact ⟨y, rfl⟩
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp hy
    refine ⟨a, hinj ?_⟩
    exact (fromSection_inclusion_app g s r hs U.1 a).trans ha.symm

end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictedInclusion (I : Y.IdealSheafData) (f : X ⟶ Y) [IsOpenImmersion f] :
    (closedModule I).restrict f ⟶ unit X :=
  (Scheme.Modules.restrictFunctor f).map (closedInclusion I) ≫
    (Scheme.Modules.restrictUnitIso f).hom

instance restrictedInclusion_mono (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] : Mono (restrictedInclusion I f) := by
  let : Mono (closedInclusion I) := inferInstanceAs (Mono (inclusion I.subschemeι))
  let : Mono ((Scheme.Modules.restrictFunctor f).map (closedInclusion I)) :=
    PiExponentSeshadri.RestrictionExact.restriction_mono f (closedInclusion I)
  exact mono_comp' (C := X.Modules) inferInstance
    ⟨fun a b h => (Iso.cancel_iso_hom_right a b (Scheme.Modules.restrictUnitIso f)).mp h⟩

lemma restrictedInclusion_app (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.Opens) (s : Γ((closedModule I).restrict f, U)) :
    (restrictedInclusion I f).val.app (op U) s =
      (f.appIso U).hom ((closedInclusion I).val.app (op (f ''ᵁ U)) s) := rfl

lemma restricted_image (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] (U : X.affineOpens) :
    ((restrictedInclusion I f).val.app (op U.1)).hom.range = (I.comap f).ideal U := by
  rw [I.ideal_comap_of_isOpenImmersion f U]
  ext r
  change Γ(X, U.1) at r
  change (∃ s, (restrictedInclusion I f).val.app (op U.1) s = r) ↔
    (f.appIso U.1).inv r ∈ I.ideal ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩
  rw [← closed_image I ⟨f ''ᵁ U.1, U.2.image_of_isOpenImmersion f⟩]
  change (∃ s, _) ↔ ∃ s, (closedInclusion I).val.app (op (f ''ᵁ U.1)) s = (f.appIso U.1).inv r
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (congrArg (fun k : Γ(Y, f ''ᵁ U.1) ⟶ Γ(Y, f ''ᵁ U.1) => k ((closedInclusion I).val.app (op (f ''ᵁ U.1)) s))
      (f.appIso U.1).hom_inv_id).symm.trans
        (congrArg (fun z : Γ(X, U.1) => (f.appIso U.1).inv z)
          ((restrictedInclusion_app I f U.1 s).symm.trans hs))
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    exact (restrictedInclusion_app I f U.1 s).trans
      ((congrArg (fun z : Γ(Y, f ''ᵁ U.1) => (f.appIso U.1).hom z) hs).trans
        (congrArg (fun k : Γ(X, U.1) ⟶ Γ(X, U.1) => k r) (f.appIso U.1).inv_hom_id))

lemma frame_restriction (I : Y.IdealSheafData) (f : X ⟶ Y)
    [IsOpenImmersion f] [IsAffine X] (r : Γ(X, ⊤))
    (hprincipal : (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ = Ideal.span {r})
    (hregular : IsLeftRegular r) :
    Nonempty ((closedModule I).restrict f ≅ unit X) := by
  have hr' : r ∈ (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ := by
    rw [hprincipal]
    exact Ideal.subset_span (Set.mem_singleton r)
  have hr : r ∈ ((restrictedInclusion I f).val.app (op ⊤)).hom.range := by
    rw [restricted_image I f ⟨⊤, isAffineOpen_top X⟩]
    exact hr'
  obtain ⟨s, hs⟩ := hr
  have hi : IsIso (fromSection (M := (closedModule I).restrict f) s) := isIso_fromSection (restrictedInclusion I f) s r hs
    (fun U => ?_) (restriction_regular r hregular)
  · exact ⟨(asIso (fromSection (M := (closedModule I).restrict f) s)).symm⟩
  · rw [restricted_image I f U, ← (I.comap f).map_ideal (U := U)
      (V := ⟨⊤, isAffineOpen_top X⟩) (by change U.1 ≤ ⊤; exact le_top), hprincipal]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

def frameOnRange (M : Y.Modules) (f : X ⟶ Y) [IsOpenImmersion f]
    (e : M.restrict f ≅ unit X) : M.restrict f.opensRange.ι ≅ unit f.opensRange.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr f.isoOpensRange_inv_comp).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp f.isoOpensRange.inv f).app M ≪≫
    (Scheme.Modules.restrictFunctor f.isoOpensRange.inv).mapIso e ≪≫
    Scheme.Modules.restrictUnitIso f.isoOpensRange.inv

end IdealModule
namespace IdealPullback

section
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]

lemma map_top (J : X.IdealSheafData) (f : X ⟶ Y) :
    (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom :=
  J.ideal_map f ⟨⊤, isAffineOpen_top Y⟩ (isAffineOpen_top X)

lemma comap_top (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  apply le_antisymm
  · let J : X.IdealSheafData := Scheme.IdealSheafData.ofIdealTop
      ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
    have h : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [map_top]
      simpa [J] using Ideal.le_comap_map
    have hh := (Scheme.IdealSheafData.le_map_iff_comap_le.mp h) ⟨⊤, isAffineOpen_top X⟩
    simpa [J] using hh
  · rw [Ideal.map_le_iff_le_comap]
    have h := (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩
    rwa [map_top] at h

end
section
open CategoryTheory AlgebraicGeometry Opposite
universe u
variable {R S : Type u} [CommRing R] [CommRing S]

def specIdeal (I : Ideal R) : (Spec (CommRingCat.of R)).IdealSheafData :=
  Scheme.IdealSheafData.ofIdealTop (I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

@[simp] lemma specIdeal_top (I : Ideal R) :
    (specIdeal I).ideal ⟨⊤, isAffineOpen_top _⟩ =
      I.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
  simp [specIdeal]

lemma specIdeal_comap (I : Ideal R) (f : R →+* S) :
    (specIdeal I).comap (Spec.map (CommRingCat.ofHom f)) = specIdeal (I.map f) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [comap_top, specIdeal_top, specIdeal_top, Ideal.map_map, Ideal.map_map]
  congr 1
  exact congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f)).symm

end
open CategoryTheory AlgebraicGeometry
universe u
variable {X Y : Scheme.{u}}

lemma comap_ι_top (I : X.IdealSheafData) (U : X.affineOpens) :
    (I.comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ =
      (I.ideal U).map U.1.topIso.inv.hom := by
  rw [I.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact (I.map_ideal (U := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1.toScheme).image_of_isOpenImmersion U.1.ι⟩)
    (V := U) (show U.1.ι ''ᵁ ⊤ ≤ U.1 from U.1.ι_image_top.le)).symm

lemma comap_ideal (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : X.affineOpens) (V : Y.affineOpens) (e : U.1 ≤ f ⁻¹ᵁ V.1) :
    (I.comap f).ideal U = (I.ideal V).map (f.appLE V.1 U.1 e).hom := by
  suffices hh : ((I.comap f).ideal U).map U.1.topIso.inv.hom =
      ((I.ideal V).map (f.appLE V.1 U.1 e).hom).map U.1.topIso.inv.hom by
    have hh' := congrArg (Ideal.map U.1.topIso.hom.hom) hh
    simpa only [Ideal.map_map, ← CommRingCat.hom_comp, Iso.inv_hom_id, Iso.inv_hom_id_assoc, Category.assoc, Category.comp_id, CommRingCat.hom_id,
      Ideal.map_id] using hh'
  rw [← comap_ι_top, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.Hom.resLE_comp_ι f e, Scheme.IdealSheafData.comap_comp,
    comap_top, comap_ι_top, Ideal.map_map, Ideal.map_map]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, ← CommRingCat.hom_comp,
    Iso.inv_hom_id_assoc]

end IdealPullback
namespace InvertibleLocal

section
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry
variable {X Y : Scheme} {I : X.IdealSheafData} {f : Y ⟶ X}
lemma invertible_of_local_equations
    (hf : ∀ y : Y, ∃ U : Y.affineOpens, y ∈ U.1 ∧
      ∃ r : Γ(U.1.toScheme, ⊤), IsRegular r ∧
      ((I.comap f).comap U.1.ι).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r}) :
    InvertiblePullbackIdeal I f := by
  let J : LineBundle Y := {
    sheaf := IdealModule.closedModule (I.comap f)
    locallyRankOne y := by
      obtain ⟨U, hyU, r, hr, hIr⟩ := hf y
      exact ⟨U.1, hyU, IdealModule.frame_restriction (I.comap f) U.1.ι r hIr hr.1⟩ }
  have : Mono (IdealModule.closedInclusion (I.comap f)) :=
    inferInstanceAs (Mono (IdealModule.inclusion (I.comap f).subschemeι))
  refine ⟨J, IdealModule.closedInclusion (I.comap f), this, ?_⟩
  intro U V e
  change ((IdealModule.closedInclusion (I.comap f)).val.app (op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal I f U V e

end
open CategoryTheory AlgebraicGeometry Opposite
open PiExponentSeshadri.Geometry

end InvertibleLocal

end PiExponentSeshadri

end

end OAI
end Source0316

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesPushdown.lean
section Source0317
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesPushdown.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading

section
open Polynomial DirectSum AlgebraicGeometry CategoryTheory
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def piece (n : ℕ) : Submodule R (reesAlgebra I) where
  carrier := {p | (p : R[X]) = monomial n ((p : R[X]).coeff n)}
  zero_mem' := by simp
  add_mem' {p q} hp hq := by
    change (p : R[X]) + q = monomial n (((p : R[X]) + q).coeff n)
    rw [coeff_add, map_add, ← hp, ← hq]
  smul_mem' a p hp := by
    change a • (p : R[X]) = monomial n ((a • (p : R[X])).coeff n)
    rw [coeff_smul, map_smul, ← hp]

lemma mem_piece (n : ℕ) (p : reesAlgebra I) :
    p ∈ piece I n ↔ (p : R[X]) = monomial n ((p : R[X]).coeff n) := Iff.rfl

def component (n : ℕ) (p : reesAlgebra I) : piece I n :=
  ⟨⟨monomial n ((p : R[X]).coeff n), reesAlgebra.monomial_mem.mpr (p.property n)⟩,
    by simp [mem_piece]⟩

@[simp] lemma component_val (n : ℕ) (p : reesAlgebra I) :
    ((component I n p : reesAlgebra I) : R[X]) = monomial n ((p : R[X]).coeff n) := rfl

def components (p : reesAlgebra I) : ⨁ n, piece I n :=
  ⟨fun n => component I n p,
    Trunc.mk ⟨(p : R[X]).support.val, fun n => by
      classical
      by_cases hn : n ∈ (p : R[X]).support
      · exact Or.inl hn
      · right
        apply Subtype.ext
        apply Subtype.ext
        have hc : (p : R[X]).coeff n = 0 := notMem_support_iff.mp hn
        simp [component_val, hc]⟩⟩

@[simp] lemma components_apply (p : reesAlgebra I) (n : ℕ) :
    components I p n = component I n p := rfl

def componentsAdd : reesAlgebra I →+ ⨁ n, piece I n where
  toFun := components I
  map_zero' := by ext n : 1; apply Subtype.ext; apply Subtype.ext; simp [component_val]
  map_add' p q := by
    ext n : 1
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (((p : R[X]) + q).coeff n) =
      monomial n ((p : R[X]).coeff n) + monomial n ((q : R[X]).coeff n)
    rw [coeff_add, map_add]

lemma piece_coeff_ne {n m : ℕ} (hnm : n ≠ m) (p : piece I n) :
    ((p : reesAlgebra I) : R[X]).coeff m = 0 := by
  rw [(mem_piece I n p.val).mp p.property, coeff_monomial, ite_eq_right hnm]

lemma components_of_piece (n : ℕ) (p : piece I n) :
    components I p.val = DirectSum.of (fun n => piece I n) n p := by
  ext m : 1
  by_cases h : n = m
  · subst m
    rw [DirectSum.of_eq_same]
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
    apply Subtype.ext
    apply Subtype.ext
    simp [component_val, piece_coeff_ne I h p]

lemma recompose_components (p : reesAlgebra I) :
    DirectSum.coeAddMonoidHom (piece I) (components I p) = p := by
  let f := DirectSum.coeAddMonoidHom (piece I)
  have hc (n : ℕ) :
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp f)) =
      ((Polynomial.lcoeff R n).toAddMonoidHom.comp
        ((reesAlgebra I).val.toAddMonoidHom.comp
          ((piece I n).subtype.toAddMonoidHom.comp (DFinsupp.evalAddMonoidHom n)))) := by
    apply DirectSum.addHom_ext
    intro m a
    dsimp only [f]
    simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of]
    change ((a : reesAlgebra I) : R[X]).coeff n =
      (((DirectSum.of (fun i => piece I i) m a) n : reesAlgebra I) : R[X]).coeff n
    by_cases h : m = n
    · subst m
      rw [DirectSum.of_eq_same]
    · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h), piece_coeff_ne I h a]
      rfl
  apply Subtype.ext
  ext n
  have h := DFunLike.congr_fun (hc n) (components I p)
  change ((f (components I p) : reesAlgebra I) : R[X]).coeff n =
    ((component I n p : reesAlgebra I) : R[X]).coeff n at h
  simpa only [component_val, coeff_monomial, ite_true] using h

instance gradedMonoid : SetLike.GradedMonoid (piece I) where
  one_mem := by simp [mem_piece]
  mul_mem {i j} {a b} ha hb := by
    change (a : R[X]) * b = monomial (i+j) (((a : R[X]) * b).coeff (i+j))
    rw [(mem_piece I i a).mp ha, (mem_piece I j b).mp hb,
      monomial_mul_monomial, coeff_monomial, ite_eq_left rfl]

instance grading : GradedAlgebra (piece I) where
  toGradedMonoid := gradedMonoid I
  decompose' := components I
  left_inv := recompose_components I
  right_inv := by
    have h : (componentsAdd I).comp (DirectSum.coeAddMonoidHom (piece I)) = .id _ := by
      apply DirectSum.addHom_ext
      intro n a
      simp only [AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of,
        AddMonoidHom.id_apply]
      exact components_of_piece I n a
    exact DFunLike.congr_fun h

def affineBlowup : Scheme.{u} := Proj (piece I)

def zeroEquiv : R ≃+* piece I 0 :=
  RingEquiv.ofBijective (algebraMap R (piece I 0)) (by
    constructor
    · intro a b h
      have hp := congrArg (fun p : piece I 0 => ((p : reesAlgebra I) : R[X])) h
      exact Polynomial.C_injective hp
    · intro p
      refine ⟨((p : reesAlgebra I) : R[X]).coeff 0, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact (show ((p : reesAlgebra I) : R[X]) =
        C (((p : reesAlgebra I) : R[X]).coeff 0) by
          simpa only [monomial_zero_left] using (mem_piece I 0 p.val).mp p.property).symm)

def zeroIso : CommRingCat.of R ≅ CommRingCat.of (piece I 0) :=
  (zeroEquiv I).toCommRingCatIso

def projection : affineBlowup I ⟶ Spec (CommRingCat.of R) :=
  Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom

instance : IsScalarTower R (piece I 0) (reesAlgebra I) :=
  IsScalarTower.of_algebraMap_eq (R := R) (S := piece I 0) (A := reesAlgebra I)
    (fun _ => rfl)

instance [IsNoetherianRing R] : Algebra.FiniteType (piece I 0) (reesAlgebra I) :=
  Algebra.FiniteType.of_restrictScalars_finiteType R (piece I 0) (reesAlgebra I)

instance projection_proper [IsNoetherianRing R] : IsProper (projection I) := by
  have hP : IsProper (Proj.toSpecZero (piece I)) := inferInstance
  have hS : IsIso (Spec.map (zeroIso I).hom) := inferInstance
  have hQ : IsProper (Spec.map (zeroIso I).hom) := by infer_instance
  exact MorphismProperty.comp_mem (@IsProper) _ _ hP hQ

end

open Polynomial DirectSum AlgebraicGeometry CategoryTheory HomogeneousLocalization
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def generator (a : I) : reesAlgebra I :=
  ⟨monomial 1 a.val, reesAlgebra.monomial_mem.mpr (by simp [a.property])⟩

@[simp] lemma generator_val (a : I) :
    (generator I a : R[X]) = monomial 1 a.val := rfl

lemma generator_mem (a : I) : generator I a ∈ piece I 1 := by
  simp [mem_piece]

def evaluation : reesAlgebra I →+* R :=
  (Polynomial.evalRingHom 1).comp (reesAlgebra I).val.toRingHom

@[simp] lemma evaluation_generator (a : I) : evaluation I (generator I a) = a.val := by
  simp [evaluation]

lemma evaluation_piece {n : ℕ} (p : piece I n) :
    evaluation I p.val = ((p : reesAlgebra I) : R[X]).coeff n := by
  change Polynomial.eval 1 ((p : reesAlgebra I) : R[X]) = _
  conv_lhs => rw [(mem_piece I n p.val).mp p.property]
  simp

abbrev chart (a : I) := HomogeneousLocalization.Away (piece I) (generator I a)

def chartMap (a : I) : chart I a →+* Localization.Away a.val :=
  (IsLocalization.map (M := Submonoid.powers (generator I a))
    (S := Localization.Away (generator I a)) (T := Submonoid.powers a.val)
    (Localization.Away a.val) (evaluation I)
    (by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩)).comp
      (algebraMap (chart I a) (Localization.Away (generator I a)))

lemma chartMap_mk (a : I) (n : ℕ) (p : reesAlgebra I)
    (hp : p ∈ piece I (n • (1 : ℕ))) :
    chartMap I a (HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) n p hp) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        (evaluation I p) ⟨a.val ^ n, (Submonoid.powers a.val).pow_mem (Submonoid.mem_powers a.val) n⟩ := by
  simp only [chartMap, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk']
  congr 1
  apply Subtype.ext
  simp

lemma chartMap_injective (a : I) : Function.Injective (chartMap I a) := by
  apply (RingHom.injective_iff_ker_eq_bot _).mpr
  apply bot_unique
  intro x hx
  change x = 0
  obtain ⟨n, p, hp, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) x
  have hzero := RingHom.mem_ker.mp hx
  rw [chartMap_mk] at hzero
  obtain ⟨⟨b, hb⟩, hbp⟩ := (IsLocalization.mk'_eq_zero_iff (M := Submonoid.powers a.val)
    (S := Localization.Away a.val) _ _).mp hzero
  obtain ⟨j, rfl⟩ := hb
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_zero, HomogeneousLocalization.Away.val_mk,
    Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff]
  refine ⟨⟨generator I a ^ j, ⟨j, rfl⟩⟩, ?_⟩
  apply Subtype.ext
  have hpn : p ∈ piece I n := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff n := evaluation_piece I ⟨p, hpn⟩
  change (generator I a : R[X]) ^ j * (p : R[X]) = 0
  rw [(mem_piece I n p).mp hpn, generator_val, monomial_pow, monomial_mul_monomial]
  rw [he] at hbp
  simp [hbp]

def chartBase (a : I) : R →+* chart I a :=
  (HomogeneousLocalization.fromZeroRingHom (piece I) (Submonoid.powers (generator I a))).comp
    (zeroEquiv I).toRingHom

lemma chartMap_base (a : I) (r : R) :
    chartMap I a (chartBase I a r) = algebraMap R (Localization.Away a.val) r := by
  have h0 : algebraMap R (reesAlgebra I) r ∈ piece I (0 • (1 : ℕ)) := by
    simp [mem_piece]
  refine (chartMap_mk I a 0 (algebraMap R (reesAlgebra I) r) h0).trans ?_
  have he : evaluation I (algebraMap R (reesAlgebra I) r) = r := by simp [evaluation]
  rw [he]
  convert IsLocalization.mk'_one (M := Submonoid.powers a.val)
    (Localization.Away a.val) r using 1
  congr 1
  apply Subtype.ext
  exact pow_zero a.val

def ratio (a b : I) : chart I a :=
  HomogeneousLocalization.Away.mk (piece I) (generator_mem I a) 1
    (generator I b) (by simpa using generator_mem I b)

lemma chartMap_ratio (a b : I) :
    chartMap I a (ratio I a b) =
      IsLocalization.mk' (M := Submonoid.powers a.val) (Localization.Away a.val)
        b.val ⟨a.val, ⟨1, pow_one _⟩⟩ := by
  simp only [ratio, chartMap_mk, evaluation_generator, pow_one]

lemma base_mul_ratio (a b : I) :
    chartBase I a a.val * ratio I a b = chartBase I a b.val := by
  apply chartMap_injective I a
  rw [map_mul, chartMap_base, chartMap_ratio, chartMap_base]
  exact IsLocalization.mk'_spec' (M := Submonoid.powers a.val)
    (Localization.Away a.val) b.val ⟨a.val, ⟨1, pow_one _⟩⟩

lemma map_ideal_principal (a : I) :
    I.map (chartBase I a) = Ideal.span {chartBase I a a.val} := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro b hb
    change chartBase I a b ∈ Ideal.span {chartBase I a a.val}
    rw [Ideal.mem_span_singleton]
    exact ⟨ratio I a ⟨b, hb⟩, (base_mul_ratio I a ⟨b, hb⟩).symm⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_map_of_mem _ a.property

lemma chart_generator_regular (a : I) :
    IsRegular (chartBase I a a.val) := by
  have hu : IsUnit (chartMap I a (chartBase I a a.val)) := by
    rw [chartMap_base]
    exact IsLocalization.map_units (Localization.Away a.val)
      (⟨a.val, 1, pow_one _⟩ : Submonoid.powers a.val)
  constructor
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.left
    simpa only [map_mul] using congrArg (chartMap I a) h
  · intro x y h
    apply chartMap_injective I a
    apply hu.isRegular.right
    simpa only [map_mul] using congrArg (chartMap I a) h

end PiExponentSeshadri.ReesGrading

namespace PiExponent.ReesPushdown

open Polynomial PiExponentSeshadri.ReesGrading

variable {R : Type*} [CommRing R]

def ordinaryPowerEquivPiece (I : Ideal R) (n : ℕ) : ↥(I ^ n : Ideal R) ≃ₗ[R] piece I n where
  toFun a := ⟨⟨monomial n a.val, reesAlgebra.monomial_mem.mpr a.property⟩,
    by simp [mem_piece]⟩
  invFun p := ⟨((p : reesAlgebra I) : R[X]).coeff n, p.val.property n⟩
  left_inv a := by apply Subtype.ext; simp
  right_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact ((mem_piece I n p.val).mp p.property).symm
  map_add' a b := by apply Subtype.ext; apply Subtype.ext; simp
  map_smul' a b := by
    apply Subtype.ext
    apply Subtype.ext
    change monomial n (a • b.val) = a • monomial n b.val
    exact (monomial n).map_smul a b.val

theorem chart_ordinaryPower_principal (I : Ideal R) (a : I) (n : ℕ) :
    (I ^ n).map (chartBase I a) = Ideal.span {(chartBase I a a.val) ^ n} := by
  rw [Ideal.map_pow, map_ideal_principal, Ideal.span_singleton_pow]

theorem ordinaryPowerEquivPiece_apply_coeff (I : Ideal R) (n : ℕ) (a : ↥(I ^ n : Ideal R)) :
    (((ordinaryPowerEquivPiece I n a : piece I n) : reesAlgebra I) : R[X]).coeff n = a.val := by
  simp [ordinaryPowerEquivPiece]

theorem chart_ordinaryPower_fraction (I : Ideal R) (a : I) (n : ℕ)
    (s : chart I a) (hs : s ∈ (I ^ n).map (chartBase I a)) :
    ∃ k : ℕ, ∃ b ∈ I ^ (n + k),
      chartMap I a s = IsLocalization.mk' (M := Submonoid.powers a.val)
        (Localization.Away a.val) b ⟨a.val ^ k, (Submonoid.powers a.val).pow_mem (Submonoid.mem_powers a.val) k⟩ := by
  rw [chart_ordinaryPower_principal, Ideal.mem_span_singleton] at hs
  obtain ⟨q, hq⟩ := hs
  obtain ⟨k, p, hp, hrep⟩ := HomogeneousLocalization.Away.mk_surjective (piece I)
    (generator_mem I a) q
  have hpn : p ∈ piece I k := by simpa using hp
  have he : evaluation I p = (p : R[X]).coeff k := evaluation_piece I ⟨p, hpn⟩
  have hb : evaluation I p ∈ I ^ k := by rw [he]; exact p.property k
  refine ⟨k, a.val ^ n * evaluation I p, ?_, ?_⟩
  · rw [pow_add]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow a.property n) hb
  · have hmap : chartMap I a ((chartBase I a a.val) ^ n) =
        algebraMap R (Localization.Away a.val) (a.val ^ n) := by
      calc
        _ = (chartMap I a (chartBase I a a.val)) ^ n := (chartMap I a).map_pow _ n
        _ = _ := by rw [chartMap_base, map_pow]
    rw [hq, map_mul, hmap, ← hrep, chartMap_mk]
    exact IsLocalization.mul_mk'_eq_mk'_of_mul _ _ _

theorem eventually_no_power_torsion [IsNoetherianRing R] (I : Ideal R) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ I ^ n,
      (∃ k : ℕ, ∀ a ∈ I ^ k, a * x = 0) → x = 0 := by
  let A : ℕ →o Ideal R :=
    ⟨fun n => (I ^ n).annihilator,
      fun i j hij => Submodule.annihilator_mono (Ideal.pow_le_pow_right hij)⟩
  obtain ⟨e, he⟩ := monotone_stabilizes_iff_noetherian.mpr
    (inferInstance : IsNoetherian R R) A
  obtain ⟨c, hc⟩ := I.exists_pow_inf_eq_pow_smul (A e)
  refine ⟨c + e, ?_⟩
  intro n hn x hxn hx
  obtain ⟨k, hk⟩ := hx
  have hxA : x ∈ A k := by
    apply Submodule.mem_annihilator.mpr
    intro a ha
    simpa only [smul_eq_mul, mul_comm] using hk a ha
  have hxAe : x ∈ A e := by
    have hxmax := (A.monotone (Nat.le_max_left k e)) hxA
    rw [he (max k e) (Nat.le_max_right k e)]
    exact hxmax
  have hinter : I ^ n ⊓ A e = I ^ (n - c) * (I ^ c ⊓ A e) := by
    simpa only [Ideal.smul_eq_mul, Ideal.mul_top] using hc n (by omega)
  have hzero : I ^ n ⊓ A e ≤ ⊥ := by
    rw [hinter]
    calc
      _ ≤ I ^ e * A e := mul_le_mul' (Ideal.pow_le_pow_right (by omega)) inf_le_right
      _ = ⊥ := by
        change I ^ e * (I ^ e).annihilator = ⊥
        rw [mul_comm, Submodule.annihilator_mul]
  exact Ideal.mem_bot.mp (hzero ⟨hxn, hxAe⟩)

end PiExponent.ReesPushdown

end

end OAI
end Source0317

-- Source: OAI/NumberTheory/PiExponent/Ampleness/ReesExceptional.lean
section Source0318
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesExceptional.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponentSeshadri.ReesGrading
open Polynomial DirectSum AlgebraicGeometry CategoryTheory TopologicalSpace
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

lemma generators_adjoin : Algebra.adjoin R (Set.range (generator I)) = ⊤ := by
  apply (Subalgebra.map_injective (f := (reesAlgebra I).val) Subtype.val_injective)
  rw [AlgHom.map_adjoin]
  have hs : (reesAlgebra I).val '' Set.range (generator I) =
      (Submodule.map (monomial 1 : R →ₗ[R] R[X]) I : Set R[X]) := by
    ext p
    constructor
    · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
      exact ⟨a.val, a.property, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨generator I ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  rw [hs, adjoin_monomial_eq_reesAlgebra]
  rw [Algebra.map_top, Subalgebra.range_val]

lemma generators_adjoin_zero :
    Algebra.adjoin (piece I 0) (Set.range (generator I)) = ⊤ := by
  apply top_unique
  intro p hp
  clear hp
  have hh : p ∈ Algebra.adjoin R (Set.range (generator I)) := by
    rw [generators_adjoin]
    trivial
  induction hh using Algebra.adjoin_induction with
  | mem x hx => exact Algebra.subset_adjoin hx
  | algebraMap r =>
    exact (Algebra.adjoin (piece I 0) (Set.range (generator I))).algebraMap_mem (zeroEquiv I r)
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

lemma iSup_generator_basicOpen :
    ⨆ a : I, Proj.basicOpen (piece I) (generator I a) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' (piece I) (generator I)
    (fun a => ⟨1, generator_mem I a⟩) (generators_adjoin_zero I)

def chartCover : (affineBlowup I).AffineOpenCover where
  I₀ := I
  X a := CommRingCat.of (chart I a)
  f a := Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)
  map_prop a := inferInstanceAs (IsOpenImmersion
    (Proj.awayι (m := 1) (piece I) (generator I a) (generator_mem I a) (show 0 < (1 : ℕ) from Nat.zero_lt_one)))
  idx x := (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose
  covers x := by
    change x ∈ (Proj.awayι (m := 1) (piece I) _ _ _).opensRange
    rw [Proj.opensRange_awayι]
    exact (Opens.mem_iSup.mp ((iSup_generator_basicOpen I).ge (Set.mem_univ x))).choose_spec

lemma chartCover_projection (a : I) :
    (chartCover I).f a ≫ projection I = Spec.map (CommRingCat.ofHom (chartBase I a)) := by
  change Proj.awayι (m := 1) (piece I) (generator I a) _ _ ≫
    (Proj.toSpecZero (piece I) ≫ Spec.map (zeroIso I).hom) = _
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl

end PiExponentSeshadri.ReesGrading
namespace PiExponentSeshadri.Geometry
open CategoryTheory AlgebraicGeometry

def lineBundleOfCover {X : Scheme} (M : X.Modules) (C : X.OpenCover)
    (h : ∀ i, Nonempty (M.restrict (C.f i) ≅ IdealModule.unit (C.X i))) : LineBundle X where
  sheaf := M
  locallyRankOne x := by
    refine ⟨(C.f (C.idx x)).opensRange, C.covers x, ?_⟩
    exact ⟨IdealModule.frameOnRange M (C.f (C.idx x)) (h (C.idx x)).some⟩

def idealLineBundle {X : Scheme} (I : X.IdealSheafData) (C : X.AffineOpenCover)
    (r : ∀ i, Γ(Spec (C.X i), ⊤))
    (h : ∀ i, (I.comap (C.f i)).ideal ⟨⊤, isAffineOpen_top _⟩ = Ideal.span {r i})
    (hr : ∀ i, IsLeftRegular (r i)) : LineBundle X :=
  lineBundleOfCover (IdealModule.closedModule I) C.openCover
    (fun i => by
      let : IsOpenImmersion (C.f i) := C.map_prop i
      exact IdealModule.frame_restriction I (C.f i) (r i) (h i) (hr i))

end PiExponentSeshadri.Geometry
namespace PiExponentSeshadri.ReesGrading

section
open CategoryTheory AlgebraicGeometry
universe u
variable {R : Type u} [CommRing R] (I : Ideal R)

def exceptionalIdeal : (affineBlowup I).IdealSheafData :=
  (IdealPullback.specIdeal I).comap (projection I)

def chartEquation (a : I) : Γ(Spec ((chartCover I).X a), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv (chartBase I a a.val)

lemma exceptional_chart (a : I) :
    ((exceptionalIdeal I).comap ((chartCover I).f a)).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.span {chartEquation I a} := by
  rw [exceptionalIdeal, ← Scheme.IdealSheafData.comap_comp, chartCover_projection]
  erw [IdealPullback.specIdeal_comap, IdealPullback.specIdeal_top, map_ideal_principal,
    Ideal.map_span, Set.image_singleton]
  rfl

lemma chartEquation_regular (a : I) : IsLeftRegular (chartEquation I a) := by
  apply IdealModule.regular_map_flat _ _ (chart_generator_regular I a).left
  exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (chart I a))).inv)

end

open CategoryTheory AlgebraicGeometry
variable {R : Type} [CommRing R] (I : Ideal R)

def exceptionalLineBundle : Geometry.LineBundle (affineBlowup I) :=
  Geometry.idealLineBundle (exceptionalIdeal I) (chartCover I) (chartEquation I)
    (exceptional_chart I) (chartEquation_regular I)

def exceptionalInclusion : (exceptionalLineBundle I).sheaf ⟶ IdealModule.unit (affineBlowup I) :=
  IdealModule.closedInclusion (exceptionalIdeal I)

instance exceptionalInclusion_mono : Mono (exceptionalInclusion I) := by
  exact inferInstanceAs (Mono (IdealModule.inclusion (exceptionalIdeal I).subschemeι))

lemma exceptional_presents : Geometry.PresentsPullbackIdeal (IdealPullback.specIdeal I)
    (projection I) (exceptionalLineBundle I) (exceptionalInclusion I) := by
  refine ⟨exceptionalInclusion_mono I, fun U V e => ?_⟩
  change ((IdealModule.closedInclusion (exceptionalIdeal I)).val.app (Opposite.op U.1)).hom.range = _
  rw [IdealModule.closed_image]
  exact IdealPullback.comap_ideal (IdealPullback.specIdeal I) (projection I) U V e

theorem exceptional_invertible : Geometry.InvertiblePullbackIdeal (IdealPullback.specIdeal I)
    (projection I) :=
  ⟨exceptionalLineBundle I, exceptionalInclusion I, exceptional_presents I⟩

end PiExponentSeshadri.ReesGrading

end

end OAI
end Source0318

-- Source: OAI/NumberTheory/PiExponent/Approximation/GlobalSectionClearing.lean
section Source0319
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/GlobalSectionClearing.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.GlobalSectionClearing
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
universe u
variable {X Y : Scheme.{u}}

def restrictScalar (X : Scheme.{u}) (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality (X : Scheme.{u}) {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def OpenSections (M : X.Modules) (U : X.Opens) := Γ(M,U)
instance (M : X.Modules) (U : X.Opens) : AddCommGroup (OpenSections M U) :=
  inferInstanceAs (AddCommGroup Γ(M,U))
instance (M : X.Modules) (U : X.Opens) : Module Γ(X,⊤) (OpenSections M U) :=
  Module.compHom Γ(M,U) (restrictScalar X U)

def openRestriction (M : X.Modules) {U V : X.Opens} (h : U ≤ V) :
    OpenSections M V →ₗ[Γ(X,⊤)] OpenSections M U where
  toFun := M.val.map (homOfLE h).op
  map_add' := map_add _
  map_smul' := by
    intro r m
    let : Module Γ(X,V) (OpenSections M V) := (M.val.obj (op V)).isModule
    let : Module Γ(X,U) (OpenSections M U) := (M.val.obj (op U)).isModule
    change M.presheaf.map (homOfLE h).op (restrictScalar X V r • (m : Γ(M,V))) =
      restrictScalar X U r • M.presheaf.map (homOfLE h).op m
    erw [M.map_smul, restrictScalar_naturality]

theorem quasicoherent_pushforward_iso (e : X ≅ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward e.hom).obj M).IsQuasicoherent := by
  let N := (Scheme.Modules.pushforward e.hom).obj M
  let q : (Scheme.Modules.pushforward e.inv).obj N ≅ M :=
    (Scheme.Modules.pushforwardComp e.hom e.inv).app M ≪≫
      (Scheme.Modules.pushforwardCongr e.hom_inv_id).app M ≪≫
      (Scheme.Modules.pushforwardId X).app M
  let j : N ≅ M.restrict e.inv :=
    ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app N).symm ≪≫
      (Scheme.Modules.restrictFunctor e.inv).mapIso q
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso j.symm inferInstance

abbrev affineToSpecModule [IsAffine X] (M : X.Modules) :=
  (Scheme.Modules.pushforward X.toSpecΓ).obj M

instance affineToSpecModule_quasicoherent [IsAffine X] (M : X.Modules)
    [M.IsQuasicoherent] : (affineToSpecModule M).IsQuasicoherent :=
  quasicoherent_pushforward_iso X.isoSpec M

theorem affine_sections_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r
      (((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) :=
  ((isIso_fromTildeΓ_iff_isLocalizing (affineToSpecModule M)).mp inferInstance) r

def affineSpecSections [IsAffine X] (M : X.Modules)
    (U : (Spec Γ(X,⊤)).Opens) :
    ((modulesSpecToSheaf.obj (affineToSpecModule M)).obj.obj (op U)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (X.toSpecΓ ⁻¹ᵁ U) where
  toFun := fun x => x
  invFun := fun x => x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    let : Module Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) :=
      (M.val.obj (op (X.toSpecΓ ⁻¹ᵁ U))).isModule
    change @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
      ((X.toSpecΓ.app U).hom
        ((Spec Γ(X,⊤)).presheaf.map U.leTop.op ((Scheme.ΓSpecIso Γ(X,⊤)).inv r))) m =
      @SMul.smul Γ(X,X.toSpecΓ ⁻¹ᵁ U) Γ(M,X.toSpecΓ ⁻¹ᵁ U) _
        (restrictScalar X (X.toSpecΓ ⁻¹ᵁ U) r) m
    congr 1
    have h := congrArg (fun f : Γ(Spec Γ(X,⊤),⊤) ⟶ Γ(X,X.toSpecΓ ⁻¹ᵁ U) =>
      f ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) (X.toSpecΓ.naturality U.leTop.op)
    simp only [CommRingCat.comp_apply, Scheme.toSpecΓ_appTop] at h
    change _ = restrictScalar X (X.toSpecΓ ⁻¹ᵁ U)
      ((Scheme.ΓSpecIso Γ(X,⊤)).hom ((Scheme.ΓSpecIso Γ(X,⊤)).inv r)) at h
    rw [(Scheme.ΓSpecIso Γ(X,⊤)).inv_hom_id_apply r] at h
    exact h

def openSectionsCongr (M : X.Modules) {U V : X.Opens} (h : U = V) :
    OpenSections M U ≃ₗ[Γ(X,⊤)] OpenSections M V := by
  subst V
  exact LinearEquiv.refl _ _

lemma openSectionsCongr_restriction (M : X.Modules) {U V : X.Opens} (h : U = V)
    (m : OpenSections M ⊤) :
    openSectionsCongr M h (openRestriction M (show U ≤ ⊤ from le_top) m) = openRestriction M (show V ≤ ⊤ from le_top) m := by
  subst V
  rfl

theorem affine_openRestriction_localize [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) :
    IsLocalizedModule.Away r (openRestriction M (X.basicOpen_le r)) := by
  let F := modulesSpecToSheaf.obj (affineToSpecModule M)
  let f := (F.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  let e0 : (F.obj.obj (op ⊤)) ≃ₗ[Γ(X,⊤)] OpenSections M ⊤ := affineSpecSections M ⊤
  let e1 := (affineSpecSections M (PrimeSpectrum.basicOpen r)).trans
    (openSectionsCongr M (Scheme.toSpecΓ_preimage_basicOpen X r))
  have hf : IsLocalizedModule.Away r f := affine_sections_localize M r
  have hq : IsLocalizedModule.Away r (e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap) := by
    let := hf
    let := IsLocalizedModule.of_linearEquiv (.powers r) f e1
    exact IsLocalizedModule.of_linearEquiv_right (.powers r) (e1.toLinearMap ∘ₗ f) e0.symm
  have he : e1.toLinearMap ∘ₗ f ∘ₗ e0.symm.toLinearMap =
      openRestriction M (X.basicOpen_le r) := by
    ext m
    exact openSectionsCongr_restriction M (Scheme.toSpecΓ_preimage_basicOpen X r) m
  rwa [he] at hq

theorem affine_basicOpen_denominators [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r^n • x := by
  let f := openRestriction M (X.basicOpen_le r)
  let : IsLocalizedModule.Away r f := affine_openRestriction_localize M r
  obtain ⟨n,y,hy⟩ := (inferInstance : IsLocalizedModule.Away r f).surj _ _ x
  exact ⟨n,y,hy.symm⟩

def openTopSections (M : X.Modules) :
    letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
    OpenSections M ⊤ ≃ₗ[Γ(X,⊤)] Γ(M,⊤) := by
  letI : Module Γ(X,⊤) Γ(M,⊤) := (M.val.obj (op ⊤)).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,⊤) Γ(M,⊤) _ (restrictScalar X ⊤ r) m =
    @SMul.smul Γ(X,⊤) Γ(M,⊤) _ r m
  congr 1
  change (X.presheaf.map (𝟙 (op ⊤))) r = r
  rw [X.presheaf.map_id]
  rfl

lemma restrictScalar_appIso (f : Y ⟶ X) [IsOpenImmersion f] (U : Y.Opens)
    (r : Γ(X,⊤)) :
    (f.appIso U).inv (restrictScalar Y U (f.appTop r)) =
      restrictScalar X (f ''ᵁ U) r := by
  have h := congrArg (fun g : Γ(X,⊤) ⟶ Γ(X,f ''ᵁ U) => g r)
    (Scheme.Hom.appLE_appIso_inv f (U := ⊤) (V := U) (by simp))
  change (f.appIso U).inv ((f.appLE ⊤ U (by simp)) r) = _ at h
  have he : f.appLE ⊤ U (by simp) = f.appTop ≫ Y.presheaf.map U.leTop.op := by
    erw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  rw [he] at h
  exact h

def restrictedOpenSections (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    (U : Y.Opens) :
    letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
    OpenSections (M.restrict f) U ≃ₗ[Γ(X,⊤)] OpenSections M (f ''ᵁ U) := by
  letI := Module.compHom (OpenSections (M.restrict f) U) f.appTop.hom
  letI : Module Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) := (M.val.obj (op (f ''ᵁ U))).isModule
  refine { toFun := fun x => x
           invFun := fun x => x
           left_inv := fun _ => rfl
           right_inv := fun _ => rfl
           map_add' := fun _ _ => rfl
           map_smul' := ?_ }
  intro r m
  change @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _
      ((f.appIso U).inv (restrictScalar Y U (f.appTop r))) m =
    @SMul.smul Γ(X,f ''ᵁ U) Γ(M,f ''ᵁ U) _ (restrictScalar X (f ''ᵁ U) r) m
  rw [restrictScalar_appIso]

lemma restrictedOpenSections_naturality (M : X.Modules) (f : Y ⟶ X) [IsOpenImmersion f]
    {U V : Y.Opens} (h : U ≤ V) (m : OpenSections (M.restrict f) V) :
    restrictedOpenSections M f U (openRestriction (M.restrict f) h m) =
      openRestriction M (f.image_mono h) (restrictedOpenSections M f V m) := rfl

theorem affine_basicOpen_zero [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M ⊤)
    (hx : openRestriction M (X.basicOpen_le r) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := affine_openRestriction_localize M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r)
      (openRestriction M (X.basicOpen_le r))).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

lemma openRestriction_comp_apply (M : X.Modules) {U V W : X.Opens}
    (hUV : U ≤ V) (hVW : V ≤ W) (x : OpenSections M W) :
    openRestriction M hUV (openRestriction M hVW x) =
      openRestriction M (hUV.trans hVW) x := by
  change M.presheaf.map _ (M.presheaf.map _ x) = M.presheaf.map _ x
  erw [← M.presheaf.map_comp_apply, ← op_comp, homOfLE_comp]

lemma openRestriction_zero_congr (M : X.Modules) {U V W : X.Opens}
    (e : U = V) (hU : U ≤ W) (hV : V ≤ W) (x : OpenSections M W)
    (h : openRestriction M hU x = 0) : openRestriction M hV x = 0 := by
  subst V
  exact h

lemma affine_immersion_zero_on [IsAffine Y] (M : X.Modules) [M.IsQuasicoherent]
    (f : Y ⟶ X) [IsOpenImmersion f] (r : Γ(X,⊤))
    (U : X.Opens) (hU : f ''ᵁ (⊤ : Y.Opens) ≤ U) (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M hU (r ^ n • x) = 0 := by
  let x' := (restrictedOpenSections M f ⊤).symm
    (openRestriction M hU x)
  have hWD : f ''ᵁ (Y.basicOpen (f.appTop r)) ≤ U ⊓ X.basicOpen r := by
    apply le_inf
    · exact (f.image_mono le_top).trans hU
    · rw [← Scheme.preimage_basicOpen_top]
      exact f.image_preimage_le _
  have hx' : openRestriction (M.restrict f) (Y.basicOpen_le (f.appTop r)) x' = 0 := by
    apply (restrictedOpenSections M f _).injective
    rw [map_zero, restrictedOpenSections_naturality]
    simp only [x', LinearEquiv.apply_symm_apply]
    rw [openRestriction_comp_apply]
    rw [← openRestriction_comp_apply M hWD (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x, hx, map_zero]
  obtain ⟨N, hN⟩ := affine_basicOpen_zero (M.restrict f) (f.appTop r) x' hx'
  refine ⟨N, fun n hn => ?_⟩
  have hi := congrArg (restrictedOpenSections M f ⊤) (hN n hn)
  let : Module Γ(X,⊤) (OpenSections (M.restrict f) ⊤) :=
    Module.compHom (OpenSections (M.restrict f) ⊤) f.appTop.hom
  have hscalar : (f.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (f.appTop r) ^ n • x' = f.appTop (r ^ n) • x'
    rw [map_pow]
  rw [hscalar, map_smul, map_zero] at hi
  simpa only [x', LinearEquiv.apply_symm_apply, map_smul] using hi

theorem compact_open_section_zero (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsCompact (U : Set X))
    (x : OpenSections M U)
    (hx : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  classical
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1
    simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun i : s => (i : X.Opens)) i
  have H (i : s) : ∃ N : ℕ, ∀ n ≥ N,
      openRestriction M (h₁ i) (r ^ n • x) = 0 := by
    let : IsAffine i.1.1.toScheme := i.1.2
    have hh := affine_immersion_zero_on M i.1.1.ι r U
      (by simpa only [Scheme.Opens.ι_image_top] using h₁ i) x hx
    obtain ⟨N, hN⟩ := hh
    exact ⟨N, fun n hn => openRestriction_zero_congr M i.1.1.ι_image_top _ _ _ (hN n hn)⟩
  choose n hn using H
  have := hs.to_subtype
  let := Fintype.ofFinite s
  refine ⟨Finset.univ.sup n, fun k hk => ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i : s => (i : X.Opens)) U
    (fun i => homOfLE (h₁ i)) (by rw [e])
  intro i
  have hi := hn i k ((Finset.le_sup (f := n) (Finset.mem_univ i)).trans hk)
  change M.presheaf.map _ (r ^ k • x) = M.presheaf.map _ 0
  rw [map_zero]
  exact hi

lemma openSectionsCongr_naturality (M : X.Modules) {U V U' V' : X.Opens}
    (eU : U = U') (eV : V = V') (h : U ≤ V) (h' : U' ≤ V')
    (x : OpenSections M V) :
    openSectionsCongr M eU (openRestriction M h x) =
      openRestriction M h' (openSectionsCongr M eV x) := by
  subst U' V'
  rfl

lemma principal_open_image (r : Γ(X,⊤)) (U : X.Opens) :
    U.ι ''ᵁ U.toScheme.basicOpen (U.ι.appTop r) = U ⊓ X.basicOpen r := by
  rw [← Scheme.preimage_basicOpen_top, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι]

def affineOpenPrincipalEquiv (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) (U.toScheme.basicOpen (U.ι.appTop r)) ≃ₗ[Γ(X,⊤)]
      OpenSections M (U ⊓ X.basicOpen r) :=
  (restrictedOpenSections M U.ι _).trans (openSectionsCongr M (principal_open_image r U))

def affineOpenTopEquiv (M : X.Modules) (U : X.Opens) :
    letI := Module.compHom (OpenSections (M.restrict U.ι) ⊤) U.ι.appTop.hom
    OpenSections (M.restrict U.ι) ⊤ ≃ₗ[Γ(X,⊤)] OpenSections M U :=
  (restrictedOpenSections M U.ι ⊤).trans (openSectionsCongr M U.ι_image_top)

lemma affineOpenPrincipalEquiv_restrict (M : X.Modules) (r : Γ(X,⊤)) (U : X.Opens)
    (y : OpenSections (M.restrict U.ι) ⊤) :
    affineOpenPrincipalEquiv M r U
      (openRestriction (M.restrict U.ι) (U.toScheme.basicOpen_le (U.ι.appTop r)) y) =
    openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left)
      (affineOpenTopEquiv M U y) := by
  dsimp only [affineOpenPrincipalEquiv, affineOpenTopEquiv, LinearEquiv.trans_apply]
  rw [restrictedOpenSections_naturality]
  exact openSectionsCongr_naturality M (principal_open_image r U) U.ι_image_top _ _ _

theorem affine_open_section_extends (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (U : X.Opens) (hU : IsAffineOpen U)
    (x : OpenSections M (U ⊓ X.basicOpen r)) :
    ∃ n : ℕ, ∃ y : OpenSections M U,
      openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y = r ^ n • x := by
  let : IsAffine U.toScheme := hU
  let : Module Γ(X,⊤) (OpenSections (M.restrict U.ι)
      (U.toScheme.basicOpen (U.ι.appTop r))) :=
    Module.compHom _ U.ι.appTop.hom
  let x' := (affineOpenPrincipalEquiv M r U).symm x
  obtain ⟨n, y, hy⟩ := affine_basicOpen_denominators (M.restrict U.ι) (U.ι.appTop r) x'
  refine ⟨n, affineOpenTopEquiv M U y, ?_⟩
  have hscalar : (U.ι.appTop r) ^ n • x' = (r ^ n) • x' := by
    change (U.ι.appTop r) ^ n • x' = U.ι.appTop (r ^ n) • x'
    rw [map_pow]
  have hh := congrArg (affineOpenPrincipalEquiv M r U) hy
  rw [hscalar, map_smul, affineOpenPrincipalEquiv_restrict] at hh
  simpa only [x', LinearEquiv.apply_symm_apply] using hh

def overlapDifference (M : X.Modules) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V) : OpenSections M (U ⊓ V) :=
  openRestriction M inf_le_left y - openRestriction M inf_le_right z

lemma overlapDifference_restrict_zero (M : X.Modules) (r : Γ(X,⊤))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) {U V : X.Opens}
    (y : OpenSections M U) (z : OpenSections M V)
    (hy : openRestriction M (show U ⊓ X.basicOpen r ≤ U from inf_le_left) y =
      r ^ N • openRestriction M inf_le_right x)
    (hz : openRestriction M (show V ⊓ X.basicOpen r ≤ V from inf_le_left) z =
      r ^ N • openRestriction M inf_le_right x) :
    openRestriction M (show (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ V from inf_le_left)
      (overlapDifference M y z) = 0 := by
  have hU : (U ⊓ V) ⊓ X.basicOpen r ≤ U ⊓ X.basicOpen r := inf_le_inf inf_le_left le_rfl
  have hV : (U ⊓ V) ⊓ X.basicOpen r ≤ V ⊓ X.basicOpen r := inf_le_inf inf_le_right le_rfl
  calc
    _ = openRestriction M hU (openRestriction M inf_le_left y) -
        openRestriction M hV (openRestriction M inf_le_left z) := by
      simp only [overlapDifference, map_sub, openRestriction_comp_apply]
    _ = 0 := by
      rw [hy, hz, map_smul, map_smul, openRestriction_comp_apply, openRestriction_comp_apply,
        sub_self]

lemma overlapDifference_smul_zero_iff (M : X.Modules) (r : Γ(X,⊤))
    {U V : X.Opens} (y : OpenSections M U) (z : OpenSections M V) (K : ℕ) :
    r ^ K • overlapDifference M y z = 0 ↔
      openRestriction M (show U ⊓ V ≤ U from inf_le_left) (r ^ K • y) =
      openRestriction M (show U ⊓ V ≤ V from inf_le_right) (r ^ K • z) := by
  simp only [overlapDifference, smul_sub, map_smul, sub_eq_zero]

theorem clear_finite_overlap_discrepancies (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∀ i j,
      openRestriction M (show U i ⊓ U j ≤ U i from inf_le_left) (r ^ K • y i) =
      openRestriction M (show U i ⊓ U j ≤ U j from inf_le_right) (r ^ K • y j) := by
  classical
  have h (ij : ι × ι) := compact_open_section_zero M r (U ij.1 ⊓ U ij.2)
    (hcompact ij.1 ij.2) (overlapDifference M (y ij.1) (y ij.2))
    (overlapDifference_restrict_zero M r x N _ _ (hy ij.1) (hy ij.2))
  choose k hk using h
  let K := Finset.univ.sup k
  refine ⟨K, fun i j => ?_⟩
  apply (overlapDifference_smul_zero_iff M r (y i) (y j) K).mp
  exact hk (i,j) K (Finset.le_sup (f := k) (Finset.mem_univ (i,j)))

lemma restriction_of_glued_power (M : X.Modules) (r : Γ(X,⊤))
    {ι : Type*} (U : ι → X.Opens) (hcover : (⨆ i, U i) = ⊤)
    (x : OpenSections M (X.basicOpen r)) (N K : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x)
    (z : OpenSections M ⊤)
    (hz : ∀ i, openRestriction M (show U i ≤ ⊤ from le_top) z = r ^ K • y i) :
    openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  apply TopCat.Sheaf.eq_of_locally_eq' ⟨_, M.isSheaf⟩ (fun i => U i ⊓ X.basicOpen r)
    (X.basicOpen r) (fun i => homOfLE inf_le_right)
    (by rw [← iSup_inf_eq, hcover, top_inf_eq])
  intro i
  change openRestriction M inf_le_right (openRestriction M (X.basicOpen_le r) z) =
    openRestriction M inf_le_right (r ^ (N + K) • x)
  rw [openRestriction_comp_apply,
    ← openRestriction_comp_apply M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) le_top z,
    hz i, map_smul, hy i, map_smul, ← mul_smul, ← pow_add, Nat.add_comm K N]

theorem finite_cover_power_gluing (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hcover : (⨆ i, U i) = ⊤)
    (hcompact : ∀ i j, IsCompact ((U i ⊓ U j : X.Opens) : Set X))
    (x : OpenSections M (X.basicOpen r)) (N : ℕ) (y : ∀ i, OpenSections M (U i))
    (hy : ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
      r ^ N • openRestriction M inf_le_right x) :
    ∃ K : ℕ, ∃ z : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) z = r ^ (N + K) • x := by
  obtain ⟨K, hK⟩ := clear_finite_overlap_discrepancies M r U hcompact x N y hy
  have hh := TopCat.Sheaf.existsUnique_gluing' ⟨_, M.isSheaf⟩ U ⊤
    (fun i => homOfLE (show U i ≤ ⊤ from le_top)) (by rw [hcover]) (fun i => r ^ K • y i) ?_
  · obtain ⟨z, hz, _⟩ := hh
    exact ⟨K, z, restriction_of_glued_power M r U hcover x N K y hy z hz⟩
  · intro i j
    exact hK i j

theorem finite_affine_local_extensions (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) {ι : Type*} [Fintype ι] (U : ι → X.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∃ y : ∀ i, OpenSections M (U i),
      ∀ i, openRestriction M (show U i ⊓ X.basicOpen r ≤ U i from inf_le_left) (y i) =
        r ^ N • openRestriction M inf_le_right x := by
  classical
  choose n y hy using fun i => affine_open_section_extends M r (U i) (hU i)
    (openRestriction M (show U i ⊓ X.basicOpen r ≤ X.basicOpen r from inf_le_right) x)
  let N := Finset.univ.sup n
  refine ⟨N, fun i => r ^ (N - n i) • y i, fun i => ?_⟩
  rw [map_smul, hy i, ← mul_smul, ← pow_add,
    Nat.sub_add_cancel (Finset.le_sup (f := n) (Finset.mem_univ i))]

theorem global_section_extends [NoetherianSpace X] (M : X.Modules) [M.IsQuasicoherent]
    (r : Γ(X,⊤)) (x : OpenSections M (X.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : OpenSections M ⊤,
      openRestriction M (X.basicOpen_le r) y = r ^ n • x := by
  classical
  obtain ⟨s, hs, e⟩ :=
    (isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (X := X)
      (U := ((⊤ : X.Opens) : Set X))).mp
      ⟨NoetherianSpace.isCompact _, (⊤ : X.Opens).2⟩
  have hcover : (⨆ i : s, (i : X.Opens)) = ⊤ := by
    ext1
    simpa using e.symm
  have := hs.to_subtype
  let := Fintype.ofFinite s
  obtain ⟨N, y, hy⟩ := finite_affine_local_extensions M r (fun i : s => (i : X.Opens))
    (fun i => i.1.2) x
  obtain ⟨K, z, hz⟩ := finite_cover_power_gluing M r (fun i : s => (i : X.Opens)) hcover
    (fun i j => NoetherianSpace.isCompact _) x N y hy
  refine ⟨N + K, fun n hn => ⟨r ^ (n - (N + K)) • z, ?_⟩⟩
  rw [map_smul, hz, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem global_section_extends_native [NoetherianSpace X]
    (M : X.Modules) [M.IsQuasicoherent] (r : Γ(X,⊤)) (x : Γ(M, X.basicOpen r)) :
    letI : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
      (M.val.obj (op (X.basicOpen r))).isModule
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : Γ(M,⊤),
      M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
        (restrictScalar X (X.basicOpen r) r) ^ n • x := by
  let : Module Γ(X, X.basicOpen r) Γ(M, X.basicOpen r) :=
    (M.val.obj (op (X.basicOpen r))).isModule
  obtain ⟨N, hN⟩ := global_section_extends M r x
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨y, hy⟩ := hN n hn
  refine ⟨y, ?_⟩
  change M.presheaf.map (homOfLE (X.basicOpen_le r)).op y =
    (restrictScalar X (X.basicOpen r) (r ^ n)) • x at hy
  simpa only [map_pow] using hy

end
end PiExponent.GlobalSectionClearing

end OAI
end Source0319

-- Source: OAI/NumberTheory/PiExponent/Ampleness/CoherentAffineFinite.lean
section Source0320
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/CoherentAffineFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.CoherentAffineFinite
noncomputable section
universe u
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

private theorem epi_iso_comp_iso {C : Type*} [Category C] {A B D E : C}
    (i : A ≅ B) (p : B ⟶ D) (hp : Epi p) (j : D ≅ E) :
    Epi (i.hom ≫ p ≫ j.hom) := by
  let : Epi p := hp
  infer_instance

private theorem finitePresentation_quasicoherent {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : M.IsQuasicoherent :=
  (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent

theorem spec_sections_finite_of_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  let : Finite s.I := hs.finite
  let : Fintype s.I := Fintype.ofFinite s.I
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let a : tilde (ModuleCat.of R (s.I →₀ R)) ⟶ tilde N :=
    (tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv
  let f : ModuleCat.of R (s.I →₀ R) ⟶ N := (tilde.functor R).preimage a
  have : Epi s.π := s.epi
  have : Epi (asIso M.fromTildeΓ).inv := inferInstance
  have ha : Epi a := by
    change Epi ((tildeFinsupp s.I).hom ≫ s.π ≫ (asIso M.fromTildeΓ).inv)
    exact epi_iso_comp_iso (tildeFinsupp s.I) s.π s.epi (asIso M.fromTildeΓ).symm
  have hf : Epi f := (tilde.functor R).epi_of_epi_map (by
    change Epi ((tilde.functor R).map ((tilde.functor R).preimage a))
    exact (Functor.map_preimage (tilde.functor R) a).symm ▸ ha)
  exact Module.Finite.of_surjective f.hom ((ModuleCat.epi_iff_surjective f).mp hf)

theorem affine_sections_finite_of_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    (s : M.GeneratingSections) [hs : s.IsFiniteType] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let F : SheafOfModules X.ringCatSheaf ⥤ SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf :=
    Scheme.Modules.restrictFunctor f
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction f).leftAdjoint_preservesColimits
  let J := M.restrict f
  let t := s.map F (Scheme.Modules.restrictUnitIso f).symm
  let : t.IsFiniteType := ⟨hs.finite⟩
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_generators J t
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

def LocallyFinitelyGenerated {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ s : (M.restrict U.ι).GeneratingSections, s.IsFiniteType

theorem locallyFinitelyGenerated_of_finitePresentation {X : Scheme.{u}}
    (M : X.Modules) [M.IsFinitePresentation] : LocallyFinitelyGenerated M := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  intro x
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  refine ⟨q.X i, hi, ?_⟩
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let t := (q.presentation i).generators.map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩⟩

theorem finite_generators_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    ∃ t : (M.restrict V.ι).GeneratingSections, t.IsFiniteType := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_open_sections_finite_of_generators {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U)
    (s : (M.restrict U.ι).GeneratingSections) [s.IsFiniteType] :
    Module.Finite Γ(X,U) Γ(M,U) := by
  let : IsAffine U.toScheme := hU
  let : Module.Finite Γ(U.toScheme,⊤) Γ(M.restrict U.ι,⊤) :=
    affine_sections_finite_of_generators (M.restrict U.ι) s
  let σ := (U.ι.appIso ⊤).inv.hom
  let φ : Γ(M.restrict U.ι,⊤) →ₛₗ[σ] Γ(M,U.ι ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso U.ι ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso U.ι ⊤).hom).surjective
  have h := Module.Finite.of_surjective φ hφ
  rwa [U.ι_image_top] at h

theorem spec_sections_finite_of_localGenerators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)) := by
  classical
  let D (r : R) : (Spec R).Opens := PrimeSpectrum.basicOpen r
  let t : Set R := {r | ∃ s : (M.restrict (D r).ι).GeneratingSections, s.IsFiniteType}
  have ht : Ideal.span t = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    apply top_unique
    intro x hx
    obtain ⟨U,hxU,s,hs⟩ := hM x
    obtain ⟨_,⟨_,⟨r,rfl⟩,rfl⟩,hxr,hrU⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxU U.isOpen
    exact Opens.mem_iSup.mpr ⟨r, Opens.mem_iSup.mpr
      ⟨finite_generators_of_le M hrU s,hxr⟩⟩
  let N := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  let A (r : t) := Γ(Spec R, PrimeSpectrum.basicOpen r.val)
  let P (r : t) := Γ(M, PrimeSpectrum.basicOpen r.val)
  let (r : t) : Algebra R (A r) := StructureSheaf.openAlgebra (R := R) (op (PrimeSpectrum.basicOpen r.val))
  let (r : t) : IsLocalization.Away r.val (A r) := inferInstanceAs
    (IsLocalization.Away r.val ((Spec.structureSheaf R).obj.obj (op (PrimeSpectrum.basicOpen r.val))))
  let (r : t) : Module (A r) (P r) :=
    (M.val.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : Module R (P r) :=
    ((modulesSpecToSheaf.obj M).obj.obj (op (PrimeSpectrum.basicOpen r.val))).isModule
  let (r : t) : IsScalarTower R (A r) (P r) :=
    IsScalarTower.of_compHom R (A r) (P r)
  let f (r : t) : N →ₗ[R] P r :=
    ((modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op).hom
  have hloc := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance
  let (r : t) : IsLocalizedModule.Away r.val (f r) := hloc r.val
  have hfin (r : t) : Module.Finite (A r) (P r) := by
    obtain ⟨s, hs⟩ := r.property
    exact affine_open_sections_finite_of_generators M (D r.val)
      (IsAffineOpen.Spec_basicOpen r.val) s
  exact Module.Finite.of_localizationSpan' t ht f hfin

theorem LocallyFinitelyGenerated.restrict {X Y : Scheme.{u}} {M : Y.Modules}
    (hM : LocallyFinitelyGenerated M) (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyFinitelyGenerated (M.restrict f) := by
  intro x
  obtain ⟨U, hxU, s, hs⟩ := hM (f x)
  let V := f ⁻¹ᵁ U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (f ∣_ U)
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction (f ∣_ U)).leftAdjoint_preservesColimits
  let t := s.map F
    (Scheme.Modules.restrictUnitIso (f ∣_ U)).symm
  let e := (Scheme.Modules.restrictFunctorComp (f ∣_ U) U.ι).app M
  have e' : M.restrict (V.ι ≫ f) ≅ (M.restrict U.ι).restrict (f ∣_ U) := by
    change M.restrict ((f ∣_ U) ≫ U.ι) ≅ (M.restrict U.ι).restrict (f ∣_ U) at e
    simpa only [V, morphismRestrict_ι] using e
  let e'' := ((Scheme.Modules.restrictFunctorComp V.ι f).app M).symm ≪≫ e'
  exact ⟨V, hxU, SheafOfModules.GeneratingSections.equivOfIso e''.symm t,
    ⟨SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := s)⟩⟩

theorem affine_sections_finite_of_localGenerators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let R := Γ(X,⊤)
  let N := (modulesSpecToSheaf.obj J).obj.obj (op ⊤)
  let : Module.Finite R N := spec_sections_finite_of_localGenerators J
    (hM.restrict f)
  let σ : R →+* Γ(X,f ''ᵁ ⊤) := (f.appIso ⊤).inv.hom.comp (Scheme.ΓSpecIso R).inv.hom
  let φ : N →ₛₗ[σ] Γ(M,f ''ᵁ ⊤) := {
    toFun := (M.restrictAppIso f ⊤).hom
    map_add' := map_add _
    map_smul' := by intro r m; rfl }
  have hφ : Function.Surjective φ :=
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).hom).surjective
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have h := Module.Finite.of_surjective φ hφ
  rw [hf] at h
  exact h

theorem affine_sections_finite {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsFinitePresentation] : Module.Finite Γ(X,⊤) Γ(M,⊤) := by
  let := finitePresentation_quasicoherent M
  exact affine_sections_finite_of_localGenerators M (locallyFinitelyGenerated_of_finitePresentation M)

theorem finite_isoSpec_sections {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    Module.Finite Γ(X,⊤)
      ((modulesSpecToSheaf.obj (M.restrict X.isoSpec.inv)).obj.obj (op ⊤)) := by
  let f := X.isoSpec.inv
  let R := Γ(X,⊤)
  let N : ModuleCat R := (modulesSpecToSheaf.obj (M.restrict f)).obj.obj (op ⊤)
  have hf : f ''ᵁ (⊤ : (Spec R).Opens) = ⊤ := by
    ext x
    change (∃ y : Spec R, y ∈ (⊤ : (Spec R).Opens) ∧ f y = x) ↔ True
    simp only [Opens.mem_top, true_and, iff_true]
    exact (ConcreteCategory.bijective_of_isIso f.base).surjective x
  have : Module.Finite Γ(X,f ''ᵁ ⊤) Γ(M,f ''ᵁ ⊤) := by
    rw [hf]
    infer_instance
  let σ : Γ(X,f ''ᵁ ⊤) →+* R := (Scheme.ΓSpecIso R).hom.hom.comp (f.appIso ⊤).hom.hom
  let φ : Γ(M,f ''ᵁ ⊤) →ₛₗ[σ] N := {
    toFun := (M.restrictAppIso f ⊤).inv
    map_add' := map_add _
    map_smul' := by
      intro r m
      change (M.restrictAppIso f ⊤).inv (r • m) =
        ((Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom ((f.appIso ⊤).hom r))) •
          (M.restrictAppIso f ⊤).inv m
      rw [Iso.hom_inv_id_apply]
      exact congr($(M.smul_restrictAppIso_inv f ⊤ r) m) }
  exact Module.Finite.of_surjective φ
    (ConcreteCategory.bijective_of_isIso (M.restrictAppIso f ⊤).inv).surjective

theorem spec_exists_finite_generators {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let N : ModuleCat R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  obtain ⟨I,hI,v,hv⟩ : ∃ (I : Type u) (_ : Finite I) (v : I → N),
      Submodule.span R (Set.range v) = ⊤ :=
    Submodule.fg_iff_exists_finite_generating_family.mp (Module.Finite.fg_top (R := R) (M := N))
  let f : ModuleCat.of R (I →₀ R) ⟶ N := ModuleCat.ofHom (X := I →₀ R) (Y := N) (Finsupp.linearCombination (M := N) R v)
  have : Epi f := (ModuleCat.epi_iff_surjective f).mpr <| by
    change Function.Surjective (Finsupp.linearCombination (M := N) R v)
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination, hv]
  let p : SheafOfModules.free I ⟶ M :=
    (tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ
  have hmap : Epi ((tilde.functor R).map f) := inferInstance
  have : Epi M.fromTildeΓ := inferInstance
  have hp : Epi p := by
    change Epi ((tildeFinsupp I).inv ≫ (tilde.functor R).map f ≫ M.fromTildeΓ)
    let hΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
    exact epi_iso_comp_iso (tildeFinsupp I).symm ((tilde.functor R).map f) hmap
      (@asIso _ _ _ _ M.fromTildeΓ hΓ)
  let s : M.GeneratingSections := {
    I := I
    s := M.freeHomEquiv p
    epi := by simpa only [Equiv.symm_apply_apply] using hp }
  exact ⟨s, ⟨hI⟩⟩

theorem affine_exists_finite_generators {X : Scheme.{u}} [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ s : M.GeneratingSections, s.IsFiniteType := by
  let f := X.isoSpec.inv
  let J := M.restrict f
  let : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj J).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨s,hs⟩ := spec_exists_finite_generators J
  let g := X.isoSpec.hom
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor g
  let : Limits.PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.restrictAdjunction g).leftAdjoint_preservesColimits
  let t := s.map F (Scheme.Modules.restrictUnitIso g).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp g f).app M
  have e₂ : M.restrict (𝟙 X) ≅ J.restrict g := by
    change M.restrict (g ≫ f) ≅ J.restrict g at e₁
    simpa only [g, f, Iso.hom_inv_id] using e₁
  let e := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨SheafOfModules.GeneratingSections.equivOfIso e t,
    ⟨hs.finite⟩⟩

end
end PiExponent.CoherentAffineFinite

end OAI
end Source0320

-- Source: OAI/NumberTheory/PiExponent/Approximation/CoherentTwistPresentation.lean
section Source0321
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoherentTwistPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace PiExponent.CoherentTwist

universe u
variable {R : CommRingCat.{u}} (M : (Spec R).Modules) [M.IsQuasicoherent]

abbrev affineSections (U : (Spec R).Opens) :=
  (modulesSpecToSheaf.obj M).obj.obj (op U)

abbrev principalRestriction (r : R) :=
  ((modulesSpecToSheaf.obj M).obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom

open TopologicalSpace
variable {X : Scheme.{u}} {P Q : X.Modules}

lemma app_zero_of_restrict (φ : P ⟶ Q) (U W : X.Opens) (hW : W ≤ U)
    (h : (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ.app W = 0 := by
  have hz := congrArg (fun q : P.restrict U.ι ⟶ Q.restrict U.ι =>
    q.app (U.ι ⁻¹ᵁ W)) h
  have he : U.ι ''ᵁ U.ι ⁻¹ᵁ W = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hW]
  change φ.app (U.ι ''ᵁ U.ι ⁻¹ᵁ W) = 0 at hz
  suffices hh : ∀ A : X.Opens, A = W → φ.app A = 0 → φ.app W = 0 from hh _ he hz
  intro A hA hφ
  subst A
  exact hφ

lemma eq_zero_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (Scheme.Modules.restrictFunctor U.ι).map φ = 0) : φ = 0 := by
  ext W m
  change φ.app W m = 0
  let F : (X : TopCat).Sheaf AddCommGrpCat := (SheafOfModules.toSheaf X.ringCatSheaf).obj Q
  apply TopCat.Presheaf.section_ext F W (φ.app W m) 0
  intro x hx
  obtain ⟨U,hxU,hU⟩ := h x
  let V : X.Opens := W ⊓ U
  have hv : φ.app V = 0 := app_zero_of_restrict φ U V inf_le_right hU
  change Q.presheaf.germ W x hx (φ.app W m) = Q.presheaf.germ W x hx 0
  rw [← TopCat.Presheaf.germ_res_apply Q.presheaf (homOfLE (show V ≤ W from inf_le_left))
    x (show x ∈ V from ⟨hx,hxU⟩)]
  have hn := CategoryTheory.congr_fun (φ.mapPresheaf.naturality
    (homOfLE (show V ≤ W from inf_le_left)).op) m
  change φ.app V (P.presheaf.map (homOfLE inf_le_left).op m) =
    Q.presheaf.map (homOfLE inf_le_left).op (φ.app W m) at hn
  rw [← hn,hv]
  simp

lemma epi_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Epi ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Epi φ := by
  apply (Preadditive.epi_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U,hx,hU⟩ := h x
  let := hU
  refine ⟨U,hx,?_⟩
  apply (cancel_epi ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp,hg,Functor.map_zero,comp_zero]

lemma mono_of_local (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Mono ((Scheme.Modules.restrictFunctor U.ι).map φ)) : Mono φ := by
  apply (Preadditive.mono_iff_cancel_zero _).mpr
  intro T g hg
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  refine ⟨U, hx, ?_⟩
  apply (cancel_mono ((Scheme.Modules.restrictFunctor U.ι).map φ)).mp
  rw [← Functor.map_comp, hg, Functor.map_zero, zero_comp]

lemma exact_of_local (S : ShortComplex X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      (S.map (Scheme.Modules.restrictFunctor U.ι)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply eq_zero_of_local
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  have hz : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj S.homology) :=
    ((ShortComplex.exact_iff_isZero_homology _).mp hU).of_iso
      (S.mapHomologyIso (Scheme.Modules.restrictFunctor U.ι)).symm
  refine ⟨U, hx, ?_⟩
  rw [CategoryTheory.Functor.map_id]
  exact hz.eq_of_src _ _

end PiExponent.CoherentTwist

namespace PiExponentSeshadri.Geometry
open MonoidalCategory
variable {X : Scheme}

private lemma tensorRestrict_natural {C D : Type*} [Category C] [Category D]
    [mC : MonoidalCategory C] [mD : MonoidalCategory D] (R F : C ⥤ D) [F.OplaxMonoidal]
    (e : R ≅ F) {M N P Q : C} (f : M ⟶ N) (g : P ⟶ Q) :
    R.map (f ⊗ₘ g) ≫ (e.hom.app (N ⊗ Q) ≫
      Functor.OplaxMonoidal.δ F N Q ≫ (e.inv.app N ⊗ₘ e.inv.app Q)) =
    (e.hom.app (M ⊗ P) ≫ Functor.OplaxMonoidal.δ F M P ≫
      (e.inv.app M ⊗ₘ e.inv.app P)) ≫ (R.map f ⊗ₘ R.map g) := by
  rw [← Category.assoc, e.hom.naturality, Category.assoc,
    ← Category.assoc (F.map (f ⊗ₘ g)), ← Functor.OplaxMonoidal.δ_natural,
    Category.assoc, tensorHom_comp_tensorHom, e.inv.naturality,
    e.inv.naturality, ← tensorHom_comp_tensorHom]
  simp only [Category.assoc]

private lemma modulePresheafTensorRestrict_natural_aux (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    type_of% (tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g) :=
  tensorRestrict_natural
    (C := PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (D := PresheafOfModules
      ((U.ι.opensFunctor.op ⋙ X.presheaf) ⋙ forget₂ CommRingCat RingCat))
    (mC := PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf))
    (mD := PresheafOfModulesOfCommRing.monoidalCategory
      (R := U.ι.opensFunctor.op ⋙ X.presheaf))
    (modulePresheafRestrict U.ι)
    (PresheafOfModules.pushforward₀OfCommRingCat U.ι.opensFunctor X.presheaf)
    (modulePresheafRestrictOpensIso U) f g

lemma modulePresheafTensorRestrict_natural (U : X.Opens)
    {M N P Q : PresheafOfModules X.ringCatSheaf.obj}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (modulePresheafRestrict U.ι).map
        (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f g) ≫
      (modulePresheafTensorRestrict U N Q).hom =
    (modulePresheafTensorRestrict U M P).hom ≫
      PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
        ((modulePresheafRestrict U.ι).map f) ((modulePresheafRestrict U.ι).map g) := by
  dsimp only [modulePresheafTensorRestrict, Iso.trans_hom, Iso.symm_hom,
    Functor.Monoidal.μIso_inv, tensorIso_hom]
  exact modulePresheafTensorRestrict_natural_aux U f g

lemma moduleTensorRestrict_natural (U : X.Opens) {M N P Q : X.Modules}
    (f : M ⟶ N) (g : P ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f g) ≫
      (moduleTensorRestrict U N Q).hom =
    (moduleTensorRestrict U M P).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
        ((Scheme.Modules.restrictFunctor U.ι).map g) := by
  let K : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let R : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let Rpre : PresheafOfModules X.ringCatSheaf.obj ⥤
      PresheafOfModules U.toScheme.ringCatSheaf.obj := modulePresheafRestrict U.ι
  let S : PresheafOfModules U.toScheme.ringCatSheaf.obj ⥤ U.toScheme.Modules :=
    PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  let e : K ⋙ R ≅ Rpre ⋙ S := moduleSheafificationRestrict U.ι
  let h := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val
  let k := PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := U.toScheme.presheaf)
    (Rpre.map f.val) (Rpre.map g.val)
  let a := (modulePresheafTensorRestrict U M.val P.val).hom
  let b := (modulePresheafTensorRestrict U N.val Q.val).hom
  change R.map (K.map h) ≫ (e.hom.app _ ≫ S.map b) =
    (e.hom.app _ ≫ S.map a) ≫ S.map k
  have ht : Rpre.map h ≫ b = a ≫ k := modulePresheafTensorRestrict_natural U f.val g.val
  calc
    _ = (R.map (K.map h) ≫ e.hom.app _) ≫ S.map b :=
      (Category.assoc _ _ _).symm
    _ = (e.hom.app _ ≫ S.map (Rpre.map h)) ≫ S.map b :=
      congrArg (· ≫ S.map b) (e.hom.naturality h)
    _ = e.hom.app _ ≫ (S.map (Rpre.map h) ≫ S.map b) := Category.assoc _ _ _
    _ = e.hom.app _ ≫ S.map (Rpre.map h ≫ b) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _).symm
    _ = e.hom.app _ ≫ S.map (a ≫ k) :=
      congrArg (fun t => e.hom.app _ ≫ S.map t) ht
    _ = e.hom.app _ ≫ (S.map a ≫ S.map k) :=
      congrArg (e.hom.app _ ≫ ·) (S.map_comp _ _)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorRightFunctor (L : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := moduleTensor X M L
  map f := moduleTensorMap f (𝟙 L)
  map_id M := moduleTensorMap_id M L
  map_comp f g := by simpa using moduleTensorMap_comp f g (𝟙 L) (𝟙 L)

@[simp] theorem moduleTensorIso_hom {M N P Q : X.Modules}
    (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).hom = moduleTensorMap e.hom f.hom := rfl

@[reassoc] theorem moduleTensorRightUnit_natural {M N : X.Modules} (f : M ⟶ N) :
    moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom =
      (moduleTensorRightUnit M).hom ≫ f := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let S : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf)
    (𝟙 X.ringCatSheaf.obj)
  change S.map (f.val ⊗ₘ 𝟙 _) ≫ (S.map (ρ_ N.val).hom ≫ adj.counit.app N) =
    (S.map (ρ_ M.val).hom ≫ adj.counit.app M) ≫ f
  have hu : (f.val ⊗ₘ 𝟙 _) ≫ (ρ_ N.val).hom = (ρ_ M.val).hom ≫ f.val := by
    simpa only [tensorHom_id] using rightUnitor_naturality f.val
  have hS : S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom =
      S.map (ρ_ M.val).hom ≫ S.map f.val :=
    (S.map_comp _ _).symm.trans ((congrArg S.map hu).trans (S.map_comp _ _))
  calc
    _ = (S.map (f.val ⊗ₘ 𝟙 _) ≫ S.map (ρ_ N.val).hom) ≫ adj.counit.app N :=
      (Category.assoc _ _ _).symm
    _ = (S.map (ρ_ M.val).hom ≫ S.map f.val) ≫ adj.counit.app N :=
      congrArg (· ≫ adj.counit.app N) hS
    _ = S.map (ρ_ M.val).hom ≫ (S.map f.val ≫ adj.counit.app N) :=
      Category.assoc _ _ _
    _ = S.map (ρ_ M.val).hom ≫ (adj.counit.app M ≫ f) :=
      congrArg (S.map (ρ_ M.val).hom ≫ ·) (adj.counit.naturality f)
    _ = _ := (Category.assoc _ _ _).symm

def moduleTensorFrame (M : X.Modules) {L : X.Modules}
    (e : L ≅ structureSheaf X) : moduleTensor X M L ≅ M :=
  moduleTensorIso (Iso.refl M) e ≪≫ moduleTensorRightUnit M

@[reassoc] theorem moduleTensorFrame_natural {M N L : X.Modules}
    (f : M ⟶ N) (e : L ≅ structureSheaf X) :
    moduleTensorMap f (𝟙 L) ≫ (moduleTensorFrame N e).hom =
      (moduleTensorFrame M e).hom ≫ f := by
  simp only [moduleTensorFrame, Iso.trans_hom, moduleTensorIso_hom, Iso.refl_hom]
  calc
    _ = moduleTensorMap f e.hom ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = moduleTensorMap (𝟙 M) e.hom ≫
        moduleTensorMap f (𝟙 (structureSheaf X)) ≫ (moduleTensorRightUnit N).hom := by
      rw [← Category.assoc, ← moduleTensorMap_comp]
      simp only [Category.comp_id, Category.id_comp]
    _ = _ := by rw [moduleTensorRightUnit_natural, Category.assoc]

def moduleTensorRestrictFrame (U : X.Opens) (L : X.Modules)
    (e : L.restrict U.ι ≅ structureSheaf U.toScheme) :
    moduleTensorRightFunctor L ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι :=
  NatIso.ofComponents
    (fun M => moduleTensorRestrict U M L ≪≫ moduleTensorFrame (M.restrict U.ι) e)
    (by
      intro M N f
      change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (𝟙 L)) ≫
          ((moduleTensorRestrict U N L).hom ≫ (moduleTensorFrame (N.restrict U.ι) e).hom) =
        ((moduleTensorRestrict U M L).hom ≫ (moduleTensorFrame (M.restrict U.ι) e).hom) ≫
          (Scheme.Modules.restrictFunctor U.ι).map f
      rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
        CategoryTheory.Functor.map_id, moduleTensorFrame_natural, Category.assoc])

theorem moduleTensorMap_epi {M N : X.Modules} (f : M ⟶ N) [Epi f]
    (L : LineBundle X) : Epi (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.epi_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Epi (F.map f) := inferInstanceAs
    (Epi ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Epi (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

theorem moduleTensorMap_mono {M N : X.Modules} (f : M ⟶ N) [Mono f]
    (L : LineBundle X) : Mono (moduleTensorMap f (𝟙 L.sheaf)) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
  let E : moduleTensorRightFunctor L.sheaf ⋙ F ≅ F := moduleTensorRestrictFrame U L.sheaf e
  have h : F.map (moduleTensorMap f (𝟙 L.sheaf)) =
      (E.app M).hom ≫ F.map f ≫ (E.app N).inv := by
    exact ((E.app N).eq_comp_inv.mpr (E.hom.naturality f)).trans
      (Category.assoc _ _ _)
  rw [h]
  let : Mono (F.map f) := inferInstanceAs
    (Mono ((Scheme.Modules.restrictFunctor U.ι).map f))
  let : IsIso (E.app M).hom := (E.app M).isIso_hom
  let : IsIso (E.app N).inv := (E.app N).isIso_inv
  exact (inferInstance : Mono (C := U.toScheme.Modules)
    ((E.app M).hom ≫ F.map f ≫ (E.app N).inv))

instance moduleTensorRightFunctor_preservesZero (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).PreservesZeroMorphisms where
  map_zero M N := by
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let E := moduleTensorRestrictFrame U L.sheaf e
    apply (cancel_mono (E.app N).hom).mp
    rw [zero_comp]
    change ((moduleTensorRightFunctor L.sheaf ⋙ Scheme.Modules.restrictFunctor U.ι).map
      (0 : M ⟶ N)) ≫ E.hom.app N = 0
    rw [E.hom.naturality, CategoryTheory.Functor.map_zero, comp_zero]

theorem moduleTensorRightFunctor_exact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).Exact := by
  apply PiExponent.CoherentTwist.exact_of_local
  intro x
  obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
  refine ⟨U, hx, ?_⟩
  exact ShortComplex.exact_of_iso
    (S.mapNatIso (moduleTensorRestrictFrame U L.sheaf e)).symm
    (hS.map (Scheme.Modules.restrictFunctor U.ι))

theorem moduleTensorRightFunctor_shortExact (L : LineBundle X)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTensorRightFunctor L.sheaf)).ShortExact where
  exact := moduleTensorRightFunctor_exact L S hS.exact
  mono_f := by
    have := hS.mono_f
    exact moduleTensorMap_mono S.f L
  epi_g := by
    have := hS.epi_g
    exact moduleTensorMap_epi S.g L

instance moduleTensorRightFunctor_additive (L : LineBundle X) :
    (moduleTensorRightFunctor L.sheaf).Additive where
  map_add {M N} {f g} := by
    apply sub_eq_zero.mp
    apply PiExponent.CoherentTwist.eq_zero_of_local
    intro x
    obtain ⟨U, hx, ⟨e⟩⟩ := L.locallyRankOne x
    refine ⟨U, hx, ?_⟩
    let F := Scheme.Modules.restrictFunctor U.ι
    let T := moduleTensorRightFunctor L.sheaf
    let E := moduleTensorRestrictFrame U L.sheaf e
    have h (a : M ⟶ N) : F.map (T.map a) =
        (E.app M).hom ≫ F.map a ≫ (E.app N).inv := by
      apply (cancel_mono (E.app N).hom).mp
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
      exact E.hom.naturality a
    change F.map (T.map (f + g) - (T.map f + T.map g)) = 0
    rw [F.map_sub, F.map_add, h (f+g), h f, h g, F.map_add,
      Preadditive.add_comp, Preadditive.comp_add, sub_self]

def moduleTwistFunctor (L : LineBundle X) : ℕ → X.Modules ⥤ X.Modules
  | 0 => 𝟭 _
  | n + 1 => moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf

instance moduleTwistFunctor_additive (L : LineBundle X) (n : ℕ) :
    (moduleTwistFunctor L n).Additive := by
  induction n with
  | zero => change (𝟭 X.Modules).Additive; infer_instance
  | succ n ih =>
    change (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf).Additive
    infer_instance

theorem moduleTwistFunctor_add (L : LineBundle X) (m n : ℕ) :
    moduleTwistFunctor L (m+n) = moduleTwistFunctor L m ⋙ moduleTwistFunctor L n := by
  induction n with
  | zero =>
    change moduleTwistFunctor L m = moduleTwistFunctor L m ⋙ 𝟭 _
    rfl
  | succ n ih =>
    change moduleTwistFunctor L (m+n) ⋙ moduleTensorRightFunctor L.sheaf =
      moduleTwistFunctor L m ⋙ (moduleTwistFunctor L n ⋙ moduleTensorRightFunctor L.sheaf)
    rw [ih]
    rfl

theorem moduleTwistFunctor_shortExact (L : LineBundle X) (n : ℕ)
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (moduleTwistFunctor L n)).ShortExact := by
  induction n with
  | zero => exact hS
  | succ n ih =>
    change ((S.map (moduleTwistFunctor L n)).map
      (moduleTensorRightFunctor L.sheaf)).ShortExact
    exact moduleTensorRightFunctor_shortExact L (S.map (moduleTwistFunctor L n)) ih

def moduleTensorComm (M N : X.Modules) : moduleTensor X M N ≅ moduleTensor X N M := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let : SymmetricCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.symmetricCategory (R := X.presheaf)
  exact (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso (β_ M.val N.val)

def moduleTwistUnitIso (L : LineBundle X) : ∀ n : ℕ,
    (moduleTwistFunctor L n).obj (structureSheaf X) ≅ modulePow X L.sheaf n
  | 0 => Iso.refl _
  | n+1 => moduleTensorIso (moduleTwistUnitIso L n) (Iso.refl L.sheaf) ≪≫
      moduleTensorComm (modulePow X L.sheaf n) L.sheaf

end PiExponentSeshadri.Geometry

end

end OAI
end Source0321

-- Source: OAI/NumberTheory/PiExponent/Approximation/TwistSections.lean
section Source0322
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TwistSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable {X : Scheme}

def moduleSectionMultiplyRight (M : X.Modules) {L : X.Modules}
    (s : structureSheaf X ⟶ L) : M ⟶ moduleTensor X M L :=
  (moduleTensorRightUnit M).inv ≫ moduleTensorMap (𝟙 M) s

@[reassoc] theorem moduleSectionMultiplyRight_natural {M N L : X.Modules}
    (f : M ⟶ N) (s : structureSheaf X ⟶ L) :
    f ≫ moduleSectionMultiplyRight N s =
      moduleSectionMultiplyRight M s ≫ moduleTensorMap f (𝟙 L) := by
  have h : f ≫ (moduleTensorRightUnit N).inv =
      (moduleTensorRightUnit M).inv ≫ moduleTensorMap f (𝟙 (structureSheaf X)) := by
    apply (cancel_mono (moduleTensorRightUnit N).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [moduleTensorRightUnit_natural]
    simp
  unfold moduleSectionMultiplyRight
  rw [← Category.assoc, h, Category.assoc, ← moduleTensorMap_comp,
    Category.comp_id, Category.id_comp]
  rw [Category.assoc, ← moduleTensorMap_comp]
  simp

def moduleSectionMultiplyRightNat {L : X.Modules} (s : structureSheaf X ⟶ L) :
    𝟭 X.Modules ⟶ moduleTensorRightFunctor L where
  app M := moduleSectionMultiplyRight M s
  naturality _ _ f := moduleSectionMultiplyRight_natural f s

def moduleTwistStep (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+1) where
  app M := moduleSectionMultiplyRight ((moduleTwistFunctor L n).obj M) s
  naturality _ _ f := moduleSectionMultiplyRight_natural ((moduleTwistFunctor L n).map f) s

def moduleTwistSection (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) :
    ∀ n : ℕ, 𝟭 X.Modules ⟶ moduleTwistFunctor L n
  | 0 => 𝟙 _
  | n+1 => moduleTwistSection L s n ≫ moduleTwistStep L s n

def moduleTwistForward (L : LineBundle X) (s : structureSheaf X ⟶ L.sheaf) (n : ℕ) :
    ∀ k : ℕ, moduleTwistFunctor L n ⟶ moduleTwistFunctor L (n+k)
  | 0 => 𝟙 _
  | k+1 => moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k)

@[simp] theorem moduleTwistSection_add (L : LineBundle X)
    (s : structureSheaf X ⟶ L.sheaf) (n k : ℕ) :
    moduleTwistSection L s (n+k) = moduleTwistSection L s n ≫ moduleTwistForward L s n k := by
  induction k with
  | zero => exact (Category.comp_id _).symm
  | succ k ih =>
    change moduleTwistSection L s (n+k) ≫ moduleTwistStep L s (n+k) =
      moduleTwistSection L s n ≫
        (moduleTwistForward L s n k ≫ moduleTwistStep L s (n+k))
    rw [ih, Category.assoc]

def moduleTwistRestrictFrame (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
    ∀ n : ℕ, moduleTwistFunctor L n ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.restrictFunctor U.ι
  | 0 => Iso.refl _
  | n+1 => Functor.isoWhiskerLeft (moduleTwistFunctor L n)
      (moduleTensorRestrictFrame U L.sheaf e) ≪≫ moduleTwistRestrictFrame L U e n

@[simp] theorem moduleTwistRestrictFrame_zero (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) :
    ((moduleTwistRestrictFrame L U e 0).app M).hom = 𝟙 (M.restrict U.ι) := rfl

@[simp] theorem moduleTwistRestrictFrame_succ (L : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) (M : X.Modules) (n : ℕ) :
    ((moduleTwistRestrictFrame L U e (n+1)).app M).hom =
      ((moduleTensorRestrictFrame U L.sheaf e).app ((moduleTwistFunctor L n).obj M)).hom ≫
        ((moduleTwistRestrictFrame L U e n).app M).hom := rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0322

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteGlobalPresentation.lean
section Source0323
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FiniteGlobalPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.FiniteGlobalPresentation
noncomputable section
universe u v₁ v₂ u₁ u₂
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponent.CoherentAffineFinite

section PresentationMap
variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {C' : Type u₂} [Category.{v₂} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}} [HasSheafify J' AddCommGrpCat.{u}]
  [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

instance presentation_map_isFinite (P : M.Presentation) [P.IsFinite]
    (F : SheafOfModules.{u} R ⥤ SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u,u} F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R)) :
    (P.map F η).IsFinite where
  isFiniteType_generators := ⟨by
    rw [SheafOfModules.Presentation.map_generators_I]
    infer_instance⟩
  isFiniteType_relations := ⟨by
    rw [SheafOfModules.Presentation.map_relations_I]
    infer_instance⟩
def presentationOfIso {N : SheafOfModules.{u} R} (e : M ≅ N)
    (P : M.Presentation) : N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

end PresentationMap

theorem isFinitePresentation_of_presentation {X : Scheme.{u}} {M : X.Modules}
    (P : M.Presentation) [hP : P.IsFinite] : M.IsFinitePresentation := by
  let q := P.quasicoherentData
  have : q.IsFinitePresentation := by
    constructor
    intro U
    exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem tilde_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    (N : ModuleCat R) [Module.Finite R N] :
    ∃ P : (tilde N).Presentation, P.IsFinite := by
  classical
  obtain ⟨s,hs⟩ := Module.Finite.fg_top (R := R) (M := N)
  let K := LinearMap.ker (Finsupp.linearCombination (M := N) R ((↑) : s → N))
  obtain ⟨t,ht⟩ := IsNoetherian.noetherian K
  let P := presentationTilde N (s : Set N) hs (t : Set (s →₀ R)) ht
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite s
      infer_instance
    · constructor
      change Finite t
      infer_instance
  exact ⟨P,inferInstance⟩

theorem spec_kernel_isQuasicoherent {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsQuasicoherent := by
  let hm := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  let hn := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N
  let em := @asIso _ _ _ _ M.fromTildeΓ hm
  let en := @asIso _ _ _ _ N.fromTildeΓ hn
  let g := (tilde.functor R).preimage
    (em.hom ≫ f ≫ en.inv)
  let e : (tilde.functor R).obj (kernel g) ≅ kernel f :=
    PreservesKernel.iso (tilde.functor R) g ≪≫
      kernel.mapIso ((tilde.functor R).map g) f em
        en (by
          change (tilde.functor R).map ((tilde.functor R).preimage _) ≫ _ = _
          erw [Functor.map_preimage]
          exact (Category.assoc em.hom (f ≫ en.inv) en.hom).trans
            (congrArg (fun q => em.hom ≫ q)
              ((Category.assoc f en.inv en.hom).trans
                ((congrArg (fun q => f ≫ q) en.inv_hom_id).trans (Category.comp_id f)))))
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e
    (inferInstanceAs (tilde (kernel g)).IsQuasicoherent)

theorem spec_exists_finitePresentation_of_sections {R : CommRingCat.{u}} [IsNoetherianRing R]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] :
    ∃ P : M.Presentation, P.IsFinite := by
  let : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  obtain ⟨P,hP⟩ := tilde_exists_finitePresentation
    ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))
  let h := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact ⟨presentationOfIso (@asIso _ _ _ _ M.fromTildeΓ h) P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem spec_kernel_exists_finitePresentation {R : CommRingCat.{u}} [IsNoetherianRing R]
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    [Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤))] (f : M ⟶ N) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  have := spec_kernel_isQuasicoherent f
  have : (moduleSpecΓFunctor (R := R)).IsRightAdjoint := tilde.adjunction.isRightAdjoint
  have : Module.Finite R (moduleSpecΓFunctor.obj M) :=
    inferInstanceAs (Module.Finite R ((modulesSpecToSheaf.obj M).obj.obj (op ⊤)))
  let g := moduleSpecΓFunctor.map (kernel.ι f)
  have : Mono g := inferInstanceAs (Mono (moduleSpecΓFunctor.map (kernel.ι f)))
  have : Module.Finite R ((modulesSpecToSheaf.obj (kernel f)).obj.obj (op ⊤)) :=
    Module.Finite.of_injective g.hom ((ModuleCat.mono_iff_injective g).mp inferInstance)
  exact spec_exists_finitePresentation_of_sections (kernel f)

def presentationOver_of_restrict {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (P : (M.restrict U.ι).Presentation) : (M.over U).Presentation := by
  let E := Scheme.Modules.overEquiv U
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤
      SheafOfModules (Sheaf.over X.ringCatSheaf U) := E.inverse
  let : PreservesColimitsOfSize.{u,u} F :=
    E.symm.toAdjunction.leftAdjoint_preservesColimits
  let e : E.inverse.obj (M.restrict U.ι) ≅ M.over U :=
    E.inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
      (E.unitIso.app (M.over U)).symm
  let : IsIso e.hom := e.isIso_hom
  exact presentationOfIso e (P.map F (E.unitIso.app _))

instance presentationOver_of_restrict_isFinite {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    (presentationOver_of_restrict M U P).IsFinite := by
  exact ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩

theorem isFinitePresentation_of_affine_presentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ U : X.affineOpens, ∃ P : (M.restrict U.1.ι).Presentation, P.IsFinite) :
    M.IsFinitePresentation := by
  classical
  let pres (U : X.affineOpens) := (h U).choose
  have hpres (U : X.affineOpens) : (pres U).IsFinite := (h U).choose_spec
  let q : M.QuasicoherentData := {
    I := X.affineOpens
    X U := U.1
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hx
      obtain ⟨U,hU,hxU,hUt⟩ := exists_isAffineOpen_mem_and_subset
        (show x ∈ (⊤ : X.Opens) from trivial)
      exact Opens.mem_iSup.mpr ⟨⟨U,hU⟩,hxU⟩
    presentation U := presentationOver_of_restrict M U.1 (pres U) }
  have : q.IsFinitePresentation := by
    constructor
    intro U
    change (presentationOver_of_restrict M U.1 (pres U)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem affine_kernel_exists_finitePresentation {X : Scheme.{u}}
    [IsAffine X] [IsLocallyNoetherian X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    (hM : LocallyFinitelyGenerated M) :
    ∃ P : (kernel f).Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let F := Scheme.Modules.restrictFunctor a
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    spec_sections_finite_of_localGenerators (M.restrict a) (hM.restrict a)
  obtain ⟨P,hP⟩ := spec_kernel_exists_finitePresentation (F.map f)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  let P' := presentationOfIso e.symm P
  let b := X.isoSpec.hom
  let G : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{u,u} G :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P'.map G (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app (kernel f)
  have e₂ : (kernel f).restrict (𝟙 X) ≅ ((kernel f).restrict a).restrict b := by
    change (kernel f).restrict (b ≫ a) ≅ ((kernel f).restrict a).restrict b at e₁
    simpa only [b, a, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app (kernel f)
  let : IsIso e₃.hom := e₃.isIso_hom
  exact ⟨presentationOfIso e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem free_isFinitePresentation (X : Scheme.{u}) (I : Type u) [Finite I] :
    (SheafOfModules.free (R := X.ringCatSheaf) I).IsFinitePresentation := by
  let f : SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} Empty) ⟶
      SheafOfModules.free I := 0
  let P := SheafOfModules.presentationOfIsCokernelFree f (𝟙 _) (by simp [f])
    (CokernelCofork.IsColimit.ofId f rfl)
  have : P.IsFinite := by
    constructor
    · constructor
      change Finite I
      infer_instance
    · constructor
      change Finite (ULift.{u} Empty)
      infer_instance
  exact isFinitePresentation_of_presentation P

theorem kernel_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    {M N : X.Modules} [M.IsFinitePresentation] [N.IsQuasicoherent] (f : M ⟶ N) :
    (kernel f).IsFinitePresentation := by
  apply isFinitePresentation_of_affine_presentations
  intro U
  have : IsAffine U.1.toScheme := U.2
  let F := Scheme.Modules.restrictFunctor U.1.ι
  let : M.IsQuasicoherent :=
    (SheafOfModules.IsFinitePresentation.exists_quasicoherentData M).choose.isQuasicoherent
  obtain ⟨P,hP⟩ := affine_kernel_exists_finitePresentation (F.map f)
    ((locallyFinitelyGenerated_of_finitePresentation M).restrict U.1.ι)
  let e := PreservesKernel.iso F f
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm P,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem kernel_generators_isFinitePresentation {X : Scheme.{u}} [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] (s : M.GeneratingSections) [hs : s.IsFiniteType] :
    (kernel s.π).IsFinitePresentation := by
  let : Finite s.I := hs.finite
  have := free_isFinitePresentation X s.I
  exact kernel_isFinitePresentation s.π

theorem exists_local_finitePresentation {X : Scheme.{u}} (M : X.Modules)
    [M.IsFinitePresentation] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ P : (M.restrict U.ι).Presentation, P.IsFinite := by
  obtain ⟨q,hq⟩ := SheafOfModules.IsFinitePresentation.exists_quasicoherentData M
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  obtain ⟨i,hi⟩ := Opens.mem_iSup.mp (show x ∈ ⨆ i, q.X i by rw [hcov]; trivial)
  let F : SheafOfModules (Sheaf.over X.ringCatSheaf (q.X i)) ⥤
      SheafOfModules (Scheme.Opens.toScheme (X := X) (q.X i)).ringCatSheaf :=
    (Scheme.Modules.overEquiv (q.X i)).functor
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.overEquiv (q.X i)).toAdjunction.leftAdjoint_preservesColimits
  let : (q.presentation i).IsFinite := hq.isFinite_presentation i
  let P := (q.presentation i).map F (Iso.refl _)
  let e := (Scheme.Modules.overFunctorEquiv (q.X i)).app M
  let : IsIso e.hom := e.isIso_hom
  exact ⟨q.X i, hi, presentationOfIso e P,
    ⟨⟨(hq.isFinite_presentation i).isFiniteType_generators.finite⟩,
      ⟨(hq.isFinite_presentation i).isFiniteType_relations.finite⟩⟩⟩

theorem isFinitePresentation_of_localPresentations {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      ∃ P : (M.restrict U.ι).Presentation, P.IsFinite) : M.IsFinitePresentation := by
  classical
  choose U hx P hP using h
  have hP' (x : X) : (P x).IsFinite := hP x
  let q : M.QuasicoherentData := {
    I := X
    X := U
    coversTop := by
      rw [Opens.coversTop_iff]
      apply top_unique
      intro x hxtop
      exact Opens.mem_iSup.mpr ⟨x,hx x⟩
    presentation x := presentationOver_of_restrict M (U x) (P x) }
  have : q.IsFinitePresentation := by
    constructor
    intro x
    change (presentationOver_of_restrict M (U x) (P x)).IsFinite
    infer_instance
  exact { exists_quasicoherentData := ⟨q, inferInstance⟩ }

theorem finitePresentation_of_le {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens}
    (h : V ≤ U) (P : (M.restrict U.ι).Presentation) [hP : P.IsFinite] :
    ∃ Q : (M.restrict V.ι).Presentation, Q.IsFinite := by
  let F : SheafOfModules U.toScheme.ringCatSheaf ⥤ SheafOfModules V.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor (X.homOfLE h)
  let : PreservesColimitsOfSize.{u,u} F :=
    (Scheme.Modules.restrictAdjunction (X.homOfLE h)).leftAdjoint_preservesColimits
  let Q := P.map F
    (Scheme.Modules.restrictUnitIso (X.homOfLE h)).symm
  let e := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M
  simp only [X.homOfLE_ι h] at e
  let : IsIso e.inv := e.isIso_inv
  exact ⟨presentationOfIso e.symm Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

def restrictIsoOfLE {X : Scheme.{u}} {M N : X.Modules} {U V : X.Opens}
    (h : V ≤ U) (e : M.restrict U.ι ≅ N.restrict U.ι) :
    M.restrict V.ι ≅ N.restrict V.ι := by
  let e' := (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso e ≪≫
    ((Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app N).symm
  simp only [X.homOfLE_ι h] at e'
  exact e'

theorem isFinitePresentation_of_locally_iso {X : Scheme.{u}} (M N : X.Modules)
    [M.IsFinitePresentation]
    (h : ∀ x : X, ∃ V : X.Opens, x ∈ V ∧ Nonempty (N.restrict V.ι ≅ M.restrict V.ι)) :
    N.IsFinitePresentation := by
  apply isFinitePresentation_of_localPresentations
  intro x
  obtain ⟨V,hxV,⟨e⟩⟩ := h x
  obtain ⟨U,hxU,P,hP⟩ := exists_local_finitePresentation M x
  obtain ⟨Q,hQ⟩ := finitePresentation_of_le M (V := U ⊓ V) inf_le_left P
  let e' := restrictIsoOfLE (V := U ⊓ V) inf_le_right e
  let : IsIso e'.inv := e'.isIso_inv
  exact ⟨U ⊓ V, ⟨hxU,hxV⟩, presentationOfIso e'.symm Q,
    ⟨⟨hQ.isFiniteType_generators.finite⟩, ⟨hQ.isFiniteType_relations.finite⟩⟩⟩

theorem moduleTwist_isFinitePresentation {X : Scheme.{0}}
    (L : PiExponentSeshadri.Geometry.LineBundle X) (n : ℕ) (M : X.Modules)
    [M.IsFinitePresentation] :
    ((PiExponentSeshadri.Geometry.moduleTwistFunctor L n).obj M).IsFinitePresentation := by
  apply isFinitePresentation_of_locally_iso M
  intro x
  obtain ⟨U,hxU,⟨e⟩⟩ := L.locallyRankOne x
  exact ⟨U,hxU,⟨(PiExponentSeshadri.Geometry.moduleTwistRestrictFrame L U e n).app M⟩⟩

end
end PiExponent.FiniteGlobalPresentation

end OAI
end Source0323

-- Source: OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardAffine.lean
section Source0324
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/ClosedPushforwardAffine.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.ClosedPushforwardAffine
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CoherentAffineFinite FiniteGlobalPresentation
variable {X Y : Scheme.{0}}

private def transportPresentation {Z : Scheme.{0}}
    {M N : SheafOfModules Z.ringCatSheaf} (e : M ≅ N) (P : M.Presentation) :
    N.Presentation := by
  let : IsIso e.hom := e.isIso_hom
  exact P.ofIsIso e.hom

theorem affine_pushforward_quasicoherent [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  let MX := (Scheme.Modules.pushforward X.isoSpec.hom).obj M
  have : MX.IsQuasicoherent := GlobalSectionClearing.quasicoherent_pushforward_iso X.isoSpec M
  let MY := (Scheme.Modules.pushforward (Spec.map f.appTop)).obj MX
  have : MY.IsQuasicoherent :=
    (isQuasicoherent_iff_isIso_fromTildeΓ MY).mpr (isIso_fromTildeΓ_pushforward f.appTop MX)
  have hback : ((Scheme.Modules.pushforward Y.isoSpec.inv).obj MY).IsQuasicoherent :=
    GlobalSectionClearing.quasicoherent_pushforward_iso Y.isoSpec.symm MY
  let e₁ := (Scheme.Modules.pushforward Y.isoSpec.inv).mapIso
    ((Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).app M)
  let e₂ := (Scheme.Modules.pushforwardComp (X.isoSpec.hom ≫ Spec.map f.appTop) Y.isoSpec.inv).app M
  have hf : (X.isoSpec.hom ≫ Spec.map f.appTop) ≫ Y.isoSpec.inv = f := by
    rw [Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let e₃ := (Scheme.Modules.pushforwardCongr hf).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso (e₁ ≪≫ e₂ ≪≫ e₃) hback

theorem affine_pushforward_sections_finite [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsQuasicoherent]
    (hM : LocallyFinitelyGenerated M) :
    Module.Finite Γ(Y,⊤) Γ((Scheme.Modules.pushforward f).obj M,⊤) := by
  have hfin : Module.Finite Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := by
    simpa only [Scheme.Hom.preimage_top] using! affine_sections_finite_of_localGenerators M hM
  let σ : Γ(Y,⊤) →+* Γ(X,f ⁻¹ᵁ (⊤ : Y.Opens)) := (f.app ⊤).hom
  have : RingHomSurjective σ := ⟨f.app_surjective ⊤ (isAffineOpen_top Y)⟩
  let ψ : Γ((Scheme.Modules.pushforward f).obj M,⊤) →ₛₗ[σ] Γ(M,f ⁻¹ᵁ (⊤ : Y.Opens)) := {
    toFun := fun x => x
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact (ψ.finite_iff_of_bijective ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩).mpr hfin

theorem affine_exists_finitePresentation_of_sections [IsAffine X] [IsLocallyNoetherian X]
    (M : X.Modules) [M.IsQuasicoherent] [Module.Finite Γ(X,⊤) Γ(M,⊤)] :
    ∃ P : M.Presentation, P.IsFinite := by
  let a := X.isoSpec.inv
  let b := X.isoSpec.hom
  have : IsNoetherianRing Γ(X,⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : Module.Finite Γ(X,⊤) ((modulesSpecToSheaf.obj (M.restrict a)).obj.obj (op ⊤)) :=
    finite_isoSpec_sections M
  obtain ⟨P,hP⟩ := spec_exists_finitePresentation_of_sections (M.restrict a)
  let F : SheafOfModules (Spec Γ(X,⊤)).ringCatSheaf ⥤ SheafOfModules X.ringCatSheaf :=
    Scheme.Modules.restrictFunctor b
  let : PreservesColimitsOfSize.{0,0} F :=
    (Scheme.Modules.restrictAdjunction b).leftAdjoint_preservesColimits
  let Q := P.map F (Scheme.Modules.restrictUnitIso b).symm
  let e₁ := (Scheme.Modules.restrictFunctorComp b a).app M
  have e₂ : M.restrict (𝟙 X) ≅ ((M.restrict a).restrict b) := by
    change M.restrict (b ≫ a) ≅ ((M.restrict a).restrict b) at e₁
    simpa only [a, b, Iso.hom_inv_id] using e₁
  let e₃ := e₂.symm ≪≫ Scheme.Modules.restrictFunctorId.app M
  exact ⟨transportPresentation (Z := X) e₃ Q,
    ⟨⟨hP.isFiniteType_generators.finite⟩, ⟨hP.isFiniteType_relations.finite⟩⟩⟩

theorem affine_pushforward_exists_finitePresentation [IsAffine X] [IsAffine Y]
    [IsLocallyNoetherian Y] (f : X ⟶ Y) [IsClosedImmersion f]
    (M : X.Modules) [M.IsQuasicoherent] (hM : LocallyFinitelyGenerated M) :
    ∃ P : ((Scheme.Modules.pushforward f).obj M).Presentation, P.IsFinite := by
  have := affine_pushforward_quasicoherent f M
  have := affine_pushforward_sections_finite f M hM
  exact affine_exists_finitePresentation_of_sections ((Scheme.Modules.pushforward f).obj M)

end
end PiExponent.ClosedPushforwardAffine

end OAI
end Source0324
