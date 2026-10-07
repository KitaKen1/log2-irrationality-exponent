/- Generated rc4 checkpoint for LogTwo.
Modified from the reduced edition: new imports, separate module compilation,
and synchronous elaboration. Original source blocks and notices are retained.
See ../../../THIRD_PARTY_NOTICES.txt and ../../reduction.json.
-/
module
public import LogTwoCheckpoints.Part000
public import LogTwoCheckpoints.Part001
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import Mathlib.RingTheory.PowerSeries.Log
public import Mathlib.Tactic
@[expose] public section
set_option Elab.async false

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexCounting.lean
section Source0050
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexCounting.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

def natWeightedSimplex {d : ℕ} (w : Fin d → ℕ) (N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (N + 1))).filter
    (fun a => ∑ i, w i * a i ≤ N)

theorem mem_natWeightedSimplex {d : ℕ} {w : Fin d → ℕ}
    (hw : ∀ i, 0 < w i) {N : ℕ} {a : Fin d → ℕ} :
    a ∈ natWeightedSimplex w N ↔ ∑ i, w i * a i ≤ N := by
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    have h₁ : a i ≤ w i * a i := Nat.le_mul_of_pos_left (a i) (hw i)
    have h₂ : w i * a i ≤ ∑ j, w j * a j :=
      Finset.single_le_sum (f := fun j => w j * a j)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega

def residueRectangle {d : ℕ} (w : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset (fun i => Finset.range (w i))

@[simp] theorem mem_residueRectangle {d : ℕ} {w r : Fin d → ℕ} :
    r ∈ residueRectangle w ↔ ∀ i, r i < w i := by
  simp [residueRectangle, Fintype.mem_piFinset]

@[simp] theorem card_residueRectangle {d : ℕ} (w : Fin d → ℕ) :
    (residueRectangle w).card = ∏ i, w i := by
  simp [residueRectangle, Fintype.card_piFinset]

theorem simplex_count_lower_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex (fun _ : Fin d => 1) N).card ≤
      (natWeightedSimplex w N).card * ∏ i, w i := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : (Fin d → ℕ) → (Fin d → ℕ) × (Fin d → ℕ) :=
    fun b => (fun i => b i / w i, fun i => b i % w i)
  apply Finset.card_le_card_of_injOn f
  · intro b hb
    apply Finset.mem_product.mpr
    constructor
    · apply (mem_natWeightedSimplex hw).mpr
      have hb' := (mem_natWeightedSimplex (fun _ => by decide)).mp hb
      simp only [one_mul] at hb'
      exact (Finset.sum_le_sum (fun i _ => Nat.mul_div_le (b i) (w i))).trans hb'
    · exact mem_residueRectangle.mpr (fun i => Nat.mod_lt (b i) (hw i))
  · intro a ha b hb hab
    have hq := congrArg Prod.fst hab
    have hr := congrArg Prod.snd hab
    funext i
    have hqi := congrFun hq i
    have hri := congrFun hr i
    change a i / w i = b i / w i at hqi
    change a i % w i = b i % w i at hri
    have ha' := Nat.div_add_mod (a i) (w i)
    have hb' := Nat.div_add_mod (b i) (w i)
    calc
      a i = w i * (a i / w i) + a i % w i := ha'.symm
      _ = w i * (b i / w i) + b i % w i := by rw [hqi, hri]
      _ = b i := hb'

theorem simplex_count_upper_sandwich {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) (N : ℕ) :
    (natWeightedSimplex w N).card * (∏ i, w i) ≤
      (natWeightedSimplex (fun _ : Fin d => 1) (N + ∑ i, (w i - 1))).card := by
  rw [← card_residueRectangle, ← Finset.card_product]
  let f : ((Fin d → ℕ) × (Fin d → ℕ)) → (Fin d → ℕ) :=
    fun ar i => w i * ar.1 i + ar.2 i
  apply Finset.card_le_card_of_injOn f
  · intro ar har
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    apply (mem_natWeightedSimplex (fun _ => by decide)).mpr
    simp only [one_mul]
    change ∑ i, (w i * ar.1 i + ar.2 i) ≤ _
    rw [Finset.sum_add_distrib]
    apply Nat.add_le_add ((mem_natWeightedSimplex hw).mp ha)
    apply Finset.sum_le_sum
    intro i hi
    have := mem_residueRectangle.mp hr i
    omega
  · intro ar har bs hbs hab
    obtain ⟨ha, hr⟩ := Finset.mem_product.mp har
    obtain ⟨hb, hs⟩ := Finset.mem_product.mp hbs
    apply Prod.ext
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hdiv := congrArg (fun n => n / w i) hi
      rw [Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (ar.1 i)),
        Nat.add_div_of_dvd_right (Nat.dvd_mul_right (w i) (bs.1 i))] at hdiv
      simpa [Nat.div_eq_of_lt hri, Nat.div_eq_of_lt hsi,
        Nat.mul_div_cancel_left _ (hw i)] using hdiv
    · funext i
      have hi := congrFun hab i
      change w i * ar.1 i + ar.2 i = w i * bs.1 i + bs.2 i at hi
      have hri := mem_residueRectangle.mp hr i
      have hsi := mem_residueRectangle.mp hs i
      have hmod := congrArg (fun n => n % w i) hi
      simpa [Nat.add_mod, Nat.mod_eq_of_lt hri, Nat.mod_eq_of_lt hsi] using hmod

@[simp] theorem natWeightedSimplex_one (d N : ℕ) :
    natWeightedSimplex (fun _ : Fin d => 1) N = unweightedSimplex d N := by
  ext a
  rw [mem_natWeightedSimplex (w := fun _ : Fin d => 1) (fun _ => by decide), mem_unweightedSimplex]
  simp only [one_mul]

open Filter Topology

theorem tendsto_card_natWeightedSimplex {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) :
    Tendsto (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) / (N : ℝ) ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)))) := by
  let P : ℝ := ∏ i, (w i : ℝ)
  have hP : 0 < P := Finset.prod_pos (fun i _ => by exact_mod_cast hw i)
  have hs : Tendsto
      (fun N : ℕ => ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d)
      atTop (𝓝 (1 / (d.factorial : ℝ))) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_card_unweightedSimplex d)
      (tendsto_card_unweightedSimplex_add d (∑ i, (w i - 1)))
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_lower_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
    · intro N
      apply div_le_div_of_nonneg_right _ (by positivity)
      have h := simplex_count_upper_sandwich w hw N
      rw [natWeightedSimplex_one] at h
      dsimp [P]
      exact_mod_cast h
  have h := hs.div_const P
  have heq : 1 / (d.factorial : ℝ) / P =
      1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ)) := by
    simp only [P, div_div]
  rw [heq] at h
  apply h.congr'
  exact Filter.Eventually.of_forall (fun N => by
    change ((natWeightedSimplex w N).card : ℝ) * P / (N : ℝ) ^ d / P = _
    field_simp)

noncomputable def realWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (Fintype.piFinset (fun i => Finset.range (⌊H / w i⌋₊ + 1))).filter
    (fun a => ∑ i, w i * (a i : ℝ) ≤ H)

noncomputable def strictWeightedSimplex {d : ℕ} (w : Fin d → ℝ) (H : ℝ) :
    Finset (Fin d → ℕ) := by
  classical
  exact (realWeightedSimplex w H).filter (fun a => ∑ i, w i * (a i : ℝ) < H)

theorem mem_realWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ realWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) ≤ H := by
  classical
  constructor
  · exact fun h => (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, h⟩
    intro i
    apply Finset.mem_range.mpr
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    rw [mul_comm]
    exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
      (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans h

theorem mem_strictWeightedSimplex {d : ℕ} {w : Fin d → ℝ}
    (hw : ∀ i, 0 < w i) {H : ℝ} {a : Fin d → ℕ} :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  simp only [strictWeightedSimplex, Finset.mem_filter, mem_realWeightedSimplex hw,
    and_iff_right_iff_imp]
  exact fun h => h.le

theorem realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c H : ℝ} (hc : 0 < c) (hH : 0 ≤ H) :
    realWeightedSimplex (fun i => (w i : ℝ) / c) H =
      natWeightedSimplex w ⌊c * H⌋₊ := by
  ext a
  rw [mem_realWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc),
    mem_natWeightedSimplex hw, Nat.le_floor_iff (mul_nonneg hc.le hH)]
  have hs : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
      ((∑ i, w i * a i : ℕ) : ℝ) / c := by
    simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
  rw [hs, div_le_iff₀ hc, mul_comm H c]

theorem tendsto_card_realWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((realWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have h := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc 0
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
  simp only [add_zero, realWeightedSimplex_scaled w hw hc hH]

theorem tendsto_card_strictWeightedSimplex_scaled {d : ℕ} (w : Fin d → ℕ)
    (hw : ∀ i, 0 < w i) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun H : ℝ => ((strictWeightedSimplex (fun i => (w i : ℝ) / c) H).card : ℝ) / H ^ d)
      atTop (𝓝 ((1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * c ^ d)) := by
  have hlo := tendsto_normalized_natFloor_affine
    (tendsto_card_natWeightedSimplex w hw) hc (-1)
  have hhi := tendsto_card_realWeightedSimplex_scaled w hw hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_ge_atTop (1 / c)] with H hH
    have hHpos : 0 < H := (div_pos zero_lt_one hc).trans_le hH
    have hcH : 1 ≤ c * H := by
      have := (div_le_iff₀ hc).mp hH
      nlinarith
    apply div_le_div_of_nonneg_right _ (pow_nonneg hHpos.le d)
    exact_mod_cast (Finset.card_le_card (show
      natWeightedSimplex w ⌊c * H + -1⌋₊ ⊆
      strictWeightedSimplex (fun i => (w i : ℝ) / c) H from by
        intro a ha
        apply (mem_strictWeightedSimplex (fun i => div_pos (by exact_mod_cast hw i) hc)).mpr
        have ha' := (mem_natWeightedSimplex hw).mp ha
        have hs : ((∑ i, w i * a i : ℕ) : ℝ) ≤ c * H + -1 :=
          (Nat.le_floor_iff (by linarith)).mp ha'
        have heq : (∑ i, (w i : ℝ) / c * (a i : ℝ)) =
            ((∑ i, w i * a i : ℕ) : ℝ) / c := by
          simp [Nat.cast_sum, Nat.cast_mul, Finset.sum_div, div_mul_eq_mul_div]
        rw [heq, div_lt_iff₀ hc]
        nlinarith))
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with H hH
    apply div_le_div_of_nonneg_right _ (pow_nonneg hH d)
    exact_mod_cast (Finset.card_le_card (Finset.filter_subset
      (fun a : Fin d → ℕ => ∑ i, (w i : ℝ) / c * (a i : ℝ) < H)
      (realWeightedSimplex (fun i => (w i : ℝ) / c) H)))

end PiExponent

end OAI
end Source0050

-- Source: OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean
section Source0051
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/InterpolationMatrix.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent.InterpolationMatrix

noncomputable def exponentVector {m : ℕ} (a : Fin m → ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm a

@[simp] theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    exponentVector a i = a i := by
  simp [exponentVector]

noncomputable def truncatedLog (T : ℕ) : Polynomial ℂ :=
  PowerSeries.trunc T (PowerSeries.log ℂ)

@[simp] theorem truncatedLog_coeff (T k : ℕ) :
    (truncatedLog T).coeff k =
      if k < T then
        if k = 0 then 0 else algebraMap ℚ ℂ ((-1 : ℚ) ^ (k + 1) / k)
      else 0 := by
  simp [truncatedLog, PowerSeries.coeff_trunc]

noncomputable def monomialImage {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j h : ℕ) (a : Fin m → ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.C ((1 + Polynomial.X) ^ h) *
    ∏ i, (MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) +
      MvPolynomial.X i) ^ a i

noncomputable def entry {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j s : ℕ) (b : Fin m → ℕ)
    (h : ℕ) (a : Fin m → ℕ) : ℂ :=
  ((monomialImage r G j h a).coeff (exponentVector b)).coeff s

noncomputable def sectionImage {m : ℕ} {C : Type*} [Fintype C]
    (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ)
    (h : C → ℕ) (a : C → Fin m → ℕ) (x : C → ℂ) (j : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) :=
  ∑ c, MvPolynomial.C (Polynomial.C (x c)) * monomialImage r G j (h c) (a c)

def columnWeights {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases w0 w

noncomputable def rowWeights {m : ℕ} (v0 θ : ℝ) (w : Fin m → ℝ) : Fin (m + 1) → ℝ :=
  Fin.cases v0 (fun i => w i / θ)

abbrev Column {m : ℕ} (w0 : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  ↥(PiExponent.realWeightedSimplex (columnWeights w0 w) H)

abbrev Row {m : ℕ} (K : ℕ) (v0 θ : ℝ) (w : Fin m → ℝ) (H : ℝ) :=
  Fin K × ↥(PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H)

theorem column_mem_iff {m : ℕ} {w0 H : ℝ} {w : Fin m → ℝ}
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i) (a : Fin (m + 1) → ℕ) :
    a ∈ PiExponent.realWeightedSimplex (columnWeights w0 w) H ↔
      w0 * (a 0 : ℝ) + ∑ i, w i * (a i.succ : ℝ) ≤ H := by
  have hp : ∀ i, 0 < columnWeights w0 w i := by
    intro i
    refine Fin.cases hw0 (fun j => hw j) i
  rw [PiExponent.mem_realWeightedSimplex hp, Fin.sum_univ_succ]
  rfl

theorem row_mem_iff {m : ℕ} {v0 θ H : ℝ} {w : Fin m → ℝ}
    (hv0 : 0 < v0) (hθ : 0 < θ) (hw : ∀ i, 0 < w i) (b : Fin (m + 1) → ℕ) :
    b ∈ PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H ↔
      v0 * (b 0 : ℝ) + (∑ i, w i * (b i.succ : ℝ)) / θ < H := by
  have hp : ∀ i, 0 < rowWeights v0 θ w i := by
    intro i
    refine Fin.cases hv0 (fun j => div_pos (hw j) hθ) i
  rw [PiExponent.mem_strictWeightedSimplex hp, Fin.sum_univ_succ]
  simp only [rowWeights, Fin.cases_zero, Fin.cases_succ, div_mul_eq_mul_div,
    Finset.sum_div]

noncomputable def matrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  fun ρ c => entry r G ρ.1.val (ρ.2.1 0) (fun i => ρ.2.1 i.succ)
    (c.1 0) (fun i => c.1 i.succ)

noncomputable def linearEvaluation {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (G : Fin m → Polynomial ℂ) :
    (Column w0 w H → ℂ) →ₗ[ℂ] (Row K v0 θ w H → ℂ) :=
  (matrix K w0 v0 θ w H r G).mulVecLin

@[simp] theorem row_card {m : ℕ} (K : ℕ) (v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) :
    Fintype.card (Row K v0 θ w H) =
      K * (PiExponent.strictWeightedSimplex (rowWeights v0 θ w) H).card := by
  classical
  simp [Row]

theorem exists_full_row_minor_of_surjective
    {R C K : Type*} [Fintype R] [Fintype C] [DecidableEq R] [Field K]
    (A : Matrix R C K) (hA : Function.Surjective A.mulVecLin) :
    ∃ selection : R → C, Function.Injective selection ∧
      (A.submatrix id selection).det ≠ 0 := by
  classical
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hA
  have hexp : (A * B).det =
      ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
    calc
      (A * B).det = ∑ p : R → C, ∑ σ : Equiv.Perm R,
          ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, A (σ i) (p i) * B (p i) i := by
        simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum,
          Finset.mul_sum, Fintype.piFinset_univ]
        rw [Finset.sum_comm]
      _ = ∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [Matrix.det_apply', Matrix.submatrix_apply, id_eq,
          Finset.prod_mul_distrib, ← mul_assoc, ← Finset.sum_mul]
  have hsum : (∑ p : R → C, (A.submatrix id p).det * ∏ i, B (p i) i) ≠ 0 := by
    rw [← hexp, hB, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨p, _, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hdet : (A.submatrix id p).det ≠ 0 := by
    intro h
    apply hp
    rw [h, zero_mul]
  refine ⟨p, ?_, hdet⟩
  intro i j hij
  by_contra hne
  exact hdet (Matrix.det_zero_of_column_eq hne (fun k => congrArg (A k) hij))

noncomputable def truncatedLogMatrix {m : ℕ} (K : ℕ) (w0 v0 θ : ℝ)
    (w : Fin m → ℝ) (H : ℝ) (r : Fin m → ℂ) (T : Fin m → ℕ) :
    Matrix (Row K v0 θ w H) (Column w0 w H) ℂ :=
  matrix K w0 v0 θ w H r (fun i => truncatedLog (T i))

end PiExponent.InterpolationMatrix

end OAI
end Source0051

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexRationalWeights.lean
section Source0052
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexRationalWeights.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators

namespace PiExponent

theorem positive_rational_weights_common_denominator {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : Fin d → ℕ,
      (∀ i, 0 < w i) ∧ ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ) := by
  classical
  let D : ℕ := ∏ i, (ρ i).den
  have hD : 0 < D := Finset.prod_pos (fun i _ => (ρ i).den_pos)
  have hd : ∀ i, (ρ i).den ∣ D :=
    fun i => Finset.dvd_prod_of_mem (fun j => (ρ j).den) (Finset.mem_univ i)
  choose k hk using hd
  have hkpos : ∀ i, 0 < k i := by
    intro i
    by_contra h
    have hkzero : k i = 0 := by omega
    have := hk i
    rw [hkzero, mul_zero] at this
    omega
  let w : Fin d → ℕ := fun i => (ρ i).num.toNat * k i
  refine ⟨D, hD, w, ?_, ?_⟩
  · intro i
    have hn : 0 < (ρ i).num := Rat.num_pos.mpr (hρ i)
    exact Nat.mul_pos (by omega) (hkpos i)
  · intro i
    have hnum : (((ρ i).num.toNat : ℕ) : ℝ) = ((ρ i).num : ℝ) := by
      exact_mod_cast (Int.toNat_of_nonneg (Rat.num_pos.mpr (hρ i)).le)
    have hcastD : (D : ℝ) = ((ρ i).den : ℝ) * (k i : ℝ) := by
      exact_mod_cast hk i
    have hkne : (k i : ℝ) ≠ 0 := by exact_mod_cast (hkpos i).ne'
    have hdenne : ((ρ i).den : ℝ) ≠ 0 := by exact_mod_cast (ρ i).den_ne_zero
    rw [Rat.cast_def, hcastD]
    change ((ρ i).num : ℝ) / ((ρ i).den : ℝ) =
      (((ρ i).num.toNat * k i : ℕ) : ℝ) / (((ρ i).den : ℝ) * (k i : ℝ))
    rw [Nat.cast_mul, hnum]
    field_simp

end PiExponent

end OAI
end Source0052

-- Source: OAI/NumberTheory/PiExponent/Polynomials/SimplexRational.lean
section Source0053
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/SimplexRational.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

theorem common_denominator_simplex_constant {d D : ℕ} {ρ : Fin d → ℚ}
    {w : Fin d → ℕ} (hD : 0 < D) (hw : ∀ i, 0 < w i)
    (hweights : ∀ i, (ρ i : ℝ) = (w i : ℝ) / (D : ℝ)) :
    (1 / ((d.factorial : ℝ) * ∏ i, (w i : ℝ))) * (D : ℝ) ^ d =
      1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)) := by
  have hprod : (∏ i, (ρ i : ℝ)) = (∏ i, (w i : ℝ)) / (D : ℝ) ^ d := by
    simp_rw [hweights]
    rw [Finset.prod_div_distrib]
    simp
  have hDne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hPne : (∏ i, (w i : ℝ)) ≠ 0 :=
    (Finset.prod_pos (fun i _ => by exact_mod_cast hw i)).ne'
  have hfac : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  rw [hprod]
  field_simp

theorem tendsto_card_realWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((realWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_realWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

theorem tendsto_card_strictWeightedSimplex_rational {d : ℕ}
    (ρ : Fin d → ℚ) (hρ : ∀ i, 0 < ρ i) :
    Tendsto (fun H : ℝ =>
      ((strictWeightedSimplex (fun i => (ρ i : ℝ)) H).card : ℝ) / H ^ d)
      atTop (𝓝 (1 / ((d.factorial : ℝ) * ∏ i, (ρ i : ℝ)))) := by
  obtain ⟨D, hD, w, hw, hweights⟩ := positive_rational_weights_common_denominator ρ hρ
  have h := tendsto_card_strictWeightedSimplex_scaled w hw
    (show (0 : ℝ) < D by exact_mod_cast hD)
  rw [common_denominator_simplex_constant hD hw hweights] at h
  simpa only [← hweights] using h

end PiExponent

end OAI
end Source0053

-- Source: OAI/NumberTheory/PiExponent/Polynomials/AuxiliaryPolynomial.lean
section Source0054
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/AuxiliaryPolynomial.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent

noncomputable def polynomialOfCoefficients {d : ℕ} (S : Finset (Fin d → ℕ)) :
    (S → ℂ) →ₗ[ℂ] MvPolynomial (Fin d) ℂ := by
  classical
  exact
    { toFun := fun x => ∑ a : S, MvPolynomial.monomial
        (InterpolationMatrix.exponentVector a.val) (x a)
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun z x => by
        simp only [Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]  }

theorem exponentVector_injective {d : ℕ} :
    Function.Injective (@InterpolationMatrix.exponentVector d) := by
  intro a b h
  funext i
  have hi := congrArg (fun v : Fin d →₀ ℕ => v i) h
  simpa only [InterpolationMatrix.exponentVector_apply] using hi

@[simp] theorem polynomialOfCoefficients_coeff {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) (a : S) :
    (polynomialOfCoefficients S x).coeff (InterpolationMatrix.exponentVector a.val) = x a := by
  classical
  change (∑ exponent : S, MvPolynomial.monomial
    (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff
      (InterpolationMatrix.exponentVector a.val) = x a
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    have hne : InterpolationMatrix.exponentVector b.val ≠
        InterpolationMatrix.exponentVector a.val := by
      intro h
      exact hba (Subtype.ext (exponentVector_injective h))
    simp [hne]
  · simp

theorem polynomialOfCoefficients_injective {d : ℕ} (S : Finset (Fin d → ℕ)) :
    Function.Injective (polynomialOfCoefficients S) := by
  intro x y h
  funext a
  have := congrArg (fun p : MvPolynomial (Fin d) ℂ =>
    p.coeff (InterpolationMatrix.exponentVector a.val)) h
  simpa only [polynomialOfCoefficients_coeff] using this

theorem polynomialOfCoefficients_support {d : ℕ} (S : Finset (Fin d → ℕ))
    (x : S → ℂ) :
    (polynomialOfCoefficients S x).support ⊆ S.image InterpolationMatrix.exponentVector := by
  classical
  intro e he
  by_contra hn
  have hzero : (polynomialOfCoefficients S x).coeff e = 0 := by
    change (∑ exponent : S, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector exponent.val) (x exponent)).coeff e = 0
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_eq_zero
    intro a ha
    have hne : InterpolationMatrix.exponentVector a.val ≠ e := by
      intro h
      exact hn (Finset.mem_image.mpr ⟨a.val, a.property, h⟩)
    simp [MvPolynomial.coeff_monomial, hne]
  exact (MvPolynomial.mem_support_iff.mp he) hzero

theorem polynomialOfCoefficients_weighted {m : ℕ} (W : Fin (m + 1) → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    PiExponentApprox.HasWeightedDegreeLE W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  classical
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [PiExponentApprox.monomialWeight,
    InterpolationMatrix.exponentVector_apply, mul_comm] using h

theorem exists_nonzero_kernel_of_card_lt {C R : Type*} [Fintype C] [Fintype R]
    (E : (C → ℂ) →ₗ[ℂ] (R → ℂ)) (h : Fintype.card R < Fintype.card C) :
    ∃ x : C → ℂ, x ≠ 0 ∧ E x = 0 := by
  have hk : LinearMap.ker E ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt
    (by simpa only [Module.finrank_fintype_fun_eq_card] using h)
  obtain ⟨x, hx, hn⟩ := (LinearMap.ker E).ne_bot_iff.mp hk
  exact ⟨x, hn, LinearMap.mem_ker.mp hx⟩

theorem tendsto_card_strictWeightedSimplex_scale {d : ℕ} (V : Fin d → ℚ)
    (hV : ∀ i, 0 < V i) {a : ℝ} (ha : 0 < a) :
    Tendsto (fun N : ℝ =>
      ((strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℝ) / N ^ d)
      atTop (𝓝 (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)))) := by
  have ht : Tendsto (fun N : ℝ => a * N) atTop atTop :=
    Tendsto.const_mul_atTop ha tendsto_id
  have h := ((tendsto_card_strictWeightedSimplex_rational V hV).comp ht).mul_const (a ^ d)
  have heq : 1 / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) * a ^ d =
      a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ)) := by ring
  rw [heq] at h
  apply h.congr'
  exact Eventually.of_forall (fun N => by
    simp only [Function.comp_apply, mul_pow]
    field_simp)

theorem eventually_auxiliary_card_lt {d : ℕ} (W V : Fin d → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card <
        (realWeightedSimplex (fun i => (W i : ℝ)) N).card := by
  have hPW : 0 < ∏ i, (W i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hW i)
  have hPV : 0 < ∏ i, (V i : ℝ) := Finset.prod_pos (fun i _ => by exact_mod_cast hV i)
  have hF : (0 : ℝ) < d.factorial := by exact_mod_cast Nat.factorial_pos d
  have hconst : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) <
      1 / ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) := by
    have hmain := (div_lt_one hPV).mp hvol
    apply (lt_div_iff₀ (mul_pos hF hPW)).mpr
    have heq : (K : ℝ) * (a ^ d / ((d.factorial : ℝ) * ∏ i, (V i : ℝ))) *
        ((d.factorial : ℝ) * ∏ i, (W i : ℝ)) =
        (K : ℝ) * a ^ d * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) := by
      field_simp
    rw [heq]
    exact hvol
  have hsmall := ((tendsto_card_strictWeightedSimplex_scale V hV ha).const_mul (K : ℝ)).eventually_lt
    (tendsto_card_realWeightedSimplex_rational W hW) hconst
  filter_upwards [hsmall, eventually_gt_atTop (0 : ℝ)] with N hN hNpos
  have hscaled : ((K * (strictWeightedSimplex (fun i => (V i : ℝ)) (a * N)).card : ℕ) : ℝ) /
      N ^ d < ((realWeightedSimplex (fun i => (W i : ℝ)) N).card : ℝ) / N ^ d := by
    simpa only [Nat.cast_mul, mul_div_assoc] using hN
  exact_mod_cast (div_lt_div_iff_of_pos_right (pow_pos hNpos d)).mp hscaled

theorem eventually_exists_auxiliaryPolynomial {m : ℕ} (W V : Fin (m + 1) → ℚ)
    (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i) (K : ℕ)
    {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a ^ (m + 1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1) :
    ∀ᶠ N : ℝ in atTop,
      ∀ E : PiExponentApprox.FramePolynomial m →ₗ[ℂ]
        ((Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) → ℂ),
      ∃ p : PiExponentApprox.FramePolynomial m, p ≠ 0 ∧
        PiExponentApprox.HasWeightedDegreeLE (fun i => (W i : ℝ)) N p ∧ E p = 0 := by
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  intro E
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let A := E.comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a * N))) <
      Fintype.card S := by simpa [S] using hN
  obtain ⟨x, hx, hAx⟩ := exists_nonzero_kernel_of_card_lt A hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, hAx⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_weighted (fun i => (W i : ℝ))
      (fun i => by exact_mod_cast hW i) N x

end PiExponent

end OAI
end Source0054

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryAuxiliaryJet.lean
section Source0055
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryAuxiliaryJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
open Filter Topology
namespace PiExponent.OrdinaryAuxiliaryJet

def formalJet {n : ℕ} (c : Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] MvPowerSeries (Fin n) ℂ :=
  MvPolynomial.aeval (fun i => MvPowerSeries.C (c i) + MvPowerSeries.X i)

def evaluation {n : ℕ} (K : ℕ) (V : Fin n → ℝ) (H : ℝ)
    (c : Fin K → Fin n → ℂ) :
    MvPolynomial (Fin n) ℂ →ₗ[ℂ]
      ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun r =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector r.2.val)).comp
      (formalJet (c r.1)).toLinearMap)

theorem polynomialOfCoefficients_supportBound {n : ℕ} (W : Fin n → ℝ)
    (hW : ∀ i, 0 < W i) (N : ℝ)
    (x : ↥(realWeightedSimplex W N) → ℂ) :
    WeightedSliceDegree.SupportBound W N
      (polynomialOfCoefficients (realWeightedSimplex W N) x) := by
  intro e he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp
    (polynomialOfCoefficients_support _ x he)
  have h := (mem_realWeightedSimplex hW).mp ha
  simpa only [Finsupp.weight_eq_sum, InterpolationMatrix.exponentVector_apply,
    nsmul_eq_mul, mul_comm] using h

theorem eventually_exists_auxiliaryPolynomial {n : ℕ}
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^n * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (c : Fin K → Fin n → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ p : MvPolynomial (Fin n) ℂ, p ≠ 0 ∧
      WeightedSliceDegree.SupportBound (fun i => (W i : ℝ)) N p ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJet (c j) p) = 0 := by
  classical
  filter_upwards [eventually_auxiliary_card_lt W V hW hV K ha hvol] with N hN
  let S := realWeightedSimplex (fun i => (W i : ℝ)) N
  let E := (evaluation K (fun i => (V i : ℝ)) (a*N) c).comp (polynomialOfCoefficients S)
  have hcard : Fintype.card (Fin K × ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (a*N))) <
      Fintype.card S := by simpa [S] using hN
  obtain ⟨x, hx, hEx⟩ := exists_nonzero_kernel_of_card_lt E hcard
  refine ⟨polynomialOfCoefficients S x, ?_, ?_, ?_⟩
  · intro hp
    apply hx
    apply polynomialOfCoefficients_injective S
    simpa using hp
  · exact polynomialOfCoefficients_supportBound (fun i => (W i : ℝ))
      (fun i => by exact_mod_cast hW i) N x
  · intro j d hd
    have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
      apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
      simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
    have hh := congrFun hEx (j, ⟨(fun i => d i), hmem⟩)
    have hd' : InterpolationMatrix.exponentVector (fun i => d i) = d := by ext i; rfl
    simpa [E, evaluation, hd'] using hh

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0055

-- Source: OAI/NumberTheory/PiExponent/Approximation/PersistentComponents.lean
section Source0056
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PersistentComponents.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

namespace PiExponent.PersistentComponents

variable {R : Type*} [CommRing R]

theorem prime_height_step {P Q : Ideal R} (hP : P.IsPrime) (hQ : Q.IsPrime)
    (hPQ : P < Q) : P.height + 1 ≤ Q.height := by
  let := hP
  let := hQ
  exact Ideal.height_add_one_le_of_lt_of_isPrime hPQ

theorem exists_adjacent_eq_of_height_bound (P : ℕ → Ideal R) (m : ℕ)
    (hPrime : ∀ i ≤ m + 1, (P i).IsPrime)
    (hstep : ∀ i ≤ m, P i ≤ P (i + 1))
    (hheight : (P (m + 1)).height ≤ m) :
    ∃ i ≤ m, P i = P (i + 1) := by
  by_contra h
  have hneq : ∀ i ≤ m, P i ≠ P (i + 1) := by simpa only [not_exists, not_and] using h
  have hgrowth : ∀ i ≤ m + 1, (i : ℕ∞) ≤ (P i).height := by
    intro i hi
    induction i with
    | zero => exact bot_le
    | succ i ih =>
      have him : i ≤ m := by omega
      have hip : i ≤ m + 1 := by omega
      have hs := prime_height_step (hPrime i hip) (hPrime (i + 1) hi)
        (lt_of_le_of_ne (hstep i him) (hneq i him))
      have hadd : (i : ℕ∞) + 1 ≤ (P i).height + 1 := by
        gcongr
        exact ih hip
      simpa only [Nat.cast_add, Nat.cast_one] using hadd.trans hs
  have hf := (hgrowth (m + 1) le_rfl).trans hheight
  exact (by exact_mod_cast (Nat.not_succ_le_self m) : ¬ ((m + 1 : ℕ) : ℕ∞) ≤ (m : ℕ∞)) hf

theorem exists_nested_minimalPrimes (I : ℕ → Ideal R) (hI : Monotone I)
    (n : ℕ) (P : Ideal R) (hP : P.IsPrime) (hIP : I n ≤ P) :
    ∃ Q : ℕ → Ideal R,
      (∀ i ≤ n, Q i ∈ (I i).minimalPrimes) ∧
      (∀ i < n, Q i ≤ Q (i + 1)) ∧ Q n ≤ P := by
  induction n generalizing P with
  | zero =>
    let := hP
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le hIP
    refine ⟨fun _ => Q, ?_, ?_, hQP⟩
    · intro i hi
      have hi0 : i = 0 := by omega
      simpa only [hi0] using hQ
    · intro i hi
      omega
  | succ n ih =>
    let := hP
    obtain ⟨Qlast, hQlast, hQlastP⟩ := Ideal.exists_minimalPrimes_le hIP
    obtain ⟨Q, hQ, hstep, hQlastle⟩ :=
      ih Qlast hQlast.isPrime ((hI (Nat.le_succ n)).trans hQlast.le)
    refine ⟨fun i => if i = n + 1 then Qlast else Q i, ?_, ?_, ?_⟩
    · intro i hi
      by_cases hei : i = n + 1
      · simpa [hei] using hQlast
      · simpa [hei] using hQ i (by omega)
    · intro i hi
      have hin : i ≠ n + 1 := by omega
      by_cases hei : i = n
      · simpa [hei] using hQlastle
      · have hip : i + 1 ≠ n + 1 := by omega
        simpa [hin, hip, hei] using hstep i (by omega)
    · simpa [Nat.succ_eq_add_one] using hQlastP

theorem exists_persistent_minimalPrime (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ I (r + 1) ≤ Q ∧ Q ≤ P := by
  obtain ⟨Q, hQ, hstep, hQP⟩ := exists_nested_minimalPrimes I hI (m + 2) P hP hIP
  have hmono : ∀ i j, i ≤ j → j ≤ m + 2 → Q i ≤ Q j := by
    intro i j hij hj
    induction j with
    | zero =>
      have hi : i = 0 := by omega
      simp only [hi, le_refl]
    | succ j ih =>
      by_cases heq : i = j + 1
      · simp [heq]
      · exact (ih (by omega) (by omega)).trans (hstep j (by omega))
  have hbound : (Q (m + 1)).height ≤ m :=
    (Ideal.height_mono ((hmono (m + 1) (m + 2) (by omega) le_rfl).trans hQP)).trans hheight
  obtain ⟨r, hr, heq⟩ := exists_adjacent_eq_of_height_bound Q m
    (fun i hi => (hQ i (by omega)).isPrime) (fun i hi => hstep i (by omega)) hbound
  refine ⟨r, by omega, Q r, hQ r (by omega), ?_, ?_⟩
  · rw [heq]
    exact (hQ (r + 1) (by omega)).le
  · exact (hmono r (m + 2) (by omega) le_rfl).trans hQP

theorem minimalPrime_persists {I J Q : Ideal R} (hIJ : I ≤ J)
    (hQ : Q ∈ I.minimalPrimes) (hJQ : J ≤ Q) : Q ∈ J.minimalPrimes := by
  refine ⟨⟨hQ.isPrime, hJQ⟩, ?_⟩
  intro P hP hPQ
  exact hQ.2 ⟨hP.1, hIJ.trans hP.2⟩ hPQ

theorem exists_persistent_minimalPrime_pair (I : ℕ → Ideal R) (hI : Monotone I)
    (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P := by
  obtain ⟨r, hr, Q, hQ, hnext, hQP⟩ :=
    exists_persistent_minimalPrime I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQ, minimalPrime_persists (hI (Nat.le_succ r)) hQ hnext, hQP⟩

theorem minimalPrime_height_pos_of_nonzero_mem [IsDomain R] {I Q : Ideal R}
    (hQ : Q ∈ I.minimalPrimes) {F : R} (hF : F ≠ 0) (hFI : F ∈ I) :
    1 ≤ Q.height := by
  have hQbot : Q ≠ ⊥ := by
    intro h
    have hFQ := hQ.le hFI
    simp only [h, Ideal.mem_bot] at hFQ
    exact hF hFQ
  exact Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hQbot)

theorem exists_persistent_component_positive_height [IsDomain R]
    (I : ℕ → Ideal R) (hI : Monotone I) (m : ℕ) (P : Ideal R) (hP : P.IsPrime)
    (hIP : I (m + 2) ≤ P) (hheight : P.height ≤ m)
    {F : R} (hF : F ≠ 0) (hFI : F ∈ I 0) :
    ∃ r < m + 2, ∃ Q : Ideal R,
      Q ∈ (I r).minimalPrimes ∧ Q ∈ (I (r + 1)).minimalPrimes ∧ Q ≤ P ∧
      1 ≤ Q.height ∧ Q.height ≤ m := by
  obtain ⟨r, hr, Q, hQr, hQnext, hQP⟩ :=
    exists_persistent_minimalPrime_pair I hI m P hP hIP hheight
  exact ⟨r, hr, Q, hQr, hQnext, hQP,
    minimalPrime_height_pos_of_nonzero_mem hQr hF ((hI (Nat.zero_le r)) hFI),
    (Ideal.height_mono hQP).trans hheight⟩

end PiExponent.PersistentComponents

end OAI
end Source0056

-- Source: OAI/NumberTheory/PiExponent/Jets/DerivativeIdeals.lean
section Source0057
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/DerivativeIdeals.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.DerivativeIdeals

variable {C R ι : Type*} [CommRing C] [CommRing R] [Algebra C R]

def wordDerivative (D : ι → Derivation C R R) (word : List ι) (f : R) : R :=
  word.foldr (fun i g => D i g) f

@[simp] theorem wordDerivative_nil (D : ι → Derivation C R R) (f : R) :
    wordDerivative D [] f = f := rfl

@[simp] theorem wordDerivative_cons (D : ι → Derivation C R R) (i : ι)
    (word : List ι) (f : R) : wordDerivative D (i :: word) f = D i (wordDerivative D word f) := rfl

def wordCost (cost : ι → ℝ) (word : List ι) : ℝ := (word.map cost).sum

@[simp] theorem wordCost_nil (cost : ι → ℝ) : wordCost cost [] = 0 := rfl
@[simp] theorem wordCost_cons (cost : ι → ℝ) (i : ι) (word : List ι) :
    wordCost cost (i :: word) = cost i + wordCost cost word := rfl

def derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ) (bound : ℝ) (f : R) :
    Ideal R := Ideal.span {g | ∃ word, wordCost cost word ≤ bound ∧ wordDerivative D word f = g}

theorem word_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (bound : ℝ) (f : R) (word : List ι) (hw : wordCost cost word ≤ bound) :
    wordDerivative D word f ∈ derivativeIdeal D cost bound f :=
  Ideal.subset_span ⟨word, hw, rfl⟩

theorem derivativeIdeal_mono (D : ι → Derivation C R R) (cost : ι → ℝ)
    (f : R) {a b : ℝ} (hab : a ≤ b) :
    derivativeIdeal D cost a f ≤ derivativeIdeal D cost b f := by
  apply Ideal.span_mono
  rintro g ⟨word, hw, rfl⟩
  exact ⟨word, hw.trans hab, rfl⟩

def derivativeCore (D : Derivation C R R) (I : Ideal R) : Ideal R where
  carrier := {f | f ∈ I ∧ D f ∈ I}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact ⟨I.zero_mem, I.zero_mem⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨I.add_mem hf.1 hg.1, ?_⟩
    rw [map_add]
    exact I.add_mem hf.2 hg.2
  smul_mem' := by
    intro r f hf
    change r * f ∈ I ∧ D (r * f) ∈ I
    refine ⟨I.mul_mem_left r hf.1, ?_⟩
    rw [Derivation.leibniz]
    exact I.add_mem (I.mul_mem_left r hf.2) (by
      simpa only [smul_eq_mul, mul_comm] using I.mul_mem_left (D r) hf.1)

theorem derivation_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (i : ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    D i g ∈ derivativeIdeal D cost (bound + cost i) f := by
  let I := derivativeIdeal D cost (bound + cost i) f
  have hle : derivativeIdeal D cost bound f ≤ derivativeCore (D i) I := by
    apply Ideal.span_le.mpr
    rintro g ⟨word, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f word
        (hw.trans (le_add_of_nonneg_right (hcost i)))
    · exact word_mem_derivativeIdeal D cost (bound + cost i) f (i :: word)
        (by simpa only [wordCost_cons, add_comm] using add_le_add_left hw (cost i))
  exact (hle hg).2

theorem wordDerivative_mem_derivativeIdeal (D : ι → Derivation C R R) (cost : ι → ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (bound : ℝ) (f g : R) (word : List ι)
    (hg : g ∈ derivativeIdeal D cost bound f) :
    wordDerivative D word g ∈ derivativeIdeal D cost (bound + wordCost cost word) f := by
  induction word with
  | nil => simpa only [wordDerivative_nil, wordCost_nil, add_zero] using hg
  | cons i word ih =>
    have h := derivation_mem_derivativeIdeal D cost hcost
      (bound + wordCost cost word) f (wordDerivative D word g) i ih
    simpa only [wordDerivative_cons, wordCost_cons, add_assoc,
      add_comm (wordCost cost word) (cost i)] using h

theorem derivative_vanishes_on_persistent_ideal (D : ι → Derivation C R R)
    (cost : ι → ℝ) (hcost : ∀ i, 0 ≤ cost i) (bound delta : ℝ) (f g : R)
    (Q : Ideal R) (hg : g ∈ derivativeIdeal D cost bound f)
    (hpersist : derivativeIdeal D cost (bound + delta) f ≤ Q)
    (word : List ι) (hw : wordCost cost word ≤ delta) :
    wordDerivative D word g ∈ Q := by
  apply hpersist
  have hb : bound + wordCost cost word ≤ bound + delta := by linarith
  exact derivativeIdeal_mono D cost f hb
    (wordDerivative_mem_derivativeIdeal D cost hcost bound f g word hg)

end PiExponent.DerivativeIdeals
end

end OAI
end Source0057

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryDerivativeIdeals.lean
section Source0058
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryDerivativeIdeals.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDerivatives

open scoped BigOperators
open DerivativeIdeals

abbrev Polynomial (n : ℕ) := MvPolynomial (Fin n) ℂ

def partialFrame (n : ℕ) (i : Fin n) : Derivation ℚ (Polynomial n) (Polynomial n) :=
  (MvPolynomial.pderiv i).restrictScalars ℚ

@[simp] theorem partialFrame_apply (n : ℕ) (i : Fin n) (p : Polynomial n) :
    partialFrame n i p = MvPolynomial.pderiv i p := rfl

def word (n : ℕ) (l : List (Fin n)) (p : Polynomial n) : Polynomial n :=
  wordDerivative (partialFrame n) l p

@[simp] theorem word_nil (n : ℕ) (p : Polynomial n) : word n [] p = p := rfl
@[simp] theorem word_cons (n : ℕ) (i : Fin n) (l : List (Fin n)) (p : Polynomial n) :
    word n (i :: l) p = MvPolynomial.pderiv i (word n l p) := rfl

def ideal (n : ℕ) (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) : Ideal (Polynomial n) :=
  derivativeIdeal (partialFrame n) cost bound p

theorem supportBound_pderiv {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p) (i : Fin n) :
    WeightedSliceDegree.SupportBound W (N - W i) (MvPolynomial.pderiv i p) := by
  intro d hd
  have hshift : d + Finsupp.single i 1 ∈ p.support := by
    apply MvPolynomial.mem_support_iff.mpr
    intro hz
    have hh := MvPolynomial.mem_support_iff.mp hd
    apply hh
    rw [MvPolynomial.coeff_pderiv, hz, zero_mul]
  apply (le_sub_iff_add_le).mpr
  have h := hp _ hshift
  simpa only [map_add, Finsupp.weight_single, one_smul] using h

theorem supportBound_word {n : ℕ} (W : Fin n → ℝ) (N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : List (Fin n)) :
    WeightedSliceDegree.SupportBound W N (word n l p) := by
  induction l with
  | nil => exact hp
  | cons i l ih =>
    exact (supportBound_pderiv W N (word n l p) ih i).mono (sub_le_self N (hW i))

abbrev BoundedWords {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) :=
  {l : List (Fin n) // wordCost cost l ≤ bound}

def equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    BoundedWords cost bound → Polynomial n := fun l => word n l.1 p

theorem span_equations {n : ℕ} (cost : Fin n → ℝ) (bound : ℝ) (p : Polynomial n) :
    Ideal.span (Set.range (equations cost bound p)) = ideal n cost bound p := by
  unfold ideal derivativeIdeal
  congr 1
  ext g
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨l, hl, rfl⟩
    exact ⟨⟨l, hl⟩, rfl⟩

theorem equation_supportBound {n : ℕ} (cost W : Fin n → ℝ) (bound N : ℝ)
    (p : Polynomial n) (hp : WeightedSliceDegree.SupportBound W N p)
    (hW : ∀ i, 0 ≤ W i) (l : BoundedWords cost bound) :
    WeightedSliceDegree.SupportBound W N (equations cost bound p l) :=
  supportBound_word W N p hp hW l.1

end PiExponent.OrdinaryDerivatives
end

end OAI
end Source0058

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryJetDerivatives.lean
section Source0059
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryJetDerivatives.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

theorem formalJet_pderiv {n : ℕ} (c : Fin n → ℂ) (i : Fin n)
    (p : MvPolynomial (Fin n) ℂ) :
    formalJet c (MvPolynomial.pderiv i p) = MvPowerSeries.pderiv i (formalJet c p) := by
  apply FormalLogJet.derivation_map_of_X (formalJet c) (MvPolynomial.pderiv i)
    (MvPowerSeries.pderiv i) _ p
  intro j
  by_cases hij : i = j
  · subst j
    simp [formalJet]
  · simp [formalJet, MvPowerSeries.pderiv_X_of_ne, Ne.symm hij]

theorem formalJet_word_vanishing {n : ℕ} (c : Fin n → ℂ)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (word : List (Fin n)) :
    formalJet c (OrdinaryDerivatives.word n word p) ∈
      JetGeometry.rationalWeightedIdeal v hv (H - (word.map v).sum) := by
  induction word with
  | nil => simpa only [OrdinaryDerivatives.word_nil, List.map_nil, List.sum_nil, sub_zero] using hp
  | cons i word ih =>
    rw [OrdinaryDerivatives.word_cons, formalJet_pderiv]
    have h := FormalJetDerivatives.pderiv_mem_rationalWeightedIdeal v hv
      (H - (word.map v).sum) (formalJet c (OrdinaryDerivatives.word n word p)) ih i
    simpa only [List.map_cons, List.sum_cons, sub_sub, add_comm] using h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0059

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryBranchEvaluation.lean
section Source0060
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryBranchEvaluation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryAuxiliaryJet

open MvPowerSeries

def branchCoordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ) :
    Fin n → PowerSeries ℂ := fun i => x i - PowerSeries.C (c i)

theorem branchCoordinates_hasSubst {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i) :
    HasSubst (branchCoordinates c x) := by
  apply hasSubst_of_constantCoeff_zero
  intro i
  change PowerSeries.constantCoeff (x i - PowerSeries.C (c i)) = 0
  rw [map_sub, hx i, PowerSeries.constantCoeff_C, sub_self]

theorem formalJet_subst_branch {n : ℕ} (c : Fin n → ℂ)
    (x : Fin n → PowerSeries ℂ) (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (p : MvPolynomial (Fin n) ℂ) :
    subst (branchCoordinates c x) (formalJet c p) = MvPolynomial.aeval x p := by
  let ha := branchCoordinates_hasSubst c x hx
  have heq : (substAlgHom ha).comp (formalJet c) = MvPolynomial.aeval x := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, formalJet, MvPolynomial.aeval_X, map_add]
    rw [substAlgHom_X, substAlgHom_apply, subst_C]
    change PowerSeries.C (c i) + (x i - PowerSeries.C (c i)) = x i
    ring
  simpa only [AlgHom.comp_apply, substAlgHom_apply] using AlgHom.congr_fun heq p

theorem ordinaryWord_branch_order {n : ℕ}
    (c : Fin n → ℂ) (x : Fin n → PowerSeries ℂ)
    (hx : ∀ i, PowerSeries.constantCoeff (x i) = c i)
    (v : Fin n → ℚ) (hv : ∀ i, 0 ≤ v i) (mu H : ℚ) (hmu : 0 ≤ mu)
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v hv H)
    (hcontact : ∀ i (k : ℕ), (branchCoordinates c x i).order = (k : ℕ∞) →
      mu * v i ≤ (k : ℚ)) (word : List (Fin n)) :
    (⌈mu * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      PowerSeries.order (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := FormalBranchOrder.rational_powerSeries_order_subst_of_mem_weightedIdeal
    v hv mu (H - (word.map v).sum) hmu
    (formalJet c (OrdinaryDerivatives.word n word p)) (branchCoordinates c x)
    (branchCoordinates_hasSubst c x hx)
    (formalJet_word_vanishing c v hv H p hp word) hcontact
  rwa [formalJet_subst_branch c x hx] at h

end PiExponent.OrdinaryAuxiliaryJet
end

end OAI
end Source0060

-- Source: OAI/NumberTheory/PiExponent/Jets/OrdinaryDVRBranchJet.lean
section Source0061
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/OrdinaryDVRBranchJet.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.OrdinaryDVRBranchJet
open OrdinaryAuxiliaryJet

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem expansion_aeval {n : ℕ} (x : Fin n → A) (p : MvPolynomial (Fin n) ℂ) :
    DVRBranch.expansion ℂ A (MvPolynomial.aeval x p) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) p := by
  have h : (DVRBranch.expansion ℂ A).comp (MvPolynomial.aeval x) =
      MvPolynomial.aeval (fun i => DVRBranch.expansion ℂ A (x i)) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  exact AlgHom.congr_fun h p

def coordinates {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A) :
    Fin n → PowerSeries ℂ :=
  branchCoordinates c (fun i => DVRBranch.expansion ℂ A (x i))

theorem coordinates_centered {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i) :
    ∀ i, PowerSeries.constantCoeff (coordinates c x i) = 0 := by
  intro i
  change PowerSeries.constantCoeff
    (DVRBranch.expansion ℂ A (x i) - PowerSeries.C (c i)) = 0
  rw [map_sub, DVRBranch.expansion_constantCoeff, hx i,
    PowerSeries.constantCoeff_C, sub_self]

theorem coordinates_nonzero {n : ℕ} (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    ∃ i, coordinates c x i ≠ 0 := by
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro hz
  apply hi
  apply DVRBranch.expansion_injective ℂ A
  rw [AlgHom.commutes]
  change DVRBranch.expansion ℂ A (x i) = PowerSeries.C (c i)
  exact sub_eq_zero.mp hz

def contact {n : ℕ} (v : Fin n → ℚ) (c : Fin n → ℂ) (x : Fin n → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) : ℚ :=
  BranchContact.contact v (coordinates c x) (coordinates_nonzero c x hnc)

theorem contact_pos {n : ℕ} (v : Fin n → ℚ) (hv : ∀ i, 0 < v i)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    0 < contact v c x hnc :=
  BranchContact.contact_pos v hv _ _ (coordinates_centered c x hx)

theorem ordinaryWord_addVal_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n)) :
    (⌈contact v c x hnc * (H - (word.map v).sum)⌉₊ : ℕ∞) ≤
      IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)) := by
  have h := ordinaryWord_branch_order c (fun i => DVRBranch.expansion ℂ A (x i))
    (fun i => by simpa using hx i) v (fun i => (hv i).le)
    (contact v c x hnc) H (contact_pos v hv c x hx hnc).le p hp
    (BranchContact.contact_bound v hv _ _) word
  rwa [← expansion_aeval, DVRBranch.expansion_order] at h

theorem ordinaryWord_addVal_toNat_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((IsDiscreteValuationRing.addVal A
        (MvPolynomial.aeval x (OrdinaryDerivatives.word n word p))).toNat : ℚ) := by
  have h := ordinaryWord_addVal_lower v hv H c x hx hnc p hp word
  have hn := IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hne
  have hh := ENat.toNat_le_toNat h hn
  exact Nat.ceil_le.mp (by simpa using hh)

theorem ordinaryWord_colength_lower {n : ℕ}
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (c : Fin n → ℂ) (x : Fin n → A)
    (hx : ∀ i, CurveLocalOrder.residueAugmentation ℂ A (x i) = c i)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i))
    (p : MvPolynomial (Fin n) ℂ)
    (hp : formalJet c p ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval x (OrdinaryDerivatives.word n word p) ≠ 0) :
    contact v c x hnc * (H - (word.map v).sum) ≤
      ((Module.length A (A ⧸ Ideal.span {
        MvPolynomial.aeval x (OrdinaryDerivatives.word n word p)})).toNat : ℚ) := by
  rw [CurveLocalOrder.length_quotient_span_eq_addVal hne]
  exact ordinaryWord_addVal_toNat_lower v hv H c x hx hnc p hp word hne

end PiExponent.OrdinaryDVRBranchJet
end

end OAI
end Source0061

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/FibreContact.lean
section Source0062
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/FibreContact.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.FibreContact

theorem contact_zero_cons {m : ℕ} (v : Fin (m+1) → ℚ)
    (a : Fin m → PowerSeries ℂ) (ha : ∃ i, a i ≠ 0)
    (hfull : ∃ i, (Fin.cases 0 a : Fin (m+1) → PowerSeries ℂ) i ≠ 0) :
    BranchContact.contact v (Fin.cases 0 a) hfull =
      BranchContact.contact (fun i => v i.succ) a ha := by
  apply le_antisymm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains (fun i => v i.succ) a ha
    have hh := BranchContact.contact_le v
      (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull i.succ
      (by simpa only [Fin.cases_succ] using hi)
    simp only [Fin.cases_succ] at hh
    exact hh.trans_eq he.symm
  · obtain ⟨i, hi, he⟩ := BranchContact.exists_attains v (Fin.cases (0 : PowerSeries ℂ) a : Fin (m+1) → PowerSeries ℂ) hfull
    cases i using Fin.cases with
    | zero => exact (hi rfl).elim
    | succ i =>
      have hh := BranchContact.contact_le (fun i => v i.succ) a ha i
        (by simpa only [Fin.cases_succ] using hi)
      simp only [Fin.cases_succ] at he
      exact hh.trans_eq he.symm

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra ℂ A] [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField A)]

theorem coordinates_one {m : ℕ} (c : Fin m → ℂ) (x : Fin m → A) :
    DVRBranchJet.coordinates c (1 : A) x =
      Fin.cases 0 (OrdinaryDVRBranchJet.coordinates c x) := by
  funext i
  cases i using Fin.cases with
  | zero => simp [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates]
  | succ i =>
    simp only [DVRBranchJet.coordinates, FormalBranchEvaluation.branchCoordinates,
      Fin.cases_succ, map_one, sub_self,
      PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log, sub_zero]
    rfl

theorem logarithmic_contact_eq_ordinary {m : ℕ} (v : Fin (m+1) → ℚ)
    (c : Fin m → ℂ) (x : Fin m → A)
    (hnc : ∃ i, x i ≠ algebraMap ℂ A (c i)) :
    DVRBranchJet.contact v c (1 : A) x (Or.inr hnc) =
      OrdinaryDVRBranchJet.contact (fun i => v i.succ) c x hnc := by
  have ha := OrdinaryDVRBranchJet.coordinates_nonzero c x hnc
  have hb : ∃ i, (Fin.cases (0 : PowerSeries ℂ)
      (OrdinaryDVRBranchJet.coordinates c x) : Fin (m+1) → PowerSeries ℂ) i ≠ 0 := by
    obtain ⟨i, hi⟩ := ha
    exact ⟨i.succ, by simpa only [Fin.cases_succ] using hi⟩
  have hcongr {b d : Fin (m+1) → PowerSeries ℂ} (he : b = d)
      (hb : ∃ i, b i ≠ 0) (hd : ∃ i, d i ≠ 0) :
      BranchContact.contact v b hb = BranchContact.contact v d hd := by subst d; rfl
  exact (hcongr (coordinates_one c x)
    (DVRBranchJet.coordinates_nonzero c 1 x (Or.inr hnc)) hb).trans
      (contact_zero_cons v (OrdinaryDVRBranchJet.coordinates c x) ha hb)

theorem weightedPole_le {ι : Type*} [Fintype ι]
    (w z : ι → ℚ) (t : ℚ) (ht : 0 ≤ t) (hcoord : ∀ i, -z i / w i ≤ t) :
    WeightedCurveDegree.weightedPole w z ≤ t := by
  apply Finset.sup'_le
  intro i hi
  cases i with
  | none => exact ht
  | some i => exact hcoord i

theorem weightedPole_zero_cons {m : ℕ} (w : Fin (m+1) → ℚ) (z : Fin m → ℚ) :
    WeightedCurveDegree.weightedPole w (Fin.cases 0 z) =
      WeightedCurveDegree.weightedPole (fun i => w i.succ) z := by
  let zz : Fin (m+1) → ℚ := Fin.cases 0 z
  let ww : Fin m → ℚ := fun i => w i.succ
  change WeightedCurveDegree.weightedPole w zz = WeightedCurveDegree.weightedPole ww z
  have hz0 : zz 0 = 0 := rfl
  have hzs (i : Fin m) : zz i.succ = z i := rfl
  have hws (i : Fin m) : ww i = w i.succ := rfl
  have hleft0 := WeightedCurveDegree.weightedPole_nonneg w zz
  have hright0 := WeightedCurveDegree.weightedPole_nonneg ww z
  apply le_antisymm
  · apply weightedPole_le w zz _ hright0
    intro i
    cases i using Fin.cases with
    | zero => simpa only [hz0, neg_zero, zero_div] using hright0
    | succ i =>
      rw [hzs]
      have hh := WeightedCurveDegree.div_le_weightedPole ww z i
      rw [hws] at hh
      exact hh
  · apply weightedPole_le ww z _ hleft0
    intro i
    have hh := WeightedCurveDegree.div_le_weightedPole w zz i.succ
    rw [hzs] at hh
    rw [hws]
    exact hh

theorem coordinatePole_one {E : Type*} [Field E] {m : ℕ}
    (val : AddValuation E (WithTop ℤ)) (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    WeightedPolynomialPole.coordinatePole val (Fin.cases 1 x) w =
      WeightedPolynomialPole.coordinatePole val x (fun i => w i.succ) := by
  have h1 : WeightedPolynomialPole.coordinateOrder val 1 = 0 := by
    simp [WeightedPolynomialPole.coordinateOrder]
  have he : (fun i : Fin (m+1) =>
      (WeightedPolynomialPole.coordinateOrder val ((Fin.cases (1 : E) x : Fin (m+1) → E) i) : ℚ)) =
      Fin.cases 0 (fun i => (WeightedPolynomialPole.coordinateOrder val (x i) : ℚ)) := by
    funext i
    cases i using Fin.cases <;> simp [h1]
  unfold WeightedPolynomialPole.coordinatePole
  rw [he]
  exact weightedPole_zero_cons w _

theorem weightedDegree_one {E : Type*} [Field E] [Algebra ℂ E] {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (w : Fin (m+1) → ℚ) (x : Fin m → E) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
  have he : CurveContactSum.weightedPoleDivisor hfinite
      (Fin.cases (1 : E) x : Fin (m+1) → E) w =
      CurveContactSum.weightedPoleDivisor hfinite x (fun i => w i.succ) := by
    ext p
    exact coordinatePole_one p.valuation w x
  unfold CurveContactSum.weightedDegree
  rw [he]

end PiExponent.FibreContact
end

end OAI
end Source0062

-- Source: OAI/NumberTheory/PiExponent/Geometry/PlaceCenteredBranch.lean
section Source0063
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/PlaceCenteredBranch.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
namespace PiExponent.PlaceCenteredBranch

open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole

variable {E ι : Type*} [Field E] [Algebra ℂ E]

def lift (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : ring p :=
  ⟨z i, hc.coordinate_nonneg i⟩

@[simp] theorem lift_coe (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (i : ι) : (lift p z c hc i : E) = z i := rfl

theorem lift_nonconstant (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i)) :
    ∃ i, lift p z c hc i ≠ algebraMap ℂ (ring p) (c i) := by
  obtain ⟨i,hi⟩ := hnc
  refine ⟨i,?_⟩
  intro he
  exact hi (congrArg (fun a : ring p => (a : E)) he)

theorem lift_aeval (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ)
    (hc : Centered z c p) (f : MvPolynomial ι ℂ) :
    algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f) =
      MvPolynomial.aeval z f := by
  exact MvPolynomial.comp_aeval_apply (f := lift p z c hc)
    (IsScalarTower.toAlgHom ℂ (ring p) E) f

theorem coordinateOrder_aeval_eq_length
    (p : NormalizedPlace ℂ E) (z : ι → E) (c : ι → ℂ) (hc : Centered z c p)
    (f : MvPolynomial ι ℂ) (hne : MvPolynomial.aeval z f ≠ 0) :
    coordinateOrder p.valuation (MvPolynomial.aeval z f) =
      ((Module.length (ring p) ((ring p) ⧸
        Ideal.span {MvPolynomial.aeval (lift p z c hc) f})).toNat : ℤ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) f ≠ 0 := by
    intro h
    apply hne
    rw [← lift_aeval p z c hc f, h, map_zero]
  rw [coordinateOrder, dite_eq_right hne, valuation_eq_fractionAddValuation p]
  have hu : Units.mk0 (MvPolynomial.aeval z f) hne =
      Units.mk0 (algebraMap (ring p) E (MvPolynomial.aeval (lift p z c hc) f))
        ((map_ne_zero_iff _ (IsFractionRing.injective (ring p) E)).mpr hn) := by
    apply Units.ext
    exact (lift_aeval p z c hc f).symm
  rw [hu]
  exact CurveLocalOrder.integerOrder_field_image_eq_length hn

variable (p : NormalizedPlace ℂ E)
    [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

theorem lift_residue (z : ι → E) (c : ι → ℂ) (hc : Centered z c p) (i : ι) :
    CurveLocalOrder.residueAugmentation ℂ (ring p) (lift p z c hc i) = c i := by
  have hm : lift p z c hc i - algebraMap ℂ (ring p) (c i) ∈
      IsLocalRing.maximalIdeal (ring p) := by
    apply p.valuation.toValuation.mem_maximalIdeal_iff.mpr
    exact hc i
  have hz : CurveLocalOrder.residueAugmentation ℂ (ring p)
      (lift p z c hc i - algebraMap ℂ (ring p) (c i)) = 0 := by
    change (CurveLocalOrder.residueCoefficientEquiv ℂ (ring p)).symm
      (IsLocalRing.residue (ring p) _) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).mpr hm, map_zero]
  rw [map_sub, CurveLocalOrder.residueAugmentation_algebraMap, sub_eq_zero] at hz
  exact hz

omit [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))] in
theorem logLift_nonconstant {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    lift p z (Fin.cases 1 c) hc 0 ≠ 1 ∨
      ∃ i, lift p z (Fin.cases 1 c) hc i.succ ≠ algebraMap ℂ (ring p) (c i) := by
  obtain ⟨i,hi⟩ := lift_nonconstant p z (Fin.cases 1 c) hc hnc
  cases i using Fin.cases with
  | zero => exact Or.inl (by simpa using hi)
  | succ i => exact Or.inr ⟨i,hi⟩

def logContact {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) : ℚ :=
  DVRBranchJet.contact v c (lift p z (Fin.cases 1 c) hc 0)
    (fun i => lift p z (Fin.cases 1 c) hc i.succ) (logLift_nonconstant p z c hc hnc)

theorem logContact_pos {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContact p z c hc hnc v := by
  exact DVRBranchJet.contact_pos v hv c _ _
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ) _

def ordinaryContact {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) : ℚ :=
  OrdinaryDVRBranchJet.contact v c (lift p z c hc) (lift_nonconstant p z c hc hnc)

theorem logWord_field_order_lower {m : ℕ} (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (Fin.cases 1 c) p)
    (hnc : ∃ i : Fin (m+1), z i ≠ algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : PiExponentApprox.FramePolynomial m)
    (hf : FormalLogJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f) ≠ 0) :
    logContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation
        (MvPolynomial.aeval z (PiExponentApprox.polynomialFrameWord m word f)) : ℚ) := by
  let x := lift p z (Fin.cases 1 c) hc
  have he : (fun i => Fin.cases (x 0) (fun j => x j.succ) i) = x := by
    funext i
    cases i using Fin.cases <;> rfl
  have hn : MvPolynomial.aeval x (PiExponentApprox.polynomialFrameWord m word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z (Fin.cases 1 c) hc, hz, map_zero]
  have hb := DVRBranchJet.frameWord_colength_lower v hv H c (x 0) (fun i => x i.succ)
    (lift_residue p z (Fin.cases 1 c) hc 0)
    (fun i => lift_residue p z (Fin.cases 1 c) hc i.succ)
    (logLift_nonconstant p z c hc hnc) f hf word (he.symm ▸ hn)
  have heval := congrArg (fun u : Fin (m+1) → ring p =>
    MvPolynomial.aeval u (PiExponentApprox.polynomialFrameWord m word f)) he
  rw [heval] at hb
  rw [coordinateOrder_aeval_eq_length p z (Fin.cases 1 c) hc _ hne]
  simpa only [Int.cast_natCast, logContact, x] using hb

theorem ordinaryWord_field_order_lower {n : ℕ} (z : Fin n → E) (c : Fin n → ℂ)
    (hc : Centered z c p) (hnc : ∃ i, z i ≠ algebraMap ℂ E (c i))
    (v : Fin n → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ)
    (f : MvPolynomial (Fin n) ℂ)
    (hf : OrdinaryAuxiliaryJet.formalJet c f ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin n))
    (hne : MvPolynomial.aeval z (OrdinaryDerivatives.word n word f) ≠ 0) :
    ordinaryContact p z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (OrdinaryDerivatives.word n word f)) : ℚ) := by
  have hn : MvPolynomial.aeval (lift p z c hc) (OrdinaryDerivatives.word n word f) ≠ 0 := by
    intro hz
    apply hne
    rw [← lift_aeval p z c hc, hz, map_zero]
  rw [coordinateOrder_aeval_eq_length p z c hc _ hne]
  simpa only [Int.cast_natCast, ordinaryContact] using
    OrdinaryDVRBranchJet.ordinaryWord_colength_lower v hv H c (lift p z c hc)
      (lift_residue p z c hc) (lift_nonconstant p z c hc hnc) f hf word hn

theorem fibre_nonconstant {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i)) :
    ∃ i, x i ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i,hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp at hi
  | succ i => exact ⟨i,hi⟩

theorem logContact_one {m : ℕ} (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (1 : E) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E ((Fin.cases (1 : ℂ) c : Fin (m+1) → ℂ) i))
    (v : Fin (m+1) → ℚ) :
    logContact p (Fin.cases (1 : E) x) c hc hnc v =
      ordinaryContact p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc)
        (fun i => v i.succ) := by
  have hy : lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc 0 = 1 :=
    Subtype.ext rfl
  have hx : (fun i => lift p (Fin.cases (1 : E) x) (Fin.cases (1 : ℂ) c) hc i.succ) =
      lift p x c (fun i => hc i.succ) := rfl
  simpa only [logContact, ordinaryContact, hy, hx] using
    FibreContact.logarithmic_contact_eq_ordinary v c (lift p x c (fun i => hc i.succ))
      (lift_nonconstant p x c (fun i => hc i.succ) (fibre_nonconstant x c hnc))

end PiExponent.PlaceCenteredBranch

end

end OAI
end Source0063

-- Source: LogTwo/Geometry/NormalizedContact.lean
section Source0064
/-! Local logarithmic contact at an arbitrary nonzero Y-coordinate. The old
Y=1 theorem is applied after normalization; the final order is that of the
original polynomial at the original curve coordinates. -/
namespace LogTwo.Geometry

open OAI PiExponent PiExponentApprox
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
noncomputable section

variable {E : Type*} [Field E] [Algebra ℂ E]

def centerPoint {m : ℕ} (y : ℂ) (c : Fin m → ℂ) : Fin (m+1) → ℂ := Fin.cases y c

theorem valuation_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    p.valuation (f / algebraMap ℂ E y) = p.valuation f := by
  rw [p.valuation.map_div, CurveProductFormula.valuation_constant_eq_zero p y hy, sub_zero]

theorem coordinateOrder_div_constant (p : NormalizedPlace ℂ E) (y : ℂ) (hy : y ≠ 0) (f : E) :
    coordinateOrder p.valuation (f / algebraMap ℂ E y) = coordinateOrder p.valuation f := by
  classical
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  by_cases hf : f = 0
  · simp [hf, coordinateOrder]
  · simp only [coordinateOrder, dif_neg (div_ne_zero hf hy'), dif_neg hf]
    apply WithTop.coe_injective
    rw [WeightedCurveDegree.coe_integerOrder, WeightedCurveDegree.coe_integerOrder]
    exact valuation_div_constant p y hy f

theorem coordinatePole_normalizeY (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    coordinatePole p.valuation (normalizeY y z) w = coordinatePole p.valuation z w := by
  have he : ∀ i, coordinateOrder p.valuation (normalizeY y z i) = coordinateOrder p.valuation (z i) := by
    intro i
    cases i using Fin.cases with
    | zero => exact coordinateOrder_div_constant p y hy (z 0)
    | succ i => rfl
  simp only [coordinatePole, he]

theorem weightedDegree_normalizeY {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite (normalizeY y z) w =
      CurveContactSum.weightedDegree hfinite z w := by
  have he : CurveContactSum.weightedPoleDivisor hfinite (normalizeY y z) w =
      CurveContactSum.weightedPoleDivisor hfinite z w := by
    ext p
    exact coordinatePole_normalizeY p y hy z w
  unfold CurveContactSum.weightedDegree
  rw [he]

theorem valuation_normalizeY_sub_center (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) (i : Fin (m+1)) :
    p.valuation (normalizeY y z i - algebraMap ℂ E (centerPoint 1 c i)) =
      p.valuation (z i - algebraMap ℂ E (centerPoint y c i)) := by
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have he : normalizeY y z 0 - algebraMap ℂ E (centerPoint 1 c 0) =
        (z 0 - algebraMap ℂ E y) / algebraMap ℂ E y := by
      simp [normalizeY, centerPoint, sub_div, hy']
    rw [he, valuation_div_constant p y hy]
    rfl
  | succ i => rfl

theorem normalized_centered_iff (p : NormalizedPlace ℂ E) {m : ℕ}
    (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ) :
    Centered (normalizeY y z) (centerPoint 1 c) p ↔ Centered z (centerPoint y c) p := by
  unfold Centered
  simp only [valuation_normalizeY_sub_center p y hy]

theorem normalized_nonconstant {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) :
    ∃ i, normalizeY y z i ≠ algebraMap ℂ E (centerPoint 1 c i) := by
  obtain ⟨i, hi⟩ := hnc
  refine ⟨i, ?_⟩
  intro he
  apply hi
  cases i using Fin.cases with
  | zero =>
    have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
    have hd : z 0 / algebraMap ℂ E y = 1 := by simpa [normalizeY, centerPoint] using he
    exact (div_eq_one_iff_eq hy').mp hd
  | succ i => exact he

/-- A constant Y-coordinate forces every centered branch, even at different
places, to belong to the same center when the Y-centers are distinct. -/
theorem center_index_unique_of_constantY {m : ℕ} {J : Type*}
    (y : J → ℂ) (hy : Function.Injective y) (c : J → Fin m → ℂ)
    (z : Fin (m+1) → E) (a : ℂ) (hconst : z 0 = algebraMap ℂ E a)
    (j k : J) (p q : NormalizedPlace ℂ E)
    (hp : Centered z (centerPoint (y j) (c j)) p)
    (hq : Centered z (centerPoint (y k) (c k)) q) : j = k := by
  apply hy
  exact (hp.constant_coordinate 0 a hconst).symm.trans (hq.constant_coordinate 0 a hconst)

variable (p : NormalizedPlace ℂ E)
  [Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p))]

def logContactAt {m : ℕ} (y : ℂ) (hy : y ≠ 0) (z : Fin (m+1) → E) (c : Fin m → ℂ)
    (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) : ℚ :=
  PlaceCenteredBranch.logContact p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc) v

theorem logContactAt_pos {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) : 0 < logContactAt p y hy z c hc hnc v :=
  PlaceCenteredBranch.logContact_pos p _ _ _ _ v hv

/-- The existing local derivative-order estimate, now at Y=y rather than Y=1. -/
theorem logWord_order_lower_at {m : ℕ} (y : ℂ) (hy : y ≠ 0)
    (z : Fin (m+1) → E) (c : Fin m → ℂ) (hc : Centered z (centerPoint y c) p)
    (hnc : ∃ i, z i ≠ algebraMap ℂ E (centerPoint y c i))
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i) (H : ℚ) (F : FramePolynomial m)
    (hF : formalJetAt y c F ∈ JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) H)
    (word : List (Fin (m+1)))
    (hne : MvPolynomial.aeval z (polynomialFrameWord m word F) ≠ 0) :
    logContactAt p y hy z c hc hnc v * (H - (word.map v).sum) ≤
      (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℚ) := by
  have hn : MvPolynomial.aeval (normalizeY y z)
      (polynomialFrameWord m word (scaleY y F)) ≠ 0 := by
    rw [aeval_normalizeY_scaled_word y hy]
    exact hne
  have hb := PlaceCenteredBranch.logWord_field_order_lower p (normalizeY y z) c
    ((normalized_centered_iff p y hy z c).mpr hc) (normalized_nonconstant y hy z c hnc)
    v hv H (scaleY y F) hF word hn
  rw [aeval_normalizeY_scaled_word y hy] at hb
  exact hb

theorem normalizeY_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) :
    normalizeY y (Fin.cases (algebraMap ℂ E y) x) = Fin.cases (1 : E) x := by
  have hy' : algebraMap ℂ E y ≠ 0 := (map_ne_zero_iff _ (algebraMap ℂ E).injective).mpr hy
  funext i
  cases i using Fin.cases <;> simp [normalizeY, hy']

theorem fiber_nonconstant_at {m : ℕ} (y : ℂ) (x : Fin m → E) (c : Fin m → ℂ)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) : ∃ i, x i ≠ algebraMap ℂ E (c i) := by
  obtain ⟨i, hi⟩ := hnc
  cases i using Fin.cases with
  | zero => simp [centerPoint] at hi
  | succ i => exact ⟨i, hi⟩

/-- On the constant Y=y fiber, logarithmic contact is exactly ordinary contact. -/
theorem logContactAt_fiber {m : ℕ} (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (c : Fin m → ℂ)
    (hc : Centered (Fin.cases (algebraMap ℂ E y) x) (centerPoint y c) p)
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i)) (v : Fin (m+1) → ℚ) :
    logContactAt p y hy (Fin.cases (algebraMap ℂ E y) x) c hc hnc v =
      PlaceCenteredBranch.ordinaryContact p x c (fun i => hc i.succ)
        (fiber_nonconstant_at y x c hnc) (fun i => v i.succ) := by
  unfold logContactAt
  simp only [normalizeY_fiber y hy]
  exact PlaceCenteredBranch.logContact_one p x c _ _ v

end
end LogTwo.Geometry
end Source0064

-- Source: LogTwo/Geometry/JetTruncation.lean
section Source0065
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the formal-log truncation proof to varying Y-centers and scaled polynomials.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
FormalLogTruncation.formalLog_packets_surjective_iff_truncated (Apache-2.0).
Modified here to allow a family of different Y-centers; see THIRD_PARTY_NOTICES.txt.

Transfer interpolation surjectivity through a filtration-preserving change
of variables. The full and truncated coefficient packets need not be equal. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogTruncation PiExponent.JetGeometry
noncomputable section

def truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) :
    FramePolynomial m →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (truncatedFormalJet c T).comp (scaleY y)

theorem shiftMap_truncatedJetAt {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (P : FramePolynomial m) :
    shiftMap (fun i => logTail (T i)) (fun i => logTail_constantCoeff (T i))
      (truncatedJetAt y c T P) = formalJetAt y c P :=
  shiftMap_truncatedFormalJet c T (scaleY y P)

/-- For an entire family of different Y-centers, one common shift of jet variables
transfers surjectivity. No equality of the individual coefficient packets is used. -/
theorem formalJetAt_surjective_iff_truncated {m : ℕ} {α J : Type*}
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i) (H : ℚ)
    (T : Fin m → ℕ) (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (y : J → ℂ) (c : J → Fin m → ℂ) (P : α → FramePolynomial m) :
    Function.Surjective (fun a j => rationalCoefficientPacket v H (formalJetAt (y j) (c j) (P a))) ↔
      Function.Surjective (fun a j => rationalCoefficientPacket v H
        (truncatedJetAt (y j) (c j) T (P a))) := by
  let tail := fun i => logTail (T i)
  let ht := fun i => logTail_constantCoeff (T i)
  let e := shiftEquiv tail ht
  have hw : ∀ i, (tail i).toMvPowerSeries (0 : Fin (m+1)) ∈
      rationalWeightedIdeal v hv (v i.succ) :=
    fun i => logTail_mem_rationalWeightedIdeal v hv (T i) (v i.succ) (hT i)
  have he : ∀ f ∈ rationalWeightedIdeal v hv H, e f ∈ rationalWeightedIdeal v hv H :=
    fun f hf => (shiftEquiv_mem_iff tail ht v hv hw H f).mpr hf
  have hi : ∀ f ∈ rationalWeightedIdeal v hv H, e.symm f ∈ rationalWeightedIdeal v hv H := by
    intro f hf
    apply (shiftEquiv_mem_iff tail ht v hv hw H (e.symm f)).mp
    change e (e.symm f) ∈ rationalWeightedIdeal v hv H
    simpa only [AlgEquiv.apply_symm_apply] using hf
  have hh := packets_surjective_comp_equiv_iff v hv H e he hi
    (fun a j => truncatedJetAt (y j) (c j) T (P a))
  simpa only [e, tail, ht, shiftEquiv_apply, shiftMap_truncatedJetAt] using hh

end
end LogTwo.Geometry
end Source0065

-- Source: LogTwo/Analysis/CenterGrowth.lean
section Source0066
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-! The extra growth from the centers Y=2^j. These estimates control individual
positive factors and Leibniz products. They do not transfer a determinant bound
from the Y=1 matrix: its cancellations still require a separate analytic proof. -/
namespace LogTwo.Analysis
open LogTwo.Interpolation LogTwo.Parameters Filter
open scoped Topology
noncomputable section

def centerGrowth {m : ℕ} (w : Weights m) : ℝ :=
  Real.log 2 * ((w.K : ℝ) / (w.w0 : ℝ))

end
end LogTwo.Analysis
end Source0066

-- Source: OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateContactBound.lean
section Source0067
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoordinateContactBound.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section
open scoped BigOperators
namespace PiExponent.CoordinateContactBound

open WeightedSliceDegree CurveValuationCenter CurveCenters

theorem supportBound_X_sub_C
    {K ι : Type*} [Field K] (W : ι → ℝ) (i : ι) (hi : 0 ≤ W i) (c : K) :
    SupportBound W (W i) (MvPolynomial.X i - MvPolynomial.C c) := by
  have hX : SupportBound W (W i) (MvPolynomial.X i : MvPolynomial ι K) :=
    supportBound_X W i
  have hC : SupportBound W (W i) (MvPolynomial.C (-c)) := (supportBound_C W (-c)).mono hi
  simpa only [map_neg, sub_eq_add_neg] using hX.add hC

@[simp] theorem ordinary_formalJet_X_sub_C {n : ℕ} (c : Fin n → ℂ) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) =
      MvPowerSeries.X i := by
  simp only [OrdinaryAuxiliaryJet.formalJet, map_sub, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  change MvPowerSeries.C (c i) + MvPowerSeries.X i - MvPowerSeries.C (c i) = MvPowerSeries.X i
  abel

theorem X_mem_rationalWeightedIdeal
    {K ι : Type*} [CommRing K] (V : ι → ℚ) (hV : ∀ i, 0 ≤ V i) (i : ι) :
    MvPowerSeries.X i ∈ (JetGeometry.rationalWeightedIdeal V hV (V i) :
      Ideal (MvPowerSeries ι K)) := by
  classical
  intro d hd
  rw [MvPowerSeries.coeff_X, ite_eq_right]
  intro he
  subst d
  simp [Finsupp.weight_single] at hd

theorem ordinary_formalJet_coordinate_mem {n : ℕ} (c : Fin n → ℂ)
    (V : Fin n → ℚ) (hV : ∀ i, 0 ≤ V i) (i : Fin n) :
    OrdinaryAuxiliaryJet.formalJet c (MvPolynomial.X i - MvPolynomial.C (c i)) ∈
      JetGeometry.rationalWeightedIdeal V hV (V i) := by
  rw [ordinary_formalJet_X_sub_C]
  exact X_mem_rationalWeightedIdeal V hV i

theorem coordinate_contact_sum_le
    {E : Type*} [Field E] [Algebra ℂ E] {n : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (x : Fin n → E) (c : Fin n → ℂ)
    (W V : Fin n → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (i : Fin n) (hne : x i - algebraMap ℂ E (c i) ≠ 0)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered x c p)
    (hres : ∀ p ∈ S,
      Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (PlaceValuationRing.ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (PlaceCenteredBranch.ordinaryContact p x c (hc p hp)
        ⟨i, sub_ne_zero.mp hne⟩ V : ℝ)) :
    (V i : ℝ) * (∑ p ∈ S, μ p) ≤
      (W i : ℝ) * CurveContactSum.weightedDegree hfinite x W := by
  let f : MvPolynomial (Fin n) ℂ := MvPolynomial.X i - MvPolynomial.C (c i)
  have hfe : MvPolynomial.aeval x f = x i - algebraMap ℂ E (c i) := by simp [f]
  apply CurveContactSum.polynomial_contact_sum_le hfinite x W hW
    (W i : ℝ) (V i : ℝ) (by exact_mod_cast (hW i).le) f
    (supportBound_X_sub_C (fun j => (W j : ℝ)) i (by exact_mod_cast (hW i).le) (c i))
    (hfe ▸ hne) S μ
  intro p hp
  let := hres p hp
  rw [hμ p hp]
  have h := PlaceCenteredBranch.ordinaryWord_field_order_lower p x c (hc p hp)
    ⟨i, sub_ne_zero.mp hne⟩ V hV (V i) f
    (ordinary_formalJet_coordinate_mem c V (fun j => (hV j).le) i) []
    (by simpa only [OrdinaryDerivatives.word_nil, hfe] using hne)
  simp only [List.map_nil, List.sum_nil, sub_zero, OrdinaryDerivatives.word_nil] at h
  exact_mod_cast (by simpa only [mul_comm] using h :
    V i * PlaceCenteredBranch.ordinaryContact p x c (hc p hp) ⟨i, sub_ne_zero.mp hne⟩ V ≤
      (WeightedPolynomialPole.coordinateOrder p.valuation (MvPolynomial.aeval x f) : ℚ))

end PiExponent.CoordinateContactBound

end

end OAI
end Source0067

-- Source: LogTwo/Geometry/ConstantFiber.lean
section Source0068
/-! The actual contact-sum bound on one constant nonzero Y fiber. This uses the
existing coordinate-contact theorem, rather than assuming a per-center bound.
The global argument forcing an exceptional curve onto such a fiber is separate. -/
namespace LogTwo.Geometry
open OAI PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

theorem weightedDegree_constant_fiber {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (w : Fin (m+1) → ℚ) :
    CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E y) x) w =
      CurveContactSum.weightedDegree hfinite x (fun i => w i.succ) := by
  calc
    _ = CurveContactSum.weightedDegree hfinite
        (normalizeY y (Fin.cases (algebraMap ℂ E y) x)) w :=
      (weightedDegree_normalizeY hfinite y hy _ w).symm
    _ = CurveContactSum.weightedDegree hfinite (Fin.cases (1 : E) x) w := by
      rw [normalizeY_fiber y hy]
    _ = _ := FibreContact.weightedDegree_one hfinite w x

/-- On Y=y, V_i=W_i/theta gives sum(contact) <= theta*degree. The contact
function is required to be the actual normalized logarithmic contact; no local
or global inequality is an input. Center-index uniqueness is a separate lemma. -/
theorem constant_fiber_contact_sum_le {m : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (y : ℂ) (hy : y ≠ 0) (x : Fin m → E) (c : Fin m → ℂ)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (hratio : ∀ i : Fin m, w i.succ = theta * v i.succ)
    (S : Finset (NormalizedPlace ℂ E))
    (hc : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E y) x) (centerPoint y c) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hnc : ∃ i : Fin (m+1), (Fin.cases (algebraMap ℂ E y) x : Fin (m+1) → E) i ≠
      algebraMap ℂ E (centerPoint y c i))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p y hy (Fin.cases (algebraMap ℂ E y) x) c (hc p hp) hnc v : ℝ)) :
    (∑ p ∈ S, μ p) ≤ (theta : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E y) x) w := by
  obtain ⟨i, hi⟩ := fiber_nonconstant_at y x c hnc
  have hcenter : ∀ p ∈ S, Centered x c p := fun p hp k => hc p hp k.succ
  have hbound := CoordinateContactBound.coordinate_contact_sum_le hfinite x c
    (fun k => w k.succ) (fun k => v k.succ)
    (fun k => hw k.succ) (fun k => hv k.succ) i (sub_ne_zero.mpr hi)
    S hcenter hres μ (by
      intro p hp
      letI := hres p hp
      simpa only [logContactAt_fiber] using hμ p hp)
  have hratioR : (w i.succ : ℝ) = (v i.succ : ℝ) * (theta : ℝ) := by
    exact_mod_cast (hratio i).trans (mul_comm theta (v i.succ))
  rw [hratioR, mul_assoc] at hbound
  have hpos : (0 : ℝ) < v i.succ := by exact_mod_cast hv i.succ
  have hsum := (mul_le_mul_iff_right₀ hpos).mp hbound
  simpa only [weightedDegree_constant_fiber hfinite y hy x w] using hsum

/-- If the Y-centers are distinct and Y is constant, every selected branch has
one common center. Summing the actual contacts therefore loses no factor K. -/
theorem constant_fiber_family_contact_sum_le {m : ℕ} {J : Type*}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (a : ℂ) (x : Fin m → E) (y : J → ℂ) (hy : Function.Injective y)
    (hy0 : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (theta : ℚ) (htheta : 0 ≤ theta)
    (hratio : ∀ i : Fin m, w i.succ = theta * v i.succ)
    (S : Finset (NormalizedPlace ℂ E)) (j : NormalizedPlace ℂ E → J)
    (hc : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E a) x)
      (centerPoint (y (j p)) (c (j p))) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (hnc : ∀ k : J, ∃ i : Fin (m+1),
      (Fin.cases (algebraMap ℂ E a) x : Fin (m+1) → E) i ≠
        algebraMap ℂ E (centerPoint (y k) (c k) i))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p (y (j p)) (hy0 (j p))
        (Fin.cases (algebraMap ℂ E a) x) (c (j p)) (hc p hp) (hnc (j p)) v : ℝ)) :
    (∑ p ∈ S, μ p) ≤ (theta : ℝ) *
      CurveContactSum.weightedDegree hfinite (Fin.cases (algebraMap ℂ E a) x) w := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨p0, hp0⟩ := hS
    have he : ∀ p ∈ S, j p = j p0 := by
      intro p hp
      exact center_index_unique_of_constantY y hy c _ a rfl
        (j p) (j p0) p p0 (hc p hp) (hc p0 hp0)
    have ha : a = y (j p0) := (hc p0 hp0).constant_coordinate 0 a rfl
    subst a
    have hcenter : ∀ p ∈ S, Centered (Fin.cases (algebraMap ℂ E (y (j p0))) x)
        (centerPoint (y (j p0)) (c (j p0))) p := by
      intro p hp
      simpa only [he p hp] using hc p hp
    apply constant_fiber_contact_sum_le hfinite (y (j p0)) (hy0 (j p0)) x (c (j p0))
      w v hw hv theta hratio S hcenter hres (hnc (j p0)) μ
    intro p hp
    letI := hres p hp
    simpa only [he p hp] using hμ p hp
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.sum_empty]
    exact mul_nonneg (by exact_mod_cast htheta)
      (CurveContactSum.weightedDegree_nonneg hfinite _ w)

end
end LogTwo.Geometry
end Source0068

-- Source: LogTwo/Geometry/JetMatrix.lean
section Source0069
/-! The actual rational matrix entries are the coefficients of the truncated
complex jets. Renaming the distinguished variable preserves coefficients. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox
open PiExponent.FormalLogJet PiExponent.FormalLogTruncation
open LogTwo.Interpolation
noncomputable section

/-- Coefficient extension Q -> C, followed by none -> 0 and some i -> i.succ. -/
def rationalJetEmbedding (m : ℕ) :
    MvPolynomial (Option (Fin m)) ℚ →+* MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.coeToMvPowerSeries.ringHom.comp
    ((MvPolynomial.rename (_root_.finSuccEquiv m).symm).toRingHom.comp
      (MvPolynomial.map (algebraMap ℚ ℂ)))

@[simp] theorem rationalJetEmbedding_C (m : ℕ) (a : ℚ) :
    rationalJetEmbedding m (MvPolynomial.C a) = MvPowerSeries.C (a : ℂ) := by
  simp [rationalJetEmbedding]

@[simp] theorem rationalJetEmbedding_X (m : ℕ) (i : Option (Fin m)) :
    rationalJetEmbedding m (MvPolynomial.X i) =
      MvPowerSeries.X ((_root_.finSuccEquiv m).symm i) := by
  simp [rationalJetEmbedding]

theorem coeff_rationalJetEmbedding {m : ℕ}
    (P : MvPolynomial (Option (Fin m)) ℚ) (d : Option (Fin m) →₀ ℕ) :
    MvPowerSeries.coeff (d.mapDomain (_root_.finSuccEquiv m).symm)
      (rationalJetEmbedding m P) = (P.coeff d : ℂ) := by
  change (MvPolynomial.rename (_root_.finSuccEquiv m).symm
    (MvPolynomial.map (algebraMap ℚ ℂ) P)).coeff _ = _
  rw [MvPolynomial.coeff_rename_mapDomain _ (_root_.finSuccEquiv m).symm.injective]
  exact MvPolynomial.coeff_map _ _ _

/-- The finite sum uses precisely the same cutoff as PowerSeries.trunc. -/
theorem rationalJetEmbedding_truncatedLog (m T : ℕ) :
    rationalJetEmbedding m (truncatedLog T) =
      liftSeries m (PowerSeries.trunc T (PowerSeries.log ℂ) : PowerSeries ℂ) := by
  induction T with
  | zero => simp [truncatedLog]
  | succ T ih =>
    by_cases hT : T = 0
    · subst T
      simp [truncatedLog, PowerSeries.trunc_succ, PowerSeries.coeff_log]
    · have hT1 : 1 ≤ T := Nat.one_le_iff_ne_zero.mpr hT
      have hs : truncatedLog (m := m) (T+1) = truncatedLog T +
          MvPolynomial.C ((-1 : ℚ) ^ (T+1) / T) * MvPolynomial.X none ^ T := by
        exact Finset.sum_Ico_succ_top hT1 _
      rw [hs, map_add, map_mul, map_pow, rationalJetEmbedding_C,
        rationalJetEmbedding_X, _root_.finSuccEquiv_symm_none, ih,
        PowerSeries.trunc_succ]
      simp [PowerSeries.coeff_log, hT, ← Polynomial.C_mul_X_pow_eq_monomial,
        liftSeries_eq_toMvPowerSeries]

theorem truncatedJetAt_frameMonomial {m : ℕ} (y : ℂ) (c : Fin m → ℂ)
    (T : Fin m → ℕ) (h : ℕ) (α : Fin m → ℕ) :
    truncatedJetAt y c T (frameMonomial h α) =
      MvPowerSeries.C (y ^ h) * (1 + MvPowerSeries.X 0) ^ h *
      ∏ i, (MvPowerSeries.C (c i) +
        liftSeries m (PowerSeries.trunc (T i) (PowerSeries.log ℂ) : PowerSeries ℂ) +
        MvPowerSeries.X i.succ) ^ α i := by
  simp [truncatedJetAt, truncatedFormalJet, frameMonomial, scaleY, map_prod,
    mul_pow, MvPowerSeries.algebraMap_apply, add_comm, add_left_comm, add_assoc]

/-- Equality for every column, before any admissibility or interpolation assumptions. -/
theorem rationalJetEmbedding_columnExpansion {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (j : ℕ) (col : Column m) :
    rationalJetEmbedding m (columnExpansion r T j col) =
      truncatedJetAt ((2 : ℂ)^j) (fun i => (j : ℂ) * (r i : ℂ)) T
        (frameMonomial col.h col.alpha) := by
  rw [truncatedJetAt_frameMonomial]
  simp [columnExpansion, map_prod, rationalJetEmbedding_truncatedLog, pow_mul]

/-- Exact bridge from the manuscript's rational matrix to the geometric jet. -/
theorem coefficientMatrix_eq_truncatedJetAt {m : ℕ}
    (r : Fin m → ℚ) (T : Fin m → ℕ) (row : Row m) (col : Column m) :
    (coefficientMatrix r T row col : ℂ) =
      MvPowerSeries.coeff ((rowExponent row).mapDomain (_root_.finSuccEquiv m).symm)
        (truncatedJetAt ((2 : ℂ)^row.j)
          (fun i => (row.j : ℂ) * (r i : ℂ)) T (frameMonomial col.h col.alpha)) := by
  rw [← rationalJetEmbedding_columnExpansion, coeff_rationalJetEmbedding]
  rfl

end
end LogTwo.Geometry
end Source0069

-- Source: OAI/NumberTheory/PiExponent/Jets/FormalJetIndices.lean
section Source0070
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Jets/FormalJetIndices.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

namespace OAI

noncomputable section

namespace PiExponent.FormalMatrixBridge

@[simp] theorem exponentVector_coe {n : ℕ} (d : Fin n →₀ ℕ) :
    InterpolationMatrix.exponentVector (fun i => d i) = d := by
  ext i
  simp

theorem cast_finsupp_weight {n : ℕ} (V : Fin n → ℚ) (d : Fin n →₀ ℕ) :
    (Finsupp.weight V d : ℝ) = ∑ i, (V i : ℝ) * (d i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, mul_comm]

def rationalJetIndexEquiv {n : ℕ} (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ) :
    {d : Fin n →₀ ℕ // Finsupp.weight V d < H} ≃
      ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ)) where
  toFun d := ⟨fun i => d.val i, by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    rw [← cast_finsupp_weight]
    exact_mod_cast d.property⟩
  invFun a := ⟨InterpolationMatrix.exponentVector a.val, by
    have ha := (mem_strictWeightedSimplex
      (fun i => by exact_mod_cast hV i)).mp a.property
    have hcast : (Finsupp.weight V (InterpolationMatrix.exponentVector a.val) : ℝ) <
        (H : ℝ) := by
      simpa only [cast_finsupp_weight, InterpolationMatrix.exponentVector_apply] using ha
    exact_mod_cast hcast⟩
  left_inv d := by apply Subtype.ext; exact exponentVector_coe d.val
  right_inv a := by apply Subtype.ext; funext i; simp

@[simp] theorem rationalJetIndexEquiv_apply_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (d : {d : Fin n →₀ ℕ // Finsupp.weight V d < H}) :
    (rationalJetIndexEquiv V hV H d).val = fun i => d.val i := rfl

@[simp] theorem rationalJetIndexEquiv_symm_val {n : ℕ}
    (V : Fin n → ℚ) (hV : ∀ i, 0 < V i) (H : ℚ)
    (a : ↥(strictWeightedSimplex (fun i => (V i : ℝ)) (H : ℝ))) :
    ((rationalJetIndexEquiv V hV H).symm a).val =
      InterpolationMatrix.exponentVector a.val := rfl

theorem polynomialOfCoefficients_of_weighted {m : ℕ}
    (W : Fin (m + 1) → ℝ) (hW : ∀ i, 0 < W i) (H : ℝ)
    (p : PiExponentApprox.FramePolynomial m)
    (hp : PiExponentApprox.HasWeightedDegreeLE W H p) :
    polynomialOfCoefficients (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val)) = p := by
  classical
  ext d
  by_cases hd : (fun i => d i) ∈ realWeightedSimplex W H
  · have he := polynomialOfCoefficients_coeff (realWeightedSimplex W H)
      (fun a => p.coeff (InterpolationMatrix.exponentVector a.val))
      ⟨fun i => d i, hd⟩
    simpa only [exponentVector_coe] using he
  · have hpzero : p.coeff d = 0 := by
      by_contra hne
      apply hd
      apply (mem_realWeightedSimplex hW).mpr
      simpa only [PiExponentApprox.monomialWeight, mul_comm] using
        hp d (MvPolynomial.mem_support_iff.mpr hne)
    rw [hpzero]
    by_contra hne
    have hmem := MvPolynomial.mem_support_iff.mpr hne
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp
      (polynomialOfCoefficients_support _ _ hmem)
    apply hd
    have hea : a = fun i => d i := by
      funext i
      simpa only [InterpolationMatrix.exponentVector_apply] using
        congrArg (fun e : Fin (m + 1) →₀ ℕ => e i) he
    simpa only [← hea] using ha

end PiExponent.FormalMatrixBridge

end

end OAI
end Source0070

-- Source: LogTwo/Geometry/WeightedIndices.lean
section Source0071
/-! Finite weighted indices for the manuscript's actual rational matrix. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent
noncomputable section

def columnWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℝ :=
  InterpolationMatrix.columnWeights w.w0 (fun i => w.w i)

def jetWeight {m : ℕ} (w : Weights m) : Fin (m+1) → ℚ :=
  Fin.cases w.v0 (fun i => w.w i / w.theta)

theorem columnWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < columnWeight w i := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change (0 : ℝ) < w.w0
    exact_mod_cast w.w0_pos
  · change (0 : ℝ) < w.w j
    exact_mod_cast w.w_pos j

theorem jetWeight_pos {m : ℕ} (w : Weights m) : ∀ i, 0 < jetWeight w i :=
  fun i => Fin.cases w.v0_pos (fun j => div_pos (w.w_pos j) w.theta_pos) i

theorem cast_jetWeight {m : ℕ} (w : Weights m) :
    (fun i => (jetWeight w i : ℝ)) =
      InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [jetWeight, InterpolationMatrix.rowWeights]

abbrev ColumnIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  ↥(realWeightedSimplex (columnWeight w) (H : ℝ))

abbrev RowIndex {m : ℕ} (w : Weights m) (H : ℚ) :=
  Fin w.K × ↥(strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ))

def columnOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    LogTwo.Interpolation.Column m := ⟨c.val 0, fun i => c.val i.succ⟩

def rowOfIndex {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    LogTwo.Interpolation.Row m := ⟨r.1.val, r.2.val 0, fun i => r.2.val i.succ⟩

theorem columnOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (c : ColumnIndex w H) :
    AdmissibleColumn w H (columnOfIndex c) := by
  have hc := (InterpolationMatrix.column_mem_iff
    (show (0 : ℝ) < w.w0 by exact_mod_cast w.w0_pos)
    (fun i => show (0 : ℝ) < w.w i by exact_mod_cast w.w_pos i) c.val).mp c.property
  unfold AdmissibleColumn columnOfIndex
  exact_mod_cast hc

theorem rowOfIndex_valid {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    AdmissibleRow w H (rowOfIndex r) := by
  refine ⟨r.1.isLt, ?_⟩
  have hr : r.2.val ∈ strictWeightedSimplex
      (InterpolationMatrix.rowWeights w.v0 w.theta (fun i => w.w i)) (H : ℝ) := by
    simpa only [← cast_jetWeight] using r.2.property
  have hb := (InterpolationMatrix.row_mem_iff
    (show (0 : ℝ) < w.v0 by exact_mod_cast w.v0_pos)
    (show (0 : ℝ) < w.theta by exact_mod_cast w.theta_pos)
    (fun i => show (0 : ℝ) < w.w i by exact_mod_cast w.w_pos i) r.2.val).mp hr
  change w.v0 * (r.2.val 0 : ℚ) + (∑ i, w.w i * (r.2.val i.succ : ℚ)) / w.theta < H
  exact_mod_cast hb

theorem columnOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@columnOfIndex m w H) := by
  intro a b hab
  apply Subtype.ext
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg LogTwo.Interpolation.Column.h hab
  · exact congrFun (congrArg LogTwo.Interpolation.Column.alpha hab) j

theorem rowOfIndex_injective {m : ℕ} (w : Weights m) (H : ℚ) :
    Function.Injective (@rowOfIndex m w H) := by
  intro a b hab
  apply Prod.ext
  · exact Fin.ext (congrArg LogTwo.Interpolation.Row.j hab)
  · apply Subtype.ext
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact congrArg LogTwo.Interpolation.Row.s hab
    · exact congrFun (congrArg LogTwo.Interpolation.Row.beta hab) j

theorem exists_rowIndex {m : ℕ} (w : Weights m) (H : ℚ)
    (r : LogTwo.Interpolation.Row m) (hr : AdmissibleRow w H r) :
    ∃ a : RowIndex w H, rowOfIndex a = r := by
  let b : Fin (m+1) → ℕ := Fin.cases r.s r.beta
  have hb : b ∈ strictWeightedSimplex (fun i => (jetWeight w i : ℝ)) (H : ℝ) := by
    rw [cast_jetWeight]
    apply (InterpolationMatrix.row_mem_iff
      (by exact_mod_cast w.v0_pos) (by exact_mod_cast w.theta_pos)
      (fun i => by exact_mod_cast w.w_pos i) b).mpr
    change (w.v0 : ℝ) * r.s + (∑ i, (w.w i : ℝ) * r.beta i) / w.theta < H
    exact_mod_cast hr.2
  exact ⟨(⟨r.j, hr.1⟩, ⟨b, hb⟩), rfl⟩

theorem rowExponent_index {m : ℕ} {w : Weights m} {H : ℚ} (r : RowIndex w H) :
    (rowExponent (rowOfIndex r)).mapDomain (_root_.finSuccEquiv m).symm =
      InterpolationMatrix.exponentVector r.2.val := by
  ext i
  rw [Finsupp.mapDomain_equiv_apply]
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [rowExponent, rowOfIndex, InterpolationMatrix.exponentVector]

end
end LogTwo.Geometry
end Source0071

-- Source: LogTwo/Geometry/InterpolationBridge.lean
section Source0072
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt packet surjectivity to varying Y-centers and add rational determinant descent.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Conditional bridge from weighted polynomial interpolation to the actual
rational full-row minor. The interpolation surjectivity is an explicit input. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox LogTwo.Interpolation
open PiExponent PiExponent.FormalMatrixBridge PiExponent.JetGeometry
noncomputable section

def indexedMatrix {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) :
    Matrix (RowIndex w H) (ColumnIndex w H) ℂ :=
  fun a b => (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ)

theorem monomial_eq_C_mul_frameMonomial {m : ℕ} (a : Fin (m+1) → ℕ) (z : ℂ) :
    MvPolynomial.monomial (InterpolationMatrix.exponentVector a) z =
      MvPolynomial.C z * frameMonomial (a 0) (fun i => a i.succ) := by
  rw [MvPolynomial.monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  rfl

theorem indexedMatrix_mulVec_eq_coeff {m : ℕ} (w : Weights m) (H : ℚ)
    (r : Fin m → ℚ) (T : Fin m → ℕ) (x : ColumnIndex w H → ℂ)
    (a : RowIndex w H) :
    (indexedMatrix w H r T).mulVec x a =
      MvPowerSeries.coeff (InterpolationMatrix.exponentVector a.2.val)
        (truncatedJetAt ((2 : ℂ)^a.1.val) (fun i => (a.1.val : ℂ)*(r i : ℂ)) T
          (polynomialOfCoefficients (realWeightedSimplex (columnWeight w) (H : ℝ)) x)) := by
  classical
  change (∑ b, (coefficientMatrix r T (rowOfIndex a) (columnOfIndex b) : ℂ) * x b) = _
  simp only [coefficientMatrix_eq_truncatedJetAt, rowExponent_index]
  change _ = MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (∑ b : ColumnIndex w H, MvPolynomial.monomial
      (InterpolationMatrix.exponentVector b.val) (x b)))
  simp only [map_sum, monomial_eq_C_mul_frameMonomial, map_mul]
  apply Finset.sum_congr rfl
  intro b hb
  simp [rowOfIndex, columnOfIndex, MvPowerSeries.algebraMap_apply,
    mul_comm]

/-- The degree constraint applies to one global polynomial for all centers. -/
theorem indexedMatrix_surjective_of_truncated_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (truncatedJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) T (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by
  classical
  intro y
  let e := rationalJetIndexEquiv (jetWeight w) (jetWeight_pos w) H
  let z : Fin w.K → RationalCoefficientPacket (R := ℂ) (jetWeight w) H :=
    fun j d => y (j, e d)
  obtain ⟨a, ha⟩ := hpacket z
  let x : ColumnIndex w H → ℂ :=
    fun c => (P a).coeff (InterpolationMatrix.exponentVector c.val)
  refine ⟨x, ?_⟩
  funext ρ
  change (indexedMatrix w H r T).mulVec x ρ = y ρ
  rw [indexedMatrix_mulVec_eq_coeff]
  change MvPowerSeries.coeff _ (truncatedJetAt _ _ T
    (polynomialOfCoefficients _ (fun c => (P a).coeff
      (InterpolationMatrix.exponentVector c.val)))) = _
  rw [polynomialOfCoefficients_of_weighted _ (columnWeight_pos w) _ (P a) (hdegree a)]
  have hh := congrFun (congrFun ha ρ.1) (e.symm ρ.2)
  change MvPowerSeries.coeff (e.symm ρ.2).val
    (truncatedJetAt _ _ T (P a)) = z ρ.1 (e.symm ρ.2) at hh
  simpa only [e, rationalJetIndexEquiv_symm_val, z, Equiv.apply_symm_apply] using hh

theorem indexedMatrix_surjective_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Function.Surjective (indexedMatrix w H r T).mulVecLin := by
  apply indexedMatrix_surjective_of_truncated_packets w H r T P hdegree
  exact (formalJetAt_surjective_iff_truncated (jetWeight w)
    (fun i => (jetWeight_pos w i).le) H T hT
    (fun j : Fin w.K => (2 : ℂ)^j.val)
    (fun j i => (j.val : ℂ)*(r i : ℂ)) P).mp hpacket

/-- Complex surjectivity selects rational columns with a nonzero rational determinant.
The certificate enumerates every admissible row, including when the row set is empty. -/
theorem fullRowMinor_of_indexedMatrix_surjective {m : ℕ}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hsurj : Function.Surjective (indexedMatrix w H r T).mulVecLin) :
    Nonempty (FullRowMinor w H r T) := by
  classical
  obtain ⟨select, hselect, hdet⟩ :=
    InterpolationMatrix.exists_full_row_minor_of_surjective (indexedMatrix w H r T) hsurj
  let e := (Fintype.equivFin (RowIndex w H)).symm
  refine ⟨{
    size := Fintype.card (RowIndex w H)
    rows := fun i => rowOfIndex (e i)
    columns := fun i => columnOfIndex (select (e i))
    rows_injective := (rowOfIndex_injective w H).comp e.injective
    columns_injective := (columnOfIndex_injective w H).comp (hselect.comp e.injective)
    row_valid := fun i => rowOfIndex_valid (e i)
    all_rows := ?_
    column_valid := fun i => columnOfIndex_valid (select (e i))
    det_ne_zero := ?_ }⟩
  · intro row hrow
    obtain ⟨a, ha⟩ := exists_rowIndex w H row hrow
    exact ⟨e.symm a, by simpa using ha⟩
  · have hd : (((indexedMatrix w H r T).submatrix id select).submatrix e e).det ≠ 0 := by
      rwa [Matrix.det_submatrix_equiv_self]
    intro hz
    apply hd
    let A : Matrix (Fin (Fintype.card (RowIndex w H))) _ ℚ :=
      fun i j => coefficientMatrix r T (rowOfIndex (e i)) (columnOfIndex (select (e j)))
    change (A.map (fun q : ℚ => (q : ℂ))).det = 0
    rw [← Rat.cast_det]
    have hA : A.det = 0 := hz
    rw [hA]
    norm_num

/-- The remaining geometric obligation is exactly the displayed packet surjectivity. -/
theorem fullRowMinor_of_formal_packets {m : ℕ} {α : Type*}
    (w : Weights m) (H : ℚ) (r : Fin m → ℚ) (T : Fin m → ℕ)
    (hT : ∀ i, w.w i / w.theta ≤ (T i : ℚ) * w.v0)
    (P : α → FramePolynomial m)
    (hdegree : ∀ a, HasWeightedDegreeLE (columnWeight w) (H : ℝ) (P a))
    (hpacket : Function.Surjective (fun a => fun j : Fin w.K =>
      rationalCoefficientPacket (jetWeight w) H
        (formalJetAt ((2 : ℂ)^j.val) (fun i => (j.val : ℂ)*(r i : ℂ)) (P a)))) :
    Nonempty (FullRowMinor w H r T) :=
  fullRowMinor_of_indexedMatrix_surjective w H r T
    (indexedMatrix_surjective_of_formal_packets w H r T hT P hdegree hpacket)

end
end LogTwo.Geometry
end Source0072

-- Source: LogTwo/Geometry/AuxiliaryAtCenters.lean
section Source0073
-- Modified in this edition: unused plain lemmas removed; see reduction.json.
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt the auxiliary-jet proof to varying Y-centers and simultaneous derivative words.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Jets/FormalAuxiliaryJet.lean (Apache-2.0). The same global polynomial now vanishes
at varying Y-centers. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent PiExponent.JetGeometry
open Filter Topology
noncomputable section

def formalEvaluationAtCenters {m : ℕ} (K : ℕ)
    (V : Fin (m+1) → ℝ) (H : ℝ) (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    FramePolynomial m →ₗ[ℂ] ((Fin K × ↥(strictWeightedSimplex V H)) → ℂ) :=
  LinearMap.pi (fun ρ =>
    (MvPowerSeries.coeff (InterpolationMatrix.exponentVector ρ.2.val)).comp
      (formalJetAt (y ρ.1) (c ρ.1)).toLinearMap)

/-- Dimension counting supplies one nonzero polynomial, vanishing simultaneously
at every center. The volume inequality is an explicit hypothesis. -/
theorem eventually_exists_auxiliary_at_centers {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℝ} (ha : 0 < a)
    (hvol : (K : ℝ) * a^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℝ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j d, Finsupp.weight (fun i => (V i : ℝ)) d < a*N →
        MvPowerSeries.coeff d (formalJetAt (y j) (c j) P) = 0 := by
  filter_upwards [eventually_exists_auxiliaryPolynomial W V hW hV K ha hvol] with N hN
  obtain ⟨P, hP, hw, he⟩ :=
    hN (formalEvaluationAtCenters K (fun i => (V i : ℝ)) (a*N) y c)
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  have hmem : (fun i => d i) ∈ strictWeightedSimplex (fun i => (V i : ℝ)) (a*N) := by
    apply (mem_strictWeightedSimplex (fun i => by exact_mod_cast hV i)).mpr
    simpa [Finsupp.weight_eq_sum, nsmul_eq_mul, mul_comm] using hd
  have hh := congrFun he (j, ⟨(fun i => d i), hmem⟩)
  simpa [formalEvaluationAtCenters, FormalMatrixBridge.exponentVector_coe] using hh

theorem eventually_exists_auxiliary_at_centers_nat {m : ℕ}
    (W V : Fin (m+1) → ℚ) (hW : ∀ i, 0 < W i) (hV : ∀ i, 0 < V i)
    (K : ℕ) {a : ℚ} (ha : 0 < a)
    (hvol : (K : ℝ) * (a : ℝ)^(m+1) * (∏ i, (W i : ℝ)) / (∏ i, (V i : ℝ)) < 1)
    (y : Fin K → ℂ) (c : Fin K → Fin m → ℂ) :
    ∀ᶠ N : ℕ in atTop, ∃ P : FramePolynomial m, P ≠ 0 ∧
      HasWeightedDegreeLE (fun i => (W i : ℝ)) N P ∧
      ∀ j, formalJetAt (y j) (c j) P ∈
        rationalWeightedIdeal V (fun i => (hV i).le) (a*N) := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (eventually_exists_auxiliary_at_centers W V hW hV K (by exact_mod_cast ha) hvol y c)
  filter_upwards [h] with N hN
  obtain ⟨P, hP, hw, hv⟩ := hN
  refine ⟨P, hP, hw, ?_⟩
  intro j d hd
  apply hv j d
  have hcast : ((Finsupp.weight V d : ℚ) : ℝ) < (a : ℝ)*(N : ℝ) := by exact_mod_cast hd
  simpa [Finsupp.weight_eq_sum, nsmul_eq_mul] using hcast

end
end LogTwo.Geometry
end Source0073

-- Source: LogTwo/Geometry/CurveWordVanishing.lean
section Source0074
/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Adapt logarithmic word vanishing to nonzero Y-centers and normalized contacts.
See ../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

/-! Adapted from openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Cohomology/CurveDerivativeVanishing.lean (Apache-2.0). This version uses arbitrary
nonzero Y-centers and any finite family of actual normalized contacts. It does
not import the global rigidity theorem. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry
open OAI PiExponentApprox PiExponent
open CurveValuationCenter CurveCenters PlaceValuationRing WeightedPolynomialPole
open Filter Topology
noncomputable section
variable {E : Type*} [Field E] [Algebra ℂ E]

/-- Excess actual contact forces low-cost derivative words to vanish identically
on the curve. Local order bounds are proved from jets, rather than assumed. -/
theorem curve_words_vanish_of_excess {m K : ℕ}
    (hfinite : ∀ f : E, Transcendental ℂ f →
      FiniteDimensional (IntermediateField.adjoin ℂ {f}) E)
    (z : Fin (m+1) → E) (y : Fin K → ℂ) (hy : ∀ j, y j ≠ 0)
    (c : Fin K → Fin m → ℂ)
    (hnc : ∀ j, ∃ i, z i ≠ algebraMap ℂ E (centerPoint (y j) (c j) i))
    (w v : Fin (m+1) → ℚ) (hw : ∀ i, 0 < w i) (hv : ∀ i, 0 < v i)
    (S : Finset (NormalizedPlace ℂ E)) (center : NormalizedPlace ℂ E → Fin K)
    (hc : ∀ p ∈ S, Centered z (centerPoint (y (center p)) (c (center p))) p)
    (hres : ∀ p ∈ S, Algebra.IsIntegral ℂ (IsLocalRing.ResidueField (ring p)))
    (μ : NormalizedPlace ℂ E → ℝ)
    (hμ : ∀ p (hp : p ∈ S), letI := hres p hp;
      μ p = (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ))
    (sigma : ℚ) (hsigma : 0 < sigma) (N : ℕ) (hN : 0 < N)
    (F : FramePolynomial m)
    (hF : HasWeightedDegreeLE (fun i => (w i : ℝ)) N F)
    (hjet : ∀ j, formalJetAt (y j) (c j) F ∈
      JetGeometry.rationalWeightedIdeal v (fun i => (hv i).le) ((1+3*sigma)*N))
    (hexcess : CurveContactSum.weightedDegree hfinite z w <
      (1+(sigma : ℝ)) * ∑ p ∈ S, μ p) :
    ∀ word : List (Fin (m+1)), (word.map v).sum ≤ sigma*N →
      MvPolynomial.aeval z (polynomialFrameWord m word F) = 0 := by
  intro word hword
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsigR : (0 : ℝ) < sigma := by exact_mod_cast hsigma
  have hdegree : ∀ d ∈ (polynomialFrameWord m word F).support,
      Finsupp.weight (fun i => (w i : ℝ)) d ≤ (N : ℝ) := by
    have hd := hF.polynomialFrameWord (fun i => by exact_mod_cast (hw i).le) word
    intro d hdmem
    simpa only [Finsupp.weight_eq_sum, nsmul_eq_mul, monomialWeight] using hd d hdmem
  have hsum : 0 ≤ ∑ p ∈ S, μ p := by
    apply Finset.sum_nonneg
    intro p hp
    letI := hres p hp
    rw [hμ p hp]
    exact_mod_cast (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
  apply CurveContactSum.polynomial_eq_zero_of_excess_contact hfinite z w hw
    (N : ℝ) ((1+2*(sigma : ℝ))*N) hNR.le (polynomialFrameWord m word F) hdegree S μ
  · intro hne p hp
    letI := hres p hp
    have hret : (1+2*sigma)*(N : ℚ) ≤ (1+3*sigma)*N - (word.map v).sum := by
      nlinarith
    have hlocal := logWord_order_lower_at p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv ((1+3*sigma)*N)
      F (hjet (center p)) word hne
    have hpos := (logContactAt_pos p (y (center p)) (hy (center p)) z
      (c (center p)) (hc p hp) (hnc (center p)) v hv).le
    have hq := (mul_le_mul_of_nonneg_left hret hpos).trans hlocal
    have hr : (logContactAt p (y (center p)) (hy (center p)) z (c (center p))
        (hc p hp) (hnc (center p)) v : ℝ) * ((1+2*(sigma : ℝ))*N) ≤
        (coordinateOrder p.valuation (MvPolynomial.aeval z (polynomialFrameWord m word F)) : ℝ) := by
      exact_mod_cast hq
    simpa only [← hμ p hp, mul_comm] using hr
  · calc
      (N : ℝ) * CurveContactSum.weightedDegree hfinite z w <
          N * ((1+(sigma : ℝ)) * ∑ p ∈ S, μ p) := mul_lt_mul_of_pos_left hexcess hNR
      _ = (1+(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) := by ring
      _ ≤ (1+2*(sigma : ℝ)) * (N * ∑ p ∈ S, μ p) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hNR.le hsum)
      _ = _ := by ring

end
end LogTwo.Geometry
end Source0074
