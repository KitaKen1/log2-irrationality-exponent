module

public import LogTwo.Geometry.NormalizedContact
public import OAI.NumberTheory.PiExponent.LocalAlgebra.CoordinateContactBound

@[expose] public section

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
