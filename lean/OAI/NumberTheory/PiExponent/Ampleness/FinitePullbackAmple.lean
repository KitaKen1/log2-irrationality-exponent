/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/FinitePullbackAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree
public import OAI.NumberTheory.PiExponent.Ampleness.AmpleFromCover
public import OAI.NumberTheory.PiExponent.Ampleness.ClosedAmpleRestriction

@[expose] public section

namespace OAI

noncomputable section
namespace PiExponentSeshadri.Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X Y : Scheme.{0}}

theorem LineBundle.IsAmple.of_pow (L : LineBundle X) {d : ℕ} (hd : 0 < d)
    (hL : (L.pow d).IsAmple) : L.IsAmple := by
  intro x V hx
  obtain ⟨n, hn, s, hxs, hsV, hsa⟩ := hL x V hx
  have he := PiExponent.AmpleIso.sectionOpen_postcomp_iso s (linePowerMul L d n)
  exact ⟨d*n, Nat.mul_pos hd hn, s ≫ (linePowerMul L d n).hom,
    he.symm ▸ hxs, he.le.trans hsV, he.symm ▸ hsa⟩

theorem LineBundle.IsAmple.pullback_finite [CompactSpace X] [IsIntegral Y] [CompactSpace Y]
    (L : LineBundle X) (hL : L.IsAmple) (f : Y ⟶ X) [IsFinite f] :
    (L.pullback f).IsAmple := by
  obtain ⟨d, hd, l, s, hc, ha, _⟩ := L.ample_common_degree_cover hL
  let t (i : Fin l) := pullbackPowerSection L f d (s i)
  have ht (i : Fin l) : sectionOpen Y (t i) = f ⁻¹ᵁ sectionOpen X (s i) :=
    sectionOpen_pullbackPowerSection L f d (s i)
  have htc : (⨆ i, sectionOpen Y (t i)) = ⊤ := by
    apply top_le_iff.mp
    intro y _
    have hy : f y ∈ ⨆ i, sectionOpen X (s i) := by rw [hc]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact Opens.mem_iSup.mpr ⟨i, by rw [ht]; exact hi⟩
  have hta (i : Fin l) : IsAffineOpen (sectionOpen Y (t i)) := by
    rw [ht]
    exact (ha i).preimage f
  exact LineBundle.IsAmple.of_pow (L.pullback f) hd
    (((L.pullback f).pow d).ample_of_affine_section_cover t htc hta)

end PiExponentSeshadri.Geometry

end

end OAI
