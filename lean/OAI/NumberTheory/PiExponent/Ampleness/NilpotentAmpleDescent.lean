/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NilpotentAmpleDescent.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AmpleCommonDegree
public import OAI.NumberTheory.PiExponent.Approximation.ClosedPowerSectionLifting
public import OAI.NumberTheory.PiExponent.Cohomology.NilpotentIdealVanishing

@[expose] public section

namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem isAffineOpen_of_fullSupport_preimage [IsNoetherian X]
    (I : X.IdealSheafData) (hI : I.support = ⊤) (U : X.Opens)
    (hU : IsAffineOpen (I.subschemeι ⁻¹ᵁ U)) : IsAffineOpen U := by
  let : IsLocallyNoetherian U.toScheme := LocallyOfFiniteType.isLocallyNoetherian U.ι
  let : NoetherianSpace U.toScheme := U.ι.isOpenEmbedding.isInducing.noetherianSpace
  let : CompactSpace U.toScheme := NoetherianSpace.compactSpace U.toScheme
  let : IsNoetherian U.toScheme := {}
  let J := I.comap U.ι
  have hJ : J.support = ⊤ := by
    dsimp only [J]
    rw [Scheme.IdealSheafData.support_comap, hI]
    rfl
  let e : J.subscheme ≅ (I.subschemeι ⁻¹ᵁ U).toScheme :=
    I.comapIso U.ι ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict I.subschemeι U
  let : IsAffine (I.subschemeι ⁻¹ᵁ U).toScheme := hU
  let : IsAffine J.subscheme := IsAffine.of_isIso e.hom
  exact isAffine_of_fullSupport J hJ

theorem fullSupport_eventual_powerSection_surjective [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) :
    ∃ B, ∀ n, B ≤ n → Function.Surjective (pullbackPowerSection L I.subschemeι n) := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_ideal_twist_ext_zero p I hI L hL
  exact ⟨B, fun n hn => pullbackPowerSection_surjective_of_ideal_ext_zero I.subschemeι L n
    (hB n hn 1 (by decide))⟩

theorem LineBundle.isAmple_of_fullSupport [IsNoetherian X]
    {R : Type} [CommRing R] [IsNoetherianRing R]
    (p : X ⟶ Spec (CommRingCat.of R)) [IsProper p]
    (I : X.IdealSheafData) (hI : I.support = ⊤)
    (L : LineBundle X) (hL : (L.pullback I.subschemeι).IsAmple) : L.IsAmple := by
  obtain ⟨B,hB⟩ := fullSupport_eventual_powerSection_surjective p I hI L hL
  intro x V hx
  obtain ⟨y,hy⟩ := subscheme_surjective_of_fullSupport I hI x
  have hyV : y ∈ I.subschemeι ⁻¹ᵁ V := by change I.subschemeι y ∈ V; rwa [hy]
  obtain ⟨d,hd,s,hys,hsV,hsa⟩ := hL y (I.subschemeι ⁻¹ᵁ V) hyV
  let m := B+1
  have hm : 0 < m := Nat.succ_pos B
  let σ : GlobalSections I.subscheme ((L.pullback I.subschemeι).pow (d*m)).sheaf :=
    powerSection s m ≫ (linePowerMul (L.pullback I.subschemeι) d m).hom
  have hσ : sectionOpen I.subscheme σ = sectionOpen I.subscheme s := by
    exact (PiExponent.AmpleIso.sectionOpen_postcomp_iso
      (powerSection s m) (linePowerMul (L.pullback I.subschemeι) d m)).trans
      (((L.pullback I.subschemeι).pow d).sectionOpen_power s hm)
  have hBd : B ≤ d*m := (Nat.le_succ B).trans (Nat.le_mul_of_pos_left m hd)
  obtain ⟨t,ht⟩ := hB (d*m) hBd σ
  have hpre : I.subschemeι ⁻¹ᵁ sectionOpen X t = sectionOpen I.subscheme s := by
    exact (sectionOpen_pullbackPowerSection L I.subschemeι (d*m) t).symm.trans
      ((congrArg (fun u : GlobalSections I.subscheme
        ((L.pullback I.subschemeι).pow (d*m)).sheaf => sectionOpen I.subscheme u) ht).trans hσ)
  refine ⟨d*m, Nat.mul_pos hd hm, t, ?_, ?_, ?_⟩
  · have hyT : y ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by rw [hpre]; exact hys
    change I.subschemeι y ∈ sectionOpen X t at hyT
    rwa [hy] at hyT
  · intro z hz
    obtain ⟨w,hw⟩ := subscheme_surjective_of_fullSupport I hI z
    have hwT : w ∈ I.subschemeι ⁻¹ᵁ sectionOpen X t := by change I.subschemeι w ∈ sectionOpen X t; rwa [hw]
    rw [hpre] at hwT
    have hwV := hsV hwT
    change I.subschemeι w ∈ V at hwV
    rwa [hw] at hwV
  · apply isAffineOpen_of_fullSupport_preimage I hI
    rw [hpre]
    exact hsa

end
end PiExponentSeshadri.Geometry

end OAI
