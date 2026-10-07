/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiDivisorAmple.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.NakaiBasepointFree
public import OAI.NumberTheory.PiExponent.Approximation.GeneratorsSectionCover
public import OAI.NumberTheory.PiExponent.Cohomology.NoetherianAmpleSerreVanishing

@[expose] public section

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry
open PiExponent.SectionZeroIdeal
variable {X : Scheme.{0}}

theorem eventual_zeroDivisor_power_generation
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    [NoetherianSpace (zeroIdeal L s).subscheme]
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ y : (zeroIdeal L s).subscheme, ∃ σ :
      GlobalSections (zeroIdeal L s).subscheme
        ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf),
      y ∈ sectionOpen (zeroIdeal L s).subscheme σ := by
  let i := (zeroIdeal L s).subschemeι
  obtain ⟨N,hN⟩ := GeneratorsSectionCover.ample_eventual_fin_section_cover (L.pullback i) hD
  refine ⟨N,fun n hn y => ?_⟩
  obtain ⟨k,t,ht⟩ := hN (n+1) (by omega)
  have hy : y ∈ ⨆ j, sectionOpen (zeroIdeal L s).subscheme (t j) := by rw [ht]; trivial
  obtain ⟨j,hj⟩ := Opens.mem_iSup.mp hy
  let e := PiExponentSeshadri.PullbackTensor.powIso i L (n+1)
  refine ⟨t j ≫ e.inv,?_⟩
  change y ∈ PiExponentSeshadri.SectionOpens.isoOpen (t j ≫ e.symm.hom)
  exact (PiExponentSeshadri.SectionOpens.isoOpen_postcomp (t j) e.symm).ge hj

theorem eventual_zeroDivisor_power_cohomology_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∀ q, 0 < q → ∀ z :
      cohomology ((Scheme.Modules.pullback (zeroIdeal L s).subschemeι).obj (L.pow (n+1)).sheaf) q,
      z = 0 := by
  let i := (zeroIdeal L s).subschemeι
  obtain ⟨N,hN⟩ := GeometrySupport.NoetherianAmpleSerreVanishing.ample_power_cohomology_zero
    (i ≫ p) (L.pullback i) hD
  refine ⟨N,fun n hn q hq => ?_⟩
  exact GeometrySupport.SerrePowerDescent.ext_zero_of_iso
    (PiExponentSeshadri.PullbackTensor.powIso i L (n+1)).symm q (hN (n+1) (by omega) q hq)

theorem eventual_power_section_cover_of_ample_zeroDivisor
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (L : LineBundle X) (s : GlobalSections X L.sheaf) [Mono s]
    (hfinite : ∀ n, letI := Module.compHom (cohomology (L.pow n).sheaf 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).sheaf 1))
    (hD : (L.pullback (zeroIdeal L s).subschemeι).IsAmple) :
    ∃ N, ∀ n, N ≤ n → ∃ l : ℕ, ∃ t : Fin l → GlobalSections X (L.pow (n+1)).sheaf,
      (⨆ j, sectionOpen X (t j)) = ⊤ := by
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  let i := (zeroIdeal L s).subschemeι
  let : IsLocallyNoetherian (zeroIdeal L s).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (i ≫ p)
  let : CompactSpace (zeroIdeal L s).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace (i ≫ p)
  let : IsNoetherian (zeroIdeal L s).subscheme := {}
  obtain ⟨N,hN⟩ := eventual_zeroDivisor_power_cohomology_zero p L s hD
  exact eventual_power_section_cover_of_divisor p L s hfinite
    ⟨N,fun n hn => hN n hn 1 (by decide)⟩
    (eventual_zeroDivisor_power_generation L s hD)

end
end PiExponent.NumericalAmpleness

end OAI
