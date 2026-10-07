/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CoherentProjectiveFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.AmpleGlobalGeneration
public import OAI.NumberTheory.PiExponent.Approximation.ClosedPushforwardLinear
public import OAI.NumberTheory.PiExponent.LocalAlgebra.PositiveCoherentExtFiniteness

@[expose] public section

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry

variable {X Y : Scheme.{0}}

theorem coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  apply CoherentExtFiniteness.coherent_cohomology_finite_of_presentations p
    l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover _ M q
  intro A hA
  obtain ⟨n, hn⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A s hcover haffine
  obtain ⟨g, hg⟩ := hn n le_rfl
  let : g.IsFiniteType := hg
  exact ⟨NegativeTwistPresentations.coherentFinitePresentation L (N n) g (hpair n) p
    (hfinite n)⟩

theorem closed_coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M q) := by
  exact ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward f p M q
    (coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine N hpair hfinite
      ((Scheme.Modules.pushforward f).obj M) q)

theorem positive_coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, 0 < q → letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) := by
  apply CoherentExtFiniteness.positive_coherent_cohomology_finite_of_presentations p
    l hl (fun i => PiExponentSeshadri.SectionOpens.isoOpen (s i)) haffine hcover _ M q hq
  intro A hA
  obtain ⟨n, hn⟩ := AmpleGlobalGeneration.eventual_global_generators_of_section_cover
    L A s hcover haffine
  obtain ⟨g, hg⟩ := hn n le_rfl
  let : g.IsFiniteType := hg
  exact ⟨NegativeTwistPresentations.positiveCoherentFinitePresentation L (N n) g (hpair n) p
    (hfinite n)⟩

theorem closed_positive_coherent_cohomology_finite_of_standard_twists
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) [IsClosedImmersion f]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (N : ℕ → LineBundle Y)
    (hpair : ∀ n, moduleTensor Y (L.pow n).sheaf (N n).sheaf ≅ structureSheaf Y)
    (hfinite : ∀ n q, 0 < q → letI := Module.compHom (cohomology (N n).sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (N n).sheaf q))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    letI := Module.compHom (cohomology M q) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M q) := by
  exact ClosedImmersionSerreTransfer.finiteDimensional_of_pushforward f p M q
    (positive_coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine N hpair hfinite
      ((Scheme.Modules.pushforward f).obj M) q hq)

end
end PiExponent.CoherentProjectiveFinite

end OAI
