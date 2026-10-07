/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/CoherentInverseFinite.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.CoherentProjectiveFinite
public import OAI.NumberTheory.PiExponent.Geometry.LineBundleInverse

@[expose] public section

namespace OAI

namespace PiExponent.CoherentProjectiveFinite
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PiExponentSeshadri.Geometry
variable {X Y : Scheme.{0}}

theorem positive_coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q, 0 < q →
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) :=
  positive_coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q hq

theorem closed_positive_coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) [IsClosedImmersion f] (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q, 0 < q →
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) (hq : 0 < q) :
    letI := Module.compHom (cohomology M q) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M q) :=
  closed_positive_coherent_cohomology_finite_of_standard_twists f p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q hq

theorem coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q,
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : Y.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars p)
    FiniteDimensional ℂ (cohomology M q) :=
  coherent_cohomology_finite_of_standard_twists p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q

theorem closed_coherent_cohomology_finite_of_inverse_powers
    [IsNoetherian Y] [IsAffineHom (pullback.diagonal (terminal.from Y))]
    (f : X ⟶ Y) [IsClosedImmersion f] (p : Y ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle Y) (l : ℕ) (hl : 0 < l)
    (s : Fin l → (structureSheaf Y ⟶ L.sheaf))
    (hcover : (⨆ i, PiExponentSeshadri.SectionOpens.isoOpen (s i)) = ⊤)
    (haffine : ∀ i, IsAffineOpen (PiExponentSeshadri.SectionOpens.isoOpen (s i)))
    (hfinite : ∀ n q,
      letI := Module.compHom (cohomology (L.pow n).inverse.sheaf q) (baseScalars p)
      FiniteDimensional ℂ (cohomology (L.pow n).inverse.sheaf q))
    (M : X.Modules) [M.IsFinitePresentation] (q : ℕ) :
    letI := Module.compHom (cohomology M q) (baseScalars (f ≫ p))
    FiniteDimensional ℂ (cohomology M q) :=
  closed_coherent_cohomology_finite_of_standard_twists f p L l hl s hcover haffine
    (fun n => (L.pow n).inverse) (fun n => lineTensorInverseIso (L.pow n)) hfinite M q

end
end PiExponent.CoherentProjectiveFinite

end OAI
