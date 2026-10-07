/-
Modification notice for the LogTwo project.
Adapted from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Changes: Extract generic graded-domain Proj lemmas into the project namespace.
See ../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Geometry.ProjectiveDenseChart

@[expose] public section

/-! Integral Proj of a graded domain with a nonempty projective spectrum.
Adapted from openai/math Ampleness/BlowupProperIntegral.lean, pinned commit,
Apache-2.0. Extracting these general lemmas avoids importing the entire blowup
construction before it is needed. See THIRD_PARTY_NOTICES.txt. -/
namespace LogTwo.Geometry.IntegralProj
noncomputable section
open AlgebraicGeometry
universe u v
variable {A : Type u} {σ : Type v} [CommRing A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

instance homogeneous_isReduced (S : Submonoid A) [_root_.IsReduced A] :
    _root_.IsReduced (HomogeneousLocalization 𝒜 S) :=
  isReduced_of_injective (algebraMap (HomogeneousLocalization 𝒜 S) (Localization S))
    (HomogeneousLocalization.val_injective S)

instance proj_isReduced [_root_.IsReduced A] : IsReduced (Proj 𝒜) := by
  have (x : Proj 𝒜) : _root_.IsReduced ((Proj 𝒜).presheaf.stalk x) :=
    isReduced_of_injective (Proj.stalkIso' 𝒜 x) (Proj.stalkIso' 𝒜 x).injective
  exact isReduced_of_isReduced_stalk _

def genericPoint [IsDomain A] [Nonempty (Proj 𝒜)] : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := ⊥
  isPrime := Ideal.isPrime_bot
  not_irrelevant_le h := by
    obtain ⟨x⟩ := ‹Nonempty (Proj 𝒜)›
    exact x.not_irrelevant_le (h.trans bot_le)

lemma genericPoint_dense [IsDomain A] [Nonempty (Proj 𝒜)] :
    closure ({genericPoint 𝒜} : Set (ProjectiveSpectrum 𝒜)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  exact (ProjectiveSpectrum.le_iff_mem_closure 𝒜 _ _).mp
    (show (genericPoint 𝒜).asHomogeneousIdeal ≤ x.asHomogeneousIdeal from bot_le)

instance proj_irreducible [IsDomain A] [Nonempty (Proj 𝒜)] :
    IrreducibleSpace (Proj 𝒜) := by
  apply (irreducibleSpace_def _).mpr
  change IsIrreducible (Set.univ : Set (ProjectiveSpectrum 𝒜))
  rw [← genericPoint_dense 𝒜]
  exact (isIrreducible_singleton).closure

instance proj_isIntegral [IsDomain A] [Nonempty (Proj 𝒜)] : IsIntegral (Proj 𝒜) :=
  (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨inferInstance, inferInstance⟩


end
end LogTwo.Geometry.IntegralProj
