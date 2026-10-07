module
public import Mathlib
@[expose] public section

section Source0000
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/FiniteCoverCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
end Source0000

section Source0001
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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

lemma powerSection_natural {M N : X.Modules} (s : structureSheaf X ⟶ M)
    (f : M ⟶ N) (n : ℕ) :
    powerSection s n ≫ modulePowMap f n = powerSection (s ≫ f) n := by
  simp only [powerSection, modulePowMap_comp, Category.assoc]

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
end Source0001

section Source0002
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Polynomials/FrameCoefficients.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
end Source0002

section Source0003
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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
end Source0003

section Source0004
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/CoherentTwistPresentation.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
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

theorem principalRestriction_localizes (r : R) :
    IsLocalizedModule.Away r (principalRestriction M r) :=
  ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance) r

theorem principal_section_extends (r : R)
    (x : affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : affineSections M ⊤,
      principalRestriction M r y = r ^ n • x := by
  let := principalRestriction_localizes M r
  obtain ⟨N, y, hy⟩ := (inferInstance : IsLocalizedModule.Away r
    (principalRestriction M r)).surj _ _ x
  refine ⟨N, fun n hn => ⟨r ^ (n - N) • y, ?_⟩⟩
  rw [map_smul, ← hy, ← mul_smul, ← pow_add, Nat.sub_add_cancel hn]

theorem principal_section_zero (r : R) (x : affineSections M ⊤)
    (hx : principalRestriction M r x = 0) :
    ∃ N : ℕ, ∀ n ≥ N, r ^ n • x = 0 := by
  let := principalRestriction_localizes M r
  obtain ⟨⟨_, N, rfl⟩, hN⟩ :=
    (IsLocalizedModule.eq_zero_iff (.powers r) (principalRestriction M r)).mp hx
  change r ^ N • x = 0 at hN
  refine ⟨N, fun n hn => ?_⟩
  rw [← Nat.sub_add_cancel hn, pow_add, mul_smul, hN, smul_zero]

theorem finite_principal_sections_extend {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M (PrimeSpectrum.basicOpen r)) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ y : ι → affineSections M ⊤,
      ∀ i, principalRestriction M r (y i) = r ^ n • x i := by
  classical
  choose N hN using fun i => principal_section_extends M r (x i)
  refine ⟨Finset.univ.sup N, fun n hn => ?_⟩
  have hn' (i : ι) : N i ≤ n :=
    (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  choose y hy using fun i => hN i n (hn' i)
  exact ⟨y, hy⟩

theorem finite_principal_sections_zero {ι : Type*} [Fintype ι] (r : R)
    (x : ι → affineSections M ⊤)
    (hx : ∀ i, principalRestriction M r (x i) = 0) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ i, r ^ n • x i = 0 := by
  classical
  choose N hN using fun i => principal_section_zero M r (x i) (hx i)
  refine ⟨Finset.univ.sup N, fun n hn i => ?_⟩
  exact hN i n ((Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn)

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
end Source0004

section Source0005
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/OpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.OpenBaseChange
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma restrict_unit_app {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) :
    ((Scheme.Modules.restrictAdjunction i).unit.app M).app W =
      M.presheaf.map (homOfLE (i.image_preimage_le W)).op := rfl

lemma restrict_unit_app_iso {Z T : Scheme.{0}} (i : Z ⟶ T) [IsOpenImmersion i]
    (M : T.Modules) (W : T.Opens) (hW : W ≤ i.opensRange) :
    IsIso (((Scheme.Modules.restrictAdjunction i).unit.app M).app W) := by
  rw [restrict_unit_app]
  have he : i ''ᵁ i ⁻¹ᵁ W = W := by
    rw [i.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hW]
  have hi : IsIso (homOfLE (i.image_preimage_le W)) :=
    homOfLE_isIso_of_eq _ he
  let e := @asIso _ _ _ _ (homOfLE (i.image_preimage_le W)) hi
  exact (M.presheaf.mapIso e.op).isIso_hom

def rightSquare :
    Scheme.Modules.pushforward (f ⁻¹ᵁ U).ι ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward (f ∣_ U) ⋙ Scheme.Modules.pushforward U.ι :=
  Scheme.Modules.pushforwardComp _ _ ≪≫
    Scheme.Modules.pushforwardCongr (morphismRestrict_ι f U).symm ≪≫
      (Scheme.Modules.pushforwardComp _ _).symm

def hom (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ⟶
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) :=
  (Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M)) ≫
  (Scheme.Modules.restrictFunctor U.ι).map
    ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)) ≫
  (Scheme.Modules.restrictAdjunction U.ι).counit.app
    ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))

instance hom_isIso (M : X.Modules) : IsIso (hom f U M) := by
  have ha : IsIso ((Scheme.Modules.restrictFunctor U.ι).map
    ((Scheme.Modules.pushforward f).map
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M))) := by
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro W
    change IsIso (((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
      (f ⁻¹ᵁ (U.ι ''ᵁ W)))
    apply restrict_unit_app_iso
    rw [Scheme.Opens.opensRange_ι]
    apply (Opens.map f.base).monotone
    simpa only [Scheme.Opens.opensRange_ι] using U.ι.image_le_opensRange W
  unfold hom
  infer_instance

def iso (M : X.Modules) :
    ((Scheme.Modules.pushforward f).obj M).restrict U.ι ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι) := asIso (hom f U M)

end
end PiExponentSeshadri.OpenBaseChange

end OAI
end Source0005

section Source0006
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

universe u

namespace SectionOpens

section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N : X.Modules}

lemma isIso_of_stalks (f : M ⟶ N)
    (h : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map f.mapPresheaf)) :
    IsIso f := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let A : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  let B : TopCat.Sheaf Ab X := ⟨N.presheaf, N.isSheaf⟩
  let φ : A ⟶ B := ⟨f.mapPresheaf⟩
  let (x : U) : IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map φ.hom) := h x.val
  exact TopCat.Presheaf.app_isIso_of_stalkFunctor_map_iso φ U

lemma stalk_isIso_of_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    [IsIso ((Scheme.Modules.restrictFunctor φ).map f)] (y : Y) :
    IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf) := by
  apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mp
  change IsIso ((TopCat.Presheaf.stalkFunctor Ab y).map
    ((Scheme.Modules.toPresheaf Y).map ((Scheme.Modules.restrictFunctor φ).map f)))
  infer_instance

lemma restrict_isIso_of_stalks (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ]
    (h : ∀ y : Y, IsIso ((TopCat.Presheaf.stalkFunctor Ab (φ y)).map f.mapPresheaf)) :
    IsIso ((Scheme.Modules.restrictFunctor φ).map f) := by
  apply isIso_of_stalks
  intro y
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ y) f).mpr (h y)

lemma isIso_of_locally_isIso (f : M ⟶ N)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)) : IsIso f := by
  apply isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := h x
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x, hx⟩

def isoOpen (f : M ⟶ N) : X.Opens :=
  ⨆ (U : X.Opens) (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)), U

lemma mem_isoOpen_iff (f : M ⟶ N) (x : X) :
    x ∈ isoOpen f ↔ ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map f) := by
  simp only [isoOpen, Opens.mem_iSup]
  aesop

theorem isIso_restrict_isoOpen (f : M ⟶ N) :
    IsIso ((Scheme.Modules.restrictFunctor (isoOpen f).ι).map f) := by
  apply restrict_isIso_of_stalks
  intro x
  obtain ⟨U, hx, hU⟩ := (mem_isoOpen_iff f x.val).mp x.property
  let := hU
  exact stalk_isIso_of_restrict f U.ι ⟨x.val, hx⟩

end

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}} {M N P : X.Modules}

lemma isoOpen_postcomp (f : M ⟶ N) (e : N ≅ P) :
    isoOpen (f ≫ e.hom) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (f ≫ e.hom) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_right
      ((Scheme.Modules.restrictFunctor U.ι).map f) ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (f ≫ e.hom) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_precomp (e : P ≅ M) (f : M ⟶ N) :
    isoOpen (e.hom ≫ f) = isoOpen f := by
  apply le_antisymm
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff (e.hom ≫ f) x).mp hx
    refine (mem_isoOpen_iff f x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp] at hU
    let := hU
    exact IsIso.of_isIso_comp_left
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ((Scheme.Modules.restrictFunctor U.ι).map f)
  · intro x hx
    obtain ⟨U, hxU, hU⟩ := (mem_isoOpen_iff f x).mp hx
    refine (mem_isoOpen_iff (e.hom ≫ f) x).mpr ⟨U, hxU, ?_⟩
    rw [Functor.map_comp]
    let := hU
    infer_instance

lemma isoOpen_restrict (f : M ⟶ N) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    isoOpen ((Scheme.Modules.restrictFunctor φ).map f) = φ ⁻¹ᵁ isoOpen f := by
  ext y
  constructor
  · intro hy
    obtain ⟨V, hyV, hV⟩ := (mem_isoOpen_iff _ y).mp hy
    let := hV
    apply (mem_isoOpen_iff f (φ y)).mpr
    refine ⟨φ ''ᵁ V, ⟨y, hyV, rfl⟩, ?_⟩
    apply restrict_isIso_of_stalks
    intro x
    obtain ⟨z, hz, he⟩ := x.property
    change φ z = x.val at he
    change IsIso ((TopCat.Presheaf.stalkFunctor Ab x.val).map f.mapPresheaf)
    rw [← he]
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z) f).mp
    exact stalk_isIso_of_restrict ((Scheme.Modules.restrictFunctor φ).map f) V.ι ⟨z, hz⟩
  · intro hy
    change φ y ∈ isoOpen f at hy
    let U := φ ⁻¹ᵁ isoOpen f
    apply (mem_isoOpen_iff _ y).mpr
    refine ⟨U, hy, ?_⟩
    apply restrict_isIso_of_stalks
    intro z
    apply (NatIso.isIso_map_iff (Scheme.Modules.restrictStalkNatIso φ z.val) f).mpr
    let := isIso_restrict_isoOpen f
    exact stalk_isIso_of_restrict f (isoOpen f).ι ⟨φ z.val, z.property⟩

end SectionOpens
namespace Frames
open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry
variable {X Y : Scheme.{u}}

lemma isUnit_iff_basicOpen_top (c : Γ(X, ⊤)) :
    IsUnit c ↔ X.basicOpen c = ⊤ := by
  refine ⟨X.basicOpen_of_isUnit, fun h => ?_⟩
  apply X.toRingedSpace.isUnit_of_isUnit_germ ⊤ c
  intro x hx
  apply (X.mem_basicOpen c x hx).mp
  rw [h]
  trivial

lemma coefficient_restrict_isUnit {M : X.Modules} (e : M ≅ O X)
    (s : O X ⟶ M) (φ : Y ⟶ X) [IsOpenImmersion φ] :
    IsUnit (φ.appTop (coefficient e s)) ↔
      IsIso ((Scheme.Modules.restrictFunctor φ).map s) := by
  rw [← coefficient_restrict, coefficient_isUnit_iff]
  let F : X.Modules ⥤ Y.Modules := Scheme.Modules.restrictFunctor φ
  let e : F.obj (O X) ≅ O Y := Scheme.Modules.restrictUnitIso φ
  exact isIso_comp_left_iff e.inv (F.map s)

theorem isoOpen_eq_basicOpen {M : X.Modules} (e : M ≅ O X) (s : O X ⟶ M) :
    SectionOpens.isoOpen s = X.basicOpen (coefficient e s) := by
  ext x
  constructor
  · intro hx
    obtain ⟨U, hxU, hU⟩ := (SectionOpens.mem_isoOpen_iff s x).mp hx
    have hc := (coefficient_restrict_isUnit e s U.ι).mpr hU
    have hb := U.toScheme.basicOpen_of_isUnit hc
    rw [← Scheme.preimage_basicOpen_top] at hb
    have H : (⟨x, hxU⟩ : U.toScheme) ∈ U.ι ⁻¹ᵁ X.basicOpen (coefficient e s) := by
      rw [hb]; trivial
    exact H
  · intro hx
    let U := X.basicOpen (coefficient e s)
    refine (SectionOpens.mem_isoOpen_iff s x).mpr ⟨U, hx, ?_⟩
    apply (coefficient_restrict_isUnit e s U.ι).mp
    apply (isUnit_iff_basicOpen_top _).mpr
    rw [← Scheme.preimage_basicOpen_top]
    ext z
    change z.val ∈ X.basicOpen (coefficient e s) ↔ True
    exact iff_true_intro z.property

lemma isoOpen_restrictSection {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] :
    SectionOpens.isoOpen (restrictSection φ s) = φ ⁻¹ᵁ SectionOpens.isoOpen s := by
  exact (SectionOpens.isoOpen_precomp (Scheme.Modules.restrictUnitIso φ).symm
    ((Scheme.Modules.restrictFunctor φ).map s)).trans (SectionOpens.isoOpen_restrict s φ)

theorem preimage_isoOpen {M : X.Modules} (s : O X ⟶ M)
    (φ : Y ⟶ X) [IsOpenImmersion φ] (e : M.restrict φ ≅ O Y) :
    φ ⁻¹ᵁ SectionOpens.isoOpen s =
      Y.basicOpen (coefficient e (restrictSection φ s)) := by
  rw [← isoOpen_restrictSection, isoOpen_eq_basicOpen e]

end Frames

end PiExponentSeshadri

end

end OAI
end Source0006

section Source0007
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameTensorPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

lemma tensor_unit_end {C : Type*} [Category C] [MonoidalCategory C]
    (f g : 𝟙_ C ⟶ 𝟙_ C) :
    (f ⊗ₘ g) ≫ (λ_ (𝟙_ C)).hom = (λ_ (𝟙_ C)).hom ≫ (f ≫ g) := by
  rw [MonoidalCategory.tensorHom_def, Category.assoc, leftUnitor_naturality, ← Category.assoc,
    unitors_equal, rightUnitor_naturality, Category.assoc]

lemma moduleTensorUnit_scalar (f g : structureSheaf X ⟶ structureSheaf X) :
    moduleTensorMap f g ≫ (moduleTensorUnit (structureSheaf X)).hom =
      (moduleTensorUnit (structureSheaf X)).hom ≫ (f ≫ g) := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  have h : (f.val ⊗ₘ g.val) ≫ (λ_ (structureSheaf X).val).hom =
      (λ_ (structureSheaf X).val).hom ≫ (f ≫ g).val := by
    let f₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := f.val
    let g₀ : 𝟙_ (PresheafOfModules X.ringCatSheaf.obj) ⟶
        𝟙_ (PresheafOfModules X.ringCatSheaf.obj) := g.val
    exact tensor_unit_end f₀ g₀
  change F.map (f.val ⊗ₘ g.val) ≫ (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) =
    (F.map (λ_ (structureSheaf X).val).hom ≫ ε.app (structureSheaf X)) ≫ (f ≫ g)
  erw [← Category.assoc, ← F.map_comp, h, F.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact ε.naturality (f ≫ g)

def endPower (f : structureSheaf X ⟶ structureSheaf X) : ℕ → (structureSheaf X ⟶ structureSheaf X)
  | 0 => 𝟙 _
  | n + 1 => f ≫ endPower f n

lemma endValue_endPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    endValue (endPower f n) = endValue f ^ n := by
  induction n with
  | zero =>
    change (1 : Γ(X, ⊤)) = endValue f ^ 0
    exact (pow_zero _).symm
  | succ n hn =>
    calc
      endValue (endPower f (n + 1)) = endValue f * endValue (endPower f n) :=
        endValue_comp f (endPower f n)
      _ = endValue f * endValue f ^ n := congrArg (endValue f * ·) hn
      _ = _ := (pow_succ' _ _).symm

lemma moduleTensorUnit_natural {M N : X.Modules} (g : M ⟶ N) :
    moduleTensorMap (𝟙 (structureSheaf X)) g ≫ (moduleTensorUnit N).hom =
      (moduleTensorUnit M).hom ≫ g := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  let F : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules :=
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let G : X.Modules ⥤ PresheafOfModules X.ringCatSheaf.obj :=
    SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)
  let ε : G ⋙ F ⟶ 𝟭 X.Modules :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit
  change F.map ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫
    (F.map (λ_ N.val).hom ≫ ε.app N) =
    (F.map (λ_ M.val).hom ≫ ε.app M) ≫ g
  have h : ((𝟙 (structureSheaf X).val) ⊗ₘ g.val) ≫ (λ_ N.val).hom =
      (λ_ M.val).hom ≫ g.val := by
    rw [id_tensorHom]
    exact leftUnitor_naturality g.val
  have hF : F.map (𝟙 (structureSheaf X).val ⊗ₘ g.val) ≫ F.map (λ_ N.val).hom =
      F.map (λ_ M.val).hom ≫ F.map g.val :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h).trans (F.map_comp _ _))
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ ε.app N) hF).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (F.map (λ_ M.val).hom ≫ ·) (ε.naturality g)).trans ?_
  exact (Category.assoc _ _ _).symm

lemma modulePowMap_unitPower (f : structureSheaf X ⟶ structureSheaf X) (n : ℕ) :
    modulePowMap f n ≫ (unitPowerIso n).hom =
      (unitPowerIso n).hom ≫ endPower f n := by
  induction n with
  | zero =>
    change 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X) = 𝟙 (structureSheaf X) ≫ 𝟙 (structureSheaf X)
    rfl
  | succ n hn =>
    change moduleTensorMap f (modulePowMap f n) ≫
      ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) =
        ((moduleTensorUnit _).hom ≫ (unitPowerIso n).hom) ≫ (f ≫ endPower f n)
    calc
      _ = moduleTensorMap f (modulePowMap f n) ≫
          moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [moduleTensorUnit_natural]
      _ = moduleTensorMap f ((unitPowerIso n).hom ≫ endPower f n) ≫
            (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.comp_id, hn]
      _ = moduleTensorMap (𝟙 (structureSheaf X)) (unitPowerIso n).hom ≫
          moduleTensorMap f (endPower f n) ≫ (moduleTensorUnit (structureSheaf X)).hom := by
        rw [← Category.assoc, ← moduleTensorMap_comp, Category.id_comp]
      _ = (moduleTensorUnit (modulePow X (structureSheaf X) n)).hom ≫
          (unitPowerIso n).hom ≫ (f ≫ endPower f n) := by
        rw [moduleTensorUnit_scalar, ← Category.assoc, moduleTensorUnit_natural,
          Category.assoc]
      _ = _ := by simp only [Category.assoc]

def globalPowerFrame {M : X.Modules} (e : M ≅ structureSheaf X) (n : ℕ) :
    modulePow X M n ≅ structureSheaf X :=
  (modulePowFunctor n).mapIso e ≪≫ unitPowerIso n

lemma powerSection_coefficient {M : X.Modules} (e : M ≅ structureSheaf X)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (globalPowerFrame e n) (powerSection s n) = coefficient e s ^ n := by
  change endValue ((unitPowerIso n).inv ≫ modulePowMap s n ≫
    (modulePowMap e.hom n ≫ (unitPowerIso n).hom)) = _
  erw [← Category.assoc (modulePowMap s n), ← modulePowMap_comp,
    modulePowMap_unitPower, Iso.inv_hom_id_assoc, endValue_endPower]
  rfl

lemma frameChange_globalPowerFrame {M : X.Modules}
    (e f : M ≅ structureSheaf X) (n : ℕ) :
    (frameChange (globalPowerFrame e n) (globalPowerFrame f n) : Γ(X,⊤)) =
      (frameChange e f : Γ(X,⊤)) ^ n := by
  have h := powerSection_coefficient f e.inv n
  exact h

end
end PiExponentSeshadri.Geometry

end OAI
end Source0007

section Source0008
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPowerRestriction.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace MonoidalCategory
open scoped AlgebraicGeometry
variable {X : Scheme}

def modulePowRestrict (U : X.Opens) (M : X.Modules) :
    ∀ n, (modulePow X M n).restrict U.ι ≅ modulePow U.toScheme (M.restrict U.ι) n
  | 0 => Scheme.Modules.restrictUnitIso U.ι
  | n + 1 => moduleTensorRestrict U M (modulePow X M n) ≪≫
      moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)

lemma modulePowRestrict_natural (U : X.Opens) {M N : X.Modules} (f : M ⟶ N) (n : ℕ) :
    (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) ≫
      (modulePowRestrict U N n).hom =
    (modulePowRestrict U M n).hom ≫
      modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n := by
  induction n with
  | zero =>
    change (Scheme.Modules.restrictFunctor U.ι).map (𝟙 (structureSheaf X)) ≫
      (Scheme.Modules.restrictUnitIso U.ι).hom =
      (Scheme.Modules.restrictUnitIso U.ι).hom ≫ 𝟙 _
    erw [(Scheme.Modules.restrictFunctor U.ι).map_id, Category.id_comp]
  | succ n hn =>
    change (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap f (modulePowMap f n)) ≫
      ((moduleTensorRestrict U N (modulePow X N n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U N n)).hom) =
      ((moduleTensorRestrict U M (modulePow X M n)).hom ≫
        (moduleTensorIso (Iso.refl _) (modulePowRestrict U M n)).hom) ≫
          moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map f)
            (modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n)
    simp only [moduleTensorIso_hom, Iso.refl_hom]
    rw [← Category.assoc, moduleTensorRestrict_natural, Category.assoc,
      ← moduleTensorMap_comp, Category.comp_id, hn]
    rw [Category.assoc, ← moduleTensorMap_comp, Category.id_comp]

lemma modulePowMap_restrict_isIso (U : X.Opens) {M N : X.Modules} (f : M ⟶ N)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map f)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n)) := by
  have h := modulePowRestrict_natural U f n
  have heq : (Scheme.Modules.restrictFunctor U.ι).map (modulePowMap f n) =
      (modulePowRestrict U M n).hom ≫
        modulePowMap ((Scheme.Modules.restrictFunctor U.ι).map f) n ≫
          (modulePowRestrict U N n).inv := by
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [heq]
  infer_instance

lemma powerSection_restrict_isIso (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] (n : ℕ) :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (powerSection s n)) := by
  let := modulePowMap_restrict_isIso U s n
  unfold powerSection
  rw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  infer_instance

lemma sectionOpen_le_powerSection {M : X.Modules} (s : structureSheaf X ⟶ M) (n : ℕ) :
    sectionOpen X s ≤ sectionOpen X (powerSection s n) := by
  refine iSup_le fun U => iSup_le fun hU => ?_
  let := hU
  exact le_iSup_of_le U (le_iSup_of_le (powerSection_restrict_isIso U s n) le_rfl)

end

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def powerRestrictionUnit (U : X.Opens) (n : ℕ) :
    structureSheaf U.toScheme ≅ structureSheaf U.toScheme :=
  (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
    (Scheme.Modules.restrictFunctor U.ι).mapIso (unitPowerIso n).symm ≪≫
      modulePowRestrict U (structureSheaf X) n ≪≫
        (modulePowFunctor n).mapIso (Scheme.Modules.restrictUnitIso U.ι) ≪≫
          unitPowerIso n

lemma restrictPowerSection_factor (U : X.Opens) {M : X.Modules}
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom =
      (powerRestrictionUnit U n).hom ≫
        powerSection (restrictSection U.ι s) n := by
  have hs : (Scheme.Modules.restrictUnitIso U.ι).hom ≫ restrictSection U.ι s =
      (Scheme.Modules.restrictFunctor U.ι).map s := by
    let F : X.Modules ⥤ U.toScheme.Modules := Scheme.Modules.restrictFunctor U.ι
    let e : F.obj (structureSheaf X) ≅ structureSheaf U.toScheme :=
      Scheme.Modules.restrictUnitIso U.ι
    exact e.hom_inv_id_assoc (F.map s)
  dsimp only [restrictSection, powerSection, powerRestrictionUnit, Iso.trans_hom,
    Iso.symm_hom, Functor.mapIso_hom, modulePowFunctor]
  erw [(Scheme.Modules.restrictFunctor U.ι).map_comp]
  repeat' erw [Category.assoc]
  erw [modulePowRestrict_natural]
  erw [Iso.hom_inv_id_assoc, ← modulePowMap_comp]
  erw [show (Scheme.Modules.restrictUnitIso U.ι).hom ≫
      ((Scheme.Modules.restrictUnitIso U.ι).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map s) =
        (Scheme.Modules.restrictFunctor U.ι).map s from hs]
  rfl

end PiExponentSeshadri.Geometry

end

end OAI
end Source0008

section Source0009
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/SectionPowerOpens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Frames
open CategoryTheory AlgebraicGeometry
lemma coefficient_precompose {X : Scheme} {M : X.Modules} (e : M ≅ O X)
    (a : O X ⟶ O X) (s : O X ⟶ M) :
    coefficient e (a ≫ s) = endValue a * coefficient e s := by
  change endValue ((a ≫ s) ≫ e.hom) = _
  rw [Category.assoc]
  exact endValue_comp a (s ≫ e.hom)
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
open PiExponentSeshadri.Frames
variable {X : Scheme}

def localPowerFrame (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme) (n : ℕ) :
    (modulePow X M n).restrict U.ι ≅ structureSheaf U.toScheme :=
  modulePowRestrict U M n ≪≫ globalPowerFrame e n

lemma local_powerSection_coefficient (U : X.Opens) {M : X.Modules}
    (e : M.restrict U.ι ≅ structureSheaf U.toScheme)
    (s : structureSheaf X ⟶ M) (n : ℕ) :
    coefficient (localPowerFrame U e n) (restrictSection U.ι (powerSection s n)) =
      endValue (powerRestrictionUnit U n).hom *
        coefficient e (restrictSection U.ι s) ^ n := by
  change coefficient (globalPowerFrame e n)
    (restrictSection U.ι (powerSection s n) ≫ (modulePowRestrict U M n).hom) = _
  calc
    _ = coefficient (globalPowerFrame e n)
        ((powerRestrictionUnit U n).hom ≫ powerSection (restrictSection U.ι s) n) :=
      congrArg (coefficient (globalPowerFrame e n)) (restrictPowerSection_factor U s n)
    _ = endValue (powerRestrictionUnit U n).hom *
        coefficient (globalPowerFrame e n) (powerSection (restrictSection U.ι s) n) :=
      coefficient_precompose _ _ _
    _ = _ := congrArg (endValue (powerRestrictionUnit U n).hom * ·)
      (powerSection_coefficient e _ n)

lemma local_powerSection_coefficient_unit (U : X.Opens) (n : ℕ) :
    IsUnit (endValue (powerRestrictionUnit U n).hom) := by
  have h : IsIso (powerRestrictionUnit U n).hom := inferInstance
  exact (end_isIso_iff (powerRestrictionUnit U n).hom).mp h

theorem LineBundle.sectionOpen_power (L : LineBundle X) (s : GlobalSections X L.sheaf)
    {n : ℕ} (hn : 0 < n) :
    sectionOpen X (powerSection s n) = sectionOpen X s := by
  have hlocal (U : X.Opens) (e : L.sheaf.restrict U.ι ≅ structureSheaf U.toScheme) :
      U.ι ⁻¹ᵁ sectionOpen X (powerSection s n) = U.ι ⁻¹ᵁ sectionOpen X s := by
    change U.ι ⁻¹ᵁ SectionOpens.isoOpen (powerSection s n) =
      U.ι ⁻¹ᵁ SectionOpens.isoOpen s
    calc
      _ = U.toScheme.basicOpen (coefficient (localPowerFrame U e n)
          (restrictSection U.ι (powerSection s n))) :=
        preimage_isoOpen (powerSection s n) U.ι (localPowerFrame U e n)
      _ = U.toScheme.basicOpen (endValue (powerRestrictionUnit U n).hom *
          coefficient e (restrictSection U.ι s) ^ n) :=
        congrArg U.toScheme.basicOpen (local_powerSection_coefficient U e s n)
      _ = U.toScheme.basicOpen (coefficient e (restrictSection U.ι s)) := by
        rw [Scheme.basicOpen_mul,
          Scheme.basicOpen_of_isUnit _ (local_powerSection_coefficient_unit U n),
          top_inf_eq]
        exact U.toScheme.basicOpen_pow (coefficient e (restrictSection U.ι s)) hn
      _ = _ := (preimage_isoOpen s U.ι e).symm
  ext x
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  have h := congrArg (fun V : U.toScheme.Opens => (⟨x, hxU⟩ : U.toScheme) ∈ V) (hlocal U e)
  exact Iff.of_eq h

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0009

section Source0010
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/IntegralLineSections.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable {X : Scheme}

lemma trivialModule_restriction_injective [IsIntegral X] (M : X.Modules)
    (e : M ≅ structureSheaf X) {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (M.presheaf.map i.op) := by
  intro s t h
  apply (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.toPresheaf X).mapIso e).app (Opposite.op V)).hom).injective
  have hn := e.hom.mapPresheaf.naturality i.op
  have heq := congrArg (fun a => e.hom.app U a) h
  have hh (a : Γ(M, V)) :
      e.hom.app U (M.presheaf.map i.op a) =
        X.presheaf.map i.op (e.hom.app V a) := by
    exact CategoryTheory.congr_fun hn a
  rw [hh, hh] at heq
  exact map_injective_of_isIntegral X i heq

theorem LineBundle.restriction_injective [IsIntegral X] (L : LineBundle X)
    {U V : X.Opens} (i : U ⟶ V) [Nonempty U] :
    Function.Injective (L.sheaf.presheaf.map i.op) := by
  intro s t h
  apply L.sheaf.isSheaf.section_ext
  intro x hx
  obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
  let f := T.ι
  let U' : T.toScheme.Opens := f ⁻¹ᵁ U
  let V' : T.toScheme.Opens := f ⁻¹ᵁ V
  have hU' : Nonempty U' := by
    obtain ⟨y, hyT, hyU⟩ := nonempty_preirreducible_inter T.isOpen U.isOpen
      ⟨x, hxT⟩ (by obtain ⟨u⟩ := ‹Nonempty U›; exact ⟨u.val, u.property⟩)
    exact ⟨⟨⟨y, hyT⟩, hyU⟩⟩
  have : Nonempty U' := hU'
  have : Nonempty T := ⟨⟨x, hxT⟩⟩
  let j : U' ⟶ V' := homOfLE (fun _ h => leOfHom i h)
  let W := f ''ᵁ V'
  have hWV : W ≤ V := f.image_preimage_le V
  refine ⟨W, hWV, ?_, ?_⟩
  · exact ⟨⟨x, hxT⟩, hx, rfl⟩
  · apply trivialModule_restriction_injective (L.sheaf.restrict f) e j
    change L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op s) =
      L.sheaf.presheaf.map ((f.opensFunctor.map j).op)
        (L.sheaf.presheaf.map (homOfLE hWV).op t)
    have hh := congrArg
      (fun a => L.sheaf.presheaf.map (homOfLE (f.image_preimage_le U)).op a) h
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp] at hh ⊢
    have eq : i.op ≫ (homOfLE (f.image_preimage_le U)).op =
        (homOfLE hWV).op ≫ (f.opensFunctor.map j).op := Subsingleton.elim _ _
    rw [eq] at hh
    simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using hh

theorem LineBundle.section_restriction_injective [IsIntegral X] (L : LineBundle X)
    (U : X.Opens) [Nonempty U] :
    Function.Injective (fun s : GlobalSections X L.sheaf => s.app U (1 : Γ(X, U))) := by
  intro s t h
  have natural (s : GlobalSections X L.sheaf) (V : X.Opens) :
      s.app V (1 : Γ(X, V)) = L.sheaf.presheaf.map
        (homOfLE (show V ≤ ⊤ from le_top)).op (s.app ⊤ (1 : Γ(X, ⊤))) := by
    have hs := CategoryTheory.congr_fun (s.mapPresheaf.naturality
      (homOfLE (show V ≤ ⊤ from le_top)).op) (1 : Γ(X, ⊤))
    change s.app V (X.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op 1) =
      L.sheaf.presheaf.map (homOfLE (show V ≤ ⊤ from le_top)).op
        (s.app ⊤ (1 : Γ(X, ⊤))) at hs
    simpa only [map_one, ConcreteCategory.comp_apply] using hs
  have ht : s.app ⊤ (1 : Γ(X, ⊤)) = t.app ⊤ (1 : Γ(X, ⊤)) := by
    apply L.restriction_injective (homOfLE (show U ≤ ⊤ from le_top))
    rw [← natural s U, ← natural t U]
    exact h
  ext V a
  change Γ(X, V) at a
  have hv : s.app V (1 : Γ(X, V)) = t.app V (1 : Γ(X, V)) := by
    rw [natural s, natural t, ht]
  have scalar (s : GlobalSections X L.sheaf) :
      s.app V a = a • s.app V (1 : Γ(X, V)) := by
    have hs := s.app_smul (r := a) (x := (1 : Γ(X, V)))
    change s.app V (a * 1 : Γ(X, V)) = _ at hs
    simpa only [mul_one] using hs
  rw [scalar s, scalar t, hv]

variable [IsIntegral X]

theorem LineBundle.noZeroSMulDivisors (L : LineBundle X)
    (U : X.Opens) [Nonempty U] : NoZeroSMulDivisors Γ(X, U) Γ(L.sheaf, U) where
  eq_zero_or_eq_zero_of_smul_eq_zero {a m} h := by
    obtain ⟨x, hx⟩ := ‹Nonempty U›
    obtain ⟨T, hxT, ⟨e⟩⟩ := L.locallyRankOne x
    let V : T.toScheme.Opens := T.ι ⁻¹ᵁ U
    have : Nonempty V := ⟨⟨⟨x, hxT⟩, hx⟩⟩
    have : Nonempty T := ⟨⟨x, hxT⟩⟩
    let W : X.Opens := T.ι ''ᵁ V
    have : Nonempty W := ⟨⟨x, ⟨x, hxT⟩, hx, rfl⟩⟩
    let i : W ⟶ U := homOfLE (T.ι.image_preimage_le U)
    let ar : Γ(X, W) := X.presheaf.map i.op a
    let mr : Γ(L.sheaf, W) := L.sheaf.presheaf.map i.op m
    have hr : ar • mr = 0 := by
      have hh := congrArg (fun z => L.sheaf.presheaf.map i.op z) h
      simpa only [L.sheaf.map_smul, map_zero] using hh
    let ar' : Γ(T.toScheme, V) := (T.ι.appIso V).hom ar
    let mr' : Γ(L.sheaf.restrict T.ι, V) := (L.sheaf.restrictAppIso T.ι V).inv mr
    let cr : Γ(T.toScheme, V) := e.hom.app V mr'
    have hr' : ar' • mr' = 0 := by
      rw [← Scheme.Modules.smul_restrictAppIso_inv_apply]
      simp only [hr, map_zero]
    have hmul : ar' * cr = 0 := by
      have hh := e.hom.app_smul (r := ar') (x := mr')
      change e.hom.app V (ar' • mr') = ar' * cr at hh
      rw [hr', map_zero] at hh
      exact hh.symm
    rcases mul_eq_zero.mp hmul with ha | hm
    · left
      apply map_injective_of_isIntegral X i
      have hinj := (ConcreteCategory.bijective_of_isIso (T.ι.appIso V).hom).injective
      apply hinj
      simpa only [map_zero] using ha
    · right
      apply L.restriction_injective i
      have hinj := (ConcreteCategory.bijective_of_isIso
        (((Scheme.Modules.toPresheaf T.toScheme).mapIso e).app (Opposite.op V)).hom).injective
      apply (ConcreteCategory.bijective_of_isIso (L.sheaf.restrictAppIso T.ι V).inv).injective
      apply hinj
      change cr = e.hom.app V ((L.sheaf.restrictAppIso T.ι V).inv
        (L.sheaf.presheaf.map i.op 0))
      refine hm.trans ?_
      simp only [map_zero]
      rfl

theorem LineBundle.mono_section (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) : Mono s := by
  have hmono : Mono s.val := by
    apply PresheafOfModules.mono_of_injective
    intro U
    by_cases hU : Nonempty U.unop
    · let := hU
      let := L.noZeroSMulDivisors U.unop
      intro a b hab
      change Γ(X, U.unop) at a b
      have hc : s.app U.unop (1 : Γ(X, U.unop)) ≠ 0 := by
        intro h
        apply hs
        apply L.section_restriction_injective U.unop
        exact h
      have hscalar (a : Γ(X, U.unop)) : s.app U.unop a =
          a • s.app U.unop (1 : Γ(X, U.unop)) := by
        have hh := s.app_smul (r := a) (x := (1 : Γ(X, U.unop)))
        change s.app U.unop (a * 1 : Γ(X, U.unop)) = _ at hh
        simpa only [mul_one] using hh
      have heq : s.app U.unop a = s.app U.unop b := hab
      rw [hscalar a, hscalar b] at heq
      exact (smul_left_injective Γ(X, U.unop) hc) heq
    · have he : U.unop = ⊥ := by
        apply Opens.ext
        ext x
        exact ⟨fun hx => (hU ⟨⟨x, hx⟩⟩).elim, fun h => h.elim⟩
      have : Subsingleton Γ(X, U.unop) := by rw [he]; infer_instance
      intro a b _
      change Γ(X, U.unop) at a b
      exact Subsingleton.elim a b
  exact (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map hmono

end Geometry

namespace Frames
open CategoryTheory AlgebraicGeometry
variable {X Y : Scheme}
lemma coefficient_injective {M : X.Modules} (e : M ≅ O X) :
    Function.Injective (coefficient e) := by
  intro s t h
  apply (cancel_mono e.hom).1
  exact endValue_injective h
lemma coefficient_zero {M : X.Modules} (e : M ≅ O X) :
    coefficient e (0 : O X ⟶ M) = 0 := by
  rw [coefficient, CategoryTheory.Limits.zero_comp]
  rfl
lemma restrictSection_zero (φ : Y ⟶ X) [IsOpenImmersion φ] {M : X.Modules} :
    restrictSection φ (0 : O X ⟶ M) = 0 := by
  ext U a
  rfl
end Frames

namespace Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y : Scheme}
lemma LineBundle.restrict_sections_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y] :
    Function.Injective (fun s : GlobalSections X L.sheaf =>
      (Scheme.Modules.restrictFunctor f).map s) := by
  intro s t h
  let U : X.Opens := f ''ᵁ ⊤
  have : Nonempty U := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨f y, y, Set.mem_univ y, rfl⟩⟩
  apply L.section_restriction_injective U
  have he := congrArg (fun s : (structureSheaf X).restrict f ⟶ L.sheaf.restrict f =>
    s.app ⊤ (1 : Γ(X, U))) h
  exact he

lemma LineBundle.restricted_coefficient_injective [IsIntegral X] (L : LineBundle X)
    (f : Y ⟶ X) [IsOpenImmersion f] [Nonempty Y]
    (e : L.sheaf.restrict f ≅ O Y) :
    Function.Injective (fun s : GlobalSections X L.sheaf => coefficient e (restrictSection f s)) := by
  intro s t h
  apply L.restrict_sections_injective f
  let u : (structureSheaf X).restrict f ≅ structureSheaf Y :=
    Scheme.Modules.restrictUnitIso f
  apply (cancel_epi u.inv).mp
  exact coefficient_injective e h

lemma LineBundle.isoOpen_ne_bot [IsIntegral X] (L : LineBundle X)
    (s : O X ⟶ L.sheaf) (hs : s ≠ 0) : PiExponentSeshadri.SectionOpens.isoOpen s ≠ ⊥ := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  obtain ⟨V,hx,⟨e⟩⟩ := L.locallyRankOne x
  let : Nonempty V := ⟨⟨x,hx⟩⟩
  have hc : coefficient e (restrictSection V.ι s) ≠ 0 := by
    intro h
    apply hs
    apply L.restricted_coefficient_injective V.ι e
    have hz : coefficient e (restrictSection V.ι (0 : O X ⟶ L.sheaf)) = 0 :=
      (congrArg (coefficient e) (restrictSection_zero V.ι)).trans (coefficient_zero e)
    exact h.trans hz.symm
  intro hz
  have he := preimage_isoOpen s V.ι e
  rw [hz] at he
  have hb : V.toScheme.basicOpen (coefficient e (restrictSection V.ι s)) = ⊥ := by
    simpa only [Scheme.Hom.preimage_bot] using he.symm
  exact hc (eq_zero_of_basicOpen_eq_bot _ hb)

theorem LineBundle.sectionOpen_nonempty [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) :
    Nonempty (sectionOpen X s) := by
  have h := L.isoOpen_ne_bot s hs
  by_contra hn
  apply h
  apply TopologicalSpace.Opens.ext
  ext x
  exact ⟨fun hx => hn ⟨⟨x,hx⟩⟩, fun hx => hx.elim⟩
end Geometry

end PiExponentSeshadri

end

end OAI
end Source0010

section Source0011
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorPure.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
Expose private helpers and adjust helper names where needed for module compatibility.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry
open MonoidalCategory

variable {X Y : Scheme.{0}}

local instance sectionModule {X : Scheme.{0}}
    (P : PresheafOfModules X.ringCatSheaf.obj) (U : X.Opens) :
    Module Γ(X, U) (P.obj (op U)) := (P.obj (op U)).isModule

abbrev presheaf (M N : X.Modules) :=
  PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val

abbrev adj (X : Scheme.{0}) :=
  PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 X.ringCatSheaf.obj)

def pure (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.obj (op U) :=
  (((adj X).unit.app (presheaf M N)).app (op U)).hom (m ⊗ₜ[Γ(X,U)] n)

@[simp] lemma pure_add_left (M N : X.Modules) (U : X.Opens) (m m' : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (m+m') n = pure M N U m n + pure M N U m' n := by
  unfold pure
  rw [TensorProduct.add_tmul]
  exact map_add _ _ _

@[simp] lemma pure_add_right (M N : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (n n' : N.val.obj (op U)) :
    pure M N U m (n+n') = pure M N U m n + pure M N U m n' := by
  unfold pure
  rw [TensorProduct.tmul_add]
  exact map_add _ _ _

@[simp] lemma pure_smul_left (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U (a • m) n = a • pure M N U m n := by
  unfold pure
  rw [← TensorProduct.smul_tmul']
  exact map_smul _ _ _

@[simp] lemma pure_smul_right (M N : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    pure M N U m (a • n) = a • pure M N U m n := by
  simp only [pure]
  rw [TensorProduct.tmul_smul]
  exact map_smul _ _ _

lemma pure_restrict (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensor X M N).val.map i.op (pure M N U m n) =
      pure M N V (M.val.map i.op m) (N.val.map i.op n) := by
  exact (PresheafOfModules.naturality_apply ((adj X).unit.app (presheaf M N)) i.op
    (m ⊗ₜ[Γ(X,U)] n)).symm

lemma map_pure {M N P Q : X.Modules} (f : M ⟶ P) (g : N ⟶ Q)
    (U : X.Opens) (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorMap f g).app U (pure M N U m n) =
      pure P Q U (f.app U m) (g.app U n) := by
  have h := (adj X).unit.naturality
    (PresheafOfModulesOfCommRing.Monoidal.tensorHom (R := X.presheaf) f.val g.val)
  exact (congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] n)) h).symm

lemma hom_ext {M N P : X.Modules} {f g : moduleTensor X M N ⟶ P}
    (h : ∀ U m n, f.app U (pure M N U m n) = g.app U (pure M N U m n)) : f = g := by
  apply ((adj X).homEquiv (presheaf M N) P).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  exact h U.unop m n

lemma sheafify_restrict_unit (f : X ⟶ Y) [IsOpenImmersion f]
    (P : PresheafOfModules Y.ringCatSheaf.obj) :
    (modulePresheafRestrict f).map ((adj Y).unit.app P) ≫
      ((moduleSheafificationRestrict f).hom.app P).val =
    (adj X).unit.app ((modulePresheafRestrict f).obj P) := by
  let a := adj Y
  let b := Scheme.Modules.restrictAdjunction f
  let c := modulePresheafRestrictAdjunction f
  let d := adj X
  apply (c.homEquiv _ _).injective
  erw [Adjunction.homEquiv_unit,Functor.map_comp]
  have hn := c.unit_naturality (a.unit.app P)
  rw [← Category.assoc,hn]
  have he := Adjunction.unit_leftAdjointUniq_hom_app (a.comp b) (c.comp d) P
  have ha := a.comp_unit_app b P
  have hd := c.comp_unit_app d P
  let G : Y.Modules ⥤ PresheafOfModules Y.ringCatSheaf.obj :=
    SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)
  let I : X.Modules ⥤ Y.Modules := Scheme.Modules.pushforward f
  have hh := congrArg (fun h => h ≫ (I ⋙ G).map
    (((a.comp b).leftAdjointUniq (c.comp d)).hom.app P)) ha
  exact hh.symm.trans (he.trans hd)

lemma presheaf_restrict_pure (U : X.Opens) (M N : X.Modules)
    (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    ((modulePresheafTensorRestrict U M.val N.val).hom.app (op V)).hom
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n) = (show ((modulePresheafRestrict U.ι).obj M.val).obj (op V) from m) ⊗ₜ[Γ(U.toScheme,V)]
      (show ((modulePresheafRestrict U.ι).obj N.val).obj (op V) from n) := by
  rfl

lemma restrict_pure (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n) =
      pure (M.restrict U.ι) (N.restrict U.ι) V m n := by
  have h := sheafify_restrict_unit U.ι (presheaf M N)
  have h' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) h
  have hn := (adj U.toScheme).unit.naturality
    (modulePresheafTensorRestrict U M.val N.val).hom
  have hn' := congrArg (fun q => q.app (op V) (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) hn
  change (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
    (modulePresheafTensorRestrict U M.val N.val).hom).val.app (op V))
    (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V)
      (pure M N (U.ι ''ᵁ V) m n)) = _
  simp only [PresheafOfModules.comp_app] at h' hn'
  change (((moduleSheafificationRestrict U.ι).hom.app (presheaf M N)).val.app (op V))
    (pure M N (U.ι ''ᵁ V) m n) = _ at h'
  rw [h']
  refine hn'.symm.trans ?_
  change (((adj U.toScheme).unit.app (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V))
    (((modulePresheafTensorRestrict U M.val N.val).hom.app (op V))
      (m ⊗ₜ[Γ(X,U.ι ''ᵁ V)] n)) = _
  exact congrArg (fun t => (((adj U.toScheme).unit.app
    (presheaf (M.restrict U.ι) (N.restrict U.ι))).app (op V)) t)
      (presheaf_restrict_pure U M N V m n)

lemma restrict_pure_inv (U : X.Opens) (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (U.ι ''ᵁ V))) (n : N.val.obj (op (U.ι ''ᵁ V))) :
    (moduleTensorRestrict U M N).inv.app V (pure (M.restrict U.ι) (N.restrict U.ι) V m n) =
      pure M N (U.ι ''ᵁ V) m n := by
  have h := congrArg (fun t => (moduleTensorRestrict U M N).inv.app V t)
    (restrict_pure U M N V m n).symm
  refine h.trans ?_
  exact congrArg (fun q => q.app V (pure M N (U.ι ''ᵁ V) m n))
    (moduleTensorRestrict U M N).hom_inv_id

lemma restrict_hom_ext (U : X.Opens) {M N : X.Modules} {P : U.toScheme.Modules}
    {f g : (moduleTensor X M N).restrict U.ι ⟶ P}
    (h : ∀ (V : U.toScheme.Opens) (m : M.val.obj (op (U.ι ''ᵁ V)))
      (n : N.val.obj (op (U.ι ''ᵁ V))), f.app V (pure M N (U.ι ''ᵁ V) m n) =
      g.app V (pure M N (U.ι ''ᵁ V) m n)) : f = g := by
  apply (cancel_epi (moduleTensorRestrict U M N).inv).mp
  apply hom_ext (M := M.restrict U.ι) (N := N.restrict U.ι)
  intro V m n
  change f.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n)) =
    g.app V ((moduleTensorRestrict U M N).inv.app V (pure _ _ V m n))
  exact (congrArg (fun x => f.app V x) (restrict_pure_inv U M N V m n)).trans
    ((h V m n).trans (congrArg (fun x => g.app V x) (restrict_pure_inv U M N V m n)).symm)

lemma restrict_map (U : X.Opens) {M N P Q : X.Modules}
    (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap a b) ≫
      (moduleTensorRestrict U P Q).hom =
    (moduleTensorRestrict U M N).hom ≫
      moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) := by
  apply restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict U P Q).hom.app V
    ((moduleTensorMap a b).app (U.ι ''ᵁ V) (pure M N (U.ι ''ᵁ V) m n)) =
    (moduleTensorMap _ _).app V ((moduleTensorRestrict U M N).hom.app V
      (pure M N (U.ι ''ᵁ V) m n))
  exact (congrArg (fun x => (moduleTensorRestrict U P Q).hom.app V x)
    (map_pure a b (U.ι ''ᵁ V) m n)).trans
    ((restrict_pure U P Q V (a.app (U.ι ''ᵁ V) m) (b.app (U.ι ''ᵁ V) n)).trans
      ((map_pure ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) V m n).symm.trans
        (congrArg (fun x => (moduleTensorMap ((Scheme.Modules.restrictFunctor U.ι).map a)
          ((Scheme.Modules.restrictFunctor U.ι).map b)).app V x)
          (restrict_pure U M N V m n)).symm))

lemma unit_pure (M : X.Modules) (U : X.Opens) (a : Γ(X,U)) (m : M.val.obj (op U)) :
    (moduleTensorUnit M).hom.app U (pure (structureSheaf X) M U a m) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (λ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorUnit M).hom = (λ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (a ⊗ₜ[Γ(X,U)] m)) h

lemma right_unit_pure (M : X.Modules) (U : X.Opens) (m : M.val.obj (op U)) (a : Γ(X,U)) :
    (moduleTensorRightUnit M).hom.app U (pure M (structureSheaf X) U m a) = a • m := by
  let : MonoidalCategory (PresheafOfModules X.ringCatSheaf.obj) :=
    PresheafOfModulesOfCommRing.monoidalCategory (R := X.presheaf)
  have h := ((adj X).homEquiv _ _).apply_symm_apply (ρ_ M.val).hom
  change (adj X).homEquiv _ M (moduleTensorRightUnit M).hom = (ρ_ M.val).hom at h
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(X,U)] a)) h

end PiExponentSeshadri.TensorPure

end

end OAI
end Source0011

section Source0012
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/FrameSubopens.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Frames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
variable {X : Scheme} {M : X.Modules}

def restrictOpenFrame {U V : X.Opens} (h : V ≤ U) (e : M.restrict U.ι ≅ O U.toScheme) :
    M.restrict V.ι ≅ O V.toScheme :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) U.ι).app M ≪≫
      restrictFrame (X.homOfLE h) e

lemma restrictOpenFrame_coefficient_global {U V : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ O U.toScheme) (s : O X ⟶ M) :
    coefficient (restrictOpenFrame h e) (restrictSection V.ι s) =
      (X.homOfLE h).appTop (coefficient e (restrictSection U.ι s)) := by
  unfold restrictOpenFrame
  rw [coefficient_transport]
  rw [← restrictSection_congr (X.homOfLE_ι h) s, Category.assoc]
  have he : (Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).hom.app M ≫
      ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm.hom = 𝟙 _ :=
    Iso.hom_inv_id ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M)
  rw [he, Category.comp_id]
  exact coefficient_restrict_comp (X.homOfLE h) U.ι e s

lemma frameChange_restrictOpenFrame {U V W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V)
    (e : M.restrict U.ι ≅ O U.toScheme) (f : M.restrict V.ι ≅ O V.toScheme)
    (s : O X ⟶ M) (hs : coefficient e (restrictSection U.ι s) = 1) :
    (frameChange (restrictOpenFrame hWU e) (restrictOpenFrame hWV f) : Γ(W.toScheme,⊤)) =
      (X.homOfLE hWV).appTop (coefficient f (restrictSection V.ι s)) := by
  have h := coefficient_change (restrictOpenFrame hWU e) (restrictOpenFrame hWV f)
    (restrictSection W.ι s)
  rw [restrictOpenFrame_coefficient_global, restrictOpenFrame_coefficient_global,
    hs, map_one, mul_one] at h
  exact h.symm

end
end PiExponentSeshadri.Frames

end OAI
end Source0012

section Source0013
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullback.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X Y : Scheme.{0}}

instance opensMap_final (f : Y ⟶ X) : (Opens.map f.base).Final := by
  let : PreservesLimit (Functor.empty.{0} X.Opens) (Opens.map f.base) := by
    apply preservesLimit_of_preserves_limit_cone (isTerminalTop (α := X.Opens))
    exact (isLimitMapConeEmptyConeEquiv (Opens.map f.base) (⊤ : X.Opens)).symm isTerminalTop
  infer_instance

def pullbackRestrictIso (f : Y ⟶ X) (L : X.Modules) (U : X.Opens) :
    ((Scheme.Modules.pullback f).obj L).restrict (f ⁻¹ᵁ U).ι ≅
      (Scheme.Modules.pullback (f ∣_ U)).obj (L.restrict U.ι) :=
  (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app _ ≪≫
  (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
  (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
  ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
  (Scheme.Modules.pullback (f ∣_ U)).mapIso
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm

def LineBundle.pullback (L : LineBundle X) (f : Y ⟶ X) : LineBundle Y where
  sheaf := (Scheme.Modules.pullback f).obj L.sheaf
  locallyRankOne y := by
    obtain ⟨U,hy,⟨e⟩⟩ := L.locallyRankOne (f y)
    refine ⟨f ⁻¹ᵁ U,hy,⟨pullbackRestrictIso f L.sheaf U ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso e ≪≫ ?_⟩⟩
    letI : (Opens.map (f ∣_ U).base).Final := opensMap_final (f ∣_ U)
    letI : (SheafOfModules.pushforward (f ∣_ U).toRingCatSheafHom).IsRightAdjoint :=
      inferInstanceAs (Scheme.Modules.pushforward (f ∣_ U)).IsRightAdjoint
    let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) :=
      SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal (f ∣_ U).toRingCatSheafHom
    let a : (SheafOfModules.pullback (f ∣_ U).toRingCatSheafHom).obj
        (SheafOfModules.unit U.toScheme.ringCatSheaf) ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf :=
      @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (f ∣_ U).toRingCatSheafHom) hu
    exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

end
end PiExponentSeshadri.Geometry

end OAI
end Source0013

section Source0014
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/PushforwardTensor.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace PushforwardTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

def presheafHom (M N : X.Modules) :
    presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      ((Scheme.Modules.pushforward f).obj (moduleTensor X M N)).val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun m n => pure M N (f ⁻¹ᵁ U.unop) m n)
    (fun m m' n => pure_add_left M N _ m m' n)
    (fun a m n => pure_smul_left M N _ ((f.app U.unop).hom a) m n)
    (fun m n n' => pure_add_right M N _ m n n')
    (fun a m n => pure_smul_right M N _ ((f.app U.unop).hom a) m n)
  naturality {U V} i := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact (pure_restrict M N ((Opens.map f.base).map i.unop) m n).symm

def hom (M N : X.Modules) :
    moduleTensor Y ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj (moduleTensor X M N) :=
  ((adj Y).homEquiv _ _).symm (presheafHom f M N)

lemma hom_pure (M N : X.Modules) (U : Y.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ U))) (n : N.val.obj (op (f ⁻¹ᵁ U))) :
    (hom f M N).app U
      (pure ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N) U m n) =
      pure M N (f ⁻¹ᵁ U) m n := by
  have h := ((adj Y).homEquiv
    (presheaf ((Scheme.Modules.pushforward f).obj M) ((Scheme.Modules.pushforward f).obj N))
    ((Scheme.Modules.pushforward f).obj (moduleTensor X M N))).apply_symm_apply (presheafHom f M N)
  exact congrArg (fun q => q.app (op U) (m ⊗ₜ[Γ(Y,U)] n)) h

@[reassoc] lemma naturality {M N P Q : X.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    moduleTensorMap ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
      hom f P Q = hom f M N ≫ (Scheme.Modules.pushforward f).map (moduleTensorMap a b) := by
  apply TensorPure.hom_ext
  intro U m n
  change (hom f P Q).app U ((moduleTensorMap _ _).app U (pure _ _ U m n)) =
    (moduleTensorMap a b).app (f ⁻¹ᵁ U) ((hom f M N).app U (pure _ _ U m n))
  have h₁ := TensorPure.map_pure ((Scheme.Modules.pushforward f).map a)
    ((Scheme.Modules.pushforward f).map b) U m n
  have h₂ := hom_pure f P Q U (a.app (f ⁻¹ᵁ U) m) (b.app (f ⁻¹ᵁ U) n)
  have h₃ := hom_pure f M N U m n
  have h₄ := TensorPure.map_pure a b (f ⁻¹ᵁ U) m n
  exact ((congrArg (fun z => (hom f P Q).app U z) h₁).trans h₂).trans
    ((congrArg (fun z => (moduleTensorMap a b).app (f ⁻¹ᵁ U) z) h₃).trans h₄).symm

end PushforwardTensor

namespace Geometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Frames
variable {X Y Z : Scheme.{0}}

def pullbackUnitIso (f : Y ⟶ X) : (Scheme.Modules.pullback f).obj (O X) ≅ O Y := by
  letI : (Opens.map f.base).Final := opensMap_final f
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  let hu : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) :=
    SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal f.toRingCatSheafHom
  let a : (SheafOfModules.pullback f.toRingCatSheafHom).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅ SheafOfModules.unit Y.ringCatSheaf :=
    @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) hu
  exact { hom := a.hom, inv := a.inv, hom_inv_id := a.hom_inv_id, inv_hom_id := a.inv_hom_id }

def pullbackSection (f : Y ⟶ X) {M : X.Modules} (s : O X ⟶ M) :
    O Y ⟶ (Scheme.Modules.pullback f).obj M :=
  (pullbackUnitIso f).inv ≫ (Scheme.Modules.pullback f).map s

def pullbackFrame (f : Y ⟶ X) {M : X.Modules} (e : M ≅ O X) :
    (Scheme.Modules.pullback f).obj M ≅ O Y :=
  (Scheme.Modules.pullback f).mapIso e ≪≫ pullbackUnitIso f

lemma pullbackUnit_adjunction (f : Y ⟶ X) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    inferInstanceAs (Scheme.Modules.pushforward f).IsRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom).homEquiv _ _
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

end Geometry

end PiExponentSeshadri

end

end OAI
end Source0014

section Source0015
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorOpenBaseChange.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.OpenBaseChange

section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def leftSquare :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  (conjugateIsoEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).symm (rightSquare f U)

lemma unit_compatibility (M : Y.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (iso f U ((Scheme.Modules.pullback f).obj M)).hom =
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M) := by
  let a := Scheme.Modules.pullbackPushforwardAdjunction f
  let b := Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι
  let c := Scheme.Modules.restrictAdjunction U.ι
  let d := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  have h := unit_conjugateEquiv_symm (a.comp b) (c.comp d) (rightSquare f U).hom M
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  change (a.unit.app M ≫ (Scheme.Modules.pushforward f).map
    (b.unit.app ((Scheme.Modules.pullback f).obj M))) ≫
      (rightSquare f U).hom.app _ =
    (c.unit.app M ≫ (Scheme.Modules.pushforward U.ι).map
      (d.unit.app (M.restrict U.ι))) ≫
      (Scheme.Modules.pushforward U.ι).map
        ((Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M)) at h
  have hc := congrArg (fun q => (Scheme.Modules.restrictFunctor U.ι).map q ≫
    c.counit.app ((Scheme.Modules.pushforward (f ∣_ U)).obj
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι))) h
  simp only [Functor.map_comp, Category.assoc] at hc
  change _ = _ at hc
  have hn := c.counit.naturality
    (d.unit.app (M.restrict U.ι) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((leftSquare f U).hom.app M))
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [Functor.map_comp, Functor.map_comp] at hn
  rw [Category.assoc] at hn
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [hn] at hc
  simp only [← Category.assoc] at hc
  have ht := c.left_triangle_components M
  change (Scheme.Modules.restrictFunctor U.ι).map (c.unit.app M) ≫
    c.counit.app (M.restrict U.ι) = 𝟙 _ at ht
  rw [ht, Category.id_comp] at hc
  simpa only [a, b, c, d, iso, asIso_hom, hom, Category.assoc] using hc

end

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

lemma modules_comp_app {Z : Scheme.{0}} {M N P : Z.Modules} (a : M ⟶ N) (b : N ⟶ P)
    (W : Z.Opens) : (a ≫ b).app W = a.app W ≫ b.app W := rfl

lemma hom_app (M : X.Modules) (V : U.toScheme.Opens) :
    (hom f U M).app V = M.presheaf.map
      (eqToHom (image_morphismRestrict_preimage f U V)).op := by
  change ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).unit.app M).app
    (f ⁻¹ᵁ (U.ι ''ᵁ V)) ≫
      ((rightSquare f U).hom.app (M.restrict (f ⁻¹ᵁ U).ι)).app (U.ι ''ᵁ V) ≫
      ((Scheme.Modules.restrictAdjunction U.ι).counit.app
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (M.restrict (f ⁻¹ᵁ U).ι))).app V = _
  simp only [rightSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app]
  simp only [modules_comp_app,Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.restrict_map]
  erw [Category.id_comp, Category.comp_id, ← Functor.map_comp, ← Functor.map_comp]
  congr 1

lemma tensor_pure (M N : X.Modules) (V : U.toScheme.Opens)
    (m : M.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V))))
    (n : N.val.obj (op (f ⁻¹ᵁ (U.ι ''ᵁ V)))) :
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V
        (pure M N (f ⁻¹ᵁ (U.ι ''ᵁ V)) m n)) =
    pure (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U M).app V m) ((hom f U N).app V n) := by
  rw [hom_app, hom_app, hom_app]
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app _
    ((moduleTensor X M N).val.map _ (pure M N _ m n)) = _
  exact (congrArg (fun t => (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app
    ((f ∣_ U) ⁻¹ᵁ V) t) (pure_restrict M N
      (eqToHom (image_morphismRestrict_preimage f U V)) m n)).trans
    (restrict_pure (f ⁻¹ᵁ U) M N ((f ∣_ U) ⁻¹ᵁ V) _ _)

lemma tensor_square (M N : X.Modules) :
    (Scheme.Modules.restrictFunctor U.ι).map (PushforwardTensor.hom f M N) ≫
      (iso f U (moduleTensor X M N)).hom ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom =
    (moduleTensorRestrict U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)).hom ≫
      moduleTensorMap (iso f U M).hom (iso f U N).hom ≫
      PushforwardTensor.hom (f ∣_ U) (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) := by
  apply TensorPure.restrict_hom_ext U
  intro V m n
  change (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
    ((hom f U (moduleTensor X M N)).app V
      ((PushforwardTensor.hom f M N).app (U.ι ''ᵁ V)
        (pure _ _ (U.ι ''ᵁ V) m n))) =
    (PushforwardTensor.hom (f ∣_ U) _ _).app V
      ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V
        ((moduleTensorRestrict U _ _).hom.app V (pure _ _ (U.ι ''ᵁ V) m n)))
  have hA := congrArg (fun z =>
    (moduleTensorRestrict (f ⁻¹ᵁ U) M N).hom.app ((f ∣_ U) ⁻¹ᵁ V)
      ((hom f U (moduleTensor X M N)).app V z))
    (PushforwardTensor.hom_pure f M N (U.ι ''ᵁ V) m n)
  have hB := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V
    ((moduleTensorMap (iso f U M).hom (iso f U N).hom).app V z))
    (restrict_pure U ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N) V m n)
  have hC := congrArg (fun z => (PushforwardTensor.hom (f ∣_ U) _ _).app V z)
    (map_pure (iso f U M).hom (iso f U N).hom V m n)
  have hD := PushforwardTensor.hom_pure (f ∣_ U)
    (M.restrict (f ⁻¹ᵁ U).ι) (N.restrict (f ⁻¹ᵁ U).ι) V
      ((hom f U M).app V m) ((hom f U N).app V n)
  exact hA.trans ((tensor_pure f U M N V m n).trans ((hB.trans (hC.trans hD)).symm))

@[reassoc] lemma naturality {M N : X.Modules} (a : M ⟶ N) :
    (Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward f).map a) ≫
      (iso f U N).hom =
    (iso f U M).hom ≫ (Scheme.Modules.pushforward (f ∣_ U)).map
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map a) := by
  ext V x
  change (hom f U N).app V (a.app (f ⁻¹ᵁ (U.ι ''ᵁ V)) x) =
    a.app ((f ⁻¹ᵁ U).ι ''ᵁ ((f ∣_ U) ⁻¹ᵁ V)) ((hom f U M).app V x)
  rw [hom_app,hom_app]
  exact (CategoryTheory.congr_fun (a.mapPresheaf.naturality
    (eqToHom (image_morphismRestrict_preimage f U V)).op) x).symm

end PiExponentSeshadri.OpenBaseChange

end

end OAI
end Source0015

section Source0016
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/LinePullbackPowers.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.PullbackTensor
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MonoidalCategory
open PiExponentSeshadri.Geometry PiExponentSeshadri.TensorPure PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens)

def hom (M N : Y.Modules) : (Scheme.Modules.pullback f).obj (moduleTensor Y M N) ⟶
    moduleTensor X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _)

lemma unit_hom (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (moduleTensor Y M N) ≫
      (Scheme.Modules.pushforward f).map (hom f M N) =
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      PushforwardTensor.hom f _ _ :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).apply_symm_apply _

@[reassoc] lemma naturality {M N P Q : Y.Modules} (a : M ⟶ P) (b : N ⟶ Q) :
    (Scheme.Modules.pullback f).map (moduleTensorMap a b) ≫ hom f P Q =
      hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map a)
        ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left,Adjunction.homEquiv_naturality_right]
  simp only [hom,Equiv.apply_symm_apply]
  rw [← Category.assoc,← moduleTensorMap_comp]
  rw [Category.assoc,← PushforwardTensor.naturality,← Category.assoc,← moduleTensorMap_comp]
  rw [← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality,
    ← (Scheme.Modules.pullbackPushforwardAdjunction f).unit_naturality]

lemma unit_pure_structure (Z : Scheme.{0}) (U : Z.Opens)
    (a b : (O Z).val.obj (op U)) :
    (moduleTensorUnit (O Z)).hom.app U (pure (O Z) (O Z) U a b) =
      (show Γ(Z,U) from a) * (show Γ(Z,U) from b) :=
  TensorPure.unit_pure (O Z) U a b

lemma unit_compatibility :
    hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom =
    (Scheme.Modules.pullback f).map (moduleTensorUnit (O Y)).hom ≫
      (pullbackUnitIso f).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  let adj := Scheme.Modules.pullbackPushforwardAdjunction f
  have hl := adj.homEquiv_naturality_left (moduleTensorUnit (O Y)).hom
    (pullbackUnitIso f).hom
  have hr := adj.homEquiv_naturality_right (hom f (O Y) (O Y))
    ((moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
  have hu := congrArg (fun q => (moduleTensorUnit (O Y)).hom ≫ q)
    (pullbackUnit_adjunction f)
  refine hr.trans (Eq.trans ?_ (hu.symm.trans hl.symm))
  simp only [adj, hom, Equiv.apply_symm_apply]
  apply TensorPure.hom_ext
  intro U a b
  change (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U ((moduleTensorMap _ _).app U
        (pure (O Y) (O Y) U a b)))) =
    (f.app U) ((moduleTensorUnit (O Y)).hom.app U (pure (O Y) (O Y) U a b))
  let η := (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)
  let m := η.app U a
  let n := η.app U b
  have h₁ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U)
      ((PushforwardTensor.hom f _ _).app U z)))
    (TensorPure.map_pure η η U a b)
  have h₂ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U)
    ((moduleTensorMap (pullbackUnitIso f).hom (pullbackUnitIso f).hom).app (f ⁻¹ᵁ U) z))
    (PushforwardTensor.hom_pure f ((Scheme.Modules.pullback f).obj (O Y))
      ((Scheme.Modules.pullback f).obj (O Y)) U m n)
  have h₃ := congrArg (fun z => (moduleTensorUnit (O X)).hom.app (f ⁻¹ᵁ U) z)
    (TensorPure.map_pure (pullbackUnitIso f).hom (pullbackUnitIso f).hom (f ⁻¹ᵁ U) m n)
  refine h₁.trans (h₂.trans (h₃.trans ((unit_pure_structure X (f ⁻¹ᵁ U) _ _).trans ?_)))
  have hy := congrArg (fun z => (f.app U) z) (unit_pure_structure Y U a b)
  refine Eq.trans ?_ hy.symm
  have hu := congrArg (fun q => q.app U) (pullbackUnit_adjunction f)
  have ha := congrArg (fun q => q a) hu
  have hb := congrArg (fun q => q b) hu
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U a) =
    (f.app U) a at ha
  change (pullbackUnitIso f).hom.app (f ⁻¹ᵁ U)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app (O Y)).app U b) =
    (f.app U) b at hb
  exact (congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ U) => a * b) ha hb).trans
    (map_mul (f.app U).hom (show Γ(Y,U) from a) (show Γ(Y,U) from b)).symm

instance unit_isIso : IsIso (hom f (O Y) (O Y)) := by
  let e := (Scheme.Modules.pullback f).mapIso (moduleTensorUnit (O Y)) ≪≫
    pullbackUnitIso f
  let d := moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f) ≪≫
    moduleTensorUnit (O X)
  have hi : IsIso (hom f (O Y) (O Y) ≫ d.hom) := by
    change IsIso (hom f (O Y) (O Y) ≫
      (moduleTensorIso (pullbackUnitIso f) (pullbackUnitIso f)).hom ≫
      (moduleTensorUnit (O X)).hom)
    rw [unit_compatibility]
    exact e.isIso_hom
  let hd : IsIso (C := X.Modules) d.hom := d.isIso_hom
  exact (@isIso_comp_right_iff X.Modules _ _ _ _ _ _ hd).mp hi

lemma open_transpose (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((OpenBaseChange.leftSquare f U).hom.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
        (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom :=
  (OpenBaseChange.unit_compatibility f U M).symm

lemma restrict_compatibility (M N : Y.Modules) :
    (OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f M N) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).hom =
    (Scheme.Modules.pullback (f ∣_ U)).map (moduleTensorRestrict U M N).hom ≫
      hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι) ≫
      moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app M)
        ((OpenBaseChange.leftSquare f U).hom.app N) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  conv_rhs => rw [Adjunction.homEquiv_naturality_left,
    Adjunction.homEquiv_naturality_right]
  conv_lhs => rw [Adjunction.homEquiv_naturality_right]
  rw [open_transpose]
  have ht : (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      (hom (f ∣_ U) (M.restrict U.ι) (N.restrict U.ι)) =
      moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
        ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫
        PushforwardTensor.hom (f ∣_ U) _ _ := Equiv.apply_symm_apply _ _
  rw [ht]
  simp only [Functor.map_comp, Category.assoc]
  rw [← OpenBaseChange.naturality_assoc]
  rw [← Functor.map_comp_assoc, unit_hom, Functor.map_comp]
  simp only [Category.assoc]
  rw [OpenBaseChange.tensor_square]
  rw [← Category.assoc]
  refine (congrArg (fun q => q ≫
    moduleTensorMap (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj M)).hom
      (OpenBaseChange.iso f U ((Scheme.Modules.pullback f).obj N)).hom ≫
    PushforwardTensor.hom (f ∣_ U)
      (((Scheme.Modules.pullback f).obj M).restrict (f ⁻¹ᵁ U).ι)
      (((Scheme.Modules.pullback f).obj N).restrict (f ⁻¹ᵁ U).ι))
    (TensorPure.restrict_map U
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))).trans ?_
  simp only [Category.assoc]
  rw [← moduleTensorMap_comp_assoc]
  rw [OpenBaseChange.unit_compatibility,OpenBaseChange.unit_compatibility]
  rw [moduleTensorMap_comp]
  simp only [Category.assoc]
  exact congrArg (fun q => (moduleTensorRestrict U M N).hom ≫
    moduleTensorMap ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (M.restrict U.ι))
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app (N.restrict U.ι)) ≫ q)
    (PushforwardTensor.naturality (f ∣_ U)
      ((OpenBaseChange.leftSquare f U).hom.app M) ((OpenBaseChange.leftSquare f U).hom.app N))

lemma framed_isIso (M N : Y.Modules) (e : M ≅ O Y) (d : N ≅ O Y) :
    IsIso (hom f M N) := by
  have h := naturality f e.hom d.hom
  have : IsIso ((Scheme.Modules.pullback f).map (moduleTensorMap e.hom d.hom) ≫
      hom f (O Y) (O Y)) := by
    change IsIso ((Scheme.Modules.pullback f).map (moduleTensorIso e d).hom ≫ _)
    infer_instance
  have : IsIso (moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := by
    change IsIso (moduleTensorIso ((Scheme.Modules.pullback f).mapIso e)
      ((Scheme.Modules.pullback f).mapIso d)).hom
    infer_instance
  have hi : IsIso (hom f M N ≫ moduleTensorMap ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map d.hom)) := h ▸ inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

instance power_step_isIso (L : LineBundle Y) (n : ℕ) :
    IsIso (hom f L.sheaf (L.pow n).sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U,hx,⟨e⟩⟩ := L.locallyRankOne (f x)
  let d := modulePowFrame U e n
  refine ⟨f ⁻¹ᵁ U,hx,?_⟩
  let : IsIso (hom (f ∣_ U) (L.sheaf.restrict U.ι) ((L.pow n).sheaf.restrict U.ι)) :=
    framed_isIso (f ∣_ U) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U).hom.app (L.pow n).sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U).app L.sheaf)
      ((OpenBaseChange.leftSquare f U).app (L.pow n).sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U L.sheaf (L.pow n).sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U).hom.app (moduleTensor Y L.sheaf (L.pow n).sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map
      (hom f L.sheaf (L.pow n).sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj (L.pow n).sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U).hom.app
      (moduleTensor Y L.sheaf (L.pow n).sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def powIso (L : LineBundle Y) : ∀ n : ℕ,
    (Scheme.Modules.pullback f).obj (L.pow n).sheaf ≅ ((L.pullback f).pow n).sheaf
  | 0 => pullbackUnitIso f
  | n+1 => @asIso _ _ _ _ (hom f L.sheaf (L.pow n).sheaf) (power_step_isIso f L n) ≪≫
      moduleTensorIso (Iso.refl _) (powIso L n)

end PiExponentSeshadri.PullbackTensor

end

end OAI
end Source0016

section Source0017
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/LineBundleProduct.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

theorem common_affine_frames (L M : LineBundle X) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) ∧
      Nonempty (M.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := L.locallyRankOne x
  obtain ⟨V, hxV, ⟨d⟩⟩ := M.locallyRankOne x
  obtain ⟨W, hW, hxW, hWUV⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ U ⊓ V from ⟨hxU, hxV⟩)
  exact ⟨⟨W, hW⟩, hxW,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).1) e⟩,
    ⟨restrictOpenFrame (fun _ hx => (hWUV hx).2) d⟩⟩

def LineBundle.tensor (L M : LineBundle X) : LineBundle X where
  sheaf := moduleTensor X L.sheaf M.sheaf
  locallyRankOne x := by
    obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M x
    exact ⟨U.1, hx, ⟨moduleTensorRestrict U.1 L.sheaf M.sheaf ≪≫
      moduleTensorIso e d ≪≫ moduleTensorUnit (structureSheaf U.1.toScheme)⟩⟩

end Geometry

namespace PullbackTensor
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X Y : Scheme.{0}} (f : X ⟶ Y)

instance line_isIso (L M : LineBundle Y) : IsIso (hom f L.sheaf M.sheaf) := by
  apply PiExponentSeshadri.SectionOpens.isIso_of_locally_isIso
  intro x
  obtain ⟨U, hx, ⟨e⟩, ⟨d⟩⟩ := common_affine_frames L M (f x)
  refine ⟨f ⁻¹ᵁ U.1, hx, ?_⟩
  have := framed_isIso (f ∣_ U.1) _ _ e d
  have : IsIso (moduleTensorMap ((OpenBaseChange.leftSquare f U.1).hom.app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).hom.app M.sheaf)) := by
    change IsIso (moduleTensorIso ((OpenBaseChange.leftSquare f U.1).app L.sheaf)
      ((OpenBaseChange.leftSquare f U.1).app M.sheaf)).hom
    infer_instance
  have h := restrict_compatibility f U.1 L.sheaf M.sheaf
  have : IsIso ((OpenBaseChange.leftSquare f U.1).hom.app (moduleTensor Y L.sheaf M.sheaf) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) := by rw [h]; infer_instance
  have hi : IsIso ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U.1).ι).map (hom f L.sheaf M.sheaf) ≫
      (moduleTensorRestrict (f ⁻¹ᵁ U.1) ((Scheme.Modules.pullback f).obj L.sheaf)
        ((Scheme.Modules.pullback f).obj M.sheaf)).hom) :=
    (isIso_comp_left_iff ((OpenBaseChange.leftSquare f U.1).hom.app
      (moduleTensor Y L.sheaf M.sheaf)) _).mp inferInstance
  exact (isIso_comp_right_iff _ _).mp hi

def iso (L M : LineBundle Y) :
    (Scheme.Modules.pullback f).obj (L.tensor M).sheaf ≅
      ((L.pullback f).tensor (M.pullback f)).sheaf :=
  @asIso _ _ _ _ (hom f L.sheaf M.sheaf) (line_isIso f L M)

end PullbackTensor

end PiExponentSeshadri

end

end OAI
end Source0017

section Source0018
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Approximation/TensorSectionOpen.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri

namespace Geometry
open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def tensorFrame (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (L.tensor M).sheaf.restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L.sheaf M.sheaf ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

end Geometry

namespace TensorPure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
variable {X : Scheme.{0}}

def tensorSection {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) :
    O X ⟶ moduleTensor X M N :=
  (moduleTensorUnit (O X)).inv ≫ moduleTensorMap s t

lemma section_apply {M N : X.Modules} (s : O X ⟶ M) (t : O X ⟶ N) (U : X.Opens) :
    (tensorSection s t).app U (1 : Γ(X,U)) = pure M N U (s.app U (1 : Γ(X,U))) (t.app U (1 : Γ(X,U))) := by
  have h : (moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U)) =
      pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U)) := by
    have he := unit_pure (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))
    have he : (moduleTensorUnit (O X)).hom.app U (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = (1 : Γ(X,U)) := by
      simp only [O, structureSheaf] at he
      exact he.trans (by change (1 : Γ(X,U)) * 1 = 1; exact one_mul _)
    have hi := congrArg ((moduleTensorUnit (O X)).inv.app U) he
    change ((moduleTensorUnit (O X)).hom ≫ (moduleTensorUnit (O X)).inv).app U
      (pure (O X) (O X) U (1 : Γ(X,U)) (1 : Γ(X,U))) = _ at hi
    rw [Iso.hom_inv_id] at hi
    exact hi.symm
  change (moduleTensorMap s t).app U ((moduleTensorUnit (O X)).inv.app U (1 : Γ(X,U))) = _
  rw [h]
  exact map_pure s t U (1 : Γ(X,U)) (1 : Γ(X,U))

lemma framed_pure {M N : X.Modules} (e : M ≅ O X) (d : N ≅ O X) (U : X.Opens)
    (m : M.val.obj (op U)) (n : N.val.obj (op U)) :
    (moduleTensorIso e d ≪≫ moduleTensorUnit (O X)).hom.app U (pure M N U m n) =
      (show Γ(X,U) from e.hom.app U m) * (show Γ(X,U) from d.hom.app U n) := by
  change (moduleTensorUnit (O X)).hom.app U ((moduleTensorMap e.hom d.hom).app U
    (pure M N U m n)) = _
  exact (congrArg ((moduleTensorUnit (O X)).hom.app U) (map_pure e.hom d.hom U m n)).trans
    (unit_pure (O X) U _ _)

lemma local_framed_pure (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (V : U.toScheme.Opens) (m : L.sheaf.val.obj (op (U.ι ''ᵁ V)))
    (n : M.sheaf.val.obj (op (U.ι ''ᵁ V))) :
    (tensorFrame L M U e d).hom.app V (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n) =
      (show Γ(U.toScheme,V) from e.hom.app V m) * (show Γ(U.toScheme,V) from d.hom.app V n) := by
  change (moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V
    ((moduleTensorRestrict U L.sheaf M.sheaf).hom.app V
      (pure L.sheaf M.sheaf (U.ι ''ᵁ V) m n)) = _
  exact (congrArg ((moduleTensorIso e d ≪≫ moduleTensorUnit (O U.toScheme)).hom.app V)
    (restrict_pure U L.sheaf M.sheaf V m n)).trans (framed_pure e d V m n)

lemma local_section_coefficient (L M : LineBundle X) (U : X.Opens)
    (e : L.sheaf.restrict U.ι ≅ O U.toScheme) (d : M.sheaf.restrict U.ι ≅ O U.toScheme)
    (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    coefficient (tensorFrame L M U e d) (restrictSection U.ι (tensorSection s t)) =
      coefficient e (restrictSection U.ι s) * coefficient d (restrictSection U.ι t) := by
  change (tensorFrame L M U e d).hom.app ⊤
    ((tensorSection s t).app (U.ι ''ᵁ ⊤) ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))) =
    (show Γ(U.toScheme,⊤) from e.hom.app ⊤ (s.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤))))) *
    (show Γ(U.toScheme,⊤) from d.hom.app ⊤ (t.app (U.ι ''ᵁ ⊤)
      ((U.ι.appIso ⊤).inv (1 : Γ(U.toScheme,⊤)))))
  rw [map_one]
  exact (congrArg ((tensorFrame L M U e d).hom.app ⊤) (section_apply s t _)).trans
    (local_framed_pure L M U e d ⊤ _ _)

lemma section_open (L M : LineBundle X) (s : O X ⟶ L.sheaf) (t : O X ⟶ M.sheaf) :
    isoOpen (tensorSection s t) = isoOpen s ⊓ isoOpen t := by
  apply SetLike.coe_injective
  ext x
  obtain ⟨U,hx,⟨e⟩,⟨d⟩⟩ := common_affine_frames L M x
  have h : U.1.ι ⁻¹ᵁ isoOpen (tensorSection s t) =
      U.1.ι ⁻¹ᵁ (isoOpen s ⊓ isoOpen t) := by
    calc
      _ = U.1.toScheme.basicOpen (coefficient (tensorFrame L M U.1 e d)
          (restrictSection U.1.ι (tensorSection s t))) :=
        preimage_isoOpen (tensorSection s t) U.1.ι (tensorFrame L M U.1 e d)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s) *
          coefficient d (restrictSection U.1.ι t)) :=
        congrArg U.1.toScheme.basicOpen (local_section_coefficient L M U.1 e d s t)
      _ = U.1.toScheme.basicOpen (coefficient e (restrictSection U.1.ι s)) ⊓
          U.1.toScheme.basicOpen (coefficient d (restrictSection U.1.ι t)) :=
        U.1.toScheme.basicOpen_mul _ _
      _ = _ := congrArg₂ (· ⊓ ·) (preimage_isoOpen s U.1.ι e).symm
        (preimage_isoOpen t U.1.ι d).symm
  exact SetLike.ext_iff.mp h ⟨x,hx⟩

end TensorPure

end PiExponentSeshadri

end

end OAI
end Source0018

section Source0019
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CurveEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

noncomputable section

namespace PiExponentSeshadri.Geometry

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry
variable (X : Scheme)

def restrictScalar (U : X.Opens) : Γ(X, ⊤) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE le_top).op).hom

lemma restrictScalar_naturality {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, ⊤)) :
    X.presheaf.map i.op (restrictScalar X V r) = restrictScalar X U r := by
  change (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map i.op) r = _
  rw [← X.presheaf.map_comp]
  rfl

def sheafHomSMul {M N : X.Modules} (r : Γ(X, ⊤)) (f : M ⟶ N) : M ⟶ N where
  val := {
    app U := by
      letI : Module Γ(X, U.unop) (M.val.obj U) := (M.val.obj U).isModule
      letI : Module Γ(X, U.unop) (N.val.obj U) := (N.val.obj U).isModule
      let g : M.val.obj U →ₗ[Γ(X, U.unop)] N.val.obj U := (f.val.app U).hom
      exact ModuleCat.ofHom ((restrictScalar X U.unop r) • g)
    naturality {U V} g := by
      let : Module (X.presheaf.obj V) (N.presheaf.obj V) := (N.val.obj V).isModule
      ext m
      change restrictScalar X V.unop r • f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (restrictScalar X U.unop r • f.app U.unop m)
      have hn := CategoryTheory.congr_fun (f.mapPresheaf.naturality g) m
      change f.app V.unop (M.presheaf.map g m) =
        N.presheaf.map g (f.app U.unop m) at hn
      rw [hn]
      calc
        _ = X.presheaf.map g (restrictScalar X U.unop r) •
            N.presheaf.map g (f.app U.unop m) := by
              exact congrArg (fun a : X.presheaf.obj V =>
                a • N.presheaf.map g (f.app U.unop m))
                (restrictScalar_naturality X g.unop r).symm
        _ = _ := (N.map_smul g.unop (restrictScalar X U.unop r) (f.app U.unop m)).symm }

instance sheafHomModule (M N : X.Modules) : Module Γ(X, ⊤) (M ⟶ N) where
  smul := sheafHomSMul X
  one_smul f := by
    ext U m
    change restrictScalar X U 1 • f.app U m = f.app U m
    simp
  mul_smul r s f := by
    ext U m
    change restrictScalar X U (r * s) • f.app U m =
      restrictScalar X U r • (restrictScalar X U s • f.app U m)
    simp [mul_smul]
  smul_zero r := by
    ext U m
    change restrictScalar X U r • (0 : Γ(N, U)) = 0
    exact smul_zero _
  smul_add r f g := by
    ext U m
    change restrictScalar X U r • (f.app U m + g.app U m) =
      restrictScalar X U r • f.app U m + restrictScalar X U r • g.app U m
    exact smul_add _ _ _
  zero_smul f := by
    ext U m
    change restrictScalar X U 0 • f.app U m = 0
    simp
  add_smul r s f := by
    ext U m
    change restrictScalar X U (r + s) • f.app U m =
      restrictScalar X U r • f.app U m + restrictScalar X U s • f.app U m
    simp [add_smul]

instance sheafLinear : Linear Γ(X, ⊤) X.Modules where
  smul_comp M N P r f g := by
    ext U m
    change g.app U (restrictScalar X U r • f.app U m) =
      restrictScalar X U r • g.app U (f.app U m)
    exact g.app_smul _ _
  comp_smul M N P f r g := by
    ext U m
    rfl

end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped AlgebraicGeometry

variable {X : Scheme.{0}}

instance schemeHasExt : HasExt.{1} X.Modules := HasExt.standard X.Modules

def baseScalars (f : X ⟶ Spec (CommRingCat.of ℂ)) : ℂ →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom

abbrev complexSectionModule (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    Module ℂ (GlobalSections X M) :=
  Module.compHom _ (baseScalars f)

abbrev cohomology (M : X.Modules) (n : ℕ) : Type 1 :=
  Abelian.Ext.{1} (C := X.Modules) (structureSheaf X) M n

def cohomologyDimension (f : X ⟶ Spec (CommRingCat.of ℂ))
    (M : X.Modules) (n : ℕ) : ℕ :=
  letI : Module ℂ (cohomology M n) :=
    Module.compHom (cohomology M n) (baseScalars f)
  Module.finrank ℂ (cohomology M n)

def eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ)) (d : ℕ)
    (M : X.Modules) : ℤ :=
  ∑ n ∈ Finset.range (d + 1), (-1 : ℤ) ^ n * (cohomologyDimension f M n : ℤ)

end

open AlgebraicGeometry CategoryTheory TopologicalSpace Abelian Opposite
variable {X : Scheme}

def globalHomLinearEquiv (M : X.Modules) :
    GlobalSections X M ≃ₗ[Γ(X,⊤)] Γ(M,⊤) where
  toEquiv := FlasqueCohomology.globalHomEquiv X.ringCatSheaf M
  map_add' := by intro f g; rfl
  map_smul' := by
    intro r f
    change restrictScalar X ⊤ r • f.app ⊤ (1 : Γ(X,⊤)) = r • f.app ⊤ (1 : Γ(X,⊤))
    congr 1
    change (X.presheaf.map (𝟙 (op ⊤))) r = r
    rw [X.presheaf.map_id]
    rfl

def cohomologyZeroSections (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    let _ : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
    let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
    cohomology M 0 ≃ₗ[ℂ] Γ(M,⊤) := by
  dsimp only
  letI : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  letI : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  let e := (Ext.linearEquiv₀ (R := Γ(X,⊤)) (X := structureSheaf X) (Y := M)).trans
    (globalHomLinearEquiv M)
  exact { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars f r) x }

lemma cohomologyDimension_zero (f : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) :
    cohomologyDimension f M 0 =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      Module.finrank ℂ Γ(M,⊤) := by
  let : Module ℂ (cohomology M 0) := Module.compHom _ (baseScalars f)
  let : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
  exact (cohomologyZeroSections f M).finrank_eq

theorem affine_eulerCharacteristic (f : X ⟶ Spec (CommRingCat.of ℂ))
    [IsAffine X] [IsNoetherian X] (M : X.Modules) [M.IsQuasicoherent] (d : ℕ) :
    eulerCharacteristic f d M =
      let _ : Module ℂ Γ(M,⊤) := Module.compHom _ (baseScalars f)
      (Module.finrank ℂ Γ(M,⊤) : ℤ) := by
  unfold eulerCharacteristic
  rw [Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul, cohomologyDimension_zero]
  · intro n hn hn0
    obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    have : Subsingleton (cohomology M (m+1)) :=
      ⟨fun x y => (AffineSchemeCohomology.affine_ext_zero X M m x).trans
        (AffineSchemeCohomology.affine_ext_zero X M m y).symm⟩
    simp [cohomologyDimension, Module.finrank_zero_of_subsingleton]
  · simp

end PiExponentSeshadri.Geometry

end

end OAI
end Source0019

section Source0020
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CohomologyIso.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry
variable {X : Scheme.{0}}

def cohomologyIso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars f)
    let _ := Module.compHom (cohomology N n) (baseScalars f)
    cohomology M n ≃ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars f)
  letI := Module.compHom (cohomology N n) (baseScalars f)
  let g := (Ext.mk₀ e.hom).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  let h := (Ext.mk₀ e.inv).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  refine
    { toFun := g
      invFun := h
      map_add' := g.map_add
      map_smul' := fun r x => g.map_smul (baseScalars f r) x
      left_inv := ?_
      right_inv := ?_ }
  · intro x
    change (x.comp (Ext.mk₀ e.hom) (add_zero n)).comp (Ext.mk₀ e.inv) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.hom_inv_id, Ext.comp_mk₀_id]
  · intro x
    change (x.comp (Ext.mk₀ e.inv) (add_zero n)).comp (Ext.mk₀ e.hom) (add_zero n) = x
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.comp_mk₀_id]

lemma eulerCharacteristic_iso (f : X ⟶ Spec (CommRingCat.of ℂ))
    {M N : X.Modules} (e : M ≅ N) (d : ℕ) :
    eulerCharacteristic f d M = eulerCharacteristic f d N := by
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  let := Module.compHom (cohomology M n) (baseScalars f)
  let := Module.compHom (cohomology N n) (baseScalars f)
  exact (cohomologyIso f e n).finrank_eq

end
end PiExponentSeshadri.Geometry

end OAI
end Source0020

section Source0021
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiCohomology.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

def cohomologyMap (p : X ⟶ Spec (CommRingCat.of ℂ)) {M N : X.Modules}
    (f : M ⟶ N) (n : ℕ) :
    let _ := Module.compHom (cohomology M n) (baseScalars p)
    let _ := Module.compHom (cohomology N n) (baseScalars p)
    cohomology M n →ₗ[ℂ] cohomology N n := by
  dsimp only
  letI := Module.compHom (cohomology M n) (baseScalars p)
  letI := Module.compHom (cohomology N n) (baseScalars p)
  let g := (Ext.mk₀ f).postcompOfLinear Γ(X,⊤) (structureSheaf X) (add_zero n)
  exact { g.toAddHom with map_smul' := fun r x => g.map_smul (baseScalars p r) x }

theorem globalSections_surjective_of_h1_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (hfinite₁ : let _ := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₁ 1))
    (hfinite₂ : let _ := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology S.X₂ 1))
    (hrank : cohomologyDimension p S.X₁ 1 = cohomologyDimension p S.X₂ 1)
    (hzero : ∀ z : cohomology S.X₃ 1, z = 0) :
    Function.Surjective (fun s : GlobalSections X S.X₂ => s ≫ S.g) := by
  let := Module.compHom (cohomology S.X₁ 1) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ 1) (baseScalars p)
  have : FiniteDimensional ℂ (cohomology S.X₁ 1) := hfinite₁
  have : FiniteDimensional ℂ (cohomology S.X₂ 1) := hfinite₂
  let f := cohomologyMap p S.f 1
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hzero _)
    exact ⟨a,ha⟩
  have hinj : Function.Injective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).mpr hsurj
  intro s
  have hboundary : (Ext.mk₀ s).comp hS.extClass rfl = 0 := by
    apply hinj
    change ((Ext.mk₀ s).comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero 1) = f 0
    rw [map_zero]
    rw [Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Ext.comp_zero]
  obtain ⟨a,ha⟩ := Ext.covariant_sequence_exact₃ (structureSheaf X) hS (Ext.mk₀ s) rfl hboundary
  refine ⟨Ext.homEquiv₀ a, ?_⟩
  apply (Ext.mk₀_bijective (structureSheaf X) S.X₃).injective
  rw [← Ext.mk₀_comp_mk₀, Ext.mk₀_homEquiv₀_apply]
  exact ha

theorem eventually_constant_of_antitone_nat (a : ℕ → ℕ) (ha : Antitone a) :
    ∃ N, ∀ n, N ≤ n → a n = a N := by
  classical
  have he : ∃ k : ℕ, ∃ n, a n = k := ⟨a 0,0,rfl⟩
  obtain ⟨N,hN⟩ := Nat.find_spec he
  refine ⟨N,fun n hn => le_antisymm (ha hn) ?_⟩
  rw [hN]
  exact Nat.find_min' he ⟨n,rfl⟩

theorem eventual_globalSections_surjective
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F Q : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ F (n+1)) (g : ∀ n, F (n+1) ⟶ Q n)
    (hcomp : ∀ n, f n ≫ g n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hfinite : ∀ n, let _ := Module.compHom (cohomology (F n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (F n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (Q n) 1, z = 0) :
    ∃ N, ∀ n, N ≤ n →
      Function.Surjective (fun s : GlobalSections X (F (n+1)) => s ≫ g n) := by
  obtain ⟨N₀,hN₀⟩ := hzero
  have hdim (n : ℕ) (hn : N₀ ≤ n) :
      cohomologyDimension p (F (n+1)) 1 ≤ cohomologyDimension p (F n) 1 := by
    let := Module.compHom (cohomology (F n) 1) (baseScalars p)
    let := Module.compHom (cohomology (F (n+1)) 1) (baseScalars p)
    have : FiniteDimensional ℂ (cohomology (F n) 1) := hfinite n
    have hsurj : Function.Surjective (cohomologyMap p (f n) 1) := by
      intro b
      exact Ext.covariant_sequence_exact₂ (structureSheaf X) (hshort n) b (hN₀ n hn _)
    exact LinearMap.finrank_le_finrank_of_surjective hsurj
  let a : ℕ → ℕ := fun n => cohomologyDimension p (F (N₀+n)) 1
  have ha : Antitone a := antitone_nat_of_succ_le (fun n => by
    simpa only [a, Nat.add_assoc] using hdim (N₀+n) (Nat.le_add_right _ _))
  obtain ⟨N,hN⟩ := eventually_constant_of_antitone_nat a ha
  refine ⟨N₀+N,fun n hn => ?_⟩
  have hn₀ : N₀ ≤ n := by omega
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn₀
  have hk : N ≤ k := by omega
  have he : cohomologyDimension p (F (N₀+k)) 1 =
      cohomologyDimension p (F (N₀+k+1)) 1 := by
    exact (hN k hk).trans (by simpa only [a, Nat.add_assoc] using (hN (k+1) (by omega)).symm)
  exact globalSections_surjective_of_h1_stationary p
    (ShortComplex.mk (f (N₀+k)) (g (N₀+k)) (hcomp (N₀+k)))
    (hshort (N₀+k)) (hfinite _) (hfinite _) he (hN₀ _ (by omega))

theorem cohomologyMap_bijective_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    Function.Bijective (cohomologyMap p S.f (n+1)) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  constructor
  · apply (injective_iff_map_eq_zero (cohomologyMap p S.f (n+1))).mpr
    intro a ha
    obtain ⟨b,hb⟩ := Ext.covariant_sequence_exact₁ (structureSheaf X) hS a ha rfl
    rw [hprev b, Ext.zero_comp] at hb
    exact hb.symm
  · intro b
    exact Ext.covariant_sequence_exact₂ (structureSheaf X) hS b (hnext _)

theorem cohomologyDimension_eq_of_quotient_vanishing
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (n : ℕ) (hprev : ∀ z : cohomology S.X₃ n, z = 0)
    (hnext : ∀ z : cohomology S.X₃ (n+1), z = 0) :
    cohomologyDimension p S.X₁ (n+1) = cohomologyDimension p S.X₂ (n+1) := by
  let := Module.compHom (cohomology S.X₁ (n+1)) (baseScalars p)
  let := Module.compHom (cohomology S.X₂ (n+1)) (baseScalars p)
  exact (LinearEquiv.ofBijective (cohomologyMap p S.f (n+1))
    (cohomologyMap_bijective_of_quotient_vanishing p S hS n hprev hnext)).finrank_eq

theorem eventual_cohomologyDimension_constant_of_two_sequences
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F B Q R : ℕ → X.Modules)
    (f : ∀ n, F n ⟶ B n) (g : ∀ n, B n ⟶ Q n)
    (f' : ∀ n, F (n+1) ⟶ B n) (g' : ∀ n, B n ⟶ R n)
    (hcomp : ∀ n, f n ≫ g n = 0) (hcomp' : ∀ n, f' n ≫ g' n = 0)
    (hshort : ∀ n, (ShortComplex.mk (f n) (g n) (hcomp n)).ShortExact)
    (hshort' : ∀ n, (ShortComplex.mk (f' n) (g' n) (hcomp' n)).ShortExact)
    (q : ℕ)
    (hzero : ∃ N, ∀ n, N ≤ n →
      (∀ z : cohomology (Q n) q, z = 0) ∧
      (∀ z : cohomology (Q n) (q+1), z = 0) ∧
      (∀ z : cohomology (R n) q, z = 0) ∧
      (∀ z : cohomology (R n) (q+1), z = 0)) :
    ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) (q+1) =
      cohomologyDimension p (F N) (q+1) := by
  obtain ⟨N,hN⟩ := hzero
  have hstep (n : ℕ) (hn : N ≤ n) :
      cohomologyDimension p (F n) (q+1) = cohomologyDimension p (F (n+1)) (q+1) := by
    obtain ⟨hQ₀,hQ₁,hR₀,hR₁⟩ := hN n hn
    exact (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort n) q hQ₀ hQ₁).trans
      (cohomologyDimension_eq_of_quotient_vanishing p _ (hshort' n) q hR₀ hR₁).symm
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    exact (hstep (N+k) (by omega)).symm.trans (ih (by omega))

end
end PiExponent.NumericalAmpleness

end OAI
end Source0021

section Source0022
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/NakaiEulerGrowth.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness

noncomputable section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry Filter
open PiExponentSeshadri.Geometry
open scoped BigOperators

variable {X : Scheme.{0}}

theorem exists_nonzero_globalSection_of_cohomologyDimension_pos
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules)
    (hpos : 0 < cohomologyDimension p M 0) :
    ∃ s : GlobalSections X M, s ≠ 0 := by
  let := Module.compHom (cohomology M 0) (baseScalars p)
  have : Nontrivial (cohomology M 0) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨z,hz⟩ := exists_ne (0 : cohomology M 0)
  refine ⟨Ext.homEquiv₀ z, ?_⟩
  intro hs
  apply hz
  have hzero := congrArg (fun s : GlobalSections X M => Ext.mk₀ s) hs
  simpa only [Ext.mk₀_homEquiv₀_apply, Ext.mk₀_zero] using hzero

theorem eulerCharacteristic_eq_zero_sub_one_add_tail
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (M : X.Modules) (d : ℕ) (hd : 1 ≤ d) :
    eulerCharacteristic p d M =
      (cohomologyDimension p M 0 : ℤ) - (cohomologyDimension p M 1 : ℤ) +
        ∑ i ∈ Finset.range (d - 1),
          (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p M (i + 2) : ℤ) := by
  unfold eulerCharacteristic
  rw [show d + 1 = 2 + (d - 1) by omega, Finset.sum_range_add]
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty,
    pow_zero, one_mul, zero_add, pow_one, neg_one_mul]
  simp only [Nat.add_comm 2, sub_eq_add_neg]

theorem eventually_nonzero_globalSection_of_euler_growth
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hconstant : ∀ i, 2 ≤ i → i ≤ d →
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) i = c) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  classical
  have hh (i : Fin (d - 1)) :
      ∃ c : ℕ, ∀ᶠ n in atTop, cohomologyDimension p (F n) (i.val + 2) = c := by
    apply hconstant (i.val + 2) (by omega) (by have := i.isLt; omega)
  choose c hc using hh
  let C : ℤ := ∑ i : Fin (d - 1), (-1 : ℤ) ^ (i.val + 2) * (c i : ℤ)
  have hall : ∀ᶠ n in atTop,
      ∀ i : Fin (d - 1), cohomologyDimension p (F n) (i.val + 2) = c i :=
    Filter.eventually_all.mpr hc
  have hlarge : ∀ᶠ n in atTop, C < eulerCharacteristic p d (F n) :=
    hgrowth.eventually (eventually_gt_atTop C)
  filter_upwards [hall, hlarge] with n hn hχ
  apply exists_nonzero_globalSection_of_cohomologyDimension_pos p (F n)
  have htail : (∑ i ∈ Finset.range (d - 1),
      (-1 : ℤ) ^ (i + 2) * (cohomologyDimension p (F n) (i + 2) : ℤ)) = C := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [hn i]
  rw [eulerCharacteristic_eq_zero_sub_one_add_tail p (F n) d hd, htail] at hχ
  have hnonneg : (0 : ℤ) ≤ (cohomologyDimension p (F n) 1 : ℤ) := Int.natCast_nonneg _
  omega

theorem eventually_nonzero_globalSection_of_eventually_stationary
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (F : ℕ → X.Modules)
    (d : ℕ) (hd : 1 ≤ d)
    (hgrowth : Tendsto (fun n => eulerCharacteristic p d (F n)) atTop atTop)
    (hstationary : ∀ i, 2 ≤ i → i ≤ d →
      ∃ N, ∀ n, N ≤ n → cohomologyDimension p (F n) i =
        cohomologyDimension p (F N) i) :
    ∀ᶠ n in atTop, ∃ s : GlobalSections X (F n), s ≠ 0 := by
  apply eventually_nonzero_globalSection_of_euler_growth p F d hd hgrowth
  intro i hi hid
  obtain ⟨N,hN⟩ := hstationary i hi hid
  refine ⟨cohomologyDimension p (F N) i, ?_⟩
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN n hn

end
end PiExponent.NumericalAmpleness

end OAI
end Source0022

section Source0023
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/NakaiCartier.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open PiExponentSeshadri.Geometry
variable {X : Scheme.{0}}

private lemma mono_iso_inv_comp {C : Type*} [Category C] {A B D : C}
    (e : A ≅ B) (f : A ⟶ D) [Mono f] : Mono (e.inv ≫ f) := inferInstance

def cartierPowerMultiply (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    modulePow X L.sheaf n ⟶ modulePow X L.sheaf (n+1) :=
  (moduleTensorUnit (modulePow X L.sheaf n)).inv ≫
    moduleTensorMap s (𝟙 (modulePow X L.sheaf n))

theorem cartierPowerMultiply_mono [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    Mono (cartierPowerMultiply L s n) := by
  let := L.mono_section s hs
  have hm : Mono (moduleTensorMap s (𝟙 (modulePow X L.sheaf n))) :=
    moduleTensorMap_mono s (L.pow n)
  exact @mono_iso_inv_comp X.Modules _ _ _ _
    (moduleTensorUnit (modulePow X L.sheaf n)) _ hm

def cartierPowerQuotient (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    X.Modules := cokernel (cartierPowerMultiply L s n)

def cartierPowerSequence (L : LineBundle X) (s : GlobalSections X L.sheaf) (n : ℕ) :
    ShortComplex X.Modules :=
  ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _) (cokernel.condition _)

theorem cartierPowerSequence_shortExact [IsIntegral X] (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0) (n : ℕ) :
    (cartierPowerSequence L s n).ShortExact := by
  have := cartierPowerMultiply_mono L s hs n
  change (ShortComplex.mk (cartierPowerMultiply L s n) (cokernel.π _)
    (cokernel.condition _)).ShortExact
  exact { exact := ShortComplex.exact_cokernel _ }

theorem cartierPowerMultiply_restrict_isIso (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) (U : X.Opens)
    [IsIso ((Scheme.Modules.restrictFunctor U.ι).map s)] :
    IsIso ((Scheme.Modules.restrictFunctor U.ι).map (cartierPowerMultiply L s n)) := by
  let R := Scheme.Modules.restrictFunctor U.ι
  have h : IsIso (R.map (moduleTensorMap s (𝟙 (modulePow X L.sheaf n)))) := by
    apply (isIso_comp_right_iff _ (moduleTensorRestrict U L.sheaf _).hom).mp
    rw [moduleTensorRestrict_natural]
    infer_instance
  change IsIso (R.map ((moduleTensorUnit _).inv ≫ moduleTensorMap s (𝟙 _)))
  rw [Functor.map_comp]
  infer_instance

theorem cartierPowerQuotient_restrict_isZero (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (n : ℕ) :
    IsZero ((cartierPowerQuotient L s n).restrict (sectionOpen X s).ι) := by
  let R := Scheme.Modules.restrictFunctor (sectionOpen X s).ι
  have : IsIso (R.map s) := PiExponentSeshadri.SectionOpens.isIso_restrict_isoOpen s
  have : IsIso (R.map (cartierPowerMultiply L s n)) :=
    cartierPowerMultiply_restrict_isIso L s n (sectionOpen X s)
  have hz : R.map (cokernel.π (cartierPowerMultiply L s n)) = 0 := by
    apply (cancel_epi (R.map (cartierPowerMultiply L s n))).mp
    rw [← R.map_comp, cokernel.condition, Functor.map_zero, comp_zero]
  have hπ : Epi (R.map (cokernel.π (cartierPowerMultiply L s n))) :=
    R.map_epi (cokernel.π (cartierPowerMultiply L s n))
  exact @IsZero.of_epi_eq_zero (sectionOpen X s).toScheme.Modules _ _ _ _
    (R.map (cokernel.π (cartierPowerMultiply L s n))) hπ hz

theorem eventual_cartierPower_sections_lift [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L : LineBundle X)
    (s : GlobalSections X L.sheaf) (hs : s ≠ 0)
    (hfinite : ∀ n,
      let _ := Module.compHom (cohomology (modulePow X L.sheaf n) 1) (baseScalars p)
      FiniteDimensional ℂ (cohomology (modulePow X L.sheaf n) 1))
    (hzero : ∃ N, ∀ n, N ≤ n → ∀ z : cohomology (cartierPowerQuotient L s n) 1,
      z = 0) :
    ∃ N, ∀ n, N ≤ n → Function.Surjective
      (fun t : GlobalSections X (modulePow X L.sheaf (n+1)) =>
        t ≫ cokernel.π (cartierPowerMultiply L s n)) := by
  exact eventual_globalSections_surjective p (fun n => modulePow X L.sheaf n)
    (cartierPowerQuotient L s) (cartierPowerMultiply L s) (fun n => cokernel.π _)
    (fun n => cokernel.condition _) (fun n => cartierPowerSequence_shortExact L s hs n)
    hfinite hzero

end
end PiExponent.NumericalAmpleness

end OAI
end Source0023

section Source0024
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Geometry/CartierPowerFrames.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.CartierPowerFrames
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
variable {X : Scheme.{0}}
def sectionMultiplyLeft (L M : X.Modules) (s : structureSheaf X ⟶ L) :
    M ⟶ moduleTensor X L M :=
  (moduleTensorUnit M).inv ≫ moduleTensorMap s (𝟙 M)

def tensorFrame (L M : X.Modules) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (moduleTensor X L M).restrict U.ι ≅ O U.toScheme :=
  moduleTensorRestrict U L M ≪≫ moduleTensorIso e f ≪≫
    moduleTensorUnit (O U.toScheme)

def tensorUnitTwist (M : X.Modules) (U : X.Opens)
    (f : M.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M).symm ≪≫
    moduleTensorRestrict U (O X) M ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

private lemma frame_section {C : Type*} [Category C] {A B D : C}
    (u : A ≅ B) (s : A ⟶ D) (e : D ≅ B) :
    s ≫ e.hom = u.hom ≫ ((u.inv ≫ s) ≫ e.hom) := by
  simp

private lemma framed_multiply {C : Type*} [Category C] {A B D P Q T O : C}
    (g : O ⟶ A) (k : A ⟶ B) (m : B ⟶ D) (r : B ⟶ P) (r' : D ⟶ Q)
    (e : P ⟶ T) (e' : Q ⟶ T) (u : T ⟶ O) (a : O ⟶ O)
    (p : P ⟶ Q) (b : T ⟶ T)
    (hn : m ≫ r' = r ≫ p) (ht : p ≫ e' = e ≫ b) (hs : b ≫ u = u ≫ a) :
    g ≫ (k ≫ m) ≫ (r' ≫ e' ≫ u) = (g ≫ k ≫ r ≫ e ≫ u) ≫ a := by
  simp only [Category.assoc]
  rw [← Category.assoc m r', hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e', ht]
  simp only [Category.assoc]
  rw [hs]

lemma tensor_multiply_framed (L M : X.Modules) (s : O X ⟶ L) (U : X.Opens)
    (e : L.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    f.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map (sectionMultiplyLeft L M s) ≫
      (tensorFrame L M U e f).hom = (tensorUnitTwist M U f).hom ≫
        (restrictSection U.ι s ≫ e.hom) := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U (O X) M
  let R' := moduleTensorRestrict U L M
  let E := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let E' := moduleTensorIso e f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme := restrictSection U.ι s ≫ e.hom
  let p := moduleTensorMap (F.map s) (𝟙 (M.restrict U.ι))
  have hn : F.map (moduleTensorMap s (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U s (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map s) q) (F.map_id M))
  have he : F.map s ≫ e.hom = (Scheme.Modules.restrictUnitIso U.ι).hom ≫ a := by
    simpa only [a, restrictSection] using!
      frame_section (Scheme.Modules.restrictUnitIso U.ι) (F.map s) e
  have h₁ := (moduleTensorMap_comp (F.map s) e.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map s ≫ e.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp (Scheme.Modules.restrictUnitIso U.ι).hom a
      f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap ((Scheme.Modules.restrictUnitIso U.ι).hom ≫ a))
      (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap a (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj (O X) ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap a (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ a :=
    (moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))
  have hfinal := framed_multiply f.inv (F.map (moduleTensorUnit M).inv)
    (F.map (moduleTensorMap s (𝟙 M))) R.hom R'.hom E.hom E'.hom T.hom a p _ hn ht hs
  simpa only [sectionMultiplyLeft, tensorFrame, tensorUnitTwist] using!
    (congrArg (fun q => f.inv ≫ q ≫ (tensorFrame L M U e f).hom)
      (F.map_comp (moduleTensorUnit M).inv (moduleTensorMap s (𝟙 M)))).trans hfinal

lemma tensor_multiply_ideal (L M : X.Modules) (s : O X ⟶ L)
    (U : X.affineOpens) (e : L.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue (f.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (sectionMultiplyLeft L M s) ≫
        (tensorFrame L M U.1 e f).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} := by
  rw [tensor_multiply_framed,endValue_comp,map_mul,← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).hom) :=
    (end_isIso_iff _).mp inferInstance
  rw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.top_mul]
  rfl

theorem cartierPowerMultiply_ideal (L : LineBundle X) (s : GlobalSections X L.sheaf)
    (n : ℕ) (U : X.affineOpens)
    (e : L.sheaf.restrict U.1.ι ≅ structureSheaf U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((modulePowFrame U.1 e n).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map
        (PiExponent.NumericalAmpleness.cartierPowerMultiply L s n) ≫
      (modulePowFrame U.1 e (n+1)).hom))} =
    Ideal.span {U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))} :=
  tensor_multiply_ideal L.sheaf (modulePow X L.sheaf n) s U e (modulePowFrame U.1 e n)
end
end PiExponent.CartierPowerFrames

end OAI
end Source0024

section Source0025
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/LocalAlgebra/TensorIdealInclusion.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponentSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Frames
variable {X : Scheme.{0}}

def tensorUnitTwist (M : LineBundle X) (U : X.Opens)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) : O U.toScheme ≅ O U.toScheme :=
  f.symm ≪≫ (Scheme.Modules.restrictFunctor U.ι).mapIso (moduleTensorUnit M.sheaf).symm ≪≫
    moduleTensorRestrict U (O X) M.sheaf ≪≫
      moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f ≪≫ moduleTensorUnit (O U.toScheme)

lemma moduleTensorIso_inv {M N P Q : X.Modules} (e : M ≅ N) (f : P ≅ Q) :
    (moduleTensorIso e f).inv = moduleTensorMap e.inv f.inv := rfl

def tensorInclusion (J M : LineBundle X) (ι : J.sheaf ⟶ O X) :
    (J.tensor M).sheaf ⟶ M.sheaf :=
  moduleTensorMap ι (𝟙 M.sheaf) ≫ (moduleTensorUnit M.sheaf).hom

private lemma frame_square {C : Type*} [Category C]
    {A B A' B' T O : C} (r : A ≅ A') (r' : B ≅ B')
    (e : A' ≅ T) (e' : B' ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : A' ⟶ B') (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p)
    (hs : e.inv ≫ p ≫ e'.hom ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hs]
  simp

private lemma frame_inclusion {C : Type*} [Category C]
    {A B D O : C} (e : A ≅ O) (e' : B ≅ O) (h : B ≅ D) (f : D ≅ O)
    (m : A ⟶ B) (a : O ⟶ O) (ha : e.inv ≫ m ≫ e'.hom = a) :
    e.inv ≫ (m ≫ h.hom) ≫ f.hom = a ≫ (f.symm ≪≫ h.symm ≪≫ e').inv := by
  rw [← ha]
  simp

private lemma mono_iso_sandwich {C : Type*} [Category C]
    {A B D E F : C} (e : A ≅ B) (m : B ⟶ D) (u : D ≅ E) (v : E ≅ F)
    [Mono m] : Mono ((e.hom ≫ m ≫ u.hom) ≫ v.hom) := inferInstance

lemma tensor_inclusion_framed (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.Opens) (e : J.sheaf.restrict U.ι ≅ O U.toScheme)
    (f : M.sheaf.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame J M U e f).inv ≫
        (Scheme.Modules.restrictFunctor U.ι).map (tensorInclusion J M ι) ≫ f.hom =
      (e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.ι).hom) ≫ (tensorUnitTwist M U f).inv := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U J.sheaf M.sheaf
  let R' := moduleTensorRestrict U (O X) M.sheaf
  let E := moduleTensorIso e f
  let E' := moduleTensorIso (Scheme.Modules.restrictUnitIso U.ι) f
  let T := moduleTensorUnit (O U.toScheme)
  let a : O U.toScheme ⟶ O U.toScheme :=
    (e.inv ≫ F.map ι) ≫ (Scheme.Modules.restrictUnitIso U.ι).hom
  have hn : F.map (moduleTensorMap ι (𝟙 M.sheaf)) ≫ R'.hom =
      R.hom ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) :=
    (moduleTensorRestrict_natural U ι (𝟙 M.sheaf)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map ι) q) (F.map_id M.sheaf))
  have h₁ := (moduleTensorMap_comp e.inv (F.map ι) f.inv
    (𝟙 (M.sheaf.restrict U.ι))).symm.trans
      (congrArg (moduleTensorMap (e.inv ≫ F.map ι)) (Category.comp_id f.inv))
  have h₂ := (moduleTensorMap_comp (e.inv ≫ F.map ι)
    (Scheme.Modules.restrictUnitIso U.ι).hom f.inv f.hom).symm.trans
      (congrArg (moduleTensorMap a) f.inv_hom_id)
  have ht : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom = moduleTensorMap a (𝟙 (O U.toScheme)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ E'.hom) h₁).trans h₂)
  have hs : E.inv ≫ moduleTensorMap (F.map ι) (𝟙 (M.sheaf.restrict U.ι)) ≫
      E'.hom ≫ T.hom = T.hom ≫ a := by
    have hscalar := moduleTensorUnit_scalar (X := U.toScheme) a (𝟙 (O U.toScheme))
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun q => q ≫ T.hom) ht).trans
        (hscalar.trans (congrArg (fun q => T.hom ≫ q) (Category.comp_id a))))
  have hframe := frame_square R R' E E' T
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) _ a hn hs
  have hfinal := frame_inclusion (R ≪≫ E ≪≫ T) (R' ≪≫ E' ≪≫ T)
    (F.mapIso (moduleTensorUnit M.sheaf)) f
    (F.map (moduleTensorMap ι (𝟙 M.sheaf))) a hframe
  simpa only [tensorInclusion, tensorUnitTwist, tensorFrame] using!
    (congrArg (fun q => (tensorFrame J M U e f).inv ≫ q ≫ f.hom)
      (F.map_comp (moduleTensorMap ι (𝟙 M.sheaf)) (moduleTensorUnit M.sheaf).hom)).trans hfinal

theorem tensorInclusion_mono (J M : LineBundle X) (ι : J.sheaf ⟶ O X) [Mono ι] :
    Mono (tensorInclusion J M ι) := by
  apply PiExponent.CoherentTwist.mono_of_local
  intro x
  obtain ⟨U,hx,⟨e⟩,⟨f⟩⟩ := common_affine_frames J M x
  refine ⟨U.1,hx,?_⟩
  have hm : Mono ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom) := by
    erw [tensor_inclusion_framed]
    have hmap : Mono (C := U.1.toScheme.Modules)
        ((Scheme.Modules.restrictFunctor U.1.ι).map ι) :=
      @Functor.map_mono _ _ _ _ (Scheme.Modules.restrictFunctor U.1.ι)
        inferInstance _ _ ι (inferInstanceAs (Mono ι))
    exact @mono_iso_sandwich U.1.toScheme.Modules _ _ _ _ _ _ e.symm
      ((Scheme.Modules.restrictFunctor U.1.ι).map ι)
      (Scheme.Modules.restrictUnitIso U.1.ι) (tensorUnitTwist M U.1 f).symm hmap
  exact (mono_comp_iff_of_mono _ f.hom).mp
    ((mono_comp_iff_of_isIso (tensorFrame J M U.1 e f).inv _).mp hm)

lemma tensor_inclusion_ideal (J M : LineBundle X) (ι : J.sheaf ⟶ O X)
    (U : X.affineOpens) (e : J.sheaf.restrict U.1.ι ≅ O U.1.toScheme)
    (f : M.sheaf.restrict U.1.ι ≅ O U.1.toScheme) :
    Ideal.span {U.1.topIso.hom (endValue ((tensorFrame J M U.1 e f).inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map (tensorInclusion J M ι) ≫ f.hom))} =
    Ideal.span {U.1.topIso.hom (endValue (e.inv ≫
      (Scheme.Modules.restrictFunctor U.1.ι).map ι ≫
        (Scheme.Modules.restrictUnitIso U.1.ι).hom))} := by
  erw [tensor_inclusion_framed,endValue_comp,map_mul,
    ← Ideal.span_singleton_mul_span_singleton]
  have hu : IsUnit (endValue (tensorUnitTwist M U.1 f).inv) :=
    (end_isIso_iff _).mp inferInstance
  erw [Ideal.span_singleton_eq_top.mpr (hu.map U.1.topIso.hom.hom),Ideal.mul_top]
  rfl

end
end PiExponentSeshadri.Geometry

end OAI
end Source0025

section TensorFrameCheck
/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Cohomology/CartierMixedEuler.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/




namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames
open PiExponent.CartierPowerFrames
variable {X : Scheme.{0}}

private lemma framed_map {C : Type*} [Category C] {A B P Q T O : C}
    (r : A ≅ P) (r' : B ≅ Q) (e : P ≅ T) (e' : Q ≅ T) (u : T ≅ O)
    (m : A ⟶ B) (p : P ⟶ Q) (b : T ⟶ T) (a : O ⟶ O)
    (hn : m ≫ r'.hom = r.hom ≫ p) (ht : p ≫ e'.hom = e.hom ≫ b)
    (hs : b ≫ u.hom = u.hom ≫ a) :
    (r ≪≫ e ≪≫ u).inv ≫ m ≫ (r' ≪≫ e' ≪≫ u).hom = a := by
  simp only [Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [← Category.assoc m r'.hom, hn]
  simp only [Category.assoc]
  rw [← Category.assoc p e'.hom, ht]
  simp only [Category.assoc]
  rw [hs]
  simp

lemma tensorMap_framed (A B M : X.Modules) (φ : A ⟶ B) (U : X.Opens)
    (e : A.restrict U.ι ≅ O U.toScheme)
    (e' : B.restrict U.ι ≅ O U.toScheme)
    (f : M.restrict U.ι ≅ O U.toScheme) :
    (tensorFrame A M U e f).inv ≫
      (Scheme.Modules.restrictFunctor U.ι).map (moduleTensorMap φ (𝟙 M)) ≫
        (tensorFrame B M U e' f).hom =
      e.inv ≫ (Scheme.Modules.restrictFunctor U.ι).map φ ≫ e'.hom := by
  let F := Scheme.Modules.restrictFunctor U.ι
  let R := moduleTensorRestrict U A M
  let R' := moduleTensorRestrict U B M
  let E := moduleTensorIso e f
  let E' := moduleTensorIso e' f
  let T := moduleTensorUnit (O U.toScheme)
  let c := e.inv ≫ F.map φ ≫ e'.hom
  let p := moduleTensorMap (F.map φ) (𝟙 (M.restrict U.ι))
  have he : F.map φ ≫ e'.hom = e.hom ≫ c := by
    simp [c]
  have hn : F.map (moduleTensorMap φ (𝟙 M)) ≫ R'.hom = R.hom ≫ p :=
    (moduleTensorRestrict_natural U φ (𝟙 M)).trans
      (congrArg (fun q => R.hom ≫ moduleTensorMap (F.map φ) q) (F.map_id M))
  have h₁ := (moduleTensorMap_comp (F.map φ) e'.hom (𝟙 (M.restrict U.ι)) f.hom).symm.trans
    (congrArg (moduleTensorMap (F.map φ ≫ e'.hom)) (Category.id_comp f.hom))
  have h₂ := (moduleTensorMap_comp e.hom c f.hom (𝟙 (O U.toScheme))).symm.trans
    (congrArg (moduleTensorMap (e.hom ≫ c)) (Category.comp_id f.hom))
  have ht : p ≫ E'.hom = E.hom ≫ moduleTensorMap c (𝟙 (O U.toScheme)) :=
    h₁.trans ((congrArg (fun q : F.obj A ⟶ O U.toScheme => moduleTensorMap q f.hom)
      he).trans h₂.symm)
  have hs : moduleTensorMap c (𝟙 (O U.toScheme)) ≫ T.hom = T.hom ≫ c :=
    (moduleTensorUnit_scalar (X := U.toScheme) c (𝟙 (O U.toScheme))).trans
      (congrArg (fun q => T.hom ≫ q) (Category.comp_id c))
  simpa only [OAI.PiExponent.CartierPowerFrames.tensorFrame] using!
    framed_map R R' E E' T (F.map (moduleTensorMap φ (𝟙 M))) p _ c hn ht hs

end
end PiExponent.NumericalAmpleness
end OAI
end TensorFrameCheck
#print axioms OAI.PiExponent.NumericalAmpleness.tensorMap_framed
