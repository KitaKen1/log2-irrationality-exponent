/-
Modification notice for the LogTwo project.
Derived from openai/math (Apache-2.0), revision adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Original source: lean/OAI/NumberTheory/PiExponent/Ampleness/ReesFixedPower.lean
Changes: Convert module/import declarations to the Lean 4.34 public module format.
See ../../../../../THIRD_PARTY_NOTICES.txt for provenance and the recorded changes.
-/

module

public import OAI.NumberTheory.PiExponent.Ampleness.ReesFixedChart
public import OAI.NumberTheory.PiExponent.Ampleness.ReesProductPower

@[expose] public section

namespace OAI

namespace PiExponent.ReesFrozenPower
noncomputable section
open PiExponent.ReesFrozenChart
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {R J : Type} [CommRing R] [Fintype J] [DecidableEq J]
variable (I : Ideal R) (a : J → I) (s : Finset J)

omit [Fintype J] [DecidableEq J] in
theorem map_power_eq (n : ℕ) :
    ((I^n).map (base I a s)).map (coordinateEquiv I a s).toRingHom =
      (I^n).map (ReesProductChart.chartBase I a s) := by
  rw [Ideal.map_map]
  have he : (coordinateEquiv I a s).toRingHom.comp (base I a s) =
      ReesProductChart.chartBase I a s := by
    apply RingHom.ext
    intro r
    exact (coordinateEquiv I a s).apply_symm_apply _
  rw [he]

omit [Fintype J] [DecidableEq J] in
theorem coordinate_mem_power (n : ℕ) (x : ((I^n).map (base I a s))) :
    coordinateEquiv I a s x.val ∈ (I^n).map (ReesProductChart.chartBase I a s) := by
  have hx := Ideal.mem_map_of_mem
    (show coordinateRing I a s →+* ReesProductChart.Chart I a s from
      (coordinateEquiv I a s).toRingHom) x.property
  exact (congrArg (fun K : Ideal (ReesProductChart.Chart I a s) =>
    coordinateEquiv I a s x.val ∈ K) (map_power_eq I a s n)).mp hx

omit [Fintype J] [DecidableEq J] in
theorem inverse_map_power_eq (n : ℕ) :
    ((I^n).map (ReesProductChart.chartBase I a s)).map (coordinateEquiv I a s).symm.toRingHom =
      (I^n).map (base I a s) := by
  rw [Ideal.map_map]
  rfl

omit [Fintype J] [DecidableEq J] in
theorem inverse_mem_power (n : ℕ)
    (y : ((I^n).map (ReesProductChart.chartBase I a s))) :
    (coordinateEquiv I a s).symm y.val ∈ (I^n).map (base I a s) := by
  have hy := Ideal.mem_map_of_mem
    (show ReesProductChart.Chart I a s →+* coordinateRing I a s from
      (coordinateEquiv I a s).symm.toRingHom) y.property
  exact (congrArg (fun K : Ideal (coordinateRing I a s) =>
    (coordinateEquiv I a s).symm y.val ∈ K) (inverse_map_power_eq I a s n)).mp hy

def powerEquiv (n : ℕ) : ((I^n).map (base I a s)) ≃+
    ((I^n).map (ReesProductChart.chartBase I a s)) where
  toFun x := ⟨coordinateEquiv I a s x.val, coordinate_mem_power I a s n x⟩
  invFun y := ⟨(coordinateEquiv I a s).symm y.val, inverse_mem_power I a s n y⟩
  left_inv x := Subtype.ext ((coordinateEquiv I a s).symm_apply_apply x.val)
  right_inv y := Subtype.ext ((coordinateEquiv I a s).apply_symm_apply y.val)
  map_add' x y := Subtype.ext (map_add (coordinateEquiv I a s) x.val y.val)

omit [Fintype J] [DecidableEq J] in
@[simp] theorem powerEquiv_apply (n : ℕ) (z : ((I^n).map (base I a s))) :
    (powerEquiv I a s n z).val = coordinateEquiv I a s z.val := rfl

variable {s}

def pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ) :
    ReesLocalizedIntersections.Piece I a s n ≃+ ((I^n).map (base I a s)) :=
  (ReesProductPower.chartPowerEquiv I a hp n).trans (powerEquiv I a s n).symm

theorem coordinate_pieceEquiv {p : J} (hp : p ∈ s) (n : ℕ)
    (z : ReesLocalizedIntersections.Piece I a s n) :
    coordinateEquiv I a s (pieceEquiv I a hp n z).val =
      (ReesProductPower.chartPowerMap I a hp n z).val := by
  change (powerEquiv I a s n (pieceEquiv I a hp n z)).val = _
  exact congrArg Subtype.val ((powerEquiv I a s n).apply_symm_apply _)

end
end PiExponent.ReesFrozenPower

end OAI
