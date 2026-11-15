import Mathlib.Analysis.Complex.Polynomial.Basic
import HodgeLean.Foundations.Program.SchoenTowerL1bDeckEigenvalue

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A full order original field symmetry acts on a generating binomial element by a primitive complex scalar. -/
theorem generating_binomial_primitive_complex_scalar
    {A L : Type*} [CommRing A] [Field L]
    [Algebra ℂ A] [Algebra A L] [Algebra ℂ L] [IsScalarTower ℂ A L]
    (δ : L ≃ₐ[A] L) (m : ℕ) (hm : 0 < m) (horder : orderOf δ = m)
    (w : L) (hw : w ≠ 0) (b : A) (hpow : w ^ m = algebraMap A L b)
    (hgen : Subfield.closure (Set.range (algebraMap A L) ∪ {w}) = ⊤) :
    ∃ ζ : ℂ, IsPrimitiveRoot ζ m ∧ δ w = algebraMap ℂ L ζ * w := by
  let forget : (L ≃ₐ[A] L) →* (L ≃+* L) :=
    { toFun := AlgEquiv.toRingEquiv, map_one' := rfl, map_mul' := fun _ _ => rfl }
  have ho : orderOf δ.toRingEquiv = m :=
    (orderOf_injective forget AlgEquiv.toRingEquiv_injective δ).trans horder
  have hconst (c : ℂ) : δ.toRingEquiv (algebraMap ℂ L c) = algebraMap ℂ L c := by
    rw [IsScalarTower.algebraMap_apply ℂ A L c]
    exact δ.commutes _
  have hp : δ.toRingEquiv (w ^ m) = w ^ m := by
    rw [hpow]
    exact δ.commutes b
  obtain ⟨ζ, hζ, heig⟩ := HodgeLean.Foundations.Program.s2v_l1b_deck_binomial_scalar
    (algebraMap A L) δ.toRingEquiv w m hm hw hgen δ.commutes hconst hp ho
  exact ⟨ζ, hζ.of_map_of_injective (algebraMap ℂ L).injective, heig⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
