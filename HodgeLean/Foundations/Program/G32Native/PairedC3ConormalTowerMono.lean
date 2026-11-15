import HodgeLean.Foundations.Program.G32Native.PairedC3ConormalTowerMap

/-! # Injectivity of the algebraic conormal map in a smooth quotient tower -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct
namespace HodgeLean.Foundations.Program.G32Native

variable {K A B C : Type*} [CommRing K] [CommRing A] [CommRing B] [CommRing C]
    [Algebra K A] [Algebra K B] [Algebra K C]
    [Algebra A B] [Algebra A C] [Algebra B C]
    [IsScalarTower K A B] [IsScalarTower K A C] [IsScalarTower K B C]
    [IsScalarTower A B C]

/-- The restricted conormal map is injective when the ambient algebra
and intermediate quotient are formally smooth. No flatness of the final
quotient is needed: tensoring preserves a split injection.
Source: Hartshorne, Algebraic Geometry, II.8.12 and II.8.17. -/
theorem paired_c3_tower_conormal_injective
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K B]
    (hAB : Function.Surjective (algebraMap A B))
    (hAC : Function.Surjective (algebraMap A C)) :
    Function.Injective ((Algebra.Extension.Cotangent.map
      (pairedC3TowerExtensionMap (K := K) hAB hAC)).liftBaseChange C) := by
  let P := pairedC3QuotientPresentation (K := K) hAB
  let P' := pairedC3QuotientPresentation (K := K) hAC
  let f := pairedC3TowerExtensionMap (K := K) hAB hAC
  let c := (Algebra.Extension.Cotangent.map f).liftBaseChange C
  let d := P.cotangentComplex.baseChange C
  haveI : Algebra.FormallySmooth K P.Ring := inferInstanceAs (Algebra.FormallySmooth K A)
  obtain ⟨l, hl⟩ := P.formallySmooth_iff_split_injection.mp inferInstance
  have hleft : (l.baseChange C).comp d = LinearMap.id := by
    dsimp only [d]
    rw [← LinearMap.baseChange_comp, hl, LinearMap.baseChange_id]
  have hd : Function.Injective d :=
    (show Function.LeftInverse (l.baseChange C) d from
      fun v => LinearMap.congr_fun hleft v).injective
  let e : C ⊗[B] P.CotangentSpace ≃ₗ[C] P'.CotangentSpace :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C Ω[A⁄K]
  have hc : P'.cotangentComplex.comp c = e.toLinearMap.comp d := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro z v
    obtain ⟨t, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective v
    change P'.cotangentComplex (z • Algebra.Extension.Cotangent.map f (.mk t)) =
      e (z ⊗ₜ[B] P.cotangentComplex (.mk t))
    simp only [map_smul, Algebra.Extension.Cotangent.map_mk,
      Algebra.Extension.cotangentComplex_mk]
    change z • (1 ⊗ₜ[A] KaehlerDifferential.D K A t.val) =
      (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C Ω[A⁄K])
        (z ⊗ₜ[B] (1 ⊗ₜ[A] KaehlerDifferential.D K A t.val))
    simp only [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hinj : Function.Injective (P'.cotangentComplex.comp c) := by
    rw [hc]
    exact e.injective.comp hd
  exact Function.Injective.of_comp hinj

#print axioms paired_c3_tower_conormal_injective
end HodgeLean.Foundations.Program.G32Native
