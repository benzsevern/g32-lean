import HodgeLean.Foundations.QuotientDuality.RetainedAffineCoefficientSpec
import HodgeLean.Foundations.Program.SchoenTowerVanishingSuppliers

/-! Actual complex affine normalization charts in the original covering field. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

def fieldSourceNormalizationChartMap
    (B : Over (Spec ↧ℂ)) {L : Type} [Field L]
    (η : Spec (CommRingCat.of L) ⟶ B.left) [QuasiCompact η] [QuasiSeparated η]
    (U : B.left.affineOpens) (hU : η ⁻¹ᵁ U.1 = ⊤) :
    letI : Algebra Γ(B.left, U) L :=
      (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
    let N := integralClosure Γ(B.left, U) L
    letI : Algebra ℂ N := ((algebraMap Γ(B.left, U) N).comp
      (complexAffineCoefficient B U)).toAlgebra
    Over.mk (affineSpecStructureMap N) ⟶ Over.mk (η.fromNormalization ≫ B.hom) := by
  let R := Γ(B.left, U)
  let A := Γ(Spec (CommRingCat.of L), η ⁻¹ᵁ U.1)
  letI : Algebra R A := (η.app U.1).hom.toAlgebra
  letI : Algebra R L :=
    (η.app U.1 ≫ (s2v_fieldSourceSectionsIso η U.1 hU).hom).hom.toAlgebra
  let N := integralClosure R L
  letI : Algebra ℂ N := ((algebraMap R N).comp (complexAffineCoefficient B U)).toAlgebra
  let e₀ : A ≃+* L := (s2v_fieldSourceSectionsIso η U.1 hU).commRingCatIsoToRingEquiv
  let e : A ≃ₐ[R] L := { e₀ with commutes' := fun _ => rfl }
  let E := e.mapIntegralClosure
  let j := η.normalizationOpenCover.f U
  have hj := η.ι_fromNormalization U
  change j ≫ η.fromNormalization = _ at hj
  refine Over.homMk (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ j) ?_
  change (Spec.map (CommRingCat.ofHom E.toRingHom) ≫ j) ≫
    (η.fromNormalization ≫ B.hom) = Spec.map (CommRingCat.ofHom (algebraMap ℂ N))
  rw [Category.assoc, ← Category.assoc j η.fromNormalization B.hom, hj,
    Category.assoc, ← complexAffineCoefficient_spec B U,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1

#print axioms fieldSourceNormalizationChartMap
end HodgeLean.Foundations.QuotientDuality
