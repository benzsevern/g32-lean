import HodgeLean.Foundations.Singular.TensorScalarCochain
import HodgeLean.Foundations.Singular.TensorDegreeBoundary
import HodgeLean.Foundations.Singular.RationalSigns

/-! Closed actual tensor scalar cochains arising from closed factor cochains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual scalar tensor cochain is a cocycle whenever its two factor cochains are cocycles.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
theorem tensorScalarCochain_cocycle (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ)
    (φ : Module.Dual ℚ (K.X p)) (ψ : Module.Dual ℚ (L.X q))
    (hφ : φ.comp (K.d (p + 1) p).hom = 0) (hψ : ψ.comp (L.d (q + 1) q).hom = 0) :
    (tensorScalarCochain K L p q φ ψ).comp
      ((HomologicalComplex.tensorObj K L).d (p + q + 1) (p + q)).hom = 0 := by
  apply LinearMap.ext
  intro z
  have h₁ : (tensorScalarPairing φ ψ).comp
      (TensorProduct.map (K.d (p + 1) p).hom LinearMap.id) = 0 := by
    apply TensorProduct.ext'
    intro u v
    have hu := LinearMap.congr_fun hφ u
    change φ ((K.d (p + 1) p).hom u) = 0 at hu
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorScalarPairing_tmul,
      LinearMap.id_apply, hu, zero_mul, LinearMap.zero_apply]
  have h₂ : (tensorScalarPairing φ ψ).comp
      (TensorProduct.map LinearMap.id (L.d (q + 1) q).hom) = 0 := by
    apply TensorProduct.ext'
    intro u v
    have hv := LinearMap.congr_fun hψ v
    change ψ ((L.d (q + 1) q).hom v) = 0 at hv
    simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorScalarPairing_tmul,
      LinearMap.id_apply, hv, mul_zero, LinearMap.zero_apply]
  have hb := congrArg (fun k => ModuleCat.Hom.hom k z) (tensorDegree_boundary_projection K L p q)
  change (tensorDegreeProjection K L p q (p + q)).hom
      (((HomologicalComplex.tensorObj K L).d (p + q + 1) (p + q)).hom z) =
    TensorProduct.map (K.d (p + 1) p).hom LinearMap.id
      ((tensorDegreeProjection K L (p + 1) q (p + q + 1)).hom z) +
    ((((-1 : ℤˣ) ^ p) •
      (tensorDegreeProjection K L p (q + 1) (p + q + 1) ≫
        (K.X p ◁ L.d (q + 1) q))).hom z) at hb
  rw [rational_sign_apply] at hb
  change _ = TensorProduct.map (K.d (p + 1) p).hom LinearMap.id
      ((tensorDegreeProjection K L (p + 1) q (p + q + 1)).hom z) +
    (-1 : ℚ) ^ p • TensorProduct.map LinearMap.id (L.d (q + 1) q).hom
      ((tensorDegreeProjection K L p (q + 1) (p + q + 1)).hom z) at hb
  change tensorScalarPairing φ ψ ((tensorDegreeProjection K L p q (p + q)).hom
    (((HomologicalComplex.tensorObj K L).d (p + q + 1) (p + q)).hom z)) = 0
  rw [hb, map_add, map_smul]
  have hv₁ := LinearMap.congr_fun h₁ ((tensorDegreeProjection K L (p + 1) q (p + q + 1)).hom z)
  have hv₂ := LinearMap.congr_fun h₂ ((tensorDegreeProjection K L p (q + 1) (p + q + 1)).hom z)
  change tensorScalarPairing φ ψ (TensorProduct.map (K.d (p + 1) p).hom LinearMap.id
    ((tensorDegreeProjection K L (p + 1) q (p + q + 1)).hom z)) = 0 at hv₁
  change tensorScalarPairing φ ψ (TensorProduct.map LinearMap.id (L.d (q + 1) q).hom
    ((tensorDegreeProjection K L p (q + 1) (p + q + 1)).hom z)) = 0 at hv₂
  rw [hv₁, hv₂, smul_zero, add_zero]

#print axioms tensorScalarCochain_cocycle
end HodgeLean.Foundations.Singular
