import HodgeLean.Foundations.Singular.TensorDegreeProjections
import HodgeLean.Foundations.Singular.TensorSeparation

/-! The actual scalar cochain in a specified rational tensor bidegree. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The canonical scalar tensor cochain in one actual bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
def tensorScalarCochain (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ)
    (φ : Module.Dual ℚ (K.X p)) (ψ : Module.Dual ℚ (L.X q)) :
    Module.Dual ℚ ((HomologicalComplex.tensorObj K L).X (p + q)) :=
  (tensorScalarPairing φ ψ).comp (tensorDegreeProjection K L p q (p + q)).hom

/-- The scalar tensor cochain evaluates on its own bidegree as the specified product pairing.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
theorem tensorScalarCochain_self (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q : ℕ)
    (φ : Module.Dual ℚ (K.X p)) (ψ : Module.Dual ℚ (L.X q)) (u : K.X p) (v : L.X q) :
    tensorScalarCochain K L p q φ ψ
      ((HomologicalComplex.ιTensorObj K L p q (p + q) rfl).hom (u ⊗ₜ[ℚ] v)) = φ u * ψ v := by
  have h := congrArg (fun k => ModuleCat.Hom.hom k (u ⊗ₜ[ℚ] v))
    (tensorDegreeInclusion_projection_self K L p q (p + q) rfl)
  change (tensorDegreeProjection K L p q (p + q)).hom
    ((HomologicalComplex.ιTensorObj K L p q (p + q) rfl).hom (u ⊗ₜ[ℚ] v)) = u ⊗ₜ[ℚ] v at h
  change tensorScalarPairing φ ψ
    ((tensorDegreeProjection K L p q (p + q)).hom
      ((HomologicalComplex.ιTensorObj K L p q (p + q) rfl).hom (u ⊗ₜ[ℚ] v))) = _
  rw [h, tensorScalarPairing_tmul]

/-- The scalar tensor cochain vanishes on every distinct actual bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
theorem tensorScalarCochain_other (K L : ChainComplex (ModuleCat ℚ) ℕ) (p q r s : ℕ)
    (hrs : r + s = p + q) (h : ¬ (r = p ∧ s = q))
    (φ : Module.Dual ℚ (K.X p)) (ψ : Module.Dual ℚ (L.X q)) (u : K.X r) (v : L.X s) :
    tensorScalarCochain K L p q φ ψ
      ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) = 0 := by
  have he := congrArg (fun k => ModuleCat.Hom.hom k (u ⊗ₜ[ℚ] v))
    (tensorDegreeInclusion_projection_other K L p q r s (p + q) hrs h)
  change (tensorDegreeProjection K L p q (p + q)).hom
    ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v)) = 0 at he
  change tensorScalarPairing φ ψ
    ((tensorDegreeProjection K L p q (p + q)).hom
      ((HomologicalComplex.ιTensorObj K L r s (p + q) hrs).hom (u ⊗ₜ[ℚ] v))) = 0
  rw [he, map_zero]

#print axioms tensorScalarCochain_other
#print axioms tensorScalarCochain
#print axioms tensorScalarCochain_self
end HodgeLean.Foundations.Singular
