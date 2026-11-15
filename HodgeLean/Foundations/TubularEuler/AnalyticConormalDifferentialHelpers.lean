import Mathlib.LinearAlgebra.TensorProduct.Lift
import HodgeLean.Foundations.TubularEuler.AnalyticStalkDifferentialAlgebraHelpers

/-! # The actual analytic differential on an immersion ideal

The local ring acts on analytic covectors through its specified complex-point value map.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Topology
open scoped TensorProduct
namespace HodgeLean.Foundations.TubularEuler
open HodgeLean.Adapters

def actualIdealDifferential
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) :
    letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
    I →ₗ[X.left.presheaf.stalk x.underlying] ((Fin d → ℂ) →L[ℂ] ℂ) := by
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
  refine { toFun := fun u => actualStalkDifferential X d z x hx u.val
           map_add' := ?_
           map_smul' := ?_ }
  · intro u v
    exact actualStalkDifferential_add X d z x hx u.val v.val
  · intro r u
    change actualStalkDifferential X d z x hx (r * u.val) =
      x.stalkHom.hom r • actualStalkDifferential X d z x hx u.val
    rw [actualStalkDifferential_mul,
      a3b4g_stalkHom_eq_zero_of_mem x u.val (hIM u.property), zero_smul, add_zero]

theorem actualIdealDifferential_apply
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) (u : I) :
    actualIdealDifferential X d z x hx I hIM u = actualStalkDifferential X d z x hx u.val := by
  rfl

def actualConormalDifferential
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) :
    letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
    I.Cotangent →ₗ[X.left.presheaf.stalk x.underlying] ((Fin d → ℂ) →L[ℂ] ℂ) := by
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
  let D := actualIdealDifferential X d z x hx I hIM
  apply Ideal.Cotangent.lift D
  intro u v
  change actualStalkDifferential X d z x hx ((u : X.left.presheaf.stalk x.underlying) * v.val) = 0
  apply actualStalkDifferential_square_zero
  apply (pow_le_pow_left' hIM 2)
  rw [pow_two]
  exact Ideal.mul_mem_mul u.property v.property

theorem actualConormalDifferential_toCotangent
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) (u : I) :
    actualConormalDifferential X d z x hx I hIM (I.toCotangent u) =
      actualStalkDifferential X d z x hx u.val := by
  rfl

def actualConormalFibreDifferential
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) :
    letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
    (ℂ ⊗[X.left.presheaf.stalk x.underlying] I.Cotangent) →ₗ[ℂ] ((Fin d → ℂ) →L[ℂ] ℂ) := by
  letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
  letI := Module.compHom ((Fin d → ℂ) →L[ℂ] ℂ) x.stalkHom.hom
  letI : IsScalarTower (X.left.presheaf.stalk x.underlying) ℂ ((Fin d → ℂ) →L[ℂ] ℂ) := {
    smul_assoc := by
      intro r c v
      change (x.stalkHom.hom r * c) • v = x.stalkHom.hom r • (c • v)
      exact mul_smul _ _ _ }
  exact (actualConormalDifferential X d z x hx I hIM).liftBaseChange ℂ

theorem actualConormalFibreDifferential_tmul
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying)) (c : ℂ) (u : I) :
    letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
    actualConormalFibreDifferential X d z x hx I hIM (c ⊗ₜ I.toCotangent u) =
      c • actualStalkDifferential X d z x hx u.val := by
  rfl

theorem actualConormalFibreDifferential_regular_section
    (X : Over (Spec (CommRingCat.of ℂ))) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (z x : ComplexPoint X) (hx : x ∈ (chartAt (Fin d → ℂ) z).source)
    (I : Ideal (X.left.presheaf.stalk x.underlying))
    (hIM : I ≤ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying))
    (W : X.left.Opens) (hW : x.underlying ∈ W) (s : Γ(X.left, W))
    (hs : X.left.presheaf.germ W x.underlying hW s ∈ I) :
    letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
    actualConormalFibreDifferential X d z x hx I hIM
      ((1 : ℂ) ⊗ₜ I.toCotangent ⟨X.left.presheaf.germ W x.underlying hW s, hs⟩) =
      fderiv ℂ (fun a : Fin d → ℂ => Point.evaluate W s ((chartAt (Fin d → ℂ) z).symm a))
        ((chartAt (Fin d → ℂ) z) x) := by
  letI : Algebra (X.left.presheaf.stalk x.underlying) ℂ := x.stalkHom.hom.toAlgebra
  rw [actualConormalFibreDifferential_tmul, one_smul, actualStalkDifferential_eq_section]

#print axioms actualConormalFibreDifferential_regular_section

#print axioms actualConormalFibreDifferential_tmul

#print axioms actualConormalDifferential_toCotangent

#print axioms actualIdealDifferential_apply

end HodgeLean.Foundations.TubularEuler
