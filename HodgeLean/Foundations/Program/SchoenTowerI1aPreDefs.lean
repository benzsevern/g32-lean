import HodgeLean.Foundations.Program.SchoenCycleGeometryDefs
import Mathlib.RingTheory.Invariant.Basic

/-! # Rings and maps on invariant affine charts
Concrete chart constructions for finite scheme actions.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Regular functions fixed by pullback on a preserved open.
Source: SGA 1, Exposé V, §1, invariant affine rings. -/
def s2v_i1a_chartInvariants (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) : Subring Γ(X.left, U) where
  carrier := {r | ∀ g, ((a g).left.appLE U U (hU g)).hom r = r}
  zero_mem' := fun g => map_zero _
  one_mem' := fun g => map_one _
  add_mem' := by
    intro r s hr hs g
    rw [map_add, hr g, hs g]
  mul_mem' := by
    intro r s hr hs g
    rw [map_mul, hr g, hs g]
  neg_mem' := by
    intro r hr g
    rw [map_neg, hr g]

example (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) (r : Γ(X.left, U)) :
    r ∈ s2v_i1a_chartInvariants X G a U hU ↔
      ∀ g, ((a g).left.appLE U U (hU g)).hom r = r := Iff.rfl

/-- The affine chart map induced by inclusion of invariant regular functions.
Source: SGA 1, Exposé V, §1, the map Spec A → Spec A^G. -/
def s2v_i1a_affineQuotientMap (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    U.toScheme ⟶ Spec ↧(s2v_i1a_chartInvariants X G a U hU) :=
  U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hU).subtype)

example (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    s2v_i1a_affineQuotientMap X G a U hU = U.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hU).subtype) := rfl

end HodgeLean.Foundations.Program
