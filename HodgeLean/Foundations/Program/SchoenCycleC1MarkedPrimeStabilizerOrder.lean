import HodgeLean.Foundations.Program.SchoenCycleQuotientPointPrimeStabilizer
import HodgeLean.Foundations.Program.HurwitzPrymDefs

/-! # Marked stabilizer orders on the actual affine curve chart -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Pointwise
namespace HodgeLean.Foundations.Program

/-- Equivariance identifies the stabilizer of the actual affine section prime
with the stabilizer of the specified marked point. -/
theorem s2e_c1_marked_prime_stabilizer_card
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    (G : Type) [Group G] (a : G → (X ⟶ X))
    (ha1 : a 1 = 𝟙 X) (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] (hinv : ∀ u, a u ≫ q = q)
    (T : Type) [MulAction G T] (e : T ≃ ComplexPoint X)
    (he : ∀ g t, Point.map (a g) (e t) = e (g • t))
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (t : T) (ht : (e t).underlying ∈ q.left ⁻¹ᵁ U) :
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    let P := ((hU.preimage q.left).primeIdealOf ⟨(e t).underlying, ht⟩).asIdeal
    let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
    Nat.card (MulAction.stabilizer G o) = Nat.card (MulAction.stabilizer G t) := by
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  let P := ((hU.preimage q.left).primeIdealOf ⟨(e t).underlying, ht⟩).asIdeal
  let o : MulAction.orbit G P := ⟨P, MulAction.mem_orbit_self P⟩
  have hfix (g : G) : g • o = o ↔ g • t = t := by
    have h := s2e_quotient_point_prime_stabilizer X Y G a ha1 hamul q hinv U hU (e t) ht g
    change g • P = P ↔ Point.map (a g) (e t) = e t at h
    rw [he, e.injective.eq_iff] at h
    exact (Subtype.ext_iff).trans h
  let E : MulAction.stabilizer G o ≃ MulAction.stabilizer G t :=
    { toFun := fun g => ⟨g.val, (hfix g.val).mp g.property⟩
      invFun := fun g => ⟨g.val, (hfix g.val).mpr g.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr E

end HodgeLean.Foundations.Program
