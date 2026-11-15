import HodgeLean.Foundations.Program.SchoenSymmetricPowerAction
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Basic

/-! # Reflection of stabilizers on actual ordered chart points

Implication from separated coordinate values and actual permutation lifts to
the stabilizer of the original ordered scheme point.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Separated coordinate values reflect the actual permutation stabilizer
through a monomorphism into the retained ordered power.
Source: Schoen (1988), Lemma 2.2, printed p. 13, separating support parameters. -/
theorem s2v_l1a_tuple_point_stabilizer
    (X Z : Over (Spec ↧ℂ)) (n : ℕ)
    (v : X ⟶ g3_power Z n) [Mono v]
    (ρ : Equiv.Perm (Fin n) → (X ⟶ X))
    (hρv : ∀ g, ρ g ≫ v = v ≫ s2_permute Z n g)
    (p : ComplexPoint X) (z : Fin n → Γ(X.left, ⊤))
    (hsep : ∀ i j,
      Point.map (v ≫ g3_proj Z n i) p ≠ Point.map (v ≫ g3_proj Z n j) p →
      Point.evaluate ⊤ (z i) p ≠ Point.evaluate ⊤ (z j) p)
    (g : Equiv.Perm (Fin n))
    (hval : ∀ i, Point.evaluate ⊤ (z (g⁻¹ i)) p = Point.evaluate ⊤ (z i) p) :
    Point.map (ρ g) p = p := by
  have ht (i : Fin n) : Point.map (v ≫ g3_proj Z n (g⁻¹ i)) p =
      Point.map (v ≫ g3_proj Z n i) p := by
    by_contra hne
    exact hsep (g⁻¹ i) i hne (hval i)
  apply (cancel_mono v).mp
  change (p ≫ ρ g) ≫ v = p ≫ v
  rw [Category.assoc, hρv, ← Category.assoc]
  apply s2_product_hom_ext n
  intro i
  simp only [Category.assoc, s2_permute, s2_check_lift_proj]
  exact ht i

end HodgeLean.Foundations.Program
