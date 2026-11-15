import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints

/-! # Exact coordinate criterion for actual tuple stabilizers -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- A permutation fixes the actual tuple precisely when it preserves every projected point.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_tuple_stabilizer_iff_coordinates
    (X : Over (Spec ↧ℂ)) (n : ℕ) (x : ComplexPoint (g3_power X n))
    (σ : Equiv.Perm (Fin n)) :
    Point.map (s2_permute X n σ) x = x ↔
      ∀ i, Point.map (g3_proj X n (σ i)) x = Point.map (g3_proj X n i) x := by
  have hproj (i : Fin n) : s2_permute X n σ ≫ g3_proj X n i = g3_proj X n (σ.symm i) :=
    s2_check_lift_proj n _ i
  constructor
  · intro hx i
    have h := congrArg (fun z => Point.map (g3_proj X n (σ i)) z) hx
    change (x ≫ s2_permute X n σ) ≫ g3_proj X n (σ i) = x ≫ g3_proj X n (σ i) at h
    rw [Category.assoc, hproj, σ.symm_apply_apply] at h
    exact h.symm
  · intro hx
    apply s2e_power_hom_ext
    intro i
    change (x ≫ s2_permute X n σ) ≫ g3_proj X n i = x ≫ g3_proj X n i
    rw [Category.assoc, hproj]
    simpa only [σ.apply_symm_apply, Point.map] using (hx (σ.symm i)).symm

#print axioms s2e_tuple_stabilizer_iff_coordinates
end HodgeLean.Foundations.Program
