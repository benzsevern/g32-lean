import HodgeLean.Foundations.Program.G32Native.SelectedZeroPairNative
import HodgeLean.Foundations.Program.SchoenSelectedGeometryComplexFibers

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Transport the finite quotient's fibres through the retained point square. -/
theorem selectedCurveQuotientRows
    (S : g32p_Supplier) (Y Z : Over (Spec ↧ℂ))
    [IsProjective Y.hom] [IsProjective Z.hom]
    (C : Type) [TopologicalSpace C] [MulAction g32p_G C]
    (a : (S.H ⧸ S.χ.ker) → (Y ⟶ Y)) (p₀ : Y ⟶ Z)
    (hp₀ : ∀ u, a u ≫ p₀ = p₀)
    (eY : rsq_Quot S.χ.ker C ≃ₜ ComplexPoint Y)
    (eZ : rsq_Quot S.H C ≃ₜ ComplexPoint Z)
    (hpC : ∀ z, Point.map p₀ (eY z) = eZ (rsq_coarsen S.χ.ker z))
    (hpointAction : ∀ u y, Point.map (a u) (eY y) = eY (u • y)) :
    IsFinite p₀.left ∧ Function.Surjective (Point.map p₀) ∧
      (∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
        ∃ u, Point.map (a u) x = y) := by
  have hsurj : Function.Surjective (Point.map p₀) := by
    intro z
    obtain ⟨z, rfl⟩ := eZ.surjective z
    induction z using Quotient.inductionOn' with
    | h x => exact ⟨eY (rsq_proj S.χ.ker C x), hpC _⟩
  have horbit : ∀ x y : ComplexPoint Y, Point.map p₀ x = Point.map p₀ y ↔
      ∃ u, Point.map (a u) x = y := by
    intro x y
    constructor
    · obtain ⟨x, rfl⟩ := eY.surjective x
      obtain ⟨y, rfl⟩ := eY.surjective y
      intro hxy
      have he : rsq_coarsen S.χ.ker x = rsq_coarsen S.χ.ker y :=
        eZ.injective ((hpC x).symm.trans (hxy.trans (hpC y)))
      induction x using Quotient.inductionOn' with
      | h x =>
        induction y using Quotient.inductionOn' with
        | h y =>
          have hrel := Quotient.exact he
          obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hrel
          refine ⟨(QuotientGroup.mk g)⁻¹, ?_⟩
          rw [hpointAction]
          apply congrArg eY
          change rsq_proj S.χ.ker C (g⁻¹ • x) = rsq_proj S.χ.ker C y
          rw [← hg, inv_smul_smul]
    · rintro ⟨u, hu⟩
      rw [← hu, ← Point.map_comp_apply, hp₀]
  haveI : IsProper (p₀.left ≫ Z.hom) := by rw [Over.w]; infer_instance
  haveI : IsProper p₀.left := IsProper.of_comp p₀.left Z.hom
  have hfinite : IsFinite p₀.left := by
    apply s0_finite_of_finite_complex_fibers Y Z p₀
    intro z
    obtain ⟨x, rfl⟩ := hsurj z
    apply (Set.finite_range (fun u : S.H ⧸ S.χ.ker => Point.map (a u) x)).subset
    intro y hy
    obtain ⟨u, hu⟩ := (horbit x y).mp (Set.mem_preimage.mp hy).symm
    exact ⟨u, hu⟩
  exact ⟨hfinite, hsurj, horbit⟩

#print axioms selectedCurveQuotientRows
end HodgeLean.Foundations.Program
