import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.Program.SchoenCycleGeometryChecks
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.FunctionField

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff OnePoint
namespace HodgeLean.Foundations.Program

/-- Surjectivity on complex points is preserved by the actual finite scheme powers.
Source: the universal property of the iterated scheme product. -/
theorem n1bc_powerMap_points_surjective {Y Z : Over (Spec ↧ℂ)} (p : Y ⟶ Z)
    (hp : Function.Surjective (Point.map p)) (h : ℕ) :
    Function.Surjective (Point.map (s2_powerMap p h)) := by
  intro z
  choose y hy using fun i : Fin h => hp (Point.map (g3_proj Z h i) z)
  refine ⟨s2_lift h y, ?_⟩
  obtain ⟨hlim⟩ := spec_g3_isLimit_fan_aux Z h
  apply Fan.IsLimit.hom_ext hlim
  intro i
  change (s2_lift h y ≫ s2_powerMap p h) ≫ g3_proj Z h i = z ≫ g3_proj Z h i
  rw [Category.assoc, s2_powerMap, s2_check_lift_proj, ← Category.assoc, s2_check_lift_proj]
  exact hy i

/-- Surjectivity on complex points forces dominance over a finite-type complex base.
Source: Hartshorne, Algebraic Geometry, II.3, the density of closed points. -/
theorem n1bc_dominant_of_points_surjective {X Y : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y)
    (hf : Function.Surjective (Point.map f)) : IsDominant f.left := by
  letI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  have hr : closedPoints Y.left ⊆ Set.range f.left := by
    intro y hy
    let z : ComplexPoint Y := Over.homMk (pointOfClosedPoint Y.hom y hy) (by simp)
    obtain ⟨x, hx⟩ := hf z
    refine ⟨x.left (IsLocalRing.closedPoint ℂ), ?_⟩
    have he := congrArg (fun t : ComplexPoint Y => t.left (IsLocalRing.closedPoint ℂ)) hx
    change f.left (x.left (IsLocalRing.closedPoint ℂ)) =
      pointOfClosedPoint Y.hom y hy (IsLocalRing.closedPoint ℂ) at he
    rw [pointOfClosedPoint_apply] at he
    exact he
  rw [isDominant_iff, denseRange_iff_closure_range]
  apply Set.Subset.antisymm (Set.subset_univ _)
  rw [← closure_closedPoints (X := Y.left)]
  exact closure_mono hr

/-- The actual original covering map is surjective on complex points.
Source: Schoen (1988), §1, the quotient square for the curve power. -/
theorem n1bc_originalCover_points_surjective
    {Y Z W B : Over (Spec ↧ℂ)} (p : Y ⟶ Z)
    (hp : Function.Surjective (Point.map p)) (h : ℕ)
    (q : g3_power Y h ⟶ W) (γ : g3_power Z h ⟶ B)
    (hγ : Function.Surjective (Point.map γ)) (β : W ⟶ B)
    (hβ : q ≫ β = s2_powerMap p h ≫ γ) :
    Function.Surjective (Point.map β) := by
  intro b
  obtain ⟨z, rfl⟩ := hγ b
  obtain ⟨y, rfl⟩ := n1bc_powerMap_points_surjective p hp h z
  refine ⟨Point.map q y, ?_⟩
  change (y ≫ q) ≫ β = (y ≫ s2_powerMap p h) ≫ γ
  rw [Category.assoc, hβ, Category.assoc]


/-- A quasi-finite homomorphism over a field is finite.
Source: Mathlib, Module.Finite.of_quasiFinite. -/
theorem n1bc_finite_of_quasiFinite {K L : Type*} [Field K] [CommRing L]
    (f : K →+* L) (hf : f.QuasiFinite) : f.Finite := by
  letI := f.toAlgebra
  letI : Algebra.QuasiFinite K L := hf
  exact Module.Finite.of_quasiFinite

end HodgeLean.Foundations.Program
