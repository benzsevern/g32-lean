import HodgeLean.Foundations.Program.SchoenTowerI2aNormalQuotientComparison
import HodgeLean.Foundations.Program.SchoenTowerN1bcHelpers

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
open HodgeLean.Foundations.Program
open Set Topology TopologicalSpace
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- A proper map from a reduced complex scheme, bijective on complex points, identifies that scheme with its normal integral target. -/
theorem proper_reduced_point_bijective_isIso
    (X Y : Over (Spec ↧ℂ)) [IsReduced X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (hY : zmtiso_IsNormal Y.left)
    (hbij : Function.Bijective (Point.map f)) : IsIso f.left := by
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  haveI : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  haveI : IsDominant f.left := n1bc_dominant_of_points_surjective f hbij.surjective
  have hclosed : IsClosed (Set.range f.left) := by
    simpa only [Set.image_univ] using f.left.isClosedMap Set.univ isClosed_univ
  have hsurj : Function.Surjective f.left := Set.range_eq_univ.mp
    (hclosed.closure_eq.symm.trans f.left.denseRange.closure_range)
  have hinj : ∀ (x₁ x₂ : X.left), IsClosed ({x₁} : Set X.left) →
      IsClosed ({x₂} : Set X.left) → f.left x₁ = f.left x₂ → x₁ = x₂ := by
    intro x₁ x₂ hx₁ hx₂ hfx
    let p₁ : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x₁ hx₁)
      (pointOfClosedPoint_comp X.hom x₁ hx₁)
    let p₂ : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x₂ hx₂)
      (pointOfClosedPoint_comp X.hom x₂ hx₂)
    have hp₁ : p₁.left (IsLocalRing.closedPoint ℂ) = x₁ :=
      pointOfClosedPoint_apply X.hom x₁ hx₁ _
    have hp₂ : p₂.left (IsLocalRing.closedPoint ℂ) = x₂ :=
      pointOfClosedPoint_apply X.hom x₂ hx₂ _
    have hp : Point.map f p₁ = Point.map f p₂ := by
      apply Over.OverMorphism.ext
      apply ext_of_apply_closedPoint_eq Y.hom (Over.w (p₁ ≫ f)) (Over.w (p₂ ≫ f))
      change f.left (p₁.left (IsLocalRing.closedPoint ℂ)) = f.left (p₂.left (IsLocalRing.closedPoint ℂ))
      rw [hp₁, hp₂, hfx]
    have he := congrArg (fun p : ComplexPoint X => p.left (IsLocalRing.closedPoint ℂ))
      (hbij.injective hp)
    rwa [hp₁, hp₂] at he
  have key : ∀ A : Set X.left, IsClosed A → Set.univ ⊆ f.left '' A → Set.univ ⊆ A := by
    intro A hA hAu
    have hcl : closedPoints X.left ⊆ A := by
      intro z hz
      obtain ⟨a, haA, ha⟩ := hAu (Set.mem_univ (f.left z))
      have hfz : IsClosed ({f.left z} : Set Y.left) := by
        simpa only [Set.image_singleton] using f.left.isClosedMap {z} hz
      obtain ⟨a', ⟨ha'A, ha'f⟩, ha'c⟩ := nonempty_inter_closedPoints
        (Z := A ∩ f.left ⁻¹' {f.left z}) ⟨a, haA, ha⟩
        (hA.inter (hfz.preimage f.left.continuous)).isLocallyClosed
      rwa [hinj a' z ha'c hz ha'f] at ha'A
    rw [← closure_closedPoints]
    exact closure_minimal hcl hA
  haveI : IrreducibleSpace X.left := by
    rw [irreducibleSpace_def]
    obtain ⟨z, _⟩ := hsurj (genericPoint Y.left)
    refine ⟨⟨z, Set.mem_univ _⟩, ?_⟩
    rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro A B hA hB hAB
    have hcov : (Set.univ : Set Y.left) ⊆ f.left '' A ∪ f.left '' B := by
      intro y _
      obtain ⟨z, rfl⟩ := hsurj y
      rcases hAB (Set.mem_univ z) with h | h
      · exact Or.inl ⟨z, h, rfl⟩
      · exact Or.inr ⟨z, h, rfl⟩
    rcases (isPreirreducible_iff_isClosed_union_isClosed.1
      (IrreducibleSpace.isIrreducible_univ Y.left).2) _ _ (f.left.isClosedMap _ hA)
      (f.left.isClosedMap _ hB) hcov with h | h
    · exact Or.inl (key A hA h)
    · exact Or.inr (key B hB h)
  haveI : IsIntegral X.left := isIntegral_of_irreducibleSpace_of_isReduced X.left
  exact s2v_i2a_proper_point_bijective_isIso X Y f hY hbij

end AlgebraicGeometry.RamifiedNormalization.StageFour
