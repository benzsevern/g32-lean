import HodgeLean.Foundations.Program.SchoenCycleC1FreeEtaleSource

/-! # Actual etale neighbourhoods away from retained curve marks -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- The retained branch criterion supplies actual affine etale source
neighbourhoods away from every marked branch value. -/
theorem s2e_c1_curve_etale_source_off_marks
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1)
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u) (hinj : Function.Injective a)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (horbit : ∀ x z : ComplexPoint X, Point.map q x = Point.map q z ↔
      ∃ u, Point.map (a u) x = z)
    (T I : Type) [MulAction G T] (e : T ≃ ComplexPoint X)
    (he : ∀ g t, Point.map (a g) (e t) = e (g • t))
    (marks : I → ComplexPoint Y)
    (hbranch : ∀ t, MulAction.stabilizer G t ≠ ⊥ ↔
      ∃ i, Point.map q (e t) = marks i)
    (t : T) (ht : ∀ i, Point.map q (e t) ≠ marks i)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (hx : (e t).underlying ∈ q.left ⁻¹ᵁ U) :
    ∃ V : X.left.Opens, (e t).underlying ∈ V ∧ V ≤ q.left ⁻¹ᵁ U ∧
      IsAffineOpen V ∧ Etale (V.ι ≫ q.left) := by
  have hstab : MulAction.stabilizer G t = ⊥ := by
    by_contra hne
    obtain ⟨i, hi⟩ := (hbranch t).mp hne
    exact ht i hi
  have hfree (g : G) (hg : Point.map (a g) (e t) = e t) : g = 1 := by
    have hfix : g • t = t := e.injective ((he g t).symm.trans hg)
    have hm : g ∈ MulAction.stabilizer G t := hfix
    simpa only [hstab, Subgroup.mem_bot] using hm
  exact s2e_c1_free_point_etale_source_neighbourhood X Y hdim G a ha1 hamul hinj
    q hsurj hinv horbit U hU (e t) hx hfree

end HodgeLean.Foundations.Program
