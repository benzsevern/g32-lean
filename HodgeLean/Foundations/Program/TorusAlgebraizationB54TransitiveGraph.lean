import HodgeLean.Foundations.Program.TorusAlgebraizationB54NormalGraph
import HodgeLean.Foundations.Program.TorusAlgebraizationB54SmoothLocus

noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Set
open HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

theorem b54_morphism_ext_complexPoints {X Y : Over (Spec ↧ℂ)}
    [IsReduced X.left] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated Y.hom]
    (f g : X ⟶ Y) (h : Point.map f = Point.map g) : f = g := by
  apply Over.OverMorphism.ext
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by rw [f.w]; infer_instance
  apply AlgebraicGeometry.ext_of_apply_eq Y.hom Set.univ isOpen_univ.isLocallyClosed dense_univ
  · intro x hx hxc
    let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hxc) (by simp)
    have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hxc _
    have he := congrArg Point.underlying (congrFun h p)
    simpa only [Point.underlying_map, hp] using he
  · rw [f.w, g.w]

theorem b54_iso_of_point_equivalence (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    (hnormal : zmtiso_IsNormal X.left) (e : ComplexPoint X ≃ ComplexPoint X)
    (hgraph : ∃ C : Set (gagam_product X X).left, IsClosed C ∧
      gagam_graph X X e = Point.underlying ⁻¹' C)
    (hinv : ∃ C : Set (gagam_product X X).left, IsClosed C ∧
      gagam_graph X X e.symm = Point.underlying ⁻¹' C) :
    ∃ α : X ≅ X, Point.map α.hom = e := by
  obtain ⟨C, hC, heC⟩ := hgraph
  obtain ⟨D, hD, heD⟩ := hinv
  obtain ⟨f, hf⟩ := b54_morphism_of_closed_graph_normal X X hnormal e C hC heC
  obtain ⟨g, hg⟩ := b54_morphism_of_closed_graph_normal X X hnormal e.symm D hD heD
  have hfg : f ≫ g = 𝟙 X := by
    apply b54_morphism_ext_complexPoints
    funext p
    rw [Point.map_comp_apply, hf, hg, e.symm_apply_apply]
    rfl
  have hgf : g ≫ f = 𝟙 X := by
    apply b54_morphism_ext_complexPoints
    funext p
    rw [Point.map_comp_apply, hg, hf, e.apply_symm_apply]
    rfl
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

theorem b54_smooth_of_transitive_closed_graphs (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [IsProjective X.hom]
    (hnormal : zmtiso_IsNormal X.left)
    (hmove : ∀ p q : ComplexPoint X, ∃ e : ComplexPoint X ≃ ComplexPoint X,
      e p = q ∧
      (∃ C : Set (gagam_product X X).left, IsClosed C ∧
        gagam_graph X X e = Point.underlying ⁻¹' C) ∧
      (∃ C : Set (gagam_product X X).left, IsClosed C ∧
        gagam_graph X X e.symm = Point.underlying ⁻¹' C)) : Smooth X.hom := by
  apply b54_smooth_of_transitive_isomorphisms X.hom
  intro x y hx hy
  let p : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom x hx) (by simp)
  let q : ComplexPoint X := Over.homMk (pointOfClosedPoint X.hom y hy) (by simp)
  have hp : p.underlying = x := pointOfClosedPoint_apply X.hom x hx _
  have hq : q.underlying = y := pointOfClosedPoint_apply X.hom y hy _
  obtain ⟨e, he, hgraph, hinv⟩ := hmove p q
  obtain ⟨α, hα⟩ := b54_iso_of_point_equivalence X hnormal e hgraph hinv
  refine ⟨α, ?_⟩
  change α.hom.left x = y
  have hh := congrArg Point.underlying ((congrFun hα p).trans he)
  simpa only [Point.underlying_map, hp, hq] using hh

end HodgeLean.Foundations.Program
