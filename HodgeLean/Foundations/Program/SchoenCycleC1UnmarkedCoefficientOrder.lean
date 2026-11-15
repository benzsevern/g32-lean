import HodgeLean.Foundations.Program.SchoenCycleC1FreeCurveCoefficientOrder
import HodgeLean.Foundations.Program.SchoenCycleC1GenericLocalFieldSquare
import HodgeLean.Foundations.Program.SchoenCycleC1KummerRamificationOrders

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Away from the retained branch values, each specified native coefficient
order is divisible by the original Kummer degree. The source point, affine
neighbourhood and its free stabilizer are obtained from the actual projection.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13. -/
theorem s2e_c1_unmarked_coefficient_order_dvd
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left]
    [Smooth X.hom] [IsProjective X.hom] [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdim : TopologicalSpace.dim X.left = 1) (hdimY : TopologicalSpace.dim Y.left = 1)
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
    (hgeneric : q.left (genericPoint X.left) = genericPoint Y.left)
    (f : Y.left.functionField) (z : X.left.functionField) (hz : z ≠ 0)
    (m : ℕ) (n : ComplexPoint Y → ℤ)
    (v : ∀ y : ComplexPoint Y, (Y.left.presheaf.stalk y.underlying)ˣ)
    (hf : letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
      ∀ y : ComplexPoint Y,
        f = algebraMap _ Y.left.functionField (v y : Y.left.presheaf.stalk y.underlying) *
          algebraMap _ Y.left.functionField (s2e_native_curve_parameter Y y) ^ n y)
    (hpower : z ^ m =
      (eqToHom (congrArg Y.left.presheaf.stalk hgeneric.symm) ≫
        q.left.stalkMap (genericPoint X.left)).hom f)
    (y : ComplexPoint Y) (hy : ∀ i, y ≠ marks i) :
    (m : ℤ) ∣ n y := by
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Y.left) (x := (Point.map q x).underlying) (U := ⊤) (by trivial)
  have hstab : MulAction.stabilizer G (e.symm x) = ⊥ := by
    by_contra hne
    obtain ⟨i, hi⟩ := (hbranch (e.symm x)).mp hne
    exact hy i (by simpa only [e.apply_symm_apply] using hi)
  have hfree (g : G) (hg : Point.map (a g) x = x) : g = 1 := by
    have hfix : g • e.symm x = e.symm x := by
      apply e.injective
      simpa only [e.apply_symm_apply] using (he g (e.symm x)).symm.trans
        (by simpa only [e.apply_symm_apply] using hg)
    have hm : g ∈ MulAction.stabilizer G (e.symm x) := hfix
    simpa only [hstab, Subgroup.mem_bot] using hm
  exact s2e_c1_free_curve_coefficient_order_dvd X Y hdim hdimY G a ha1 hamul hinj
    q hsurj hinv horbit U hU x hxU hfree hgeneric f z hz m (v _) (n _) (hf _) hpower

end HodgeLean.Foundations.Program
