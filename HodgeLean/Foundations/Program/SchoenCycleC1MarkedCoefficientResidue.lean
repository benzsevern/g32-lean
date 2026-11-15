import HodgeLean.Foundations.Program.SchoenCycleC1HomeomorphicRotationSign
import HodgeLean.Foundations.Program.SchoenCycleC1NativeScalarDerivative
import HodgeLean.Foundations.Program.SchoenCycleC1ActualCurveTangentEigenorderHelpers
import HodgeLean.Foundations.Program.SchoenCycleC1MarkedCoefficientOrder
import HodgeLean.Foundations.Program.SchoenCycleC1NativeCurveOrderUnique
import HodgeLean.Foundations.Program.SchoenCycleC1RamifiedResidue

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual marked projection identifies the residue of a specified
native coefficient order, retaining the chosen global orientation sign
and the original rational eigenfunction and generic embedding. -/
theorem s2e_c1_marked_coefficient_residue
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (hdimX : TopologicalSpace.dim X.left = 1) (hdimY : TopologicalSpace.dim Y.left = 1)
    (G : Type) [Group G] [Fintype G] (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g) (hinj : Function.Injective a)
    (p : X ⟶ Y) [IsFinite p.left] (hsurj : Function.Surjective (Point.map p))
    (hinv : ∀ g, a g ≫ p = p)
    (horbit : ∀ x y : ComplexPoint X, Point.map p x = Point.map p y ↔
      ∃ g, Point.map (a g) x = y)
    (T : Type) [TopologicalSpace T] [ChartedSpace ℂ T] [IsManifold 𝓘(ℂ, ℂ) ω T]
    [MulAction G T] (e : T ≃ₜ ComplexPoint X)
    (he : ∀ g t, Point.map (a g) (e t) = e (g • t))
    (t : T) (g : G) (hg : b4_IsRotGen ℂ t g)
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (horient : relativeHomologyMap ℤ 2
      (imagePointPairMap (TopCat.ofHom ⟨e, e.continuous⟩) e.injective t)
      (b6m_surfaceLocalClass ℤ t) = ε • s2v_l1b_action_curveLocalClass X hdimX (e t))
    (hgeneric : p.left (genericPoint X.left) = genericPoint Y.left)
    (f : Y.left.functionField) (hf : f ≠ 0) (z : X.left.functionField) (hz : z ≠ 0)
    (m : ℕ) (hm : 0 < m) (q n : ℤ)
    (heig : letI := s2e_step1_action_isIso X G a ha1 hamul g
      s2e_step1_fieldPullback X.left (a g).left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint X.left)
          (Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ q) * z)
    (hpower : z ^ m = (eqToHom (congrArg Y.left.presheaf.stalk hgeneric.symm) ≫
      p.left.stalkMap (genericPoint X.left)).hom f)
    (u : (Y.left.presheaf.stalk (Point.map p (e t)).underlying)ˣ)
    (hdown : letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
      f = algebraMap _ Y.left.functionField (u : Y.left.presheaf.stalk (Point.map p (e t)).underlying) *
        algebraMap _ Y.left.functionField (s2e_native_curve_parameter Y (Point.map p (e t))) ^ n) :
    (m : ℤ) ∣ n - ε * q := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdimX]; infer_instance
  letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
  letI := s2e_step1_action_isIso X G a ha1 hamul g
  have hfix : Point.map (a g) (e t) = e t := by rw [he, hg.1]
  obtain ⟨v, r, hup, hchar⟩ := s2e_c1_actual_curve_native_tangent_eigenorder X (a g)
    (e t) hfix z hz (Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ q) heig
  obtain ⟨U, hU, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (show p.left (e t).underlying ∈ (⊤ : Y.left.Opens) from trivial)
  obtain ⟨w, b, hb, hrel⟩ := s2e_c1_marked_kummer_coefficient_order X Y hdimX hdimY
    G a ha1 hamul hinj p hsurj hinv horbit T e.toEquiv he t g hg U hU hx hgeneric
    f hf z m v r hup hpower
  have hnb := s2e_c1_native_curve_order_unique Y (Point.map p (e t)) u w n b
    (hdown.symm.trans hb)
  rw [← hnb] at hrel
  have hd := s2e_c1_homeomorphic_local_rotation_sign X hdimX T G e (a g) g
    (he g) t hg ε hε horient
  change deriv (s2v_l1b_action_nativeCoordinate X (e t) (a g)) 0 = _ at hd
  rw [s2e_c1_native_scalar_derivative X (e t) (a g) hfix] at hd
  rw [hd] at hchar
  exact s2e_c1_ramified_rotation_residue m (orderOf g) hm (orderOf_pos g) ε r n q
    hε hrel hchar

end HodgeLean.Foundations.Program
