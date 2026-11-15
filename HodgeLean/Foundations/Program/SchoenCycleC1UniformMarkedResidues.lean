import HodgeLean.Foundations.Program.SchoenCycleC1MarkedCoefficientResidue
import HodgeLean.Foundations.Program.SchoenCycleC1CyclicCharacterPhase
import HodgeLean.Foundations.Program.SchoenCycleC1NativeGlobalOrientationSign

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- One signed multiplier describes all marked native coefficient orders
modulo the original covering degree. It is constructed from the original
cyclic character and the single orientation sign of the homeomorphism. -/
theorem s2e_c1_uniform_marked_coefficient_residues
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
    (m : ℕ) (hm : 0 < m) (eG : G ≃* Multiplicative (ZMod m))
    (χ : Multiplicative (ZMod m) →* ℂˣ)
    (I : Type) (points : I → T) (rot : I → G) (k : I → ℕ)
    (hrot : ∀ i, b4_IsRotGen ℂ (points i) (rot i) ∧
      eG (rot i) = Multiplicative.ofAdd (k i : ZMod m))
    (hgeneric : p.left (genericPoint X.left) = genericPoint Y.left)
    (f : Y.left.functionField) (hf : f ≠ 0) (z : X.left.functionField) (hz : z ≠ 0)
    (heig : ∀ g : G, letI := s2e_step1_action_isIso X G a ha1 hamul g
      s2e_step1_fieldPullback X.left (a g).left z =
        HodgeLean.Foundations.Curves.stalkC (genericPoint X.left) (χ (eG g) : ℂ) * z)
    (hpower : z ^ m = (eqToHom (congrArg Y.left.presheaf.stalk hgeneric.symm) ≫
      p.left.stalkMap (genericPoint X.left)).hom f)
    (n : ComplexPoint Y → ℤ) (u : ∀ y : ComplexPoint Y, (Y.left.presheaf.stalk y.underlying)ˣ)
    (hn : letI : SmoothOfRelativeDimension 1 Y.hom := by rw [← hdimY]; infer_instance
      ∀ y : ComplexPoint Y,
        f = algebraMap _ Y.left.functionField (u y : Y.left.presheaf.stalk y.underlying) *
          algebraMap _ Y.left.functionField (s2e_native_curve_parameter Y y) ^ n y) :
    ∃ s : ℤ, ∀ i : I,
      (m : ℤ) ∣ n (Point.map p (e (points i))) - s * (k i : ℤ) := by
  letI : SmoothOfRelativeDimension 1 X.hom := by rw [← hdimX]; infer_instance
  obtain ⟨ε, hε, horient⟩ := s2e_c1_native_global_orientation_sign X hdimX e
  obtain ⟨c, _, hphase⟩ := s2e_c1_cyclic_character_phase m hm χ
  refine ⟨ε * (c : ℤ), fun i => ?_⟩
  have hχ : (χ (eG (rot i)) : ℂ) =
      Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ ((c : ℤ) * (k i : ℤ)) := by
    rw [(hrot i).2]
    have h := hphase (k i)
    rw [← zpow_natCast _ (c * k i), Nat.cast_mul] at h
    exact h
  have heigi := heig (rot i)
  rw [hχ] at heigi
  have hd := s2e_c1_marked_coefficient_residue X Y hdimX hdimY G a ha1 hamul hinj
    p hsurj hinv horbit T e he (points i) (rot i) (hrot i).1 ε hε (horient (points i))
    hgeneric f hf z hz m hm ((c : ℤ) * (k i : ℤ)) (n (Point.map p (e (points i))))
    heigi hpower (u _) (hn _)
  simpa only [mul_assoc] using hd

end HodgeLean.Foundations.Program
