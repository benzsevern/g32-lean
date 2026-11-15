import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientTopology
import HodgeLean.Foundations.Program.FiniteClosedMapSheaves
import HodgeLean.Foundations.Program.FiniteQuotientSheafTrace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- The actual quotient has finite fibres on complex points.
Source: Mumford--Fogarty--Kirwan, Geometric Invariant Theory, third edition,
Chapter 1, section 1, finite group quotients. -/
theorem s2e_finite_quotient_pointMap_finite_fibres
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f) :
    ∀ y, ((Point.map q) ⁻¹' {y}).Finite := by
  haveI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective X Y q hsurj
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  apply (Set.finite_range (fun g : G => Point.map (a g) x)).subset
  intro z hz
  obtain ⟨g, hg⟩ := s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot
    x z (by simpa using hz.symm)
  exact ⟨g, hg⟩

/-- The actual finite quotient pushforward is exact on abelian sheaves.
Source: Bredon, Sheaf Theory, second edition, II.4, direct images with finite fibres. -/
theorem s2e_finite_quotient_pushforward_preservesHomology
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f) :
    (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).PreservesHomology := by
  apply finite_closedMap_pushforward_preservesHomology
    (TopCat.ofHom (Point.continuousMap q))
    ((Point.continuous_map q).isClosedMap)
  exact s2e_finite_quotient_pointMap_finite_fibres X Y G a ha1 hamul q hsurj hinv hquot

/-- The actual quotient has a constant sheaf pullback and trace with the group
order identity and the composition formula for pullback sections.
Source: Bredon, Sheaf Theory, second edition, II.4, finite direct images. -/
theorem s2e_finite_quotient_constantSheaf_trace
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f) :
    ∃ (L : 𝓒(TopCat.of (ComplexPoint Y); ℚ) ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom (Point.continuousMap q))).obj
          𝓒(TopCat.of (ComplexPoint X); ℚ))
      (T : (TopCat.Sheaf.pushforward AddCommGrpCat (TopCat.ofHom (Point.continuousMap q))).obj
          𝓒(TopCat.of (ComplexPoint X); ℚ) ⟶ 𝓒(TopCat.of (ComplexPoint Y); ℚ)),
      L ≫ T = Fintype.card G • 𝟙 _ ∧
      ∀ (U : TopologicalSpace.Opens (ComplexPoint Y))
        (s : 𝓒(TopCat.of (ComplexPoint Y); ℚ).obj.obj (Opposite.op U))
        (x : (Point.map q) ⁻¹' U),
        constantSheafSectionEquiv (X := TopCat.of (ComplexPoint X)) (AddCommGrpCat.of ℚ)
          ((TopologicalSpace.Opens.map (TopCat.ofHom (Point.continuousMap q))).obj U)
          (L.hom.app (Opposite.op U) s) x =
        constantSheafSectionEquiv (X := TopCat.of (ComplexPoint Y)) (AddCommGrpCat.of ℚ) U s ⟨Point.map q x, x.property⟩ := by
  haveI : Surjective q.left :=
    s2e_step1_surjective_of_complexPoint_surjective X Y q hsurj
  let q' := TopCat.ofHom (Point.continuousMap q)
  let a' := s2e_quotientPointHomeomorph X G a ha1 hamul
  have ha' : ∀ g h x, a' (g * h) x = a' g (a' h x) := by
    intro g h x
    change Point.map (a (g * h)) x = Point.map (a g) (Point.map (a h) x)
    rw [hamul, Point.map_comp_apply]
  have hinv' : ∀ g x, q' (a' g x) = q' x := by
    intro g x
    change Point.map q (Point.map (a g) x) = Point.map q x
    rw [← Point.map_comp_apply, hinv]
  obtain ⟨L, hL⟩ := constantSheaf_pullback_sections q'
  have horbit' : ∀ x y, q' x = q' y → ∃ g, a' g x = y := by
    intro x y hxy
    exact s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot x y hxy
  obtain ⟨T, hT⟩ := finite_quotient_constantSheaf_trace
    (A := TopCat.of (ComplexPoint X)) (B := TopCat.of (ComplexPoint Y)) G a' ha' q'
    (Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q))
    hinv' horbit'
  refine ⟨L, T, ?_, hL⟩
  exact finite_quotient_constantSheaf_trace_degree G (fun g => a' g) q' hsurj hinv' L T hL hT

/-- The source singular cochain resolution remains a resolution after the actual
finite quotient pushforward.
Source: Bredon, Sheaf Theory, second edition, II.4, finite direct images. -/
theorem s2e_finite_quotient_pushforward_singular_resolution
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f) :
    QuasiIso (((TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).mapHomologicalComplex
        (ComplexShape.up ℕ)).map
      (AlgebraicTopology.Singular.constantsToSingularCochainSheafComplex ℚ
        (TopCat.of (ComplexPoint X)))) := by
  letI := s2e_finite_quotient_pushforward_preservesHomology X Y G a ha1 hamul q hsurj hinv hquot
  letI := AlgebraicGeometry.ComplexPoint.constantsToSingularCochain_quasiIso X ℚ
  letI : (TopCat.Sheaf.pushforward AddCommGrpCat
      (TopCat.ofHom (Point.continuousMap q))).Additive :=
    { map_add := by intros; rfl }
  infer_instance

end HodgeLean.Foundations.Program
