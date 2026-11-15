import HodgeLean.Foundations.Program.SingularTraceNormDescent
import HodgeLean.Foundations.Program.SchoenCycleP2aProofs
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientTransferAlgebra

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- Every invariant rational singular class descends along the actual finite categorical quotient.
Source: Bredon, Sheaf Theory, second edition, Chapter V, finite quotient comparison;
Schoen, Compositio Mathematica 65 (1988), printed p. 18. -/
theorem s2e_finite_quotient_invariant_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (n : ℕ) (b : Cohomology ℚ (TopCat.of (ComplexPoint X)) n)
    (hb : ∀ g, s2e_pullback ℚ (a g) n b = b) :
    ∃ c, s2e_pullback ℚ q n c = b := by
  classical
  haveI : Surjective q.left := s2e_step1_surjective_of_complexPoint_surjective X Y q hsurj
  let A := TopCat.of (ComplexPoint X)
  let B := TopCat.of (ComplexPoint Y)
  let q' : A ⟶ B := TopCat.ofHom (Point.continuousMap q)
  let a' : G → (A ⟶ A) := fun g => TopCat.ofHom (Point.continuousMap (a g))
  let ah := s2e_quotientPointHomeomorph X G a ha1 hamul
  have ha' (g h : G) (x : A) : ah (g * h) x = ah g (ah h x) := by
    change Point.map (a (g * h)) x = Point.map (a g) (Point.map (a h) x)
    rw [hamul, Point.map_comp_apply]
  have hai (g : G) : a' g ≫ q' = q' := by
    apply TopCat.hom_ext
    apply ContinuousMap.ext
    intro x
    change Point.map q (Point.map (a g) x) = Point.map q x
    rw [← Point.map_comp_apply, hinv]
  have hi (g : G) (x : A) : q' (ah g x) = q' x :=
    congrArg (fun k : A ⟶ B => k x) (hai g)
  have ho (x y : A) (hxy : q' x = q' y) : ∃ g, ah g x = y :=
    s2e_step1_finite_quotient_point_orbits X Y G a ha1 hamul q hinv hquot x y hxy
  obtain ⟨L, hL⟩ := constantSheaf_pullback_sections q'
  obtain ⟨T, hT⟩ := finite_quotient_constantSheaf_trace G ah ha' q'
    (Topology.IsQuotientMap.of_surjective_continuous hsurj (Point.continuous_map q)) hi ho
  let La := fun g => (constantSheaf_pullback_sections (a' g)).choose
  have hLa := fun g => (constantSheaf_pullback_sections (a' g)).choose_spec
  have hd := finite_quotient_constantSheaf_trace_degree G (fun g => ah g) q' hsurj hi L T hL hT
  have hn := constantSheafOverPullback_trace_norm G q' a' hai L T hL hT La hLa
  letI : ∀ U : Opens A, ParacompactSpace U := fun U => openParacompactSpace X U
  letI : ∀ U : Opens B, ParacompactSpace U :=
    s2e_finite_quotient_target_openParacompactSpace X Y G a ha1 hamul q hsurj hinv hquot
  letI := s2e_finite_quotient_pushforward_singular_resolution X Y G a ha1 hamul q hsurj hinv hquot
  let hB := s2e_finite_quotient_target_contractibleOpen_basis X Y G a ha1 hamul q hsurj hinv hquot
  obtain ⟨J, cM, t, l, hcM, _, ⟨hcomp⟩, ⟨hnorm⟩⟩ :=
    singular_resolution_two_sided_trace q' hB G a' hai L T hL La hLa hd hn
  letI := hcM
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e := ((SingularCochainComplex ℚ A).sc n).mapHomologyIso F
  let z := e.inv b
  have hg (g : G) : HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) n z = z :=
    rational_homology_forget_fixed _ _ n b (hb g)
  have hz : HomologicalComplex.homologyMap
      (∑ g : G, ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) n z =
        Fintype.card G • z := by
    let H := HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℕ) n
    change H.map (∑ g : G, (F.mapHomologicalComplex (.up ℕ)).map
      (singularCochainComplexMap ℚ (a' g))) z = _
    rw [H.map_sum]
    have heval : (∑ g : G, H.map
        ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g)))) z =
        ∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z := by
      induction Finset.univ (α := G) using Finset.induction_on with
      | empty => rfl
      | @insert g S hS ih =>
        simp only [Finset.sum_insert hS]
        change H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + _ = _
        exact congrArg (H.map ((F.mapHomologicalComplex (.up ℕ)).map (singularCochainComplexMap ℚ (a' g))) z + ·) ih
    rw [heval]
    calc
      (∑ g : G, H.map ((F.mapHomologicalComplex (.up ℕ)).map
        (singularCochainComplexMap ℚ (a' g))) z) = ∑ _g : G, z :=
          Finset.sum_congr rfl (fun g _ => hg g)
      _ = Fintype.card G • z := by rw [Finset.sum_const, Finset.card_univ]
  obtain ⟨x, hx⟩ := singular_descent_of_global_trace q' hB G a' hai J cM t l hcomp hnorm
    n Fintype.card_ne_zero z hz
  exact rational_homology_lift_of_forget (singularCochainComplexMap ℚ q') n b x hx

end HodgeLean.Foundations.Program
