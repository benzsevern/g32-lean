import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientLocalOrbits
import HodgeLean.Foundations.Program.SchoenCycleFiniteQuotientLocalCoordinates
import HodgeLean.Foundations.Program.FiniteGroupInvariantChart

/-! # Local linearization of actual scheme symmetries
The derivative representation and averaged coordinate map are constructed.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
namespace HodgeLean.Foundations.Program

/-- A finite collection of scheme symmetries fixing a marked point has a constructed
locally invertible equivariant coordinate map on any invariant chart neighborhood.
Source: Takamura, Linearization of Quotient Families, J. Math. Sci. Univ.
Tokyo 26 (2019), pp. 381–382, construction and Lemma 3.6. -/
theorem s2e_scheme_fixed_action_local_linearization
    (X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (x₀ : ComplexPoint X) (hfixed : ∀ g, Point.map (a g) x₀ = x₀)
    (U : Opens (ComplexPoint X)) (hxU : x₀ ∈ U)
    (hU : (U : Set (ComplexPoint X)) ⊆ (s2e_centeredLocalChart X d x₀).source)
    (hinv : ∀ g, ∀ x ∈ U, Point.map (a g) x ∈ U) :
    ∃ ρ : G →* ((Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)),
      ∃ F : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
        (0 : Fin d → ℂ) ∈ F.source ∧ F 0 = 0 ∧
        ∀ g x, x ∈ U →
          F (s2e_centeredLocalChart X d x₀ (Point.map (a g) x)) =
            ρ g (F (s2e_centeredLocalChart X d x₀ x)) := by
  letI := s2e_quotientPointMulAction X G a ha1 hamul
  let S : SubMulAction G (ComplexPoint X) := {
    carrier := U
    smul_mem' := fun g x hx => hinv g x hx }
  let C := s2e_centeredLocalChart X d x₀
  obtain ⟨_, hCzero, hCana⟩ := s2e_centeredLocalChart_properties X d x₀
  have hf (g : G) : g • (x₀ : ComplexPoint X) = x₀ := hfixed g
  have hA (g : G) : AnalyticAt ℂ (fun z => C (g • C.symm z)) 0 :=
    hCana (a g) (hfixed g)
  obtain ⟨ρ, F, hF0, hFzero, hFeq⟩ :=
    coordinate_action_local_linearization G S C hU U.isOpen ⟨x₀, hxU⟩ hCzero hf hA
  refine ⟨ρ, F, hF0, hFzero, ?_⟩
  intro g x hx
  exact hFeq g ⟨x, hx⟩

/-- The actual finite quotient has stabilizer-invariant local domains with
constructed equivariant coordinates locally invertible at the marked point.
Quotient fibres in the domain are the same stabilizer's orbits.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3; Takamura, Linearization of Quotient Families,
J. Math. Sci. Univ. Tokyo 26 (2019), pp. 381–382. -/
theorem s2e_finite_quotient_stabilizer_local_linearization
    (X Y : Over (Spec ↧ℂ)) (d : ℕ)
    [IsIntegral X.left] [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (x₀ : ComplexPoint X) (N : Opens (ComplexPoint X)) (hxN : x₀ ∈ N) :
    letI := s2e_quotientPointMulAction X G a ha1 hamul
    let K := MulAction.stabilizer G x₀
    ∃ U : Opens (ComplexPoint X), x₀ ∈ U ∧ U ≤ N ∧
      (∀ g : K, ∀ x ∈ U, Point.map (a g) x ∈ U) ∧
      (∀ x ∈ U, ∀ y ∈ U, Point.map q x = Point.map q y →
        ∃ g : K, Point.map (a g) x = y) ∧
      ∃ ρ : K →* ((Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ)),
        ∃ F : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
          (0 : Fin d → ℂ) ∈ F.source ∧ F 0 = 0 ∧
          ∀ g : K, ∀ x ∈ U,
            F (s2e_centeredLocalChart X d x₀ (Point.map (a g) x)) =
              ρ g (F (s2e_centeredLocalChart X d x₀ x)) := by
  classical
  have : Smooth X.hom := SmoothOfRelativeDimension.smooth (n := d) (f := X.hom)
  letI := s2e_quotientPointMulAction X G a ha1 hamul
  let K := MulAction.stabilizer G x₀
  let C := s2e_centeredLocalChart X d x₀
  have hxC : x₀ ∈ C.source := (s2e_centeredLocalChart_properties X d x₀).1
  let M : Opens (ComplexPoint X) := N ⊓ ⟨C.source, C.open_source⟩
  obtain ⟨U, hxU, hUM, hUi, hUorb⟩ :=
    s2e_finite_quotient_local_stabilizer_orbits X Y G a ha1 hamul q hsurj hinv hquot
      x₀ M ⟨hxN, hxC⟩
  have hUsource : (U : Set (ComplexPoint X)) ⊆ C.source := fun _ hx => (hUM hx).2
  let ak : K → (X ⟶ X) := fun k => a k
  have hak1 : ak 1 = 𝟙 X := ha1
  have hakmul (g h : K) : ak (g * h) = ak h ≫ ak g := hamul g h
  have hkfix (g : K) : Point.map (ak g) x₀ = x₀ := g.property
  have hkinv (g : K) (x : ComplexPoint X) (hx : x ∈ U) : Point.map (ak g) x ∈ U :=
    hUi g g.property x hx
  obtain ⟨ρ, F, hF0, hFzero, hFeq⟩ :=
    s2e_scheme_fixed_action_local_linearization X d K ak hak1 hakmul x₀ hkfix U hxU hUsource hkinv
  refine ⟨U, hxU, (fun _ hx => (hUM hx).1), ?_, ?_, ρ, F, hF0, hFzero, hFeq⟩
  · intro g x hx
    exact hkinv g x hx
  · intro x hx y hy hxy
    obtain ⟨g, hgfix, hg⟩ := hUorb x hx y hy hxy
    exact ⟨⟨g, hgfix⟩, hg⟩

/-- The actual quotient has small stabilizer-invariant domains homeomorphic through
actual equivariant coordinates to invariant open convex model domains.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter I, section 3; Takamura, Linearization of Quotient Families,
J. Math. Sci. Univ. Tokyo 26 (2019), pp. 380–382. -/
theorem s2e_finite_quotient_stabilizer_convex_coordinates
    (X Y : Over (Spec ↧ℂ)) (d : ℕ)
    [IsIntegral X.left] [SmoothOfRelativeDimension d X.hom] [IsProjective X.hom]
    [IsIntegral Y.left] [IsProjective Y.hom]
    (G : Type) [Group G] [Fintype G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left]
    (hsurj : Function.Surjective (Point.map q))
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (S : Over (Spec ↧ℂ)) (f : X ⟶ S),
      (∀ u, a u ≫ f = f) → ∃! g : Y ⟶ S, q ≫ g = f)
    (x₀ : ComplexPoint X) (N : Opens (ComplexPoint X)) (hxN : x₀ ∈ N) :
    letI := s2e_quotientPointMulAction X G a ha1 hamul
    let K := MulAction.stabilizer G x₀
    ∃ V : Opens (ComplexPoint X), x₀ ∈ V ∧ V ≤ N ∧
      (∀ g : K, ∀ x ∈ V, Point.map (a g) x ∈ V) ∧
      (∀ x ∈ V, ∀ y ∈ V, Point.map q x = Point.map q y →
        ∃ g : K, Point.map (a g) x = y) ∧
      ∃ ρ : K →* ((Fin d → ℂ) ≃L[ℝ] (Fin d → ℂ)),
        ∃ e : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ), ∃ W : Set (Fin d → ℂ),
          e x₀ = 0 ∧ (V : Set (ComplexPoint X)) ⊆ e.source ∧
          IsOpen W ∧ (0 : Fin d → ℂ) ∈ W ∧ Convex ℝ W ∧ e '' (V : Set (ComplexPoint X)) = W ∧
          (∀ g y, y ∈ W → ρ g y ∈ W) ∧
          ∀ g : K, ∀ x ∈ V, e (Point.map (a g) x) = ρ g (e x) := by
  classical
  letI := s2e_quotientPointMulAction X G a ha1 hamul
  let K := MulAction.stabilizer G x₀
  obtain ⟨U, hxU, hUN, _, hUorb, ρ, F, hF0, hFzero, hFeq⟩ :=
    s2e_finite_quotient_stabilizer_local_linearization X Y d G a ha1 hamul q hsurj hinv hquot x₀ N hxN
  let C := s2e_centeredLocalChart X d x₀
  obtain ⟨hxC, hCzero, _⟩ := s2e_centeredLocalChart_properties X d x₀
  let e := C.trans F
  have hxe : x₀ ∈ e.source := by
    change x₀ ∈ (C.trans F).source
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hxC, ?_⟩
    change C x₀ ∈ F.source
    rw [hCzero]
    exact hF0
  have hezero : e x₀ = 0 := by
    change F (C x₀) = 0
    rw [hCzero, hFzero]
  let ρR : K →* ((Fin d → ℂ) ≃L[ℝ] (Fin d → ℂ)) := {
    toFun g := (ρ g).restrictScalars ℝ
    map_one' := by
      apply ContinuousLinearEquiv.ext
      funext z
      exact congrArg (fun f : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) => f z) ρ.map_one
    map_mul' := by
      intro g h
      apply ContinuousLinearEquiv.ext
      funext z
      exact congrArg (fun f : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ) => f z) (ρ.map_mul g h) }
  have heq (g : K) (x : ComplexPoint X) (hx : x ∈ U) :
      e (Point.map (a g) x) = ρR g (e x) := hFeq g x hx
  obtain ⟨V, W, hVo, hxV, hVU, _, hVsource, hWo, hW0, hWconv, hImage, hVi, hWi⟩ :=
    equivariant_chart_invariant_neighborhood K (fun g => Point.map (a g)) x₀
      (fun g => g.property) (fun g => (Point.continuous_map (a g)).continuousAt)
      ρR e hxe hezero (U : Set (ComplexPoint X)) (U.isOpen.mem_nhds hxU) heq
      (U : Set (ComplexPoint X)) (U.isOpen.mem_nhds hxU)
  refine ⟨⟨V, hVo⟩, hxV, (fun _ hx => hUN (hVU hx)), hVi, ?_,
    ρR, e, W, hezero, hVsource, hWo, hW0, hWconv, hImage, hWi, ?_⟩
  · intro x hx y hy hxy
    exact hUorb x (hVU hx) y (hVU hy) hxy
  · intro g x hx
    exact heq g x (hVU hx)

end HodgeLean.Foundations.Program
