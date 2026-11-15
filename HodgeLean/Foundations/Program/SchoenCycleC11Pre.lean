import HodgeLean.Foundations.Program.SchoenCycleC11PreProofs

/-! # Prerequisites for projective finite etale sections
Implication from explicit finite etale, covering and section inputs to the listed interfaces.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Finite etale maps give analytic coverings with finite fibres.
Source: Hartshorne, Algebraic Geometry, Appendix B, complex analytification;
SGA 1, Expose XII, Theoreme 5.1, finite etale comparison. -/
theorem s2e_c11_finite_etale_analytic_cover
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (Point.map f) ∧
      (∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y})) :=
  s2e_c11_finite_etale_analytic_cover_aux X Y f

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (Point.map f) ∧
      (∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y})) :=
  s2e_c11_finite_etale_analytic_cover_aux X Y f


/-- Actual projective complex points, including dimension zero.
Source: Hartshorne, Algebraic Geometry, Appendix B, complex projective space;
Mathlib, SimplyConnectedSpace and LocallyPathConnectedSpace. -/
theorem s2e_c11_projective_simply_connected
    (k : ℕ) :
    SimplyConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) ∧
    LocallyPathConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :=
  s2e_c11_projective_simply_connected_aux k

example
    (k : ℕ) :
    SimplyConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) ∧
    LocallyPathConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) :=
  s2e_c11_projective_simply_connected_aux k


/-- A finite surjective covering has finitely many homeomorphic sheets.
Source: Mathlib, Topology.Homotopy.Lifting,
IsCoveringMap.existsUnique_continuousMap_lifts. -/
theorem s2e_c11_finite_cover_trivialization
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [Nonempty B] [ConnectedSpace B] [LocallyPathConnectedSpace B]
    [SimplyConnectedSpace B] (f : E → B) (hf : IsCoveringMap f)
    (hs : Function.Surjective f) (hfin : ∀ b, Set.Finite (f ⁻¹' {b})) :
    ∃ (n : ℕ) (_ : 0 < n) (e : E ≃ₜ (Fin n × B)),
      ∀ x, (e x).2 = f x :=
  s2e_c11_finite_cover_trivialization_aux f hf hs hfin

example
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [Nonempty B] [ConnectedSpace B] [LocallyPathConnectedSpace B]
    [SimplyConnectedSpace B] (f : E → B) (hf : IsCoveringMap f)
    (hs : Function.Surjective f) (hfin : ∀ b, Set.Finite (f ⁻¹' {b})) :
    ∃ (n : ℕ) (_ : 0 < n) (e : E ≃ₜ (Fin n × B)),
      ∀ x, (e x).2 = f x :=
  s2e_c11_finite_cover_trivialization_aux f hf hs hfin


/-- A continuous analytic section of a finite etale projective map is algebraic.
Source: Hartshorne, Algebraic Geometry, Appendix B, GAGA comparison;
SGA 1, Expose XII, Theoreme 5.1. -/
theorem s2e_c11_projective_section_algebraization
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    ∃ ι : (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W,
      Point.map ι = s ∧ ι ≫ β = 𝟙 _ :=
  s2e_c11_projective_section_algebraization_aux k W β s hc hs

example
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    ∃ ι : (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W,
      Point.map ι = s ∧ ι ≫ β = 𝟙 _ :=
  s2e_c11_projective_section_algebraization_aux k W β s hc hs


/-- Analytic disjointness and exhaustion transfer to all scheme points.
Source: Mathlib, AlgebraicGeometry.IsClosedImmersion, sections of separated maps;
Hartshorne, Algebraic Geometry, II.3, finite type schemes over an algebraically
closed field and density of their rational points. -/
theorem s2e_c11_sections_scheme_assembly
    (k n : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (ι : Fin n → ((Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W))
    (hsec : ∀ i, ι i ≫ β = 𝟙 _)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (Set.range (Point.map (ι i))) (Set.range (Point.map (ι j))))
    (hex : ∀ w : Point ℂ W, ∃ i, w ∈ Set.range (Point.map (ι i))) :
    (∀ i, IsClosedImmersion (ι i).left) ∧
    (∀ i, ι i ≫ β = 𝟙 _) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (ι i).left) (Set.range (ι j).left)) ∧
    (∀ w : W.left, ∃ i, w ∈ Set.range (ι i).left) :=
  s2e_c11_sections_scheme_assembly_aux k n W β ι hsec hdis hex

example
    (k n : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (ι : Fin n → ((Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W))
    (hsec : ∀ i, ι i ≫ β = 𝟙 _)
    (hdis : ∀ i j, i ≠ j →
      Disjoint (Set.range (Point.map (ι i))) (Set.range (Point.map (ι j))))
    (hex : ∀ w : Point ℂ W, ∃ i, w ∈ Set.range (Point.map (ι i))) :
    (∀ i, IsClosedImmersion (ι i).left) ∧
    (∀ i, ι i ≫ β = 𝟙 _) ∧
    (∀ i j, i ≠ j → Disjoint (Set.range (ι i).left) (Set.range (ι j).left)) ∧
    (∀ w : W.left, ∃ i, w ∈ Set.range (ι i).left) :=
  s2e_c11_sections_scheme_assembly_aux k n W β ι hsec hdis hex


/-- A continuous section selects an analytic open-and-closed sheet.
Source: Mathlib, IsCoveringMap.isLocalHomeomorph; Hartshorne,
Algebraic Geometry, Appendix B, compact complex projective space. -/
theorem s2e_c11_section_image_clopen
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    IsOpen (Set.range s) ∧ IsClosed (Set.range s) :=
  s2e_c11_section_image_clopen_aux k W β s hc hs

example
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    IsOpen (Set.range s) ∧ IsClosed (Set.range s) :=
  s2e_c11_section_image_clopen_aux k W β s hc hs


/-- The selected analytic sheet is an algebraic open-and-closed subscheme.
Source: SGA 1, Expose XII, Theoreme 5.1, full faithfulness;
Hartshorne, Algebraic Geometry, Appendix B, GAGA comparison. -/
theorem s2e_c11_section_algebraic_component
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      (Point.underlying ⁻¹' (U : Set W.left) = Set.range s) ∧
      IsIso (U.ι ≫ β.left) :=
  s2e_c11_section_algebraic_component_aux k W β s hc hs himage

example
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      (Point.underlying ⁻¹' (U : Set W.left) = Set.range s) ∧
      IsIso (U.ι ≫ β.left) :=
  s2e_c11_section_algebraic_component_aux k W β s hc hs himage


/-- A finite surjective complex morphism is surjective on complex points.
Source: Hartshorne, Algebraic Geometry, II.3, finite fibres over algebraically
closed fields; Mathlib, AlgebraicGeometry.Surjective. -/
theorem s2e_c11_finite_surjective_complex_points
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left] :
    Function.Surjective (Point.map f) :=
  s2e_c11_finite_surjective_complex_points_aux X Y f

example
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left] :
    Function.Surjective (Point.map f) :=
  s2e_c11_finite_surjective_complex_points_aux X Y f


end HodgeLean.Foundations.Program
