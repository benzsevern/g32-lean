import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Projective
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import HodgeLean.Foundations.Program.SchoenCycleC11SubProofs
import HodgeLean.Foundations.Program.SchoenCycleC11TopologyHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11ProjectiveHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11EtaleSmoothHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11AlgebraizationHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11AffineAssemblyHelpers
import HodgeLean.Foundations.Program.SchoenCycleC11AffineEtaleTransportHelpers

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
theorem s2e_c11_finite_etale_analytic_cover_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left] [Etale f.left] :
    IsCoveringMap (Point.map f) ∧
      (∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y})) := by
  apply s2e_c11_analytic_cover_of_affine_restrictions X Y f
  · apply s2e_c11_local_homeomorph_of_target_opens (Point.map f) (Point.continuous_map f)
    intro y
    obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
      (x := y.underlying) (U := ⊤) trivial
    refine ⟨Point.overOpen U, hy, Point.isOpen_overOpen U, ?_⟩
    have : IsAffine (openScheme X (f.left ⁻¹ᵁ U)).left := hU.preimage f.left
    have : IsAffine (openScheme Y U).left := hU
    have : Etale (s2e_c11_restricted_over_morphism X Y f U).left :=
      inferInstanceAs (Etale (f.left ∣_ U))
    exact s2e_c11_restricted_point_local_homeomorph X Y f U
      (s2e_c11_affine_scheme_etale_local_inverse_hi _ _
        (s2e_c11_restricted_over_morphism X Y f U))
  · intro U hU
    exact (s2e_c11_finite_affine_restriction_point_proper X Y f U hU).isClosedMap

/-- Actual projective complex points, including dimension zero.
Source: Hartshorne, Algebraic Geometry, Appendix B, complex projective space;
Mathlib, SimplyConnectedSpace and LocallyPathConnectedSpace. -/
theorem s2e_c11_projective_simply_connected_aux
    (k : ℕ) :
    SimplyConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) ∧
    LocallyPathConnectedSpace
      (Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))) := by
  have : SimplyConnectedSpace
      (Projectivization ℂ (ComplexProjectiveSpace.CoordinateSpace k)) :=
    s2e_c11_classical_projective_simply_connected_direct k
  exact ⟨(s2e_c11_projective_point_homeomorph k).symm.toHomotopyEquiv.simplyConnectedSpace,
    s2e_c11_projective_points_locally_path_connected k⟩

/-- A finite surjective covering has finitely many homeomorphic sheets.
Source: Mathlib, Topology.Homotopy.Lifting,
IsCoveringMap.existsUnique_continuousMap_lifts. -/
theorem s2e_c11_finite_cover_trivialization_aux
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    [Nonempty B] [ConnectedSpace B] [LocallyPathConnectedSpace B]
    [SimplyConnectedSpace B] (f : E → B) (hf : IsCoveringMap f)
    (hs : Function.Surjective f) (hfin : ∀ b, Set.Finite (f ⁻¹' {b})) :
    ∃ (n : ℕ) (_ : 0 < n) (e : E ≃ₜ (Fin n × B)),
      ∀ x, (e x).2 = f x := by
  classical
  let b : B := Classical.choice inferInstance
  let F := f ⁻¹' {b}
  have : Finite F := (hfin b).to_subtype
  letI : Fintype F := Fintype.ofFinite F
  have : Nonempty F := by
    obtain ⟨x, hx⟩ := hs b
    exact ⟨⟨x, hx⟩⟩
  have : DiscreteTopology F := (hf b).discreteTopology_fiber
  obtain ⟨e, he⟩ := s2e_c11_section_evaluation_homeomorph f hf b
  let q : F ≃ₜ Fin (Fintype.card F) :=
    { toEquiv := Fintype.equivFin F
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  let h := e.symm.trans (q.prodCongr (Homeomorph.refl B))
  refine ⟨Fintype.card F, Fintype.card_pos, h, ?_⟩
  intro x
  exact (he (e.symm x)).symm.trans (congrArg f (e.apply_symm_apply x))

/-- A continuous analytic section of a finite etale projective map is algebraic.
Source: Hartshorne, Algebraic Geometry, Appendix B, GAGA comparison;
SGA 1, Expose XII, Theoreme 5.1. -/
theorem s2e_c11_projective_section_algebraization_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    ∃ ι : (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) ⟶ W,
      Point.map ι = s ∧ ι ≫ β = 𝟙 _ := by
  have : Smooth W.hom := s2e_c11_projective_finite_etale_source_smooth k W β
  have : IsNoetherian W.left := s2e_c11_finite_over_projective_noetherian k W β
  have : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  have : T2Space (Point ℂ W) := s2e_c11_finite_over_projective_points_t2 k W β
  have hmap := s2e_c11_projective_finite_etale_local_homeomorph k W β
  have hcomp : Point.map β ∘ s = id := funext hs
  have hemb : Topology.IsOpenEmbedding s := by
    apply hmap.isOpenEmbedding_of_comp
    · rw [hcomp]
      exact Topology.IsOpenEmbedding.id
    · exact hc
  exact s2e_c11_algebraize_smooth_clopen_section W _ β s hs
    ⟨(isCompact_range hc).isClosed, hemb.isOpen_range⟩

/-- Analytic disjointness and exhaustion transfer to all scheme points.
Source: Mathlib, AlgebraicGeometry.IsClosedImmersion, sections of separated maps;
Hartshorne, Algebraic Geometry, II.3, finite type schemes over an algebraically
closed field and density of their rational points. -/
theorem s2e_c11_sections_scheme_assembly_aux
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
    (∀ w : W.left, ∃ i, w ∈ Set.range (ι i).left) := by
  have hι : ∀ i, IsClosedImmersion (ι i).left := by
    intro i
    have heq : (ι i).left ≫ β.left = 𝟙 _ := congrArg Over.Hom.left (hsec i)
    have : IsClosedImmersion ((ι i).left ≫ β.left) := by rw [heq]; infer_instance
    exact IsClosedImmersion.of_comp (ι i).left β.left
  have : LocallyOfFiniteType W.hom := by
    have : LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) :=
      inferInstance
    rw [← Over.w β]
    change LocallyOfFiniteType (β.left ≫ ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    infer_instance
  refine ⟨hι, hsec, ?_, ?_⟩
  · intro i j hij
    have := hι i
    have := hι j
    apply s2e_c11_complex_points_detect_intersection_aux W
      (Set.range (ι i).left) (Set.range (ι j).left)
      (ι i).left.isClosedEmbedding.isClosed_range
      (ι j).left.isClosedEmbedding.isClosed_range
    rw [show Point.underlying ⁻¹' Set.range (ι i).left =
      Set.range (Point.map (ι i)) from (range_map_of_closedImmersion (ι i)).symm,
      show Point.underlying ⁻¹' Set.range (ι j).left =
      Set.range (Point.map (ι j)) from (range_map_of_closedImmersion (ι j)).symm]
    exact hdis i j hij
  · apply s2e_c11_complex_points_detect_complement_aux W n
      (fun i ↦ Set.range (ι i).left)
    · intro i
      have := hι i
      exact (ι i).left.isClosedEmbedding.isClosed_range
    · intro w
      obtain ⟨i, hi⟩ := hex w
      have := hι i
      refine ⟨i, ?_⟩
      change w ∈ Point.underlying ⁻¹' Set.range (ι i).left
      exact (congrArg (fun A : Set (Point ℂ W) ↦ w ∈ A)
        (range_map_of_closedImmersion (ι i))).mp hi

/-- A continuous section selects an analytic open-and-closed sheet.
Source: Mathlib, IsCoveringMap.isLocalHomeomorph; Hartshorne,
Algebraic Geometry, Appendix B, compact complex projective space. -/
theorem s2e_c11_section_image_clopen_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x) :
    IsOpen (Set.range s) ∧ IsClosed (Set.range s) := by
  have : T2Space (Point ℂ W) := s2e_c11_finite_over_projective_points_t2 k W β
  have hmap := s2e_c11_projective_finite_etale_local_homeomorph k W β
  have hcomp : Point.map β ∘ s = id := funext hs
  have hemb : Topology.IsOpenEmbedding s := by
    apply hmap.isOpenEmbedding_of_comp
    · rw [hcomp]
      exact Topology.IsOpenEmbedding.id
    · exact hc
  exact ⟨hemb.isOpen_range, (isCompact_range hc).isClosed⟩

/-- The selected analytic sheet is an algebraic open-and-closed subscheme.
Source: SGA 1, Expose XII, Theoreme 5.1, full faithfulness;
Hartshorne, Algebraic Geometry, Appendix B, GAGA comparison. -/
theorem s2e_c11_section_algebraic_component_aux
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (β : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite β.left] [Etale β.left]
    (s : Point ℂ (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))) →
      Point ℂ W) (hc : Continuous s) (hs : ∀ x, Point.map β (s x) = x)
    (himage : IsOpen (Set.range s) ∧ IsClosed (Set.range s)) :
    ∃ U : W.left.Opens, IsClosed (U : Set W.left) ∧
      (Point.underlying ⁻¹' (U : Set W.left) = Set.range s) ∧
      IsIso (U.ι ≫ β.left) := by
  have : Smooth W.hom := s2e_c11_projective_finite_etale_source_smooth k W β
  have : IsNoetherian W.left := s2e_c11_finite_over_projective_noetherian k W β
  have : LocallyOfFiniteType
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))).hom :=
    inferInstanceAs (LocallyOfFiniteType (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
  obtain ⟨U, hU, hpoints⟩ := s2e_c11_smooth_analytic_clopen_algebraic W
    (Set.range s) ⟨himage.2, himage.1⟩
  exact ⟨U, hU, hpoints, s2e_c11_selected_open_isIso W _ β s hs U hU hpoints⟩

/-- A finite surjective complex morphism is surjective on complex points.
Source: Hartshorne, Algebraic Geometry, II.3, finite fibres over algebraically
closed fields; Mathlib, AlgebraicGeometry.Surjective. -/
theorem s2e_c11_finite_surjective_complex_points_aux
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left] [Surjective f.left] :
    Function.Surjective (Point.map f) := by
  haveI : LocallyOfFiniteType X.hom := by
    rw [← Over.w f]
    infer_instance
  haveI : JacobsonSpace X.left := LocallyOfFiniteType.jacobsonSpace X.hom
  intro y
  have hy : IsClosed {y.underlying} :=
    ((pointEquivClosedPoint Y.hom) ⟨y.left, Over.w y⟩).2
  obtain ⟨x, hx⟩ := f.left.surjective y.underlying
  obtain ⟨z, hz, hzc⟩ := nonempty_inter_closedPoints
    (show (f.left ⁻¹' {y.underlying}).Nonempty from ⟨x, hx⟩)
    (hy.preimage f.left.continuous).isLocallyClosed
  let p : Point ℂ X := Over.homMk (pointOfClosedPoint X.hom z hzc)
    (pointOfClosedPoint_comp X.hom z hzc)
  refine ⟨p, ?_⟩
  apply Over.OverMorphism.ext
  apply ext_of_apply_closedPoint_eq Y.hom (Over.w (p ≫ f)) (Over.w y)
  change f.left (p.underlying) = y.underlying
  have hp : p.underlying = z := pointOfClosedPoint_apply X.hom z hzc _
  exact hp ▸ hz

end HodgeLean.Foundations.Program
