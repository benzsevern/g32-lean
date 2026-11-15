import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff
import HodgeLean.Foundations.Program.SchoenCycleC11SubProofs
import Mathlib.Topology.Covering.Basic

/-! # Local assembly of finite analytic coverings
Implication from local inverses and affine restriction properties to coverings.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- A local homeomorphism restricts to a local homeomorphism over each open subset.
Source: Mathlib, IsLocalHomeomorph.of_comp and open subtype embeddings. -/
theorem s2e_c11_restrict_local_homeomorph
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {f : E → B} (hf : IsLocalHomeomorph f) {s : Set B} (hs : IsOpen s) :
    IsLocalHomeomorph (s.restrictPreimage f) := by
  have hd := (hs.preimage hf.continuous).isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hc : IsLocalHomeomorph (Subtype.val ∘ s.restrictPreimage f) := hf.comp hd
  exact hc.of_comp hs.isOpenEmbedding_subtypeVal.isLocalHomeomorph hf.continuous.restrictPreimage

/-- Locally Hausdorff proper restrictions assemble the covering without global separation.
Source: Mathlib, IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn. -/
theorem s2e_c11_covering_of_local_restrictions
    {E B : Type*} [TopologicalSpace E] [TopologicalSpace B]
    {f : E → B} (hf : IsLocalHomeomorph f)
    (hfin : ∀ b, Set.Finite (f ⁻¹' {b}))
    (hlocal : ∀ b, ∃ s : Set B, b ∈ s ∧ IsOpen s ∧
      T2Space (f ⁻¹' s) ∧ IsClosedMap (s.restrictPreimage f)) :
    IsCoveringMap f := by
  intro b
  obtain ⟨s, hb, hs, hsep, hclosed⟩ := hlocal b
  have : T2Space (f ⁻¹' s) := hsep
  have hfinS : ∀ y : s, Set.Finite ((s.restrictPreimage f) ⁻¹' {y}) := by
    intro y
    have hh : Set.Finite ((Subtype.val : (f ⁻¹' s) → E) ⁻¹' (f ⁻¹' {y.1})) :=
      (hfin y.1).preimage Subtype.val_injective.injOn
    convert hh using 1
    ext x
    exact Subtype.ext_iff
  have hcov : IsCoveringMap (s.restrictPreimage f) := by
    apply isCoveringMap_iff_isCoveringMapOn_univ.mpr
    apply hclosed.isCoveringMapOn_of_isLocalHomeomorphOn
    · exact fun y _ ↦ hfinS y
    · exact (s2e_c11_restrict_local_homeomorph hf hs).isLocalHomeomorphOn
  exact (IsCoveringMapOn.of_isCoveringMap_restrictPreimage s hs
    (hs.preimage hf.continuous) hcov) b hb

/-- The analytic preimage of an affine base open under a finite map is Hausdorff.
Source: Hartshorne, Algebraic Geometry, II.3, finite morphisms are affine;
upstream ComplexPoint.openHomeomorph and t2Space_of_isAffine. -/
theorem s2e_c11_affine_preimage_t2
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y) [IsFinite f.left]
    (U : Y.left.Opens) (hU : IsAffineOpen U) :
    T2Space ((Point.map f) ⁻¹' (Point.underlying ⁻¹' (U : Set Y.left))) := by
  have : IsAffine (openScheme X (f.left ⁻¹ᵁ U)).left := hU.preimage f.left
  have : T2Space (Point ℂ (openScheme X (f.left ⁻¹ᵁ U))) :=
    t2Space_of_isAffine _
  have ht : T2Space {x : Point ℂ X // x ∈ Point.overOpen (f.left ⁻¹ᵁ U)} :=
    (openHomeomorph X (f.left ⁻¹ᵁ U)).t2Space
  have heq : (Point.map f) ⁻¹' (Point.underlying ⁻¹' (U : Set Y.left)) =
      Point.overOpen (f.left ⁻¹ᵁ U) := by
    ext x
    exact Point.mem_overOpen_map_iff f x U
  rw [heq]
  exact ht

/-- Affine analytic restrictions suffice for the finite covering interface.
Source: Mathlib, IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn;
Hartshorne, Algebraic Geometry, Appendix B, affine analytification. -/
theorem s2e_c11_analytic_cover_of_affine_restrictions
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] (f : X ⟶ Y) [IsFinite f.left]
    (hinv : IsLocalHomeomorph (Point.map f))
    (hclosed : ∀ U : Y.left.Opens, IsAffineOpen U → IsClosedMap
      ((Point.underlying ⁻¹' (U : Set Y.left)).restrictPreimage (Point.map f))) :
    IsCoveringMap (Point.map f) ∧
      (∀ y : Point ℂ Y, Set.Finite ((Point.map f) ⁻¹' {y})) := by
  have hfin := s2e_c11_finite_point_fibres_aux X Y f
  refine ⟨s2e_c11_covering_of_local_restrictions hinv hfin ?_, hfin⟩
  intro y
  obtain ⟨U, hU, hy, _⟩ := exists_isAffineOpen_mem_and_subset
    (x := y.underlying) (U := ⊤) trivial
  refine ⟨Point.underlying ⁻¹' (U : Set Y.left), hy, ?_,
    s2e_c11_affine_preimage_t2 X Y f U hU, hclosed U hU⟩
  exact Point.isOpen_overOpen U

/-- Finite maps over projective space have Hausdorff complex-point spaces.
Source: Upstream projectiveSpace_pair_mem_affineOpen and t2Space_of_pair_mem_affineOpen;
Mathlib, finite morphisms are affine. -/
theorem s2e_c11_finite_over_projective_points_t2
    (k : ℕ) (W : Over (Spec ↧ℂ))
    (f : W ⟶ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsFinite f.left] : T2Space (Point ℂ W) := by
  apply t2Space_of_pair_mem_affineOpen W
  intro z w
  obtain ⟨U, hz, hw, hU⟩ := ComplexProjectiveSpace.projectiveSpace_pair_mem_affineOpen k
    (Point.map f z) (Point.map f w)
  exact ⟨f.left ⁻¹ᵁ U, (Point.mem_overOpen_map_iff f z U).mp hz,
    (Point.mem_overOpen_map_iff f w U).mp hw,
    (show IsAffineOpen U from hU).preimage f.left⟩

end HodgeLean.Foundations.Program
