import HodgeLean.Adapters.NormalConeB4aClassChartTransport
import HodgeLean.Adapters.NormalConeB4aClassNormalCharts
import HodgeLean.Adapters.NormalConeB4aGysinBridge2OpenCharts
import HodgeLean.Foundations.Program.SchoenCycleC2OpenInstances
import HodgeConjecture.Lemmas.AlgebraicGeometry.Smooth.Equidimensional

/-! # Flat analytic charts for an actual smooth closed component

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- Smooth closed components have flat complex charts without any constant
ambient dimension assumption.
Source: Hartshorne, Algebraic Geometry, III.10; the analytic inverse function theorem.
HC no distance; AV milestone no distance. -/
theorem s4_assembly_smooth_immersion_flat_charts
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left] [Smooth Q.hom]
    [Smooth W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (j : Q ⟶ W) [IsClosedImmersion j.left] (z : ComplexPoint Q) :
    ∃ r c : ℕ,
      ∃ e : OpenPartialHomeomorph (ComplexPoint W) ((Fin r → ℂ) × (Fin c → ℂ)),
        Point.map j z ∈ e.source ∧
          ∀ y ∈ e.source, y ∈ Set.range (Point.map j) ↔ (e y).2 = 0 := by
  let m := TopologicalSpace.dim Q.left
  letI : SmoothOfRelativeDimension m Q.hom := inferInstance
  obtain ⟨U, hU, hzU, d, hd⟩ :=
    a3b4g_exists_affine_smoothOfRelativeDimension W (Point.map j z).underlying
  let WU := ComplexPoint.openScheme W U
  let V := j.left ⁻¹ᵁ U
  let QV := ComplexPoint.openScheme Q V
  let i : QV ⟶ WU := Over.homMk (j.left ∣_ U) (by
    change (j.left ∣_ U) ≫ (U.ι ≫ W.hom) = V.ι ≫ Q.hom
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, j.w])
  letI : IsClosedImmersion i.left := inferInstanceAs (IsClosedImmersion (j.left ∣_ U))
  letI : SmoothOfRelativeDimension d WU.hom := hd
  letI : SmoothOfRelativeDimension m QV.hom := by
    change SmoothOfRelativeDimension m (V.ι ≫ Q.hom)
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 m V.ι Q.hom
  letI : IsAffine WU.left := hU
  letI : QuasiCompact WU.hom := (quasiCompact_iff_compactSpace WU.hom).mpr inferInstance
  let zV := ComplexPoint.asOpenPoint Q V z hzU
  have hzV : Point.map (ComplexPoint.openInclusion Q V) zV = z :=
    Over.OverMorphism.ext (ComplexPoint.liftToOpen_fac Q V z hzU)
  obtain ⟨e, hze, he, hflat⟩ :=
    a3b4a_classSmoothClosedImmersion_exists_holomorphic_flattening WU QV i m d zV
  letI : Nonempty (ComplexPoint WU) := ⟨Point.map i zV⟩
  obtain ⟨E, _, hsource, hval⟩ :=
    a3b4a_classHolomorphicChart_openTransport W U m (d-m) e he
  let f := Point.map (ComplexPoint.openInclusion W U)
  have hsquare : i ≫ ComplexPoint.openInclusion W U =
      ComplexPoint.openInclusion Q V ≫ j := by
    apply Over.OverMorphism.ext
    exact morphismRestrict_ι j.left U
  have hpoint : f (Point.map i zV) = Point.map j z := by
    change Point.map (i ≫ ComplexPoint.openInclusion W U) zV = _
    rw [hsquare]
    change Point.map j (Point.map (ComplexPoint.openInclusion Q V) zV) = _
    rw [hzV]
  have hS : f ⁻¹' Set.range (Point.map j) = Set.range (Point.map i) := by
    rw [ComplexPoint.range_map_of_isImmersion_of_comm W Q j,
      ComplexPoint.range_map_of_isImmersion_of_comm WU QV i]
    ext x
    change (∃ q, j.left q = U.ι x.underlying) ↔
      ∃ q : V.toScheme, (j.left ∣_ U) q = x.underlying
    have hrestr (q : V.toScheme) : U.ι ((j.left ∣_ U) q) = j.left q.val :=
      congrArg (fun g : V.toScheme ⟶ W.left => g q) (morphismRestrict_ι j.left U)
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨⟨q, ?_⟩, ?_⟩
      · change j.left q ∈ U
        rw [hq]
        exact x.underlying.property
      · apply Subtype.ext
        exact (hrestr _).trans hq
    · rintro ⟨q, hq⟩
      exact ⟨q.val, (hrestr q).symm.trans (congrArg Subtype.val hq)⟩
  refine ⟨m, d-m, E, ?_, ?_⟩
  · rw [hsource, ← hpoint]
    exact ⟨Point.map i zV, hze, rfl⟩
  · intro y hy
    rw [hsource] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    rw [hval v]
    change v ∈ f ⁻¹' Set.range (Point.map j) ↔ _
    rw [hS]
    exact hflat v hv

#print axioms s4_assembly_smooth_immersion_flat_charts
end HodgeLean.Foundations.Program
