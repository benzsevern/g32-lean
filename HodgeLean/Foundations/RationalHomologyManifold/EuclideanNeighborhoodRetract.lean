import HodgeLean.Foundations.Semialgebraic.CompatibleTriangulation
import HodgeLean.Foundations.Program.SchoenTowerHardt6RbPolyhedronFormula
import HodgeLean.Foundations.Program.SchoenTowerT11bBallFormula

/-! Finite Euclidean polyhedra retract from actual open Euclidean neighborhoods.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A finite Euclidean simplicial realization is a retract of an open Euclidean neighborhood.
Source: Rourke and Sanderson, Introduction to Piecewise-Linear Topology (1972), Chapter 3, regular neighborhoods.
HC no distance; AV milestone no distance.
-/
theorem finite_complex_euclidean_neighborhood_retract {a : ℕ}
    (K : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin a)))
    (hK : K.faces.Finite) :
    ∃ (W : Opens (EuclideanSpace ℝ (Fin a))) (hKW : K.space ⊆ W)
      (r : C(W, K.space)), ∀ x : K.space, r ⟨x.val, hKW x.property⟩ = x := by
  let E := EuclideanSpace ℝ (Fin a)
  have hKC : IsCompact K.space :=
    hK.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull ℝ)
  obtain ⟨R, hR, hKR⟩ := hKC.isBounded.subset_ball_lt 0 (0 : E)
  obtain ⟨f, hf⟩ := s2v_t11b_closedBall_formula (0 : E) R hR.le
  obtain ⟨b, hb⟩ := s2v_hardt6rb_complex_carrier_formula K hK
  have hfc : IsCompact f.realize := by rw [hf]; exact isCompact_closedBall 0 R
  have hbc : IsClosed (Subtype.val ⁻¹' b.realize : Set f.realize) := by
    rw [hb]
    exact hKC.isClosed.preimage continuous_subtype_val
  let Q := TopPair.ofSubset (X := TopCat.of f.realize) (Subtype.val ⁻¹' b.realize)
  obtain ⟨U, j, k, hjk, hk, q, hjq, _⟩ :=
    Semialgebraic.CompatibleTriangulation.compact_pair_neighbourhood_deformation f b hfc hbc
  let iK (x : K.space) : Q.snd :=
    ⟨⟨x.val, hf.symm ▸ Metric.ball_subset_closedBall (hKR x.property)⟩, hb.symm ▸ x.property⟩
  let pK : C(Q.snd, K.space) :=
    ⟨fun x => ⟨x.val.val, hb ▸ x.property⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.mp hk.isOpen_range
  let W : Opens E := ⟨V ∩ Metric.ball 0 R, hVo.inter Metric.isOpen_ball⟩
  have hKW : K.space ⊆ W := by
    intro x hx
    refine ⟨?_, hKR hx⟩
    change (⟨x, hf.symm ▸ Metric.ball_subset_closedBall (hKR hx)⟩ : f.realize) ∈
      Subtype.val ⁻¹' V
    rw [hV]
    exact ⟨j (iK ⟨x, hx⟩), ConcreteCategory.congr_hom hjk (iK ⟨x, hx⟩)⟩
  let toF : C(W, f.realize) :=
    ⟨fun w => ⟨w.val, hf.symm ▸ Metric.ball_subset_closedBall w.property.2⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hRange (w : W) : toF w ∈ Set.range k := by
    rw [← hV]
    exact w.property.1
  let toRange : C(W, Set.range k) :=
    ⟨fun w => ⟨toF w, hRange w⟩, toF.continuous.subtype_mk hRange⟩
  let e : U ≃ₜ Set.range k := hk.toIsEmbedding.toHomeomorph
  let r : C(W, K.space) :=
    ⟨fun w => pK (q (e.symm (toRange w))),
      pK.continuous.comp (q.hom.continuous.comp (e.symm.continuous.comp toRange.continuous))⟩
  refine ⟨W, hKW, r, ?_⟩
  intro x
  change pK (q (e.symm (toRange ⟨x.val, hKW x.property⟩))) = x
  have he : toRange ⟨x.val, hKW x.property⟩ = e (j (iK x)) := by
    apply Subtype.ext
    exact (ConcreteCategory.congr_hom hjk (iK x)).symm
  rw [he, e.symm_apply_apply]
  have hq : q (j (iK x)) = iK x := ConcreteCategory.congr_hom hjq (iK x)
  rw [hq]
  rfl

#print axioms finite_complex_euclidean_neighborhood_retract
end HodgeLean.Foundations.RationalHomologyManifold
