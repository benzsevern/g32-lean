import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricSplit

/-! # Product coordinates on an actual barycentric face star -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
open Semialgebraic.CompatibleTriangulation.Helpers
namespace HodgeLean.Foundations.QuotientDuality

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The normal carrier is the actual fibre over the specified positive face coordinates.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
abbrev ProperCycleNormalPoint (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) :=
  {w : ProperCycleStarPoint S | properCycle_star_face S hS w = p}

/-- The literal reweighting formula varies continuously in the old weights and the new face point.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_face_reweight_continuous (S : Finset ι) :
    Continuous (fun z : stdSimplex ℝ ι × ProperCycleFacePoint S =>
      properCycle_face_reweight S z.1 z.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  change Continuous (fun z : stdSimplex ℝ ι × ProperCycleFacePoint S =>
    if i ∈ S then (∑ j ∈ S, z.1.val j) * z.2.val.val i else z.1.val i)
  by_cases hi : i ∈ S
  · simp only [if_pos hi]
    apply Continuous.mul
    · exact continuous_finsetSum S (fun j _ =>
        (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst))
    · exact (continuous_apply i).comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd))
  · simp only [if_neg hi]
    exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)

/-- Normalized face coordinates give a continuous map from the actual positive star.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_star_face_map (S : Finset ι) (hS : S.Nonempty) :
    C(ProperCycleStarPoint S, ProperCycleFacePoint S) where
  toFun := properCycle_star_face S hS
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hc : Continuous (fun w : ProperCycleStarPoint S =>
        (⟨w.val, properCycle_star_mass_pos S hS w⟩ :
          {w : stdSimplex ℝ ι | 0 < ∑ i ∈ S, w.val i})) :=
      continuous_subtype_val.subtype_mk _
    exact (s2e_pair_faceNormalizeMap S).continuous.comp hc

/-- The actual star reweighting is continuous and preserves all selected positivity constraints.
Source: Munkres, Elements of Algebraic Topology, section 2, open stars.
HC no distance; AV milestone no distance. -/
def properCycle_star_reweight_map (S : Finset ι) (hS : S.Nonempty) :
    C(ProperCycleStarPoint S × ProperCycleFacePoint S, ProperCycleStarPoint S) where
  toFun z := ⟨properCycle_face_reweight S z.1.val z.2,
    properCycle_face_reweight_star S hS z.1 z.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (properCycle_face_reweight_continuous S).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)

/-- Resetting the face coordinates to a specified face point constructs the actual normal coordinate.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_star_normal_map (S : Finset ι) (hS : S.Nonempty)
    (p : ProperCycleFacePoint S) : C(ProperCycleStarPoint S, ProperCycleNormalPoint S hS p) where
  toFun w := ⟨properCycle_star_reweight_map S hS (w, p),
    properCycle_star_face_reweight S hS w p⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (properCycle_star_reweight_map S hS).continuous.comp
      (continuous_id.prodMk continuous_const)

/-- An actual positive barycentric star splits into its face coordinates and its actual normal fibre.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_barycentric_star_product (S : Finset ι) (hS : S.Nonempty)
    (p : ProperCycleFacePoint S) :
    ProperCycleStarPoint S ≃ₜ (ProperCycleFacePoint S × ProperCycleNormalPoint S hS p) where
  toFun w := (properCycle_star_face_map S hS w, properCycle_star_normal_map S hS p w)
  invFun z := properCycle_star_reweight_map S hS (z.2.val, z.1)
  left_inv := by
    intro w
    apply Subtype.ext
    change properCycle_face_reweight S (properCycle_face_reweight S w.val p)
      (properCycle_star_face S hS w) = w.val
    rw [properCycle_face_reweight_comp, properCycle_face_reweight_star_face]
  right_inv := by
    intro z
    apply Prod.ext
    · exact properCycle_star_face_reweight S hS z.2.val z.1
    · apply Subtype.ext
      apply Subtype.ext
      change properCycle_face_reweight S (properCycle_face_reweight S z.2.val.val z.1) p = z.2.val.val
      rw [properCycle_face_reweight_comp]
      exact (congrArg (fun q => properCycle_face_reweight S z.2.val.val q)
        z.2.property.symm).trans (properCycle_face_reweight_star_face S hS z.2.val)
  continuous_toFun := (properCycle_star_face_map S hS).continuous.prodMk
    (properCycle_star_normal_map S hS p).continuous
  continuous_invFun := (properCycle_star_reweight_map S hS).continuous.comp
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)

end HodgeLean.Foundations.QuotientDuality
