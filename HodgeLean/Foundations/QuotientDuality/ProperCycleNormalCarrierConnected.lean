import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricGoodCover
import HodgeLean.Foundations.QuotientDuality.ProperCycleBarycentricMarkedChart

/-! # Connected original normal fibres of actual finite face stars
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual normal fibre in the constructed barycentric face product is path connected, as the continuous image of its actual contractible open star.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star contractions.
HC no distance; AV milestone no distance. -/
lemma properCycle_normal_carrier_path_connected
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (hSF : S ∈ F) :
    PathConnectedSpace
      {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0} := by
  let A := {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
    ∀ i ∈ S, 0 < w.val.val i}
  let w : A := ⟨⟨p.val, S, hSF, p.property.2⟩, p.property.1⟩
  letI : ContractibleSpace A := properCycle_barycentric_star_contractible F S hS ⟨w⟩
  let j : S := ⟨hS.choose, hS.choose_spec⟩
  let e := properCycle_barycentric_vector_product F S hS p j
  have hs : Function.Surjective (fun a : A => (e a).2) := by
    intro v
    exact ⟨e.symm (0, v), congrArg Prod.snd (e.apply_symm_apply (0, v))⟩
  exact hs.pathConnectedSpace (continuous_snd.comp e.continuous)

/-- The original normal fibre has one-dimensional degree-zero rational homology.
Source: Hatcher, Algebraic Topology, section 2.1, path components and degree-zero homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_normal_carrier_homology_zero_dimension
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (hSF : S ∈ F) :
    Module.finrank ℚ (Homology ℚ (TopCat.of
      {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}) 0) = 1 := by
  let Y := {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}
  letI : PathConnectedSpace Y := properCycle_normal_carrier_path_connected F S hS p hSF
  let e := (asIso (TopCat.singularHomology₀ε (TopCat.of Y) (ModuleCat.of ℚ ℚ))).toLinearEquiv
  exact e.finrank_eq.trans (Module.finrank_self ℚ)

/-- The actual barycentric normal fibre is contractible by projecting the contraction of its actual open star.
Source: Munkres, Elements of Algebraic Topology, section 2, barycentric star contractions and product coordinates.
HC no distance; AV milestone no distance. -/
lemma properCycle_normal_carrier_contractible
    {ι : Type} [Fintype ι] [DecidableEq ι] (F : Set (Finset ι))
    (S : Finset ι) (hS : S.Nonempty) (p : ProperCycleFacePoint S) (hSF : S ∈ F) :
    ContractibleSpace
      {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0} := by
  let A := {w : {u : stdSimplex ℝ ι | ∃ s ∈ F, ∀ i ∉ s, u.val i = 0} |
    ∀ i ∈ S, 0 < w.val.val i}
  let Y := {v : ProperCycleNormalPoint S hS p | ∃ s ∈ F, ∀ i ∉ s, v.val.val.val i = 0}
  let w : A := ⟨⟨p.val, S, hSF, p.property.2⟩, p.property.1⟩
  letI : ContractibleSpace A := properCycle_barycentric_star_contractible F S hS ⟨w⟩
  let j : S := ⟨hS.choose, hS.choose_spec⟩
  let e := properCycle_barycentric_vector_product F S hS p j
  letI : ContractibleSpace (properCycle_log_tangent j × Y) := e.symm.contractibleSpace
  obtain ⟨z, ⟨H⟩⟩ := id_nullhomotopic (properCycle_log_tangent j × Y)
  apply (contractible_iff_id_nullhomotopic Y).mpr
  refine ⟨z.2, ⟨{
    toFun := fun ty => (H (ty.1, (0, ty.2))).2
    continuous_toFun := by fun_prop
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro y
    exact congrArg Prod.snd (H.map_zero_left (0, y))
  · intro y
    exact congrArg Prod.snd (H.map_one_left (0, y))

end HodgeLean.Foundations.QuotientDuality
