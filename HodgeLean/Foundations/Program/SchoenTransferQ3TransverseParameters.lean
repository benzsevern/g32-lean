import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentDomination
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeRegularSystem
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreeFlatParameters
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.RamifiedDegreePointLength
import HodgeLean.Adapters.IntersectionProductCMQuotient
import HodgeLean.Adapters.IntersectionProductCMStalk

/-! Actual regular stalk parameters for the retained transverse comparison. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing RingTheory.Sequence
open HodgeLean.Adapters AlgebraicGeometry.SingularCycles
namespace HodgeLean.Foundations.Program

/-- At a target prime of coheight k, a flat map from the actual source
pulls back a length-k regular system of target stalk parameters. -/
theorem s4_q3_exists_regular_stalk_parameters
    {X W : Over (Spec ↧ℂ)} [IsIntegral W.left] [Smooth W.hom]
    (q : X ⟶ W) [Flat q.left] (p : X.left) (k : ℕ)
    (hk : Order.coheight (q.left p) = k) :
    ∃ rs : List (W.left.presheaf.stalk (q.left p)),
      rs.length = k ∧ Ideal.ofList rs = maximalIdeal (W.left.presheaf.stalk (q.left p)) ∧
      IsRegular (W.left.presheaf.stalk (q.left p)) rs ∧
      IsRegular (X.left.presheaf.stalk p) (rs.map (q.left.stalkMap p).hom) := by
  let R := W.left.presheaf.stalk (q.left p)
  letI : IsRegularLocalRing R := a3c_isRegularLocalRing_stalk W (q.left p)
  have hdim : ringKrullDim R = k := by
    rw [ringKrullDim_stalk_eq_coheight]
    exact_mod_cast hk
  obtain ⟨rs, hlen, hgen, hdom, hreg⟩ := a3c_exists_regular_sop R
  have hlen' : rs.length = k := by
    rw [hdim] at hlen
    exact_mod_cast hlen
  have hr := regular_sequence_of_maximal_generators R k rs hdim hlen' hgen
  exact ⟨rs, hlen', hgen, hr, regular_stalk_parameters_pullback q.left p rs hr⟩

/-- The constructed transverse parameter quotient has exactly the retained
unreduced generic multiplicity, before any reduction or residue-degree factor. -/
theorem s4_q3_inverse_component_regular_parameter_length
    {X W : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    [IsNoetherian X.left] [IsNoetherian W.left] [IsIntegral W.left]
    [Smooth W.hom] [QuasiCompact W.hom]
    (q : X ⟶ W) [Flat q.left] (hq : IsOpenMap q.left)
    (k : ℕ) (x : W.left) (hx : Order.coheight x = k)
    (y : (ccm3_inverseIdeal q.left x).subscheme)
    (hy : closure ({y} : Set (ccm3_inverseIdeal q.left x).subscheme) ∈
      irreducibleComponents (ccm3_inverseIdeal q.left x).subscheme) :
    let p := (ccm3_inverseIdeal q.left x).subschemeι y
    ∃ rs : List (W.left.presheaf.stalk (q.left p)),
      rs.length = k ∧ Ideal.ofList rs = maximalIdeal (W.left.presheaf.stalk (q.left p)) ∧
      IsRegular (W.left.presheaf.stalk (q.left p)) rs ∧
      IsRegular (X.left.presheaf.stalk p) (rs.map (q.left.stalkMap p).hom) ∧
      (genericMultiplicity q.left x y (ccm3_genericLength_finite_pos q x y hy).2 : ℕ∞) =
        Module.length (X.left.presheaf.stalk p)
          (X.left.presheaf.stalk p ⧸ Ideal.ofList (rs.map (q.left.stalkMap p).hom)) := by
  let p := (ccm3_inverseIdeal q.left x).subschemeι y
  have hmap : q.left p = x := s4_q3_inverse_component_dominates q.left hq x y hy
  have hpco : Order.coheight (q.left p) = k := by rw [hmap]; exact hx
  obtain ⟨rs, hlen, hgen, hreg, hsource⟩ :=
    s4_q3_exists_regular_stalk_parameters q p k hpco
  refine ⟨rs, hlen, hgen, hreg, hsource, ?_⟩
  rw [← Ideal.map_ofList, hgen]
  exact genericMultiplicity_eq_pointFibreLength q.left x y hmap
    (ccm3_genericLength_finite_pos q x y hy).2

end HodgeLean.Foundations.Program
