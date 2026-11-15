import HodgeLean.Foundations.Program.PathCoverFamilyRetained

/-! # B6-5: the retained cover family at an admissible centre (proof)

The auxiliary of `PathCoverFamilyExists.lean`, from the construction of lane `cfp-2`.
HC no distance; AV milestone no distance.
-/

noncomputable section
open Set Manifold Filter Topology HodgeLean.Papers
open scoped ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b65z_family_exists_aux (c : Fin 10 → ℂ) (hc : c ∈ b6_chart) (g : Fin 13 → b4b_Group)
    (hg : g32h_Nielsen (fun i ↦ b4b_toMatrix (g i))) :
    Nonempty (b65z_SharedFamily c g) :=
  b65z_family_construction c hc g hg

end HodgeLean.Foundations.Program
