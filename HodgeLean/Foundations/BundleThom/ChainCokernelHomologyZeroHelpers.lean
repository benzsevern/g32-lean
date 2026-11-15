import HodgeLean.Foundations.BundleThom.RelativeChainQuasiIsoHelpers

/-! # Degree-zero homology of actual chain cokernels

Surjectivity in degree-zero homology forces vanishing of the actual chain cokernel in that degree.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- A rational chain map surjective on degree-zero homology has an actual cokernel chain complex with zero degree-zero homology.
Source: Hatcher, Algebraic Topology, §2.1, right exactness of degree-zero homology. -/
theorem i1_chainCokernelHomologyZero_isZero
    {K L : ChainComplex (ModuleCat ℚ) ℕ} (f : K ⟶ L)
    [Epi (HomologicalComplex.homologyMap f 0)] : IsZero ((cokernel f).homology 0) := by
  haveI : Epi (HomologicalComplex.homologyMap (cokernel.π f) 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel (cokernel.π f) 0 (by
      intro j
      change ¬ j + 1 = 0
      omega)
  have hz : HomologicalComplex.homologyMap (cokernel.π f) 0 = 0 := by
    apply (cancel_epi (HomologicalComplex.homologyMap f 0)).mp
    rw [← HomologicalComplex.homologyMap_comp, cokernel.condition,
      HomologicalComplex.homologyMap_zero, comp_zero]
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (HomologicalComplex.homologyMap (cokernel.π f) 0)).mp
  rw [Category.comp_id, hz, comp_zero]

end HodgeLean.Foundations.BundleThom
