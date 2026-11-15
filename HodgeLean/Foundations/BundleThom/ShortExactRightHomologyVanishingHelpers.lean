import HodgeLean.Foundations.BundleThom.RelativeChainQuasiIsoHelpers

/-! # Right-hand homology vanishing in actual rational chain sequences

The boundary map of the actual short exact sequence supplies the successor-degree comparison.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- Vanishing of middle degree-zero homology forces right degree-zero homology to vanish in an actual short exact chain sequence.
Source: Hatcher, Algebraic Topology, §2.1, right exactness of degree-zero homology. -/
theorem i1_shortExactRightHomologyZero_isZero
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact)
    (hm : IsZero (S.X₂.homology 0)) : IsZero (S.X₃.homology 0) := by
  haveI := hS.epi_g
  haveI : Epi (HomologicalComplex.homologyMap S.g 0) :=
    HomologicalComplex.epi_homologyMap_of_epi_of_not_rel S.g 0 (by
      intro j
      change ¬ j + 1 = 0
      omega)
  have hg : HomologicalComplex.homologyMap S.g 0 = 0 := hm.eq_zero_of_src _
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_epi (HomologicalComplex.homologyMap S.g 0)).mp
  rw [Category.comp_id, hg, comp_zero]

/-- Vanishing of middle successor-degree and left preceding-degree homology forces right successor-degree homology to vanish.
Source: Hatcher, Algebraic Topology, §2.1, the actual homology sequence. -/
theorem i1_shortExactRightHomologySuccessor_isZero
    (S : ShortComplex (ChainComplex (ModuleCat ℚ) ℕ)) (hS : S.ShortExact) (n : ℕ)
    (hm : IsZero (S.X₂.homology (n + 1))) (hl : IsZero (S.X₁.homology n)) :
    IsZero (S.X₃.homology (n + 1)) :=
  (hS.homology_exact₃ (n + 1) n (by rfl)).isZero_of_both_isZero hm hl

end HodgeLean.Foundations.BundleThom
