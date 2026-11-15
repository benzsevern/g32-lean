import HodgeLean.Foundations.BundleThom.ChainCoverHomologyLiftingHelpers

/-! # Homology vanishing on actual chain biproducts

The two canonical inclusions and projections retain the chain-level decomposition of the identity.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory Limits
namespace HodgeLean.Foundations.BundleThom

/-- If both rational chain complexes have zero homology in a degree, their actual biproduct has zero homology there.
Source: Hatcher, Algebraic Topology, §2.1, additivity of homology. -/
theorem i1_biprodHomology_isZero (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (hK : IsZero (K.homology n)) (hL : IsZero (L.homology n)) :
    IsZero ((K ⊞ L).homology n) := by
  have hl : HomologicalComplex.homologyMap (biprod.inl : K ⟶ K ⊞ L) n = 0 :=
    hK.eq_zero_of_src _
  have hr : HomologicalComplex.homologyMap (biprod.inr : L ⟶ K ⊞ L) n = 0 :=
    hL.eq_zero_of_src _
  have h := congrArg (fun f : K ⊞ L ⟶ K ⊞ L => HomologicalComplex.homologyMap f n)
    (biprod.total (X := K) (Y := L))
  rw [HomologicalComplex.homologyMap_add, HomologicalComplex.homologyMap_comp,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_id,
    hl, hr, comp_zero, comp_zero, add_zero] at h
  exact (IsZero.iff_id_eq_zero _).mpr h.symm

end HodgeLean.Foundations.BundleThom
