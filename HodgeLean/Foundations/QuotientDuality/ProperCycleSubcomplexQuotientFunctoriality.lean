import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexQuotient

/-! # Actual relative quotient morphisms under maps of ambient simplicial sets
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An ambient simplicial map preserving the specified subcomplexes induces the original morphism on their actual relative chain quotients.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains; Mathlib, SSet.Subcomplex.fromPreimage.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient_morphism
    {K L : SSet.{0}} (f : K ⟶ L) (P : K.Subcomplex) (Q : L.Subcomplex)
    (h : P ≤ Q.preimage f) : properCycle_subcomplex_quotient P ⟶ properCycle_subcomplex_quotient Q := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let g := SSet.Subcomplex.homOfLE h ≫ Q.fromPreimage f
  have hg : g ≫ Q.ι = P.ι ≫ f := by
    dsimp only [g]
    rw [Category.assoc, SSet.Subcomplex.fromPreimage_ι, ← Category.assoc,
      SSet.Subcomplex.homOfLE_ι]
  exact cokernel.map (C.map P.ι) (C.map Q.ι) (C.map g) (C.map f) (by
    rw [← C.map_comp, ← C.map_comp, hg])

/-- Actual ambient quotient projections commute with the induced map of relative subcomplex quotients.
Source: Mathlib, CategoryTheory.Limits.cokernel.π_desc.
HC no distance; AV milestone no distance. -/
theorem properCycle_subcomplex_quotient_morphism_projection
    {K L : SSet.{0}} (f : K ⟶ L) (P : K.Subcomplex) (Q : L.Subcomplex)
    (h : P ≤ Q.preimage f) :
    cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)) ≫
        properCycle_subcomplex_quotient_morphism f P Q h =
      SSet.chainComplexMap f (ModuleCat.of ℚ ℚ) ≫
        cokernel.π (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ)) := by
  dsimp only [properCycle_subcomplex_quotient_morphism, id_eq, cokernel.map]
  exact cokernel.π_desc _ _ _

/-- The original quotient inclusions commute with the actual relative quotient map of a fixed ambient simplicial map.
Source: properCycle_subcomplex_quotient_projection; properCycle_subcomplex_quotient_morphism_projection.
HC no distance; AV milestone no distance. -/
theorem properCycle_subcomplex_quotient_morphism_inclusion
    {K L : SSet.{0}} (f : K ⟶ L) {P P' : K.Subcomplex} {Q Q' : L.Subcomplex}
    (hP : P ≤ P') (hQ : Q ≤ Q') (h : P ≤ Q.preimage f) (h' : P' ≤ Q'.preimage f) :
    properCycle_subcomplex_quotient_map hP ≫ properCycle_subcomplex_quotient_morphism f P' Q' h' =
      properCycle_subcomplex_quotient_morphism f P Q h ≫ properCycle_subcomplex_quotient_map hQ := by
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))).mp
  rw [← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_subcomplex_quotient_morphism_projection, ← Category.assoc,
    properCycle_subcomplex_quotient_morphism_projection, Category.assoc,
    properCycle_subcomplex_quotient_projection]

end HodgeLean.Foundations.QuotientDuality
