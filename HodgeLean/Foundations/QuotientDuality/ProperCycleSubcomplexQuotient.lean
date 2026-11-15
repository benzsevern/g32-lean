import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexRelativeMV

/-! # Literal relative chain quotients of simplicial subcomplexes -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual rational chain complex modulo a specified simplicial subcomplex.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient {K : SSet.{0}} (P : K.Subcomplex) : ChainCategory ℚ :=
  cokernel (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))

/-- Inclusion of simplicial subcomplexes gives the original map of relative chain quotients.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient_map {K : SSet.{0}} {P Q : K.Subcomplex} (h : P ≤ Q) :
    properCycle_subcomplex_quotient P ⟶ properCycle_subcomplex_quotient Q :=
  cokernel.map (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))
    (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ))
    (SSet.chainComplexMap (SSet.Subcomplex.homOfLE h) (ModuleCat.of ℚ ℚ)) (𝟙 _) (by
      rw [Category.comp_id]
      let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
      change C.map _ = C.map _ ≫ C.map _
      rw [← C.map_comp]
      rfl)

/-- The actual ambient projections commute with the original subcomplex quotient maps.
Source: Hatcher, Algebraic Topology, section 2.1, relative chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_quotient_projection {K : SSet.{0}} {P Q : K.Subcomplex} (h : P ≤ Q) :
    cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)) ≫
      properCycle_subcomplex_quotient_map h =
        cokernel.π (SSet.chainComplexMap Q.ι (ModuleCat.of ℚ ℚ)) := by
  dsimp [properCycle_subcomplex_quotient_map]
  simp

/-- Every degree of the literal subcomplex quotient projection has its original cokernel universal property.
Source: Mathlib, Algebra/Homology/HomologicalComplexLimits.lean, degreewise cokernels.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient_component_cokernel
    {K : SSet.{0}} (P : K.Subcomplex) (n : ℕ) :
    IsColimit (CokernelCofork.ofπ
      (f := (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)).f n)
      ((cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))).f n) (by
        exact congrArg (fun m => m.f n)
          (cokernel.condition (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))))) :=
  CokernelCofork.mapIsColimit _ (cokernelIsCokernel _)
    (HomologicalComplex.eval (ModuleCat ℚ) (ComplexShape.down ℕ) n)

/-- The original relative quotient maps compose along actual subcomplex inclusions.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_quotient_map_comp
    {K : SSet.{0}} {P Q R : K.Subcomplex} (hPQ : P ≤ Q) (hQR : Q ≤ R) :
    properCycle_subcomplex_quotient_map hPQ ≫ properCycle_subcomplex_quotient_map hQR =
      properCycle_subcomplex_quotient_map (hPQ.trans hQR) := by
  letI : Epi (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))) := inferInstance
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))).mp
  rw [← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_subcomplex_quotient_projection, properCycle_subcomplex_quotient_projection]

/-- The original quotient map for a reflexive subcomplex inclusion is the actual identity.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative chains.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_quotient_map_refl
    {K : SSet.{0}} (P : K.Subcomplex) :
    properCycle_subcomplex_quotient_map (le_refl P) = 𝟙 (properCycle_subcomplex_quotient P) := by
  letI : Epi (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ))) := inferInstance
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap P.ι (ModuleCat.of ℚ ℚ)))).mp
  rw [properCycle_subcomplex_quotient_projection]
  erw [Category.comp_id]

/-- Equal simplicial subcomplexes have canonically isomorphic original quotients through their literal inclusion maps.
Source: Hatcher, Algebraic Topology, section 2.1, functorial relative quotients.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_quotient_iso_of_eq
    {K : SSet.{0}} {P Q : K.Subcomplex} (h : P = Q) :
    properCycle_subcomplex_quotient P ≅ properCycle_subcomplex_quotient Q where
  hom := properCycle_subcomplex_quotient_map h.le
  inv := properCycle_subcomplex_quotient_map h.ge
  hom_inv_id := by
    rw [properCycle_subcomplex_quotient_map_comp]
    exact properCycle_subcomplex_quotient_map_refl P
  inv_hom_id := by
    rw [properCycle_subcomplex_quotient_map_comp]
    exact properCycle_subcomplex_quotient_map_refl Q

/-- Union with a fixed simplicial subcomplex distributes over the actual intersection pointwise on simplices.
Source: Hatcher, Algebraic Topology, section 2.2, small-chain subcomplex unions and intersections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_sup_inf
    {K : SSet.{0}} (A P Q : K.Subcomplex) :
    (A ⊔ P) ⊓ (A ⊔ Q) = A ⊔ (P ⊓ Q) := by
  ext n z
  change ((z ∈ A.obj n ∨ z ∈ P.obj n) ∧ (z ∈ A.obj n ∨ z ∈ Q.obj n)) ↔
    z ∈ A.obj n ∨ (z ∈ P.obj n ∧ z ∈ Q.obj n)
  tauto

end HodgeLean.Foundations.QuotientDuality
