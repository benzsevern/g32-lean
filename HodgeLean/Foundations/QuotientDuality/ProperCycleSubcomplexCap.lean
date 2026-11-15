import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexCapLift

/-! # The actual descended cap between simplicial subcomplex quotients -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original cap product descends from the quotient by the union of two subcomplexes to the quotient by the second.
Source: Hatcher, Algebraic Topology, section 3.3, the relative cap product.
HC no distance; AV milestone no distance. -/
def properCycle_subcomplex_cap_hom
    {K : SSet.{0}} (A T : K.Subcomplex) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0) :
    (properCycle_subcomplex_quotient (A ⊔ T)).X (p + q) ⟶
      (properCycle_subcomplex_quotient T).X q :=
  (properCycle_subcomplex_quotient_component_cokernel (A ⊔ T) (p + q)).desc
    (CokernelCofork.ofπ
      (AlgebraicTopology.Simplicial.capHom ℚ p q φ ≫
        (cokernel.π (SSet.chainComplexMap T.ι (ModuleCat.of ℚ ℚ))).f q)
      (properCycle_subcomplex_cap_subspace_zero A T p q φ hA))

/-- Capping an original projected chain equals the original cap followed by the literal target quotient projection.
Source: Hatcher, Algebraic Topology, section 3.3, relative cap representatives.
HC no distance; AV milestone no distance. -/
lemma properCycle_subcomplex_cap_projection
    {K : SSet.{0}} (A T : K.Subcomplex) (p q : ℕ)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0) :
    (cokernel.π (SSet.chainComplexMap (A ⊔ T).ι (ModuleCat.of ℚ ℚ))).f (p + q) ≫
        properCycle_subcomplex_cap_hom A T p q φ hA =
      AlgebraicTopology.Simplicial.capHom ℚ p q φ ≫
        (cokernel.π (SSet.chainComplexMap T.ι (ModuleCat.of ℚ ℚ))).f q := by
  exact (Cofork.IsColimit.π_desc
    (properCycle_subcomplex_quotient_component_cokernel (A ⊔ T) (p + q))
    (t := CokernelCofork.ofπ _ (properCycle_subcomplex_cap_subspace_zero A T p q φ hA))).trans
      (CokernelCofork.π_ofπ _ _ _)

/-- An original even cocycle vanishing on the first subcomplex gives an actual cap chain map between the corresponding relative quotients.
Source: Hatcher, Algebraic Topology, section 3.3, the cap boundary formula.
HC no distance; AV milestone no distance. -/
def properCycle_even_subcomplex_cap_chain_map
    {K : SSet.{0}} (A T : K.Subcomplex) (p : ℕ) (hp : Even p)
    (φ : AlgebraicTopology.Simplicial.Cochain ℚ K p)
    (hA : AlgebraicTopology.Simplicial.cochainMap ℚ A.ι p φ = 0)
    (hφ : AlgebraicTopology.Simplicial.coboundary ℚ p φ = 0) :
    (properCycle_subcomplex_quotient (A ⊔ T)).restriction (properCycle_cap_tail_embedding p) ⟶
      properCycle_subcomplex_quotient T where
  f q := properCycle_subcomplex_cap_hom A T p q φ hA
  comm' i j hij := by
    have hij' : j + 1 = i := hij
    subst i
    let C := K.chainComplex (ModuleCat.of ℚ ℚ)
    let πS := cokernel.π (SSet.chainComplexMap (A ⊔ T).ι (ModuleCat.of ℚ ℚ))
    let πT := cokernel.π (SSet.chainComplexMap T.ι (ModuleCat.of ℚ ℚ))
    have hcap : AlgebraicTopology.Simplicial.capHom ℚ p (j + 1) φ ≫ C.d (j + 1) j =
        C.d (p + (j + 1)) (p + j) ≫ AlgebraicTopology.Simplicial.capHom ℚ p j φ := by
      apply ModuleCat.hom_ext
      ext c
      have h := AlgebraicTopology.Simplicial.boundary_cap_eq_of_cocycle ℚ p j φ hφ c
      rw [hp.neg_one_pow, one_smul] at h
      exact h
    letI : Epi (πS.f (p + (j + 1))) :=
      Cofork.IsColimit.epi (properCycle_subcomplex_quotient_component_cokernel (A ⊔ T) (p + (j + 1)))
    apply (cancel_epi (πS.f (p + (j + 1)))).mp
    change πS.f (p + (j + 1)) ≫
        (properCycle_subcomplex_cap_hom A T p (j + 1) φ hA ≫
          (properCycle_subcomplex_quotient T).d (j + 1) j) =
      πS.f (p + (j + 1)) ≫
        ((properCycle_subcomplex_quotient (A ⊔ T)).d (p + (j + 1)) (p + j) ≫
          properCycle_subcomplex_cap_hom A T p j φ hA)
    calc
      _ = AlgebraicTopology.Simplicial.capHom ℚ p (j + 1) φ ≫
          πT.f (j + 1) ≫ (properCycle_subcomplex_quotient T).d (j + 1) j := by
        rw [← Category.assoc, properCycle_subcomplex_cap_projection, Category.assoc]
      _ = AlgebraicTopology.Simplicial.capHom ℚ p (j + 1) φ ≫ C.d (j + 1) j ≫ πT.f j := by
        exact congrArg (fun m => AlgebraicTopology.Simplicial.capHom ℚ p (j + 1) φ ≫ m)
          (πT.comm (j + 1) j)
      _ = C.d (p + (j + 1)) (p + j) ≫ AlgebraicTopology.Simplicial.capHom ℚ p j φ ≫ πT.f j := by
        rw [← Category.assoc, hcap, Category.assoc]
      _ = C.d (p + (j + 1)) (p + j) ≫ πS.f (p + j) ≫
          properCycle_subcomplex_cap_hom A T p j φ hA := by
        rw [← properCycle_subcomplex_cap_projection A T p j φ hA]
      _ = _ := by
        exact congrArg (fun m => m ≫ properCycle_subcomplex_cap_hom A T p j φ hA)
          (πS.comm (p + (j + 1)) (p + j)).symm

end HodgeLean.Foundations.QuotientDuality
