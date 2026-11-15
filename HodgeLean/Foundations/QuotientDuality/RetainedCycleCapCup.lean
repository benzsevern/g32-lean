import HodgeLean.Foundations.QuotientDuality.RetainedCycleDerivedCapUnit

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual cap by a cup product is successive cap, retaining the source-degree identification. -/
theorem retained_chain_cap_cup (X : TopCat.{0}) (p q r : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) q) :
    Simplicial.cap ℚ (p + q) r (HodgeLean.Foundations.Singular.cupCochain X p q φ ψ) =
      (Simplicial.cap ℚ q r ψ).comp ((Simplicial.cap ℚ p (q + r) φ).comp
        ((SingularChainComplex ℚ X).XIsoOfEq (Nat.add_assoc p q r)).hom.hom) := by
  apply LinearMap.ext
  intro c
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro χ
  have h := LinearMap.congr_fun
    (HodgeLean.Foundations.Singular.cupCochain_assoc X p q r φ ψ χ) c
  change χ (Simplicial.cap ℚ (p + q) r
      (HodgeLean.Foundations.Singular.cupCochain X p q φ ψ) c) =
    χ (Simplicial.cap ℚ q r ψ (Simplicial.cap ℚ p (q + r) φ
      (((SingularChainComplex ℚ X).XIsoOfEq (Nat.add_assoc p q r)).hom.hom c))) at h
  rw [map_sub]
  exact sub_eq_zero.mpr h

/-- Actual ambient cup-cap composition descends to the relative-chain quotient. -/
theorem retained_relative_chain_cap_cup (P : TopPair.{0}) (p q r : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) p)
    (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj P.fst) q) :
    retainedRelativeAmbientCapHom P (p + q) r
        (HodgeLean.Foundations.Singular.cupCochain P.fst p q φ ψ) =
      (((relativeChainFunctor ℚ).obj P).XIsoOfEq (Nat.add_assoc p q r)).hom ≫
        retainedRelativeAmbientCapHom P p (q + r) φ ≫ retainedRelativeAmbientCapHom P q r ψ := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (p + q + r))
  change (relativeChainProjection ℚ P).f (p + q + r) ≫ _ =
    (relativeChainProjection ℚ P).f (p + q + r) ≫ _
  have hc : Simplicial.capHom ℚ (p + q) r
        (HodgeLean.Foundations.Singular.cupCochain P.fst p q φ ψ) =
      ((SingularChainComplex ℚ P.fst).XIsoOfEq (Nat.add_assoc p q r)).hom ≫
        Simplicial.capHom ℚ p (q + r) φ ≫ Simplicial.capHom ℚ q r ψ :=
    ModuleCat.hom_ext (retained_chain_cap_cup P.fst p q r φ ψ)
  simp only [← Category.assoc]
  rw [HomologicalComplex.XIsoOfEq_hom_naturality]
  simp only [Category.assoc]
  rw [retained_relative_projection_ambient_cap,
    retained_relative_projection_ambient_cap_assoc, retained_relative_projection_ambient_cap]
  rw [hc]
  simp only [Category.assoc]

/-- Successive actual cap operations give cup-cap composition on chain presheaves. -/
theorem retained_chain_presheaf_cap_cup (X : TopCat.{0}) (p q r : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) q) :
    retainedChainPresheafAmbientCap X (p + q) r
        (HodgeLean.Foundations.Singular.cupCochain X p q φ ψ) =
      ((singularChainPresheafComplex ℚ X).XIsoOfEq (Nat.add_assoc p q r)).hom ≫
        retainedChainPresheafAmbientCap X p (q + r) φ ≫ retainedChainPresheafAmbientCap X q r ψ := by
  apply NatTrans.ext
  funext U
  have he (a b : ℕ) (hab : a = b) :
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (U.unop : Set X)ᶜ)).XIsoOfEq hab).hom) =
      ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom.app U := by
    subst b
    rfl
  have h := congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_chain_cap_cup (TopPair.ofSubset (U.unop : Set X)ᶜ) p q r φ ψ)
  simp only [Functor.map_comp] at h
  rw [he] at h
  exact h

/-- Sheafification preserves the actual cup-cap composition formula. -/
theorem retained_chain_sheaf_cap_cup (X : TopCat.{0}) (p q r : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p)
    (ψ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) q) :
    retainedChainSheafAmbientCap X (p + q) r
        (HodgeLean.Foundations.Singular.cupCochain X p q φ ψ) =
      ((singularChainSheafComplex ℚ X).XIsoOfEq (Nat.add_assoc p q r)).hom ≫
        retainedChainSheafAmbientCap X p (q + r) φ ≫ retainedChainSheafAmbientCap X q r ψ := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  have he (a b : ℕ) (hab : a = b) :
      F.map ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom =
        ((singularChainSheafComplex ℚ X).XIsoOfEq hab).hom := by
    subst b
    exact F.map_id _
  have h := congrArg F.map (retained_chain_presheaf_cap_cup X p q r φ ψ)
  simp only [Functor.map_comp] at h
  rw [he] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
