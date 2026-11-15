import HodgeLean.Foundations.QuotientDuality.RetainedCycleCohomologyDerivedCap
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual cap by the constant unit is the canonical degree-zero chain identification. -/
theorem retained_chain_cap_unit (X : TopCat.{0}) (q : ℕ) :
    Simplicial.cap ℚ 0 q (HodgeLean.Foundations.Singular.unitCochain X) =
      ((SingularChainComplex ℚ X).XIsoOfEq (Nat.zero_add q)).hom.hom := by
  apply LinearMap.ext
  intro c
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro ψ
  have h := LinearMap.congr_fun
    (HodgeLean.Foundations.Simplicial.one_cupCochain (TopCat.toSSet.obj X) q ψ) c
  change ψ (Simplicial.cap ℚ 0 q (HodgeLean.Foundations.Singular.unitCochain X) c) =
    ψ (((SingularChainComplex ℚ X).XIsoOfEq (Nat.zero_add q)).hom.hom c) at h
  rw [map_sub]
  exact sub_eq_zero.mpr h

/-- Actual cap by the ambient unit is the canonical relative-chain degree identification. -/
theorem retained_relative_chain_cap_unit (P : TopPair.{0}) (q : ℕ) :
    retainedRelativeAmbientCapHom P 0 q (HodgeLean.Foundations.Singular.unitCochain P.fst) =
      (((relativeChainFunctor ℚ).obj P).XIsoOfEq (Nat.zero_add q)).hom := by
  apply Cofork.IsColimit.hom_ext
    (relativeChainProjectionComponentIsCokernelForCap ℚ P (0 + q))
  change (relativeChainProjection ℚ P).f (0 + q) ≫ _ =
    (relativeChainProjection ℚ P).f (0 + q) ≫ _
  have hc : Simplicial.capHom ℚ 0 q (HodgeLean.Foundations.Singular.unitCochain P.fst) =
      ((SingularChainComplex ℚ P.fst).XIsoOfEq (Nat.zero_add q)).hom :=
    ModuleCat.hom_ext (retained_chain_cap_unit P.fst q)
  rw [retained_relative_projection_ambient_cap, hc]
  exact (HomologicalComplex.XIsoOfEq_hom_naturality (relativeChainProjection ℚ P)
    (Nat.zero_add q)).symm

/-- The actual unit cap on chain presheaves is the canonical degree identification. -/
theorem retained_chain_presheaf_cap_unit (X : TopCat.{0}) (q : ℕ) :
    retainedChainPresheafAmbientCap X 0 q (HodgeLean.Foundations.Singular.unitCochain X) =
      ((singularChainPresheafComplex ℚ X).XIsoOfEq (Nat.zero_add q)).hom := by
  apply NatTrans.ext
  funext U
  have he (a b : ℕ) (hab : a = b) :
      (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (U.unop : Set X)ᶜ)).XIsoOfEq hab).hom) =
      ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom.app U := by
    subst b
    rfl
  have h := congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_chain_cap_unit (TopPair.ofSubset (U.unop : Set X)ᶜ) q)
  rw [he] at h
  exact h

/-- Sheafification retains the canonical unit cap identification. -/
theorem retained_chain_sheaf_cap_unit (X : TopCat.{0}) (q : ℕ) :
    retainedChainSheafAmbientCap X 0 q (HodgeLean.Foundations.Singular.unitCochain X) =
      ((singularChainSheafComplex ℚ X).XIsoOfEq (Nat.zero_add q)).hom := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  have he (a b : ℕ) (hab : a = b) :
      F.map ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom =
        ((singularChainSheafComplex ℚ X).XIsoOfEq hab).hom := by
    subst b
    exact F.map_id _
  have h := congrArg F.map (retained_chain_presheaf_cap_unit X q)
  rw [he] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
