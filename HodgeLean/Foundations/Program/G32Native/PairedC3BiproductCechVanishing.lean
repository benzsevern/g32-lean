import HodgeLean.Ported.NYLL.SchemeTheory.Cohomology.Cech.FiniteFreeTensorVanishing

/-! # Native Cech vanishing for finite biproducts -/
noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open Scheme.Modules
attribute [local instance] Abelian.hasFiniteBiproducts

variable {R : Type u} [CommRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) (J : Type u) [Finite J] (L : J → X.Modules)
  (K : X.OrderedAffineCover)

local notation "F" => toOModulePresheaf f
  (⨁ L)
local notation "G" j => toOModulePresheaf f (L j)

/-- Sections of a native finite biproduct retain their original base action. -/
def pairedC3BiproductSectionsEquiv (U : X.Opens) :
    sectionModuleOverBase f (⨁ L) U ≃ₗ[R]
      (∀ j, sectionModuleOverBase f (L j) U) := by
  let e := biproductSectionsEquiv J L U
  refine { e.toAddEquiv with map_smul' := ?_ }
  intro a x
  exact e.map_smul ((f.constToPresheaf.app (Opposite.op U)).hom a) x

/-- The section comparison commutes with each original restriction. -/
theorem paired_c3_biproduct_sections_restrict (U : X.Opens) {V : X.Opens}
    (h : V ≤ U) (x : sectionModuleOverBase f (⨁ L) U) (j : J) :
    pairedC3BiproductSectionsEquiv f J L V
      (sectionRestrictionOverBase f (⨁ L) h x) j =
    sectionRestrictionOverBase f (L j) h
      (pairedC3BiproductSectionsEquiv f J L U x j) :=
  biproductSectionsEquiv_restriction J L U h x j

/-- The cochains of the actual finite biproduct are the
tuples of the original component cochains, using the actual section comparison. -/
def pairedC3BiproductCochainEquiv (q : ℕ) :
    (F).cochain K q ≃ₗ[R] (∀ j, (G j).cochain K q) where
  toFun c j s := pairedC3BiproductSectionsEquiv f J L (K.inter s) (c s) j
  invFun c s := (pairedC3BiproductSectionsEquiv f J L (K.inter s)).symm (fun j => c j s)
  left_inv c := by
    funext s
    exact (pairedC3BiproductSectionsEquiv f J L (K.inter s)).symm_apply_apply (c s)
  right_inv c := by
    funext j s
    exact congrFun ((pairedC3BiproductSectionsEquiv f J L (K.inter s)).apply_symm_apply
      (fun j => c j s)) j
  map_add' c c' := by
    funext j s
    exact congrFun ((pairedC3BiproductSectionsEquiv f J L (K.inter s)).map_add (c s) (c' s)) j
  map_smul' a c := by
    funext j s
    exact congrFun ((pairedC3BiproductSectionsEquiv f J L (K.inter s)).map_smul a (c s)) j

/-- Each coordinate retains the original intersection and section. -/
theorem pairedC3BiproductCochainEquiv_apply (q : ℕ) (c : (F).cochain K q)
    (j : J) (s : K.Idx q) :
    pairedC3BiproductCochainEquiv f J L K q c j s =
      pairedC3BiproductSectionsEquiv f J L (K.inter s) (c s) j := rfl

/-- The original alternating Čech differential is the original
differential on each coordinate of the constructed comparison. -/
theorem pairedC3BiproductCochainEquiv_d (q : ℕ) (c : (F).cochain K q) :
    pairedC3BiproductCochainEquiv f J L K (q + 1) ((F).d K q c) =
      fun j => (G j).d K q (pairedC3BiproductCochainEquiv f J L K q c j) := by
  funext j s
  let π : (F).obj (K.inter s) →ₗ[R] (G j).obj (K.inter s) :=
    (LinearMap.proj j).comp (pairedC3BiproductSectionsEquiv f J L (K.inter s)).toLinearMap
  change π ((F).d K q c s) =
    (G j).d K q (pairedC3BiproductCochainEquiv f J L K q c j) s
  rw [OModulePresheaf.d_apply, OModulePresheaf.d_apply]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_zsmul]
  exact congrArg (fun x : (G j).obj (K.inter s) => ((-1 : ℤ) ^ (k : ℕ)) • x)
    (paired_c3_biproduct_sections_restrict f J L (K.inter (K.face s k))
      (K.inter_le_inter_face s k) (c (K.face s k)) j)

/-- Vanishing in a positive degree is preserved by taking the
actual finite biproduct. The preceding boundary is constructed
from the original coordinate boundaries and the inverse cochain comparison. -/
theorem paired_c3_biproduct_vanishing (q : ℕ) [∀ j, Subsingleton ((G j).HSucc K q)] :
    Subsingleton ((F).HSucc K q) := by
  rw [Submodule.Quotient.subsingleton_iff, Submodule.eq_top_iff']
  intro z
  let E (r : ℕ) := pairedC3BiproductCochainEquiv f J L K r
  have hcycle (j : J) : (G j).d K (q + 1) (E (q + 1) z.val j) = 0 := by
    calc
      (G j).d K (q + 1) (E (q + 1) z.val j) =
          E (q + 2) ((F).d K (q + 1) z.val) j :=
        (congrFun (pairedC3BiproductCochainEquiv_d f J L K (q + 1) z.val) j).symm
      _ = E (q + 2) 0 j :=
        congrArg (fun x : (F).cochain K (q + 2) => E (q + 2) x j) z.property
      _ = 0 := congrFun (map_zero (E (q + 2))) j
  have hboundary (j : J) : ∃ y : (G j).cochain K q, (G j).d K q y = E (q + 1) z.val j := by
    let w : LinearMap.ker ((G j).d K (q + 1)) := ⟨E (q + 1) z.val j, hcycle j⟩
    have hw : (Submodule.Quotient.mk w : (G j).HSucc K q) = 0 := Subsingleton.elim _ _
    exact (Submodule.Quotient.mk_eq_zero
      ((LinearMap.range ((G j).d K q)).comap (LinearMap.ker ((G j).d K (q + 1))).subtype)).mp hw
  choose y hy using hboundary
  change z.val ∈ LinearMap.range ((F).d K q)
  refine ⟨(E q).symm y, ?_⟩
  apply (E (q + 1)).injective
  calc
    E (q + 1) ((F).d K q ((E q).symm y)) =
        fun j => (G j).d K q (E q ((E q).symm y) j) :=
      pairedC3BiproductCochainEquiv_d f J L K q ((E q).symm y)
    _ = fun j => (G j).d K q (y j) :=
      congrArg (fun x : ∀ j, (G j).cochain K q => fun j => (G j).d K q (x j))
        ((E q).apply_symm_apply y)
    _ = E (q + 1) z.val := funext hy

#print axioms paired_c3_biproduct_vanishing
end HodgeLean.Foundations.Program.G32Native
