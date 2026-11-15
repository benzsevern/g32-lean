import HodgeLean.Foundations.QuotientDuality.RetainedCycleAmbientCapCoboundary
import HodgeLean.Foundations.QuotientDuality.RetainedCycleCapBoundaryHomotopy

noncomputable section
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular TopologicalSpace Opposite
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace HodgeLean.Foundations.QuotientDuality

/-- Cap by an ambient coboundary retains its actual homotopy formula on chain presheaves. -/
theorem retained_chain_presheaf_cap_coboundary (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    let K := singularChainPresheafComplex ℚ X
    (K.XIsoOfEq (by omega : p + q + 1 = p + 1 + q)).hom ≫
        retainedChainPresheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ) =
      (show K.X (p + q + 1) ⟶ K.X q from
        K.d (p + q + 1) (p + q) ≫ retainedChainPresheafAmbientCap X p q φ) -
        (-1 : ℤ) ^ p •
          (show K.X (p + q + 1) ⟶ K.X q from
            retainedChainPresheafAmbientCap X p (q + 1) φ ≫ K.d (q + 1) q) := by
  dsimp only
  apply NatTrans.ext
  funext U
  have he (a b : ℕ) (hab : a = b) :
      ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom.app U =
        (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
          ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset (U.unop : Set X)ᶜ)).XIsoOfEq hab).hom) := by
    subst b
    rfl
  have hh := congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
    (retained_relative_cap_coboundary_middle (TopPair.ofSubset (U.unop : Set X)ᶜ) p q φ)
  rw [retainedRelativeCapCoboundaryShortComplex, ShortComplex.comp_τ₂,
    relativeReassocShortComplexIso_hom_τ₂, retained_relative_cap_short_complex_middle] at hh
  simp only [Functor.map_comp, Functor.map_sub, Functor.map_zsmul] at hh
  erw [NatTrans.comp_app, NatTrans.app_sub, NatTrans.app_zsmul,
    NatTrans.comp_app, NatTrans.comp_app]
  rw [he]
  simp only [retainedChainPresheafAmbientCap, singularChainPresheafComplex_d,
    singularChainBoundary]
  simp only [relativeReassocChain, relativeBoundary] at hh
  exact hh

/-- Exact sheafification preserves the actual ambient coboundary cap homotopy. -/
theorem retained_chain_sheaf_cap_coboundary (X : TopCat.{0}) (p q : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    let K := singularChainSheafComplex ℚ X
    (K.XIsoOfEq (by omega : p + q + 1 = p + 1 + q)).hom ≫
        retainedChainSheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ) =
      (show K.X (p + q + 1) ⟶ K.X q from
        K.d (p + q + 1) (p + q) ≫ retainedChainSheafAmbientCap X p q φ) -
        (-1 : ℤ) ^ p • (show K.X (p + q + 1) ⟶ K.X q from
          retainedChainSheafAmbientCap X p (q + 1) φ ≫ K.d (q + 1) q) := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat
  have h := congrArg F.map (retained_chain_presheaf_cap_coboundary X p q φ)
  dsimp only at h ⊢
  have he (a b : ℕ) (hab : a = b) :
      F.map ((singularChainPresheafComplex ℚ X).XIsoOfEq hab).hom =
        ((singularChainSheafComplex ℚ X).XIsoOfEq hab).hom := by
    subst b
    exact F.map_id _
  rw [Functor.map_comp, Functor.map_sub, Functor.map_zsmul,
    Functor.map_comp, Functor.map_comp, he] at h
  exact h

/-- The homogeneous differential terms are the signed actual sheaf cap by the coboundary. -/
theorem retained_chain_sheaf_cap_coboundary_differential_terms
    (X : TopCat.{0}) (p q : ℕ) (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    let K := singularChainSheafComplex ℚ X
    (show K.X (p + 1 + q) ⟶ K.X q from
      eqToHom (by congr 1; omega : K.X (p + 1 + q) = K.X (p + (q + 1))) ≫
        retainedChainSheafAmbientCap X p (q + 1) φ ≫ K.d (q + 1) q) +
      (-1 : ℤ) ^ (p + 1) • (show K.X (p + 1 + q) ⟶ K.X q from
        K.d (p + 1 + q) (p + q) ≫ retainedChainSheafAmbientCap X p q φ) =
      (-1 : ℤ) ^ (p + 1) •
        retainedChainSheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ) := by
  let K := singularChainSheafComplex ℚ X
  have ht := congrArg
    (fun f => (K.XIsoOfEq (by omega : p + 1 + q = p + q + 1)).hom ≫ f)
    (retained_chain_sheaf_cap_coboundary X p q φ)
  dsimp only [K] at ht ⊢
  simp only [Preadditive.comp_sub, Preadditive.comp_zsmul, ← Category.assoc,
    HomologicalComplex.XIsoOfEq_hom_comp_XIsoOfEq_hom,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    HomologicalComplex.XIsoOfEq_hom_comp_d] at ht
  rw [ht]
  simp only [smul_sub, smul_smul, pow_succ, mul_neg_one, neg_smul,
    ← pow_add, ← two_mul p, pow_mul, neg_one_sq, one_pow, one_smul,
    neg_sub, sub_neg_eq_add]
  simp only [HomologicalComplex.XIsoOfEq, eqToIso.hom]
  have hs : -(-1 : ℤ) ^ p * (-1 : ℤ) ^ p = -1 := by
    rw [neg_mul, ← pow_add, ← two_mul p, pow_mul]
    simp
  rw [hs, neg_one_smul, sub_neg_eq_add]
  simp only [Category.assoc]
  exact add_comm _ _

open CochainComplex.HomComplex

/-- The actual extended sheaf-cap differential is signed cap by the ambient coboundary. -/
theorem retained_extended_sheaf_cap_coboundary (X : TopCat.{0}) (p : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    δ (p : ℤ) ((p + 1 : ℕ) : ℤ)
      (retainedExtendedCap (singularChainSheafComplex ℚ X) p
        (fun q => retainedChainSheafAmbientCap X p q φ)) =
      (-1 : ℤ) ^ (p + 1) •
        retainedExtendedCap (singularChainSheafComplex ℚ X) (p + 1)
          (fun q => retainedChainSheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ)) := by
  rw [retained_extended_cap_differential, ← retained_extended_cap_zsmul]
  congr 1
  funext q
  exact retained_chain_sheaf_cap_coboundary_differential_terms X p q φ

/-- The signed actual cap cochain is an explicit primitive for cap by an ambient coboundary. -/
theorem retained_extended_sheaf_cap_coboundary_primitive (X : TopCat.{0}) (p : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    δ (p : ℤ) ((p + 1 : ℕ) : ℤ)
      ((-1 : ℤ) ^ (p + 1) • retainedExtendedCap (singularChainSheafComplex ℚ X) p
        (fun q => retainedChainSheafAmbientCap X p q φ)) =
      retainedExtendedCap (singularChainSheafComplex ℚ X) (p + 1)
        (fun q => retainedChainSheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ)) := by
  rw [δ_smul, retained_extended_sheaf_cap_coboundary, smul_smul]
  have hs : (-1 : ℤ) ^ (p + 1) * (-1 : ℤ) ^ (p + 1) = 1 := by
    rw [← pow_add, ← two_mul (p + 1), pow_mul]
    simp
  rw [hs, one_smul]

local instance (X : TopCat.{0}) : HasDerivedCategory (TopCat.Sheaf AddCommGrpCat X) :=
  HasDerivedCategory.standard _

/-- The actual derived cap action by an ambient coboundary is zero. -/
theorem retained_derived_cap_coboundary_zero (X : TopCat.{0}) (p : ℕ)
    (φ : Simplicial.Cochain ℚ (TopCat.toSSet.obj X) p) :
    retainedDerivedCapAction X (p + 1) (Simplicial.coboundary ℚ p φ)
      (Simplicial.coboundary_coboundary ℚ p φ) = 0 := by
  let f := retainedChainSheafCapShiftHom X (p + 1) (Simplicial.coboundary ℚ p φ)
    (Simplicial.coboundary_coboundary ℚ p φ)
  let z := Cocycle.equivHomShift f
  have hz : z.1 = retainedExtendedCap (singularChainSheafComplex ℚ X) (p + 1)
      (fun q => retainedChainSheafAmbientCap X (p + 1) q (Simplicial.coboundary ℚ p φ)) := by
    simp only [z, f, retainedChainSheafCapShiftHom, retainedExtendedCapShiftHom,
      AddEquiv.apply_symm_apply]
    erw [AddEquiv.apply_symm_apply]
    rfl
  have hh := retained_derived_shift_hom_zero_of_boundary (p : ℤ) ((p + 1 : ℕ) : ℤ)
    (by omega) z
    ((-1 : ℤ) ^ (p + 1) • retainedExtendedCap (singularChainSheafComplex ℚ X) p
      (fun q => retainedChainSheafAmbientCap X p q φ))
    (by rw [hz]; exact retained_extended_sheaf_cap_coboundary_primitive X p φ)
  simp only [z, AddEquiv.symm_apply_apply] at hh
  change DerivedCategory.Q.map f ≫ _ = 0
  rw [hh, zero_comp]

end HodgeLean.Foundations.QuotientDuality
