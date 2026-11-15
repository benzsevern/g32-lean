import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cBoundaryLifting
import Mathlib.Data.ZMod.Basic

noncomputable section

namespace HodgeLean.Foundations.Program

theorem b6m_finsupp_reduction_zero_iff {ι : Type*} (n : ℕ) (c : ι →₀ ℤ) :
    c.mapRange (fun a : ℤ ↦ (a : ZMod n)) (Int.cast_zero) = 0 ↔
      ∃ q : ι →₀ ℤ, c = (n : ℤ) • q := by
  constructor
  · intro h
    have hd (i : ι) : (n : ℤ) ∣ c i := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd (c i) n).mp
      exact congrArg (fun f : ι →₀ ZMod n ↦ f i) h
    refine ⟨c.mapRange (fun a ↦ a / n) (Int.zero_ediv _), ?_⟩
    ext i
    simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]
    exact (Int.mul_ediv_cancel' (hd i)).symm
  · rintro ⟨q, rfl⟩
    ext i
    change (((n : ℤ) * q i : ℤ) : ZMod n) = 0
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul]

open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular

def b6m_singularReduction (X : TopCat) (n k : ℕ) :
    (SingularChainComplex ℤ X).X k →+ (SingularChainComplex (ZMod n) X).X k :=
  (chainGroupFinsuppIso (ZMod n) X k).symm.toLinearEquiv.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod n))).comp
      (chainGroupFinsuppIso ℤ X k).toLinearEquiv.toAddMonoidHom)

theorem b6m_singularReduction_surjective (X : TopCat) (n k : ℕ) :
    Function.Surjective (b6m_singularReduction X n k) := by
  apply (chainGroupFinsuppIso (ZMod n) X k).symm.toLinearEquiv.surjective.comp
  apply (Finsupp.mapRange_surjective (fun a : ℤ ↦ (a : ZMod n))
    (Int.cast_zero) ZMod.intCast_surjective).comp
  exact (chainGroupFinsuppIso ℤ X k).toLinearEquiv.surjective

set_option backward.isDefEq.respectTransparency false in
theorem b6m_singularReduction_zero_iff (X : TopCat) (n k : ℕ)
    (c : (SingularChainComplex ℤ X).X k) :
    b6m_singularReduction X n k c = 0 ↔
      ∃ q : (SingularChainComplex ℤ X).X k, c = (n : ℤ) • q := by
  let e := (chainGroupFinsuppIso ℤ X k).toLinearEquiv
  let f := (chainGroupFinsuppIso (ZMod n) X k).toLinearEquiv
  change f.symm ((e c).mapRange (fun a : ℤ ↦ (a : ZMod n)) (Int.cast_zero)) = 0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff, b6m_finsupp_reduction_zero_iff]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.symm q, e.injective ?_⟩
    exact hq.trans ((map_zsmul e (n : ℤ) (e.symm q)).trans
      (congrArg (fun v ↦ (n : ℤ) • v) (e.apply_symm_apply q))).symm
  · rintro ⟨q, rfl⟩
    exact ⟨e q, map_zsmul e (n : ℤ) q⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_singularReduction_iota (X : TopCat) (n k : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))) (a : ℤ) :
    b6m_singularReduction X n k
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of (ZMod n) (ZMod n)) σ).hom
        (a : ZMod n) := by
  apply (chainGroupFinsuppIso (ZMod n) X k).toLinearEquiv.injective
  change (chainGroupFinsuppIso (ZMod n) X k).toLinearEquiv
    ((chainGroupFinsuppIso (ZMod n) X k).symm.toLinearEquiv
      (((chainGroupFinsuppIso ℤ X k).toLinearEquiv
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a)).mapRange
        (fun x : ℤ ↦ (x : ZMod n)) (Int.cast_zero))) = _
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp only [Finsupp.mapRange_single]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_singularReduction_boundary (X : TopCat) (n k : ℕ)
    (c : (SingularChainComplex ℤ X).X (k + 1)) :
    b6m_singularReduction X n k (Simplicial.boundary ℤ k c) =
      Simplicial.boundary (ZMod n) k (b6m_singularReduction X n (k + 1) c) := by
  let Y := TopCat.toSSet.obj X
  have hσ (j : ℕ) (σ : Y.obj (Opposite.op (SimplexCategory.mk j))) :
      b6m_singularReduction X n j (Simplicial.chainOfSimplex ℤ σ) =
        Simplicial.chainOfSimplex (ZMod n) σ := by
    simpa only [Simplicial.chainOfSimplex, Int.cast_one] using
      b6m_singularReduction_iota X n j σ 1
  have hscale (a : ℤ) (v : (SingularChainComplex ℤ X).X k) :
      b6m_singularReduction X n k (((SingularChainComplex ℤ X).X k).isModule.smul a v) =
        (a : ZMod n) • b6m_singularReduction X n k v := by
    rw [int_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  let lift (h : Simplicial.ChainGroup ℤ Y (k + 1) →+
      (SingularChainComplex (ZMod n) X).X k) :
      Simplicial.ChainGroup ℤ Y (k + 1) →ₗ[ℤ] (SingularChainComplex (ZMod n) X).X k :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro a c
        change h ((Simplicial.ChainGroup ℤ Y (k + 1)).isModule.smul a c) = a • h c
        rw [int_smul_eq_zsmul]
        exact map_zsmul h a c }
  let f := lift ((b6m_singularReduction X n k).comp
    (Simplicial.boundary ℤ k (X := Y)).toAddMonoidHom)
  let g := lift ((Simplicial.boundary (ZMod n) k (X := Y)).toAddMonoidHom.comp
    (b6m_singularReduction X n (k + 1)))
  have hfg : f = g := by
    apply b6m_chainMap_ext Y (k + 1) _ f g
    intro σ
    change b6m_singularReduction X n k (Simplicial.boundary ℤ k
      (Simplicial.chainOfSimplex ℤ σ)) =
      Simplicial.boundary (ZMod n) k
        (b6m_singularReduction X n (k + 1) (Simplicial.chainOfSimplex ℤ σ))
    rw [hσ, Simplicial.boundary_chainOfSimplex, Simplicial.boundary_chainOfSimplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    refine (hscale ((-1 : ℤ) ^ i.val) _).trans ?_
    exact (congrArg (fun v : (SingularChainComplex (ZMod n) X).X k ↦
      (((-1 : ℤ) ^ i.val : ℤ) : ZMod n) • v) (hσ k (Y.δ i σ))).trans
      (congrArg (fun a : ZMod n ↦ a • Simplicial.chainOfSimplex (ZMod n) (Y.δ i σ))
        (by simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]))
  exact LinearMap.congr_fun hfg c

set_option backward.isDefEq.respectTransparency false in
theorem b6m_cycle_lifting_of_modular_boundary (X : TopCat) (n : ℕ)
    (c w : (SingularChainComplex ℤ X).X 2)
    (hw : ((SingularChainComplex ℤ X).d 2 1).hom w = 0)
    (v : (SingularChainComplex (ZMod n) X).X 3)
    (hv : b6m_singularReduction X n 2 c = b6m_singularReduction X n 2 w +
      ((SingularChainComplex (ZMod n) X).d 3 2).hom v) :
    ∃ W q : (SingularChainComplex ℤ X).X 2,
      ((SingularChainComplex ℤ X).d 2 1).hom W = 0 ∧ c - W = (n : ℤ) • q := by
  obtain ⟨u, hu⟩ := b6m_singularReduction_surjective X n 3 v
  let W := w + ((SingularChainComplex ℤ X).d 3 2).hom u
  have hW : ((SingularChainComplex ℤ X).d 2 1).hom W = 0 := by
    change ((SingularChainComplex ℤ X).d 2 1).hom (w + ((SingularChainComplex ℤ X).d 3 2).hom u) = 0
    rw [map_add, hw, zero_add]
    exact ConcreteCategory.congr_hom ((SingularChainComplex ℤ X).d_comp_d 3 2 1) u
  have hdu : b6m_singularReduction X n 2 (((SingularChainComplex ℤ X).d 3 2).hom u) =
      ((SingularChainComplex (ZMod n) X).d 3 2).hom (b6m_singularReduction X n 3 u) :=
    b6m_singularReduction_boundary X n 2 u
  have hred : b6m_singularReduction X n 2 (c - W) = 0 := by
    change b6m_singularReduction X n 2 (c - (w + ((SingularChainComplex ℤ X).d 3 2).hom u)) = 0
    rw [map_sub, map_add, hdu, hu, ← hv, sub_self]
  obtain ⟨q, hq⟩ := (b6m_singularReduction_zero_iff X n 2 (c - W)).mp hred
  exact ⟨W, q, hW, hq⟩

set_option backward.isDefEq.respectTransparency false in
theorem b6m_singularReduction_map {X Y : TopCat.{0}} (f : X ⟶ Y) (n k : ℕ)
    (c : (SingularChainComplex ℤ X).X k) :
    b6m_singularReduction Y n k
      (((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f k).hom c) =
      ((((singularChainComplexFunctor.{0} (ModuleCat.{0} (ZMod n))).obj
        (ModuleCat.of (ZMod n) (ZMod n))).map f).f k).hom
          (b6m_singularReduction X n k c) := by
  let F := (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f k
  let G := (((singularChainComplexFunctor.{0} (ModuleCat.{0} (ZMod n))).obj
    (ModuleCat.of (ZMod n) (ZMod n))).map f).f k
  let lift (h : (SingularChainComplex ℤ X).X k →+
      (SingularChainComplex (ZMod n) Y).X k) :
      (SingularChainComplex ℤ X).X k →ₗ[ℤ] (SingularChainComplex (ZMod n) Y).X k :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro a v
        change h (((SingularChainComplex ℤ X).X k).isModule.smul a v) = a • h v
        rw [int_smul_eq_zsmul]
        exact map_zsmul h a v }
  let lhs := lift ((b6m_singularReduction Y n k).comp F.hom.toAddMonoidHom)
  let rhs := lift (G.hom.toAddMonoidHom.comp (b6m_singularReduction X n k))
  have heq : lhs = rhs := by
    apply b6m_chainMap_ext (TopCat.toSSet.obj X) k _ lhs rhs
    intro σ
    change b6m_singularReduction Y n k (F.hom (Simplicial.chainOfSimplex ℤ σ)) =
      G.hom (b6m_singularReduction X n k (Simplicial.chainOfSimplex ℤ σ))
    have hX := b6m_singularReduction_iota X n k σ 1
    have hY := b6m_singularReduction_iota Y n k ((TopCat.toSSet.map f).app _ σ) 1
    simp only [Int.cast_one] at hX hY
    change b6m_singularReduction X n k (Simplicial.chainOfSimplex ℤ σ) =
      Simplicial.chainOfSimplex (ZMod n) σ at hX
    change b6m_singularReduction Y n k
      (Simplicial.chainOfSimplex ℤ ((TopCat.toSSet.map f).app _ σ)) =
        Simplicial.chainOfSimplex (ZMod n) ((TopCat.toSSet.map f).app _ σ) at hY
    rw [hX]
    change b6m_singularReduction Y n k
      ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f k
        (Simplicial.chainOfSimplex ℤ σ)) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of (ZMod n) (ZMod n))).f k
        (Simplicial.chainOfSimplex (ZMod n) σ)
    rw [Simplicial.chainOfSimplex_map, Simplicial.chainOfSimplex_map]
    exact hY
  exact LinearMap.congr_fun heq c

end HodgeLean.Foundations.Program
