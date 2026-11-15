import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralMap

/-! Integral extension of simplex values and lifted displacements. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Convexity
open scoped Simplicial
namespace HodgeLean.Foundations.Program

/-- Integral linear extension of values assigned to singular simplices. -/
def s4_c1a6_simplexLinear {V : Type} [AddCommGroup V]
    (X : TopCat) (n : ℕ) (g : (TopCat.toSSet.obj X) _⦋n⦌ → V) :
    (s4_c1a6_ZChains X).X n →ₗ[ℤ] V :=
  ((TopCat.toSSet.obj X).isColimitChainComplexXCofan (ModuleCat.of ℤ ℤ) n |>.desc
    (Cofan.mk _ fun σ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ V (g σ)))).hom

theorem s4_c1a6_simplexLinear_iota {V : Type} [AddCommGroup V]
    (X : TopCat) (n : ℕ) (g : (TopCat.toSSet.obj X) _⦋n⦌ → V)
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) (m : ℤ) :
    s4_c1a6_simplexLinear X n g
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom m) = m • g σ := by
  have h := ((TopCat.toSSet.obj X).isColimitChainComplexXCofan
    (ModuleCat.of ℤ ℤ) n).fac
    (Cofan.mk _ fun τ => ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ V (g τ))) ⟨σ⟩
  exact congrArg (fun k => k.hom m) h

theorem s4_c1a6_simplexLinear_comp {V W : Type} [AddCommGroup V] [AddCommGroup W]
    (X : TopCat) (n : ℕ) (g : (TopCat.toSSet.obj X) _⦋n⦌ → V) (f : V →ₗ[ℤ] W) :
    f.comp (s4_c1a6_simplexLinear X n g) = s4_c1a6_simplexLinear X n (fun σ => f (g σ)) := by
  suffices h : (ModuleCat.ofHom (f.comp (s4_c1a6_simplexLinear X n g)) :
      (s4_c1a6_ZChains X).X n ⟶ ModuleCat.of ℤ W) =
      ModuleCat.ofHom (s4_c1a6_simplexLinear X n (fun σ => f (g σ))) by
    exact congrArg ModuleCat.Hom.hom h
  apply SSet.chainComplex_hom_ext
  intro σ
  ext
  change f (s4_c1a6_simplexLinear X n g
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)) = _
  rw [s4_c1a6_simplexLinear_iota]
  change f ((1 : ℤ) • g σ) = s4_c1a6_simplexLinear X n (fun τ => f (g τ))
    (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
  rw [s4_c1a6_simplexLinear_iota, map_zsmul]

theorem s4_c1a6_simplexLinear_boundary {V : Type} [AddCommGroup V]
    (X : TopCat) (g : (TopCat.toSSet.obj X) _⦋0⦌ → V) :
    (s4_c1a6_simplexLinear X 0 g).comp ((s4_c1a6_ZChains X).d 1 0).hom =
      s4_c1a6_simplexLinear X 1 (fun σ =>
        g ((TopCat.toSSet.obj X).δ 0 σ) - g ((TopCat.toSSet.obj X).δ 1 σ)) := by
  suffices h : (ModuleCat.ofHom
      ((s4_c1a6_simplexLinear X 0 g).comp ((s4_c1a6_ZChains X).d 1 0).hom) :
        (s4_c1a6_ZChains X).X 1 ⟶ ModuleCat.of ℤ V) =
      ModuleCat.ofHom (s4_c1a6_simplexLinear X 1 (fun σ =>
        g ((TopCat.toSSet.obj X).δ 0 σ) - g ((TopCat.toSSet.obj X).δ 1 σ))) by
    exact congrArg ModuleCat.Hom.hom h
  apply SSet.chainComplex_hom_ext
  intro σ
  ext
  change s4_c1a6_simplexLinear X 0 g
      ((((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ) ≫
        (s4_c1a6_ZChains X).d 1 0).hom 1) = _
  rw [SSet.ιChainComplex_d]
  change s4_c1a6_simplexLinear X 0 g
    ((∑ k : Fin 2, (-1 : ℤ) ^ k.val •
      (TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ)
        ((TopCat.toSSet.obj X).δ k σ)).hom 1) =
    s4_c1a6_simplexLinear X 1 (fun τ =>
      g ((TopCat.toSSet.obj X).δ 0 τ) - g ((TopCat.toSSet.obj X).δ 1 τ))
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom 1)
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_add, ModuleCat.hom_neg,
    LinearMap.add_apply, LinearMap.neg_apply, map_add, map_neg, LinearMap.sum_apply,
    LinearMap.smul_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    one_zsmul, neg_one_zsmul, map_sub]
  erw [s4_c1a6_simplexLinear_iota, s4_c1a6_simplexLinear_iota,
    s4_c1a6_simplexLinear_iota]
  simp only [one_smul, sub_eq_add_neg]

end HodgeLean.Foundations.Program
