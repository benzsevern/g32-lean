import HodgeLean.Adapters.CycleClassDivisorProduct3Defs
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDualNaturality

/-! # Proof obligations for relative cup descent
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Adapters

private theorem ccm15_smallCochain_ext (Y : TopCat.{0}) (S T : Set Y) (n : ℕ)
    (f g : ccm14_smallRelativeCochain Y S T n)
    (h : f.comp ((ccm14_smallProjection Y S T).f n).hom =
      g.comp ((ccm14_smallProjection Y S T).f n).hom) : f = g := by
  have he := Cofork.IsColimit.hom_ext (ccm14_projectionIsCokernel Y S T n)
    (show (ccm14_smallProjection Y S T).f n ≫ ModuleCat.ofHom f =
      (ccm14_smallProjection Y S T).f n ≫ ModuleCat.ofHom g from ModuleCat.hom_ext h)
  exact congrArg ModuleCat.Hom.hom he

private theorem ccm15_smallCup_leibniz (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p)
    (v : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q) :
    ((ccm15_smallDual Y S T (p + q)).g.hom
        (ccm15_smallCupLinear Y S T p q u v)).comp
      ((ccm14_smallRelativeComplex Y S T).XIsoOfEq
        (show p + q + 1 = (ComplexShape.down ℕ).prev (p + q) by simp)).hom.hom =
      (ccm15_smallCupLinear Y S T (p + 1) q
          (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u) v).comp
        ((ccm14_smallRelativeComplex Y S T).XIsoOfEq
          (show p + q + 1 = (p + 1) + q by omega)).hom.hom +
      (-1 : ℚ) ^ p • ccm15_smallCupLinear Y S T p (q + 1) u
        (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v) := by
  apply ccm15_smallCochain_ext
  have hleft :
      ((ccm15_smallCupLinear Y S T (p + 1) q
          (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u) v).comp
          ((ccm14_smallRelativeComplex Y S T).XIsoOfEq
            (show p + q + 1 = (p + 1) + q by omega)).hom.hom).comp
          ((ccm14_smallProjection Y S T).f (p + q + 1)).hom =
        (ccm13_relativeCupLift Y S T (p + 1) q
          (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u) v).comp
            (reassocChain ℚ p q) := by
    have hnat := HomologicalComplex.XIsoOfEq_hom_naturality
      (ccm14_smallProjection Y S T)
      (show p + q + 1 = (p + 1) + q by omega)
    have hcast := congrArg ModuleCat.Hom.hom hnat
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hcast
    rw [LinearMap.comp_assoc, hcast, ← LinearMap.comp_assoc]
    change ((ccm14_smallRelativeCup Y S T (p + 1) q
      (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u) v).comp
        ((ccm14_smallProjection Y S T).f (p + 1 + q)).hom).comp _ = _
    rw [ccm15_smallCup_projection]
    rfl
  have hbase :
      (((ccm15_smallDual Y S T (p + q)).g.hom
          (ccm15_smallCupLinear Y S T p q u v)).comp
        ((ccm14_smallRelativeComplex Y S T).XIsoOfEq
          (show p + q + 1 = (ComplexShape.down ℕ).prev (p + q) by simp)).hom.hom).comp
        ((ccm14_smallProjection Y S T).f (p + q + 1)).hom =
      coboundary ℚ (p + q) (ccm13_relativeCupLift Y S T p q u v) := by
    simp only [ccm15_smallDual, ShortComplex.linearDual]
    dsimp only [ShortComplex.moduleCatMk, HomologicalComplex.sc,
      HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
    change ((((ccm14_smallRelativeCup Y S T p q u v).comp
      ((ccm14_smallRelativeComplex Y S T).d
        ((ComplexShape.down ℕ).prev (p + q)) (p + q)).hom).comp
          ((ccm14_smallRelativeComplex Y S T).XIsoOfEq
            (show p + q + 1 = (ComplexShape.down ℕ).prev (p + q) by simp)).hom.hom).comp
        ((ccm14_smallProjection Y S T).f (p + q + 1)).hom = _)
    have hd := congrArg ModuleCat.Hom.hom
      (HomologicalComplex.XIsoOfEq_hom_comp_d (ccm14_smallRelativeComplex Y S T)
        (show p + q + 1 = (ComplexShape.down ℕ).prev (p + q) by simp)
        (p + q))
    rw [ModuleCat.hom_comp] at hd
    have hdproj := congrArg (fun f => f.comp
      ((ccm14_smallProjection Y S T).f (p + q + 1)).hom) hd
    simp only [LinearMap.comp_assoc] at hdproj ⊢
    rw [hdproj]
    have hcomm := congrArg ModuleCat.Hom.hom
      ((ccm14_smallProjection Y S T).comm (p + q + 1) (p + q))
    rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hcomm
    rw [hcomm, ← LinearMap.comp_assoc, ccm15_smallCup_projection]
    rfl
  rw [LinearMap.add_comp, LinearMap.smul_comp, hbase, hleft]
  have hright :
      (ccm15_smallCupLinear Y S T p (q + 1) u
        (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v)).comp
          ((ccm14_smallProjection Y S T).f (p + q + 1)).hom =
        ccm13_relativeCupLift Y S T p (q + 1) u
          (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v) := by
    exact ccm15_smallCup_projection Y S T p (q + 1) u
      (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v)
  rw [hright]
  change coboundary ℚ (p + q) (ccm13_relativeCupLift Y S T p q u v) =
    (ccm13_relativeCupLift Y S T (p + 1) q
      (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u) v).comp (reassocChain ℚ p q) +
    (-1 : ℚ) ^ p • ccm13_relativeCupLift Y S T p (q + 1) u
      (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v)
  unfold ccm13_relativeCupLift
  rw [HodgeLean.Foundations.Singular.coboundary_cupCochain,
    relativeCochainToAbsolute_coboundary,
    relativeCochainToAbsolute_coboundary]
  rfl

private theorem ccm15_relative_g (Y : TopCat.{0}) (S : Set Y) (n : ℕ)
    (u : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) n) :
    ((ccm15_relativeDual Y S n).g.hom u).comp
      (((relativeChainFunctor ℚ).obj (TopPair.ofSubset Sᶜ)).XIsoOfEq
        (show n + 1 = (ComplexShape.down ℕ).prev n by simp)).hom.hom =
      relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) n u := by
  simp only [ccm15_relativeDual, ShortComplex.linearDual]
  dsimp only [ShortComplex.moduleCatMk, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']
  change (u.comp (((relativeChainFunctor ℚ).obj (TopPair.ofSubset Sᶜ)).d
    ((ComplexShape.down ℕ).prev n) n).hom).comp _ = _
  rw [LinearMap.comp_assoc]
  have hd := congrArg ModuleCat.Hom.hom
    (HomologicalComplex.XIsoOfEq_hom_comp_d
      ((relativeChainFunctor ℚ).obj (TopPair.ofSubset Sᶜ))
      (show n + 1 = (ComplexShape.down ℕ).prev n by simp) n)
  rw [ModuleCat.hom_comp] at hd
  rw [hd]
  rfl

private theorem ccm15_dual_f_succ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (u : ((K.sc (n + 1)).linearDual).X₁) :
    ((K.sc (n + 1)).linearDual).f.hom u =
      (u.comp (K.XIsoOfEq (show n = (ComplexShape.down ℕ).next (n + 1) by simp)).hom.hom).comp
        (K.d (n + 1) n).hom := by
  change u.comp (K.d (n + 1) ((ComplexShape.down ℕ).next (n + 1))).hom = _
  rw [LinearMap.comp_assoc]
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.d_comp_XIsoOfEq_hom K
    (show n = (ComplexShape.down ℕ).next (n + 1) by simp) (n + 1))
  rw [ModuleCat.hom_comp] at h
  rw [h]

private theorem ccm15_dual_f_zero (K : ChainComplex (ModuleCat ℚ) ℕ)
    (u : ((K.sc 0).linearDual).X₁) :
    (K.sc 0).linearDual.f.hom u = 0 := by
  simp [ShortComplex.linearDual, HomologicalComplex.sc,
    HomologicalComplex.shortComplexFunctor, HomologicalComplex.shortComplexFunctor']

private theorem ccm15_dual_d_mem_range (K : ChainComplex (ModuleCat ℚ) ℕ)
    (n m : ℕ) (h : m = n + 1) (w : Module.Dual ℚ (K.X n)) :
    w.comp (K.d m n).hom ∈ LinearMap.range (K.sc m).linearDual.f.hom := by
  subst m
  let e := K.XIsoOfEq (show n = (ComplexShape.down ℕ).next (n + 1) by simp)
  refine ⟨w.comp e.inv.hom, ?_⟩
  rw [ccm15_dual_f_succ]
  have he : (w.comp e.inv.hom).comp e.hom.hom = w := by
    ext x
    exact congrArg w (ConcreteCategory.congr_hom e.hom_inv_id x)
  rw [he]

private theorem ccm15_dual_g (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (w : Module.Dual ℚ (K.X n)) :
    ((K.sc n).linearDual.g.hom w).comp
      (K.XIsoOfEq (show n + 1 = (ComplexShape.down ℕ).prev n by simp)).hom.hom =
      w.comp (K.d (n + 1) n).hom := by
  change (w.comp (K.d ((ComplexShape.down ℕ).prev n) n).hom).comp _ = _
  rw [LinearMap.comp_assoc]
  have h := congrArg ModuleCat.Hom.hom (HomologicalComplex.XIsoOfEq_hom_comp_d K
    (show n + 1 = (ComplexShape.down ℕ).prev n by simp) n)
  rw [ModuleCat.hom_comp] at h
  rw [h]

private theorem ccm15_dual_boundary_of_cast (K : ChainComplex (ModuleCat ℚ) ℕ)
    (a b : ℕ) (h : a = b) (w : Module.Dual ℚ (K.X b))
    (hw : w.comp (K.XIsoOfEq h).hom.hom ∈ LinearMap.range (K.sc a).linearDual.f.hom) :
    w ∈ LinearMap.range (K.sc b).linearDual.f.hom := by
  subst b
  simpa using hw

theorem ccm15_dualComparison_quasiIso_aux (Y : TopCat.{0}) (S T : Set Y)
    (hS : IsClosed S) (hT : IsClosed T) :
    QuasiIso (HomologicalComplex.linearDualMap (ccm14_relativeComparison Y S T)) := by
  let f := ccm14_relativeComparison Y S T
  let : QuasiIso f := ccm14_relativeComparison_quasiIso Y S T hS hT
  rw [_root_.quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap,
    ConcreteCategory.isIso_iff_bijective]
  let e := (HomologicalComplex.linearDualHomologyEquiv _ n).trans
    ((asIso (HomologicalComplex.homologyMap f n)).toLinearEquiv.dualMap.trans
      (HomologicalComplex.linearDualHomologyEquiv _ n).symm)
  have he : (HomologicalComplex.homologyMap (HomologicalComplex.linearDualMap f) n).hom =
      e.toLinearMap := by
    ext a
    apply (HomologicalComplex.linearDualHomologyEquiv _ n).injective
    ext z
    rw [HomologicalComplex.linearDualHomologyEquiv_naturality]
    simp [e]
  change Function.Bijective (HomologicalComplex.homologyMap
    (HomologicalComplex.linearDualMap f) n).hom
  rw [he]
  exact e.bijective

theorem ccm15_smallCup_closed_aux (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_smallCupLinear Y S T p q u.1 v.1 ∈
      LinearMap.ker (ccm15_smallDual Y S T (p + q)).g.hom := by
  have hu := ccm15_relative_g Y S p u.1
  have hv := ccm15_relative_g Y T q v.1
  rw [show (ccm15_relativeDual Y S p).g.hom u.1 = 0 from u.2,
    LinearMap.zero_comp] at hu
  rw [show (ccm15_relativeDual Y T q).g.hom v.1 = 0 from v.2,
    LinearMap.zero_comp] at hv
  have h := ccm15_smallCup_leibniz Y S T p q u.1 v.1
  rw [← hu, ← hv] at h
  simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, smul_zero, add_zero] at h
  change (ccm15_smallDual Y S T (p + q)).g.hom
    (ccm15_smallCupLinear Y S T p q u.1 v.1) = 0
  let e := (ccm14_smallRelativeComplex Y S T).XIsoOfEq
    (show p + q + 1 = (ComplexShape.down ℕ).prev (p + q) by simp)
  have hepi : Function.Surjective e.hom.hom := fun x =>
    ⟨e.inv.hom x, ConcreteCategory.congr_hom e.inv_hom_id x⟩
  apply LinearMap.lcomp_injective_of_surjective (S := ℚ) (N := ℚ) e.hom.hom hepi
  change ((ccm15_smallDual Y S T (p + q)).g.hom
    (ccm15_smallCupLinear Y S T p q u.1 v.1)).comp e.hom.hom = 0
  exact h

theorem ccm15_smallCup_boundary_left_aux (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : (ccm15_relativeDual Y S p).X₁)
    (v : LinearMap.ker (ccm15_relativeDual Y T q).g.hom) :
    ccm15_smallCupLinear Y S T p q ((ccm15_relativeDual Y S p).f.hom u) v.1 ∈
      LinearMap.range (ccm15_smallDual Y S T (p + q)).f.hom := by
  cases p with
  | zero =>
      rw [ccm15_dual_f_zero]
      simp only [map_zero, LinearMap.zero_apply]
      exact Submodule.zero_mem _
  | succ p =>
      rw [ccm15_dual_f_succ]
      let u' : RelativeCochain ℚ (TopPair.ofSubset Sᶜ) p :=
        u.comp ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset Sᶜ)).XIsoOfEq
          (show p = (ComplexShape.down ℕ).next (p + 1) by simp)).hom.hom)
      change ccm15_smallCupLinear Y S T (p + 1) q
        (relativeCoboundary ℚ (TopPair.ofSubset Sᶜ) p u') v.1 ∈ _
      have hv := ccm15_relative_g Y T q v.1
      rw [show (ccm15_relativeDual Y T q).g.hom v.1 = 0 from v.2,
        LinearMap.zero_comp] at hv
      have h := ccm15_smallCup_leibniz Y S T p q u' v.1
      rw [← hv, ccm15_dual_g] at h
      simp only [map_zero, smul_zero, add_zero] at h
      apply ccm15_dual_boundary_of_cast _ (p + q + 1) ((p + 1) + q)
        (by omega)
      rw [← h]
      exact ccm15_dual_d_mem_range _ (p + q) (p + q + 1) rfl _

theorem ccm15_smallCup_boundary_right_aux (Y : TopCat.{0}) (S T : Set Y) (p q : ℕ)
    (u : LinearMap.ker (ccm15_relativeDual Y S p).g.hom)
    (v : (ccm15_relativeDual Y T q).X₁) :
    ccm15_smallCupLinear Y S T p q u.1 ((ccm15_relativeDual Y T q).f.hom v) ∈
      LinearMap.range (ccm15_smallDual Y S T (p + q)).f.hom := by
  cases q with
  | zero =>
      rw [ccm15_dual_f_zero]
      simp only [map_zero]
      exact Submodule.zero_mem _
  | succ q =>
      rw [ccm15_dual_f_succ]
      let v' : RelativeCochain ℚ (TopPair.ofSubset Tᶜ) q :=
        v.comp ((((relativeChainFunctor ℚ).obj (TopPair.ofSubset Tᶜ)).XIsoOfEq
          (show q = (ComplexShape.down ℕ).next (q + 1) by simp)).hom.hom)
      change ccm15_smallCupLinear Y S T p (q + 1) u.1
        (relativeCoboundary ℚ (TopPair.ofSubset Tᶜ) q v') ∈ _
      have hu := ccm15_relative_g Y S p u.1
      rw [show (ccm15_relativeDual Y S p).g.hom u.1 = 0 from u.2,
        LinearMap.zero_comp] at hu
      have h := ccm15_smallCup_leibniz Y S T p q u.1 v'
      rw [← hu, ccm15_dual_g] at h
      simp only [map_zero, LinearMap.zero_apply, LinearMap.zero_comp, zero_add] at h
      have hb := ccm15_dual_d_mem_range (ccm14_smallRelativeComplex Y S T)
        (p + q) (p + q + 1) rfl (ccm15_smallCupLinear Y S T p q u.1 v')
      rw [h] at hb
      exact (Submodule.smul_mem_iff _ (pow_ne_zero p (by norm_num : (-1 : ℚ) ≠ 0))).mp hb

#print axioms ccm15_dualComparison_quasiIso_aux
#print axioms ccm15_smallCup_closed_aux
#print axioms ccm15_smallCup_boundary_left_aux
#print axioms ccm15_smallCup_boundary_right_aux

end HodgeLean.Adapters
