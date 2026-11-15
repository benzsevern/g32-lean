import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cCoefficients
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cRelativeReduction

/-! Integral chains mapped into an arbitrary coefficient ring. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

def integralCoefficient (X : TopCat) (R : Type) [CommRing R] (k : ℕ) :
    (SingularChainComplex ℤ X).X k →+ (SingularChainComplex R X).X k :=
  (chainGroupFinsuppIso R X k).symm.toLinearEquiv.toAddMonoidHom.comp
    ((Finsupp.mapRange.addMonoidHom (Int.castAddHom R)).comp
      (chainGroupFinsuppIso ℤ X k).toLinearEquiv.toAddMonoidHom)

theorem integralCoefficient_iota (X : TopCat) (R : Type) [CommRing R] (k : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk k))) (a : ℤ) :
    integralCoefficient X R k
      (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a) =
      ((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of R R) σ).hom
        (a : R) := by
  apply (chainGroupFinsuppIso R X k).toLinearEquiv.injective
  change (chainGroupFinsuppIso R X k).toLinearEquiv
    ((chainGroupFinsuppIso R X k).symm.toLinearEquiv
      (((chainGroupFinsuppIso ℤ X k).toLinearEquiv
        (((TopCat.toSSet.obj X).ιChainComplex (R := ModuleCat.of ℤ ℤ) σ).hom a)).mapRange
        (fun x : ℤ ↦ (x : R)) (Int.cast_zero))) = _
  rw [← Iso.toLinearEquiv_symm, LinearEquiv.apply_symm_apply,
    chainGroupFinsuppIso_iota, chainGroupFinsuppIso_iota]
  simp only [Finsupp.mapRange_single]

theorem integralCoefficient_boundary (X : TopCat) (R : Type) [CommRing R] (k : ℕ)
    (c : (SingularChainComplex ℤ X).X (k + 1)) :
    integralCoefficient X R k (Simplicial.boundary ℤ k c) =
      Simplicial.boundary R k (integralCoefficient X R (k + 1) c) := by
  let Y := TopCat.toSSet.obj X
  have hσ (j : ℕ) (σ : Y.obj (Opposite.op (SimplexCategory.mk j))) :
      integralCoefficient X R j (Simplicial.chainOfSimplex ℤ σ) =
        Simplicial.chainOfSimplex R σ := by
    simpa only [Simplicial.chainOfSimplex, Int.cast_one] using
      integralCoefficient_iota X R j σ 1
  have hscale (a : ℤ) (v : (SingularChainComplex ℤ X).X k) :
      integralCoefficient X R k (((SingularChainComplex ℤ X).X k).isModule.smul a v) =
        (a : R) • integralCoefficient X R k v := by
    rw [int_smul_eq_zsmul, map_zsmul, Int.cast_smul_eq_zsmul]
  let lift (h : Simplicial.ChainGroup ℤ Y (k + 1) →+
      (SingularChainComplex R X).X k) :
      Simplicial.ChainGroup ℤ Y (k + 1) →ₗ[ℤ] (SingularChainComplex R X).X k :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro a c
        change h ((Simplicial.ChainGroup ℤ Y (k + 1)).isModule.smul a c) = a • h c
        rw [int_smul_eq_zsmul]
        exact map_zsmul h a c }
  let f := lift ((integralCoefficient X R k).comp
    (Simplicial.boundary ℤ k (X := Y)).toAddMonoidHom)
  let g := lift ((Simplicial.boundary R k (X := Y)).toAddMonoidHom.comp
    (integralCoefficient X R (k + 1)))
  have hfg : f = g := by
    apply b6m_chainMap_ext Y (k + 1) _ f g
    intro σ
    change integralCoefficient X R k (Simplicial.boundary ℤ k
      (Simplicial.chainOfSimplex ℤ σ)) =
      Simplicial.boundary R k
        (integralCoefficient X R (k + 1) (Simplicial.chainOfSimplex ℤ σ))
    rw [hσ, Simplicial.boundary_chainOfSimplex, Simplicial.boundary_chainOfSimplex, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    refine (hscale ((-1 : ℤ) ^ i.val) _).trans ?_
    exact (congrArg (fun v : (SingularChainComplex R X).X k ↦
      (((-1 : ℤ) ^ i.val : ℤ) : R) • v) (hσ k (Y.δ i σ))).trans
      (congrArg (fun a : R ↦ a • Simplicial.chainOfSimplex R (Y.δ i σ))
        (by simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]))
  exact LinearMap.congr_fun hfg c

theorem integralCoefficient_map {X Y : TopCat.{0}} (f : X ⟶ Y) (R : Type) [CommRing R] (k : ℕ)
    (c : (SingularChainComplex ℤ X).X k) :
    integralCoefficient Y R k
      (((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f k).hom c) =
      ((((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map f).f k).hom
          (integralCoefficient X R k c) := by
  let F := (((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map f).f k
  let G := (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map f).f k
  let lift (h : (SingularChainComplex ℤ X).X k →+
      (SingularChainComplex R Y).X k) :
      (SingularChainComplex ℤ X).X k →ₗ[ℤ] (SingularChainComplex R Y).X k :=
    { toFun := h
      map_add' := h.map_add
      map_smul' := by
        intro a v
        change h (((SingularChainComplex ℤ X).X k).isModule.smul a v) = a • h v
        rw [int_smul_eq_zsmul]
        exact map_zsmul h a v }
  let lhs := lift ((integralCoefficient Y R k).comp F.hom.toAddMonoidHom)
  let rhs := lift (G.hom.toAddMonoidHom.comp (integralCoefficient X R k))
  have heq : lhs = rhs := by
    apply b6m_chainMap_ext (TopCat.toSSet.obj X) k _ lhs rhs
    intro σ
    change integralCoefficient Y R k (F.hom (Simplicial.chainOfSimplex ℤ σ)) =
      G.hom (integralCoefficient X R k (Simplicial.chainOfSimplex ℤ σ))
    have hX := integralCoefficient_iota X R k σ 1
    have hY := integralCoefficient_iota Y R k ((TopCat.toSSet.map f).app _ σ) 1
    simp only [Int.cast_one] at hX hY
    change integralCoefficient X R k (Simplicial.chainOfSimplex ℤ σ) =
      Simplicial.chainOfSimplex R σ at hX
    change integralCoefficient Y R k
      (Simplicial.chainOfSimplex ℤ ((TopCat.toSSet.map f).app _ σ)) =
        Simplicial.chainOfSimplex R ((TopCat.toSSet.map f).app _ σ) at hY
    rw [hX]
    change integralCoefficient Y R k
      ((SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of ℤ ℤ)).f k
        (Simplicial.chainOfSimplex ℤ σ)) =
      (SSet.chainComplexMap (TopCat.toSSet.map f) (ModuleCat.of R R)).f k
        (Simplicial.chainOfSimplex R σ)
    rw [Simplicial.chainOfSimplex_map, Simplicial.chainOfSimplex_map]
    exact hY
  exact LinearMap.congr_fun heq c

theorem relative_integralCoefficient_preserves_zero (P : TopPair.{0}) (R : Type) [CommRing R] (k : ℕ)
    (c : ((relativeChainFunctor ℤ).obj P).cycles k)
    (d : ((relativeChainFunctor R).obj P).cycles k)
    (a : (SingularChainComplex ℤ P.fst).X k)
    (hc : ((relativeChainProjection ℤ P).f k).hom a =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c)
    (hd : ((relativeChainProjection R P).f k).hom
      (integralCoefficient P.fst R k a) =
        (((relativeChainFunctor R).obj P).iCycles k).hom d)
    (hz : (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c = 0) :
    (((relativeChainFunctor R).obj P).homologyπ k).hom d = 0 := by
  let C := SingularChainComplex ℤ P.fst
  let D := SingularChainComplex R P.fst
  let Q := (relativeChainFunctor ℤ).obj P
  let Q' := (relativeChainFunctor R).obj P
  let π := relativeChainProjection ℤ P
  let π' := relativeChainProjection R P
  obtain ⟨b, hb⟩ := (b6m_homologyπ_zero_iff_boundary ℤ Q k c).mp hz
  obtain ⟨t, ht⟩ := b6m_relativeChainProjection_surjective ℤ P (k + 1) b
  have hπdt : (π.f k).hom ((C.d (k + 1) k).hom t) = (Q.d (k + 1) k).hom b := by
    have h := congrArg (fun f => f.hom t) (π.comm (k + 1) k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [← h, ht]
  have hzero : (π.f k).hom (a - (C.d (k + 1) k).hom t) = 0 := by
    rw [map_sub, hc, hπdt, hb, sub_self]
  obtain ⟨u, hu⟩ := b6m_relativeChainProjection_exact ℤ P k _ hzero
  have hπdiff : (π'.f k).hom
      (integralCoefficient P.fst R k (a - (C.d (k + 1) k).hom t)) = 0 := by
    rw [← hu]
    change (π'.f k).hom (integralCoefficient P.fst R k
      (((((singularChainComplexFunctor.{0} (ModuleCat.{0} ℤ)).obj (ModuleCat.of ℤ ℤ)).map P.map).f k).hom u)) = 0
    rw [integralCoefficient_map]
    exact congrArg (fun f => (f.f k).hom (integralCoefficient P.snd R k u))
      (subspaceChainMap_relativeChainProjection R P)
  have hπeq : (π'.f k).hom (integralCoefficient P.fst R k a) =
      (π'.f k).hom (integralCoefficient P.fst R k ((C.d (k + 1) k).hom t)) := by
    simpa only [map_sub, sub_eq_zero] using hπdiff
  apply (b6m_homologyπ_zero_iff_boundary R Q' k d).mpr
  refine ⟨(π'.f (k + 1)).hom (integralCoefficient P.fst R (k + 1) t), ?_⟩
  have hcomm := congrArg (fun f => f.hom (integralCoefficient P.fst R (k + 1) t))
    (π'.comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcomm
  calc
    _ = (π'.f k).hom ((D.d (k + 1) k).hom
        (integralCoefficient P.fst R (k + 1) t)) := hcomm
    _ = (π'.f k).hom (integralCoefficient P.fst R k ((C.d (k + 1) k).hom t)) := by
      exact congrArg (π'.f k).hom (integralCoefficient_boundary P.fst R k t).symm
    _ = (π'.f k).hom (integralCoefficient P.fst R k a) := hπeq.symm
    _ = _ := hd

theorem relative_integralCoefficient_preserves_eq (P : TopPair.{0}) (R : Type) [CommRing R] (k : ℕ)
    (c₁ c₂ : ((relativeChainFunctor ℤ).obj P).cycles k)
    (d₁ d₂ : ((relativeChainFunctor R).obj P).cycles k)
    (a₁ a₂ : (SingularChainComplex ℤ P.fst).X k)
    (hc₁ : ((relativeChainProjection ℤ P).f k).hom a₁ =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c₁)
    (hc₂ : ((relativeChainProjection ℤ P).f k).hom a₂ =
      (((relativeChainFunctor ℤ).obj P).iCycles k).hom c₂)
    (hd₁ : ((relativeChainProjection R P).f k).hom
      (integralCoefficient P.fst R k a₁) =
        (((relativeChainFunctor R).obj P).iCycles k).hom d₁)
    (hd₂ : ((relativeChainProjection R P).f k).hom
      (integralCoefficient P.fst R k a₂) =
        (((relativeChainFunctor R).obj P).iCycles k).hom d₂)
    (h : (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c₁ =
      (((relativeChainFunctor ℤ).obj P).homologyπ k).hom c₂) :
    (((relativeChainFunctor R).obj P).homologyπ k).hom d₁ =
      (((relativeChainFunctor R).obj P).homologyπ k).hom d₂ := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply relative_integralCoefficient_preserves_zero P R k (c₁ - c₂) (d₁ - d₂) (a₁ - a₂)
  · simp only [map_sub, hc₁, hc₂]
  · simp only [map_sub, hd₁, hd₂]
  · rw [map_sub, h, sub_self]

#print axioms integralCoefficient_map
#print axioms relative_integralCoefficient_preserves_eq
end HodgeLean.Foundations.QuotientDuality
