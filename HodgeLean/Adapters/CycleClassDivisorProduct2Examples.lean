import HodgeLean.Adapters.CycleClassDivisorProduct2Defs

/-! # Nonzero relative inputs and nonempty complement-small chains
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
open HodgeLean.Foundations.Singular
open scoped Simplicial Classical
namespace HodgeLean.Adapters

/-- Discrete two-point test space.
Source: the elementary discrete-space test for relative cochains. -/
abbrev ccm14_twoPoints : TopCat.{0} := @TopCat.of Bool ⊥

/-- A constant vertex in the two-point space.
Source: the constant singular simplex. -/
def ccm14_vertex (b : Bool) : (TopCat.toSSet.obj ccm14_twoPoints) _⦋0⦌ :=
  (ccm14_twoPoints.toSSetObjEquiv _).symm (ContinuousMap.const _ b)

/-- The characteristic zero-cochain of the true vertex.
Source: Hatcher, Algebraic Topology, §3.1, cochains as functionals on simplices. -/
def ccm14_indicator : Cochain ℚ (TopCat.toSSet.obj ccm14_twoPoints) 0 := by
  classical
  exact ((TopCat.toSSet.obj ccm14_twoPoints).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) 0).desc
      (Cofan.mk _ fun σ => if σ = ccm14_vertex true then 𝟙 (ModuleCat.of ℚ ℚ) else 0) |>.hom

/-- Source: the coproduct evaluation formula for the characteristic cochain. -/
theorem ccm14_indicator_apply (σ : (TopCat.toSSet.obj ccm14_twoPoints) _⦋0⦌) :
    ccm14_indicator (chainOfSimplex ℚ σ) = if σ = ccm14_vertex true then 1 else 0 := by
  classical
  have h := (TopCat.toSSet.obj ccm14_twoPoints).isColimitChainComplexXCofan
    (ModuleCat.of ℚ ℚ) 0 |>.fac
      (Cofan.mk _ fun τ => if τ = ccm14_vertex true then 𝟙 (ModuleCat.of ℚ ℚ) else 0) ⟨σ⟩
  have h' := ConcreteCategory.congr_hom h (1 : ℚ)
  change ccm14_indicator (chainOfSimplex ℚ σ) =
    (if σ = ccm14_vertex true then 𝟙 (ModuleCat.of ℚ ℚ) else 0).hom 1 at h'
  split_ifs at h' ⊢ <;> exact h'

/-- The characteristic functional descended through the genuine relative quotient.
Source: Hatcher, Algebraic Topology, §3.1, relative cochains. -/
def ccm14_nonzeroInput : RelativeCochain ℚ
    (TopPair.ofSubset ({true} : Set ccm14_twoPoints)ᶜ) 0 := by
  classical
  let P := TopPair.ofSubset ({true} : Set ccm14_twoPoints)ᶜ
  refine ((relativeChainProjectionComponentIsCokernelForCap ℚ P 0).desc
    (CokernelCofork.ofπ (ModuleCat.ofHom ccm14_indicator) ?_)).hom
  apply SSet.chainComplex_hom_ext
  intro σ
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have hσ : (TopCat.toSSet.map P.map).app _ σ ≠ ccm14_vertex true := by
    intro h
    have hv := congrArg (fun τ => ccm14_twoPoints.toSSetObjEquiv _ τ
      (Classical.arbitrary _)) h
    have hn := (P.snd.toSSetObjEquiv _ σ (Classical.arbitrary _)).2
    exact hn (show _ = true from hv)
  have he := ccm14_indicator_apply ((TopCat.toSSet.map P.map).app _ σ)
  rw [if_neg hσ] at he
  have hi : ((TopCat.toSSet.obj P.snd).ιChainComplex
      (R := ModuleCat.of ℚ ℚ) σ).hom a = a • chainOfSimplex ℚ σ := by
    rw [chainOfSimplex, ← map_smul]
    simp
    rfl
  change ccm14_indicator
    (((SSet.chainComplexMap (TopCat.toSSet.map P.map) (ModuleCat.of ℚ ℚ)).f 0).hom
      (((TopCat.toSSet.obj P.snd).ιChainComplex (R := ModuleCat.of ℚ ℚ) σ).hom a)) = 0
  rw [hi, map_smul, map_smul, chainOfSimplex_map, he, smul_zero]

/-- Source: the defining relative quotient factorization. -/
theorem ccm14_nonzeroInput_absolute : relativeCochainToAbsolute ℚ
    (TopPair.ofSubset ({true} : Set ccm14_twoPoints)ᶜ) 0 ccm14_nonzeroInput =
      ccm14_indicator := by
  exact congrArg ModuleCat.Hom.hom
    ((Cofork.IsColimit.π_desc (relativeChainProjectionComponentIsCokernelForCap ℚ
      (TopPair.ofSubset ({true} : Set ccm14_twoPoints)ᶜ) 0)).trans
      (CokernelCofork.π_ofπ _ _ _))

/-- Source: evaluation at the true vertex detects the nonzero input. -/
example : ccm14_nonzeroInput ≠ 0 := by
  intro h
  have he := ccm14_nonzeroInput_absolute
  rw [h, map_zero] at he
  have hv := congrArg (fun f => f (chainOfSimplex ℚ (ccm14_vertex true))) he
  have hi := ccm14_indicator_apply (ccm14_vertex true)
  simp only [ite_true] at hi
  exact zero_ne_one (hv.trans hi)

/-- Source: the false vertex belongs to both complements. -/
example : Nonempty ((coverSmallSingularSubcomplex ccm14_twoPoints
    (ccm13_complementFamily ccm14_twoPoints {true} {true}) : SSet) _⦋0⦌) := by
  refine ⟨⟨ccm14_vertex false, ?_⟩⟩
  apply (mem_coverSmallSingularSubcomplex_iff_exists_preimage _ _ _).mpr
  refine ⟨false, ((TopCat.of ↥({true} : Set ccm14_twoPoints)ᶜ).toSSetObjEquiv _).symm
    (ContinuousMap.const _ ⟨false, by simp⟩), ?_⟩
  rfl

/-- Source: the descended cup of two nonzero inputs evaluates to one at the true vertex. -/
example : ccm14_smallRelativeCup ccm14_twoPoints {true} {true} 0 0
    ccm14_nonzeroInput ccm14_nonzeroInput
      (((ccm14_smallProjection ccm14_twoPoints {true} {true}).f 0).hom
        (chainOfSimplex ℚ (ccm14_vertex true))) = 1 := by
  have h : (ccm14_smallRelativeCup ccm14_twoPoints {true} {true} 0 0
      ccm14_nonzeroInput ccm14_nonzeroInput).comp
      ((ccm14_smallProjection ccm14_twoPoints {true} {true}).f 0).hom =
      ccm13_relativeCupLift ccm14_twoPoints {true} {true} 0 0
        ccm14_nonzeroInput ccm14_nonzeroInput := by
    exact congrArg ModuleCat.Hom.hom
      ((Cofork.IsColimit.π_desc
        (ccm14_projectionIsCokernel ccm14_twoPoints {true} {true} 0)).trans
          (CokernelCofork.π_ofπ _ _ _))
  have hv := LinearMap.congr_fun h (chainOfSimplex ℚ (ccm14_vertex true))
  change ccm14_smallRelativeCup _ _ _ _ _ _ _ _ = _ at hv
  apply hv.trans
  unfold ccm13_relativeCupLift
  erw [ccm14_nonzeroInput_absolute, cupCochain_apply_simplex]
  change ccm14_indicator (chainOfSimplex ℚ (ccm14_vertex true)) *
    ccm14_indicator (chainOfSimplex ℚ (ccm14_vertex true)) = 1
  simp [ccm14_indicator_apply]

end HodgeLean.Adapters
