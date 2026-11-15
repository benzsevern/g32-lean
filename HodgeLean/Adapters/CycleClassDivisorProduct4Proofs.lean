import HodgeLean.Adapters.CycleClassDivisorProduct4Construction
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11Normalization
import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian11ComparisonProofs

/-! # Supported comparison obligations

Two independent comparison obligations precede the final product law.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

private theorem ccm16_relativeCohomologyToAbsolute_naturality
    {A B : TopPair.{0}} (f : A ⟶ B) (n : ℕ) (u : RelativeCohomology ℚ B n) :
    relativeCohomologyToAbsolute ℚ A n (relativeCohomologyMap ℚ n f u) =
      cohomologyMap ℚ n (TopPair.Hom.fst f) (relativeCohomologyToAbsolute ℚ B n u) := by
  have hdual := congrArg HomologicalComplex.linearDualMap
    (TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f)
  rw [HomologicalComplex.linearDualMap_comp, HomologicalComplex.linearDualMap_comp] at hdual
  have hhom := congrArg (fun v => HomologicalComplex.homologyMap v n) hdual
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at hhom
  exact ConcreteCategory.congr_hom hhom u

private theorem ccm16_pairTransport_apply (Y : TopCat.{0}) (S : Set Y) (n : ℕ)
    (u : RelativeCohomology ℚ (neighborhoodSupportComplementPair Set.univ S) n) :
    ccm16_pairTransport Y S n u =
      relativeCohomologyMap ℚ n (ccm16_fullPairIso Y S).hom u := rfl

private theorem ccm16_fullPairIso_fst (Y : TopCat.{0}) (S : Set Y) :
    TopPair.Hom.fst (ccm16_fullPairIso Y S).hom =
      TopCat.ofHom ⟨(Homeomorph.Set.univ Y).symm,
        (Homeomorph.Set.univ Y).symm.continuous⟩ := rfl

theorem ccm16_rawComparison_unit_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] :
    rationalCohomologyLinearEquivSingular X 0 (HQ.linearEquiv X 0 (cupUnit X)) =
      Singular.unit (TopCat.of (ComplexPoint X)) := by
  rw [← bh11_cupComparison_eq_raw X 0 (cupUnit X), cupComparison_unit]

theorem ccm16_supportedComparison_forget_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S : Closeds (ComplexPoint X)) (n : ℕ) (u : H_[S]^n(X; ℚ)) :
    relativeCohomologyToAbsolute ℚ
      (TopPair.ofSubset (X := TopCat.of (ComplexPoint X)) (S : Set (ComplexPoint X))ᶜ) n
        (ccm16_supportedComparison X S n u) =
      rationalCohomologyLinearEquivSingular X n
        (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X S n u) := by
  rw [show ccm16_supportedComparison X S n u =
      ccm16_pairTransport (TopCat.of (ComplexPoint X)) S n
        (supportedSingularClass X S n u) from rfl]
  rw [ccm16_pairTransport_apply]
  rw [ccm16_relativeCohomologyToAbsolute_naturality]
  rw [ccm16_fullPairIso_fst]
  let (U : Opens (ComplexPoint X)) : ParacompactSpace U := openParacompactSpace X U
  apply (spec_singularToFieldCohomology_bijective ℚ X n).injective
  rw [singularToFieldCohomology_rationalCohomologyLinearEquivSingular]
  exact bh11_forget_support_singular_aux X S n u

private theorem ccm16_rawComparison_cup (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    {p q : ℕ} (a : HQ X p) (b : HQ X q) :
    rationalCohomologyLinearEquivSingular X (p + q)
        (HQ.linearEquiv X (p + q) ((cupProductOf X).cup rfl a b)) =
      Singular.cup (TopCat.of (ComplexPoint X)) rfl
        (rationalCohomologyLinearEquivSingular X p (HQ.linearEquiv X p a))
        (rationalCohomologyLinearEquivSingular X q (HQ.linearEquiv X q b)) := by
  rw [← bh11_cupComparison_eq_raw, cupComparison_cup,
    bh11_cupComparison_eq_raw, bh11_cupComparison_eq_raw]

theorem ccm16_supportedCup_forget_aux (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (S T : Closeds (ComplexPoint X)) (p q : ℕ)
    (u : H_[S]^p(X; ℚ)) (v : H_[T]^q(X; ℚ)) :
    (HQ.linearEquiv X (p + q)).symm
      (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X (S ⊓ T) (p + q)
        (ccm16_supportedCup X S T p q u v)) =
      (cupProductOf X).cup rfl
        ((HQ.linearEquiv X p).symm
          (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X S p u))
        ((HQ.linearEquiv X q).symm
          (AlgebraicGeometry.ComplexPoint.forgetSupport ℚ X T q v)) := by
  have hcup : ccm16_supportedComparison X (S ⊓ T) (p + q)
      (ccm16_supportedCup X S T p q u v) =
        ccm15_relativeCup (TopCat.of (ComplexPoint X)) S T p q
          (ccm16_supportedComparison X S p u)
          (ccm16_supportedComparison X T q v) := by
    simp [ccm16_supportedCup]
  have hout := ccm16_supportedComparison_forget_aux X (S ⊓ T) (p + q)
    (ccm16_supportedCup X S T p q u v)
  rw [hcup, ccm15_relativeCup_absolute,
    ccm16_supportedComparison_forget_aux, ccm16_supportedComparison_forget_aux] at hout
  have hp : HQ.linearEquiv X p
      ((HQ.linearEquiv X p).symm (ComplexPoint.forgetSupport ℚ X S p u)) =
        ComplexPoint.forgetSupport ℚ X S p u := LinearEquiv.apply_symm_apply _ _
  have hq : HQ.linearEquiv X q
      ((HQ.linearEquiv X q).symm (ComplexPoint.forgetSupport ℚ X T q v)) =
        ComplexPoint.forgetSupport ℚ X T q v := LinearEquiv.apply_symm_apply _ _
  have hraw := ccm16_rawComparison_cup X
    ((HQ.linearEquiv X p).symm (ComplexPoint.forgetSupport ℚ X S p u))
    ((HQ.linearEquiv X q).symm (ComplexPoint.forgetSupport ℚ X T q v))
  have hinputs := congrArg₂ (fun x y =>
      Singular.cup (TopCat.of (ComplexPoint X)) (rfl : p + q = p + q) x y)
    (congrArg (rationalCohomologyLinearEquivSingular X p) hp)
    (congrArg (rationalCohomologyLinearEquivSingular X q) hq)
  have hsheaf := (rationalCohomologyLinearEquivSingular X (p + q)).injective
    ((hout.symm.trans hinputs.symm).trans hraw.symm)
  have h := congrArg (HQ.linearEquiv X (p + q)).symm hsheaf
  rw [LinearEquiv.symm_apply_apply] at h
  exact h

end HodgeLean.Adapters

#print axioms HodgeLean.Adapters.ccm16_rawComparison_unit_aux
#print axioms HodgeLean.Adapters.ccm16_supportedComparison_forget_aux
#print axioms HodgeLean.Adapters.ccm16_supportedCup_forget_aux
