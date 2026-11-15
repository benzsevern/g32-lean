import HodgeLean.Foundations.IntegralHomology.StageTwo.Defs
import HodgeLean.Foundations.Program.SchoenTransferC1a4Proofs
import HodgeLean.Foundations.Program.SchoenTransferC1a5Proofs
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-! Finite normalized integral models from actual simplicial realizations.
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
open scoped Simplicial
namespace HodgeLean.Foundations.IntegralHomology.StageTwo

def normalizedIntegralBasis (K : SSet.{0}) (n : ℕ) :
    Module.Basis (K.nonDegenerate n) ℤ
      ((K.normalizedChainComplex (ModuleCat.of ℤ ℤ)).X n) :=
  (Finsupp.basisSingleOne (R := ℤ) (ι := K.nonDegenerate n)).map
    ((ModuleCat.finsuppCoconeIsColimit ℤ ℤ (K.nonDegenerate n)).coconePointUniqueUpToIso
      (K.isColimitCofanNormalizedChainComplex (ModuleCat.of ℤ ℤ) n)).toLinearEquiv

theorem normalizedIntegralBasis_apply (K : SSet.{0}) (n : ℕ)
    (s : K.nonDegenerate n) :
    normalizedIntegralBasis K n s =
      (K.ιNormalizedChainComplex (R := ModuleCat.of ℤ ℤ) s.val).hom 1 := by
  let e := (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (K.nonDegenerate n)).coconePointUniqueUpToIso
    (K.isColimitCofanNormalizedChainComplex (ModuleCat.of ℤ ℤ) n)
  change e.hom.hom (Finsupp.single s 1) = _
  have h := IsColimit.comp_coconePointUniqueUpToIso_hom
    (ModuleCat.finsuppCoconeIsColimit ℤ ℤ (K.nonDegenerate n))
    (K.isColimitCofanNormalizedChainComplex (ModuleCat.of ℤ ℤ) n) (Discrete.mk s)
  exact congrArg (fun f : ModuleCat.of ℤ ℤ ⟶ _ => f.hom 1) h

theorem normalized_integral_homotopy_comparison (K : SSet.{0}) [K.Finite]
    (X : TopCat.{0}) (e : SSet.toTop.obj K ≅ X) :
    ∃ h : HomotopyEquiv (K.normalizedChainComplex (ModuleCat.of ℤ ℤ)) (ZChains X),
      h.hom = K.fromNormalizedChainComplex (ModuleCat.of ℤ ℤ) ≫
        SSet.chainComplexMap (sSetTopAdj.unit.app K ≫ TopCat.toSSet.map e.hom)
          (ModuleCat.of ℤ ℤ) := by
  letI (n : ℕ) : Projective ((K.normalizedChainComplex (ModuleCat.of ℤ ℤ)).X n) :=
    ModuleCat.projective_of_free (normalizedIntegralBasis K n)
  letI (n : ℕ) : Projective ((ZChains X).X n) :=
    ModuleCat.projective_of_free
      ((Finsupp.basisSingleOne (R := ℤ) (ι := (TopCat.toSSet.obj X) _⦋n⦌)).map
        (chainGroupFinsuppIso ℤ X n).toLinearEquiv.symm)
  have hc := (HodgeLean.Foundations.Program.s4_c1a5_realization_comparison_aux K X e).2
  exact (ChainComplex.quasiIso_iff_of_projective _).mp hc

theorem finite_simplicial_model (K : SSet.{0}) [K.Finite]
    (X : TopCat.{0}) (e : SSet.toTop.obj K ≅ X) :
    ∃ M : FiniteChainModel X, ∀ n, M.rank n = Nat.card (K.nonDegenerate n) := by
  obtain ⟨d, hd⟩ := K.hasDimensionLT_of_finite
  letI := hd
  obtain ⟨h, _⟩ := normalized_integral_homotopy_comparison K X e
  refine ⟨{
    chains := K.normalizedChainComplex (ModuleCat.of ℤ ℤ)
    rank := fun n => Nat.card (K.nonDegenerate n)
    basis := fun n => (normalizedIntegralBasis K n).reindex (Finite.equivFin _)
    dimension := d
    bounded := ?_
    comparison := h }, fun _ => rfl⟩
  intro n hn
  haveI : IsEmpty (K.nonDegenerate n) := ⟨fun s =>
    (not_lt_of_ge (Nat.le_of_lt hn)) (K.dim_lt_of_nonDegenerate s d)⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end HodgeLean.Foundations.IntegralHomology.StageTwo
