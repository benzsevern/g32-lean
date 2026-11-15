import HodgeLean.Foundations.IntegralHomology.StageThree.Basic
import HodgeLean.Foundations.Program.SchoenTransferC1a6IntegralLiftPairing

/-! # Naturality of singular lift cocycles

HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
open HodgeLean.Adapters HodgeLean.Foundations.Program
open HodgeLean.Foundations.IntegralHomology
open scoped Simplicial
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageTwo

/-- Lift cocycles commute with the actual singular chain map of a continuous map.
Source: Hatcher, §3.1; b3Rest2_LI_eq; SSet.ι_chainComplexMap_f.
HC no distance; AV milestone no distance. -/
theorem liftCocycle_natural {V J : Type} [AddCommGroup V] [TopologicalSpace V]
    [ContinuousAdd V] [AddCommGroup J] [TopologicalSpace J]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    {X Y : TopCat.{0}} (g : X ⟶ Y) (f : Y → J) (hf : Continuous f) (ℓ : V →+ ℂ) :
    (b3Rest2_liftCocycle π hπ (f ∘ g) (hf.comp g.hom.continuous) ℓ).val =
      (b3Rest2_liftCocycle π hπ f hf ℓ).val.comp
        ((SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℂ ℂ)).f 1).hom := by
  apply cochain_ext_simplex_b3Rest2
  intro σ
  let τ := (TopCat.toSSet.map g).app _ σ
  obtain ⟨F, hF⟩ := b3Rest2_exists_lift π hπ f hf (Y.toSSetObjEquiv _ τ)
  have hl := b3Rest2_LI_eq π hπ (f ∘ g) (hf.comp g.hom.continuous) ℓ σ F hF
  have hr := b3Rest2_LI_eq π hπ f hf ℓ τ F hF
  rw [b3Rest2_liftCocycle_apply]
  change b3Rest2_LI π hπ (f ∘ g) (hf.comp g.hom.continuous) ℓ σ =
    (b3Rest2_liftCocycle π hπ f hf ℓ).val
      ((((SSet.ιChainComplex (R := ModuleCat.of ℂ ℂ) _ σ) ≫
        (SSet.chainComplexMap (TopCat.toSSet.map g) (ModuleCat.of ℂ ℂ)).f 1)).hom 1)
  rw [SSet.ι_chainComplexMap_f]
  change b3Rest2_LI π hπ (f ∘ g) (hf.comp g.hom.continuous) ℓ σ =
    (b3Rest2_liftCocycle π hπ f hf ℓ).val
      (AlgebraicTopology.Simplicial.chainOfSimplex ℂ τ)
  rw [b3Rest2_liftCocycle_apply]
  exact hl.trans hr.symm

/-- Evaluation of lift cocycles on the integral torsion quotient is natural.
Source: Hatcher, §3.1; StageThree.cocycle_natural.
HC no distance; AV milestone no distance. -/
theorem liftCocycle_pairing_natural {V J : Type} [AddCommGroup V] [TopologicalSpace V]
    [ContinuousAdd V] [AddCommGroup J] [TopologicalSpace J]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    {X Y : TopCat.{0}} (g : X ⟶ Y) (f : Y → J) (hf : Continuous f) (ℓ : V →+ ℂ)
    (a : IntegralHomology.Lattice X) :
    StageThree.cocyclePairing X
      (b3Rest2_liftCocycle π hπ (f ∘ g) (hf.comp g.hom.continuous) ℓ) a =
      StageThree.cocyclePairing Y (b3Rest2_liftCocycle π hπ f hf ℓ) (mapLattice g a) :=
  StageThree.cocycle_natural X Y g _ _ (liftCocycle_natural π hπ g f hf ℓ) a

/-- A commuting continuous additive map of covers transports the lifted cocycle exactly.
Source: Hatcher, §1.3 and §3.1; b3Rest2_LI_eq.
HC no distance; AV milestone no distance. -/
theorem liftCocycle_transport
    {V W J K X : Type} [AddCommGroup V] [TopologicalSpace V] [ContinuousAdd V]
    [AddCommGroup W] [TopologicalSpace W] [ContinuousAdd W]
    [AddCommGroup J] [TopologicalSpace J] [AddCommGroup K] [TopologicalSpace K]
    [TopologicalSpace X]
    (π : V →+ J) (hπ : IsCoveringMap π ∧ Function.Surjective π)
    (ρ : W →+ K) (hρ : IsCoveringMap ρ ∧ Function.Surjective ρ)
    (D : V →+ W) (hD : Continuous D)
    (f : X → J) (hf : Continuous f) (g : X → K) (hg : Continuous g)
    (hcomm : ∀ x v, π v = f x → ρ (D v) = g x) (ℓ : W →+ ℂ) :
    b3Rest2_liftCocycle ρ hρ g hg ℓ = b3Rest2_liftCocycle π hπ f hf (ℓ.comp D) := by
  apply Subtype.ext
  apply cochain_ext_simplex_b3Rest2
  intro σ
  obtain ⟨F, hF⟩ := b3Rest2_exists_lift π hπ f hf ((TopCat.of X).toSSetObjEquiv _ σ)
  let G : C(Convexity.StdSimplex ℝ (Fin 2), W) := ⟨D ∘ F, hD.comp F.continuous⟩
  have hG : ∀ t, ρ (G t) = g ((TopCat.of X).toSSetObjEquiv _ σ t) :=
    fun t ↦ hcomm _ _ (hF t)
  rw [b3Rest2_liftCocycle_apply, b3Rest2_liftCocycle_apply,
    b3Rest2_LI_eq ρ hρ g hg ℓ σ G hG, b3Rest2_LI_eq π hπ f hf (ℓ.comp D) σ F hF]
  exact congrArg ℓ (map_sub D _ _).symm

#print axioms liftCocycle_natural
#print axioms liftCocycle_pairing_natural
#print axioms liftCocycle_transport

end HodgeLean.Foundations.Curves.AbelAdapter.StageTwo
