import HodgeLean.Foundations.Program.G32Native.PairedC3FullSystemFibre
import HodgeLean.Foundations.Program.G32Native.PairedResidualFlatFibre
import HodgeLean.Foundations.Program.G32Native.PairedResidualJacobianDimension

/-! # The genus-rank conormal frame of the full initial Abel fibre -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.Foundations.Curves.AbelAdapter
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
variable
    (Z B : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (k r d : ℕ)
    (y : Fin (2 * r) → ComplexPoint Z) (hy : Function.Injective y)
    (W : Submodule ℂ (TangentBundle 𝓘(ℂ, Fin 1 → ℂ) (ComplexPoint Z) → ℂ))
    (hW : ∀ q, q ∈ W ↔ b4c_IsMeroForm (Module.finrank_fin_fun (n := 1) ℂ) q ∧
      (∀ p, ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      (∀ p ∉ Set.range y, AnalyticAt ℂ
        (HurwitzPrymRR_loc (Module.finrank_fin_fun (n := 1) ℂ) q p) 0) ∧
      ∀ p ∈ Set.range y, ∀ u, q ⟨p, u⟩ = 0)
    [FiniteDimensional ℂ W]
    (hgenus : 2 * k + 2 = 2 * Module.finrank ℂ
      (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) + 2 * r)
    (hd : Module.finrank ℂ W = d + 1)
    (γ : g3_power Z (2 * k) ⟶ B) [IsFinite γ.left]
    (hγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ)
    (hsurj : Function.Surjective (Point.map γ))
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
      (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v)

include hy hW hgenus hd hγ hsurj hquot
local instance : ConnectedSpace (ComplexPoint Z) := AlgebraicGeometry.ComplexPoint.connectedSpace Z
local notation "hOne" => (Module.finrank_fin_fun (n := 1) ℂ)

/-- The full initial fixed Abel fibre has a conormal frame of genus rank
in the full symmetric quotient. This concerns the full fibre before any
blow-up, and retains its actual differential-divisor map.
Source: ACGH, Geometry of Algebraic Curves I, IV.1; Hartshorne,
Algebraic Geometry, II.8, Theorem 8.17; Schoen, Compositio Mathematica
65 (1988), Lemma 2.3(ii). -/
theorem paired_c3_full_abel_fibre_conormal
    (hr : 0 < r) (p : ComplexPoint Z)
    (a : B ⟶ model (C := ComplexPoint Z) hOne)
    (ha : Point.map (γ ≫ a) = fun u => theta (C := ComplexPoint Z) hOne
      (∑ i, analyticAbel (C := ComplexPoint Z) hOne p (Point.map (g3_proj Z (2 * k) i) u)))
    (v : W) (hv : v ≠ 0) :
    let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
    ∃ ℓ : Over.mk (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) ⟶ B,
      IsClosedImmersion ℓ.left ∧
      (Point.map ℓ = fun R => residualProjectiveSystemPoint hOne y hy W
        (fun q => (hW q.val).mp q.property) hgenus γ id (ep.symm R)) ∧
      Nonempty (s2c_conormal ℓ.left ≅
        (SheafOfModules.free (R :=
          (ProjectiveSpace (Fin (d + 1)) (Spec ↧ℂ)).ringCatSheaf)
          (Fin (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)))) :
            (ProjectiveSpace (Fin (d + 1)) (Spec ↧ℂ)).Modules)) := by
  obtain ⟨ℓ, him, hℓ, e, he₁, he₂⟩ := paired_c3_full_system_abel_fibre
    Z B k r d y hy W hW hgenus hd γ hγ hsurj hquot hr p a ha v hv
  letI : IsClosedImmersion ℓ.left := him
  letI : Surjective γ.left := s2e_step1_surjective_of_complexPoint_surjective _ _ γ hsurj
  letI : SmoothOfRelativeDimension (2 * k) B.hom :=
    s2e_retained_quotient_relative_dimension Z B (2 * k) γ hγ hquot
  have hsum : ∀ u, (theta (C := ComplexPoint Z) hOne).symm (Point.map a (Point.map γ u)) =
      ∑ i, analyticAbel hOne p (Point.map (g3_proj Z (2 * k) i) u) := by
    intro u
    have hu := (Point.map_comp_apply γ a u).symm.trans (congrFun ha u)
    exact (congrArg (theta (C := ComplexPoint Z) hOne).symm hu).trans
      ((theta (C := ComplexPoint Z) hOne).symm_apply_apply _)
  have hdeg : 2 * (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2 <
      ((2 * k : ℕ) : ℤ) := by omega
  letI : Smooth a.left := residual_algebraic_abel_smooth Z B (2 * k) γ hγ hsurj hquot
    a p hsum hdeg
  letI := residual_jacobian_smooth_dimension (C := ComplexPoint Z) hOne
  let ep := s2e_finiteDimensionalProjectivePointEquiv (V := W) d hd
  let z := Point.map (ℓ ≫ a) (ep (Projectivization.mk ℂ v hv))
  letI : IsClosedImmersion z.left := by
    haveI : IsClosedImmersion (z.left ≫ (model (C := ComplexPoint Z) hOne).hom) := by
      rw [Over.w z]
      change IsClosedImmersion (𝟙 (Spec ↧ℂ))
      infer_instance
    exact IsClosedImmersion.of_comp z.left (model (C := ComplexPoint Z) hOne).hom
  have sq : IsPullback ℓ.left (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ))
      a.left z.left := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ e he₁ he₂
    rw [← he₁, Category.assoc, pullback.condition, ← Category.assoc, he₂]
  refine ⟨ℓ, him, hℓ, ⟨?_⟩⟩
  exact (Scheme.Modules.pullbackId _).symm.app (s2c_conormal ℓ.left) ≪≫
    residual_flat_fibre_source_iso (model (C := ComplexPoint Z) hOne)
      (Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z))) z ℓ.left a.left
      (ProjectiveSpace.toBase (Fin (d + 1)) (Spec ↧ℂ)) sq.flip (𝟙 _)

#print axioms paired_c3_full_abel_fibre_conormal
end HodgeLean.Foundations.Program.G32Native
