import HodgeLean.Foundations.Program.G32Native.CanonicalNormalDifferential
import HodgeLean.Foundations.Program.G32Native.NormalIdentificationTransport
import HodgeLean.Foundations.Program.SchoenCycleU1
import HodgeLean.Foundations.Curves.AbelAdapter.StageTwo.PeriodBasisCoordinates
import HodgeLean.Foundations.Curves.AbelAdapter.Defs

/-! # Retained geometry for the canonical Abel differential -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
open HodgeLean.Adapters
open scoped BigOperators Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Input geometry of a specified canonical Abel fibre and its specified etale sheet.
Source: ACGH, Geometry of Algebraic Curves I, IV.1–IV.3, canonical Abel fibres.
The fields retain the original maps and the original projective coordinates. -/
structure CanonicalAbelGeometry where
  k : ℕ
  Z : Over (Spec ↧ℂ)
  B : Over (Spec ↧ℂ)
  W : Over (Spec ↧ℂ)
  Q : Over (Spec ↧ℂ)
  integralZ : IsIntegral Z.left
  smoothCurve : Smooth Z.hom
  smoothZ : SmoothOfRelativeDimension 1 Z.hom
  projectiveZ : IsProjective Z.hom
  integralB : IsIntegral B.left
  smoothB : SmoothOfRelativeDimension (k + k) B.hom
  projectiveB : IsProjective B.hom
  smoothW : SmoothOfRelativeDimension (k + k) W.hom
  smoothQ : SmoothOfRelativeDimension k Q.hom
  γ : g3_power Z (2 * k) ⟶ B
  finiteγ : IsFinite γ.left
  surjectiveγ : Function.Surjective (Point.map γ)
  invariantγ : ∀ σ, s2_permute Z (2 * k) σ ≫ γ = γ
  quotientγ : ∀ (T : Over (Spec ↧ℂ)) (v : g3_power Z (2 * k) ⟶ T),
    (∀ σ, s2_permute Z (2 * k) σ ≫ v = v) → ∃! u : B ⟶ T, γ ≫ u = v
  β : W ⟶ B
  etaleβ : Etale β.left
  ℓ : Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B
  eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
  ι : Q ⟶ W
  immersion : IsClosedImmersion ι.left
  square : ι ≫ β = eQ.hom ≫ ℓ
  hd : Module.finrank ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) = k + 1
  hg : ((2 * k : ℕ) : ℤ) = 2 * (Module.finrank ℂ
    (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) : ℤ) - 2
  canonical : letI := integralZ
    letI := smoothCurve
    letI := smoothZ
    letI := projectiveZ
    letI : FiniteDimensional ℂ (b3_HolForm (Fin 1 → ℂ) (ComplexPoint Z)) :=
      Module.finite_of_finrank_pos (by rw [hd]; omega)
    Point.map ℓ = fun R => s2e_canonicalQuotientPoint Z B (2 * k) γ hg
      ((s2e_finiteDimensionalProjectivePointEquiv k hd).symm R)

attribute [instance] CanonicalAbelGeometry.integralZ CanonicalAbelGeometry.smoothZ
  CanonicalAbelGeometry.smoothCurve CanonicalAbelGeometry.projectiveZ CanonicalAbelGeometry.integralB
  CanonicalAbelGeometry.smoothB CanonicalAbelGeometry.projectiveB
  CanonicalAbelGeometry.smoothW CanonicalAbelGeometry.smoothQ
  CanonicalAbelGeometry.finiteγ CanonicalAbelGeometry.etaleβ CanonicalAbelGeometry.immersion

/-- Coefficient vectors act on homogeneous forms by the fixed ordered-coordinate pairing.
Source: ACGH, Geometry of Algebraic Curves I, IV.1, coordinates on the dual of holomorphic forms. -/
def coefficientDual (k : ℕ) : (Fin (k + 1) → ℂ) →ₗ[ℂ] Module.Dual ℂ (Fin (k + 1) → ℂ) where
  toFun v := {
    toFun a := ∑ i, a i * v i
    map_add' a b := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
    map_smul' c a := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      mul_assoc, Finset.mul_sum] }
  map_add' v w := by
    apply LinearMap.ext
    intro a
    change (∑ i, a i * (v i + w i)) = (∑ i, a i * v i) + ∑ i, a i * w i
    simp only [mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    apply LinearMap.ext
    intro a
    change (∑ i, a i * (c * v i)) = c * ∑ i, a i * v i
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- The homogeneous-kernel total space has the local evaluation topology used by I1.
Source: Voisin, Hodge Theory and Complex Algebraic Geometry I, 7.1, analytic vector bundles. -/
def coefficientTotalTopology (G : CanonicalAbelGeometry) :
    TopologicalSpace (TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator)) :=
  TopologicalSpace.induced
    (fun z : TotalSpace (Fin G.k → ℂ)
      (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator) =>
        (z.proj, fun a : Fin (G.k + 1) → ℂ => z.2.1 a)) inferInstance

example (k : ℕ) (v a : Fin (k + 1) → ℂ) :
    coefficientDual k v a = ∑ i, a i * v i := rfl

example (G : CanonicalAbelGeometry) : coefficientTotalTopology G =
    TopologicalSpace.induced
      (fun z : TotalSpace (Fin G.k → ℂ)
        (fun x => (g32n_homogeneousLine G.k G.eQ x).submodule.dualAnnihilator) =>
          (z.proj, fun a : Fin (G.k + 1) → ℂ => z.2.1 a)) inferInstance := rfl

#print axioms coefficientDual
#print axioms coefficientTotalTopology
end HodgeLean.Foundations.Program.G32Native
