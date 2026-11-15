import HodgeLean.Foundations.Program.SchoenTowerI2aCoefficientEmbedding
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Finite extensions at actual affine field points
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A locally quasi-finite actual affine field point is finite over every intermediate coefficient field.
Source: Mathlib, HasRingHomProperty.appTop, Algebra.QuasiFinite.of_restrictScalars and Module.Finite.of_quasiFinite. -/
theorem s2v_i2a_affine_field_point_finite
    {K : Type*} [Field K] {U : Scheme} [IsAffine U]
    (η : Spec (CommRingCat.of K) ⟶ U) [LocallyQuasiFinite η] :
    let φ : Γ(U, ⊤) →+* K := (η.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom
    letI := φ.toAlgebra
    ∀ (F : Type*) [Field F] [Algebra Γ(U, ⊤) F] [Algebra F K]
      [IsScalarTower Γ(U, ⊤) F K], Module.Finite F K := by
  intro φ
  letI : Algebra Γ(U, ⊤) K := φ.toAlgebra
  intro F hF hRF hFK hT
  have hη : η.appTop.hom.QuasiFinite :=
    HasRingHomProperty.appTop (P := @LocallyQuasiFinite) η inferInstance
  have he : (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.Finite :=
    RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.surjective
  have hφ : φ.QuasiFinite := (RingHom.QuasiFinite.of_finite he).comp hη
  letI : Algebra.QuasiFinite Γ(U, ⊤) K := hφ
  letI : Algebra.QuasiFinite F K := .of_restrictScalars Γ(U, ⊤) F K
  exact Module.Finite.of_quasiFinite

/-- Local quasi-finiteness of the initial field point propagates through every retained factorization.
Source: Mathlib, LocallyQuasiFinite.of_comp and Fin.induction. -/
theorem s2v_i2a_tower_field_points_locallyQuasiFinite
    {K : Type*} [Field K] (r : ℕ) (B : Fin (r + 1) → Scheme)
    (b : ∀ i : Fin r, B i.succ ⟶ B i.castSucc)
    (η : ∀ i, Spec (CommRingCat.of K) ⟶ B i)
    (hη : ∀ i : Fin r, η i.succ ≫ b i = η i.castSucc)
    [LocallyQuasiFinite (η 0)] : ∀ i, LocallyQuasiFinite (η i) := by
  intro i
  induction i using Fin.induction with
  | zero => infer_instance
  | succ j ih =>
    letI := ih
    haveI : LocallyQuasiFinite (η j.succ ≫ b j) := by rw [hη]; infer_instance
    exact LocallyQuasiFinite.of_comp (η j.succ) (b j)

end HodgeLean.Foundations.Program
