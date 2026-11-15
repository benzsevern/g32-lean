import HodgeLean.Foundations.Program.CurveJacobian
import HodgeLean.Foundations.Program.TorusAlgebraization
import HodgeLean.Adapters.GagaMaps

/-! # Analytic Albanese: quotient constructions

The construction uses the existing B2 quotient literally. The linear map is between the
universal covering vector spaces, rather than an endomorphism of one lattice.
HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped TensorProduct ContDiff CategoryTheory.MonObj
open Manifold CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.AnalyticAlbanese

/-- Descend a complex-linear map preserving the actual period subgroups.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, 2nd ed., §1.2.
HC no distance; AV milestone no distance. -/
def descend {Λ Μ : Type} [AddCommGroup Λ] [AddCommGroup Μ]
    (F : Submodule ℂ (ℂ ⊗[ℤ] Λ)) (G : Submodule ℂ (ℂ ⊗[ℤ] Μ))
    (L : ((ℂ ⊗[ℤ] Λ) ⧸ F) →ₗ[ℂ] ((ℂ ⊗[ℤ] Μ) ⧸ G))
    (hL : ∀ l : Λ, L (b2_latticeMap Λ F l) ∈ (b2_latticeMap Μ G).range) :
    b2_torus Λ F →+ b2_torus Μ G :=
  QuotientAddGroup.map _ _ L.toAddMonoidHom (by
    rintro _ ⟨l, rfl⟩
    exact hL l)

example : descend (Λ := Fin 2 → ℤ) b2_stdF b2_stdF
    ((2 : ℂ) • (LinearMap.id : _ →ₗ[ℂ] _))
    (fun l ↦ ⟨(2 : ℕ) • l, by simp only [LinearMap.id_apply, two_smul, map_add, LinearMap.add_apply]⟩)
    (QuotientAddGroup.mk ((1 / 3 : ℂ) • b3A_e 0)) =
      (QuotientAddGroup.mk ((2 / 3 : ℂ) • b3A_e 0) : b3_Elliptic) := by
  change QuotientAddGroup.mk ((2 : ℂ) • ((1 / 3 : ℂ) • b3A_e 0)) = _
  rw [smul_smul]
  norm_num

end HodgeLean.Foundations.AnalyticAlbanese
