import HodgeLean.Foundations.Program.PrymVariationCentreEigenLowerBound
import HodgeLean.Foundations.Program.PrymVariationCentreSaturationRange
import HodgeLean.Foundations.Program.PrymVariationCentreDimensions

noncomputable section
open HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program

theorem b63d_eigen_pullback_disjoint {M K : Type}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup K] [Module ℂ K]
    (T : M →ₗ[ℂ] M) (I : K →ₗ[ℂ] M) (hi : Function.Injective I)
    (F : Submodule ℂ K) (a b : ℂ) (hab : a ≠ b) :
    Disjoint (F ⊓ (LinearMap.ker (T - a • LinearMap.id)).comap I)
      (F ⊓ (LinearMap.ker (T - b • LinearMap.id)).comap I) := by
  apply Submodule.disjoint_def.mpr
  intro x hx hy
  have ha : T (I x) = a • I x := sub_eq_zero.mp hx.2
  have hb : T (I x) = b • I x := sub_eq_zero.mp hy.2
  have hz : (a - b) • I x = 0 := by rw [sub_smul, ← ha, ← hb, sub_self]
  have hix : I x = 0 := (smul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hab)
  exact hi (hix.trans (map_zero I).symm)

theorem b63d_period_centre_scalar (C : Type) [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [MulAction b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x)) :
    b4b_centreAct C hG = b4_latticeAct ℂ (C := C) b63d_scalarElement := by
  classical
  apply AddMonoidHom.ext
  intro y
  simp only [b4b_centreAct, AddMonoidHom.finsetSum_apply]
  simp_rw [b63d_scalarElement_unique]
  calc
    (∑ g : b4b_Group, (if g = b63d_scalarElement then b4_latticeAct ℂ g else 0) y) =
        ∑ g : b4b_Group, if g = b63d_scalarElement then b4_latticeAct ℂ g y else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      split <;> rfl
    _ = _ := by rw [Fintype.sum_ite_eq']


theorem b63d_finrank_three_of_disjoint {K : Type} [AddCommGroup K] [Module ℂ K]
    [FiniteDimensional ℂ K] (F A B : Submodule ℂ K)
    (hF : Module.finrank ℂ F = 6) (hA : A ≤ F) (hB : B ≤ F)
    (hd : Disjoint A B) (ha : 3 ≤ Module.finrank ℂ A) (hb : 3 ≤ Module.finrank ℂ B) :
    Module.finrank ℂ A = 3 ∧ Module.finrank ℂ B = 3 := by
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq A B
  rw [hd.eq_bot, finrank_bot, add_zero] at hsum
  have hdim := Submodule.finrank_mono (sup_le hA hB)
  omega

end HodgeLean.Foundations.Program
