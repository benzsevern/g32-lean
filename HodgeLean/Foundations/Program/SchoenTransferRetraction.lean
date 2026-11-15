import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Retractions within a finite-dimensional stable space of operators. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s4_retraction_in_stable_submodule
    {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V] [FiniteDimensional K W]
    (S : Submodule K (W →ₗ[K] V)) (f : V →ₗ[K] W) (g : W →ₗ[K] V)
    (hg : g ∈ S)
    (hstable : ∀ T ∈ S, (g.comp f).comp T ∈ S)
    (hinj : Function.Injective (g.comp f)) :
    ∃ T ∈ S, T.comp f = LinearMap.id := by
  let M := g.comp f
  let R : S →ₗ[K] S :=
    { toFun := fun T => ⟨M.comp T.val, hstable T.val T.property⟩
      map_add' := by
        intro T U
        apply Subtype.ext
        ext w
        exact M.map_add (T.val w) (U.val w)
      map_smul' := by
        intro c T
        apply Subtype.ext
        ext w
        exact M.map_smul c (T.val w) }
  have hR : Function.Injective R := by
    intro T U h
    apply Subtype.ext
    ext w
    apply hinj
    exact congrArg (fun Z : S => Z.val w) h
  obtain ⟨T, hT⟩ := LinearMap.surjective_of_injective hR ⟨g, hg⟩
  refine ⟨T.val, T.property, ?_⟩
  ext v
  apply hinj
  exact congrArg (fun Z : S => Z.val (f v)) hT

end HodgeLean.Foundations.Program
