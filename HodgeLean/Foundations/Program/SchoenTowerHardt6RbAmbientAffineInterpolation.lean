import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.AffineSpace.Basis

/-! Ambient affine maps realizing arbitrary heights on an independent finite vertex family. -/
noncomputable section
namespace HodgeLean.Foundations.Program

theorem s2v_hardt6rb_ambient_affine_interpolation {E : Type*}
    [AddCommGroup E] [Module ℝ E] (s : Finset E)
    (hs : AffineIndependent ℝ (fun x : s => (x.val : E))) (a : s → ℝ) :
    ∃ f : E →ᵃ[ℝ] ℝ, ∀ x : s, f x.val = a x := by
  classical
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ E := ⟨Subtype.val, ht, by simpa using hspan⟩
  let e : s → t := fun x => ⟨x.val, hst x.property⟩
  have he : Function.Injective e := fun x y h => Subtype.ext (congrArg (fun z : t => z.val) h)
  let f : E →ᵃ[ℝ] ℝ := ∑ i : s, a i • b.coord (e i)
  refine ⟨f, ?_⟩
  intro x
  let ev : (E →ᵃ[ℝ] ℝ) →+ ℝ :=
    { toFun := fun g => g (b (e x)), map_zero' := rfl, map_add' := fun _ _ => rfl }
  change ev (∑ i : s, a i • b.coord (e i)) = a x
  rw [map_sum]
  change (∑ i : s, a i * b.coord (e i) (b (e x))) = a x
  simp [b.coord_apply, he.eq_iff]

end HodgeLean.Foundations.Program
