import HodgeLean.Foundations.BundleThom.RealNormalCapHelpers

/-! # Actual equatorial normal coordinates

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.BundleThom

/-- Head and tail coordinates identify the equatorial domain with punctured lower-dimensional space times the real line.
Source: Hatcher, Algebraic Topology, §2.2, equatorial product coordinates. -/
def i1_realNormalTailHomeomorph (d : ℕ) :
    {x : Fin (d + 1) → ℝ | Fin.tail x ≠ 0} ≃ₜ
      ({y : Fin d → ℝ | y ≠ 0} × ℝ) where
  toFun := fun x => (⟨Fin.tail x.1, x.2⟩, x.1 0)
  invFun := fun y => ⟨Fin.cons y.2 y.1.1, by
    change Fin.tail (Fin.cons y.2 y.1.1 : Fin (d + 1) → ℝ) ≠ 0
    rw [Fin.tail_cons]
    exact y.1.2⟩
  left_inv := fun x => Subtype.ext (Fin.cons_self_tail x.1)
  right_inv := fun y => by simp
  continuous_toFun := by
    apply Continuous.prodMk
    · exact (continuous_pi fun j => (continuous_apply j.succ).comp continuous_subtype_val).subtype_mk _
    · exact (continuous_apply 0).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply continuous_pi
    intro j
    refine Fin.cases continuous_snd (fun i => ?_) j
    exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)

end HodgeLean.Foundations.BundleThom
