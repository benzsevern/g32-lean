import HodgeLean.Foundations.BundleThom.RealNormalPuncturedCapHelpers

/-! # Lower-dimensional coordinates on the actual punctured equator

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.BundleThom

/-- Forgetting the redundant nonzero condition identifies the actual punctured equator with its ambient nonzero-tail domain.
Source: Hatcher, Algebraic Topology, §2.2, the equatorial intersection in punctured space. -/
def i1_realNormalPuncturedEquatorForgetHomeomorph (d : ℕ) :
    {x : {x : Fin (d + 1) → ℝ | x ≠ 0} | Fin.tail x.1 ≠ 0} ≃ₜ
      {x : Fin (d + 1) → ℝ | Fin.tail x ≠ 0} where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x =>
    ⟨⟨x.1, i1_realNormalCap_ne_zero d true x.1 (Or.inl x.2)⟩, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- The actual product equator has lower-dimensional punctured normal coordinates and a real factor.
Source: Hatcher, Algebraic Topology, §2.2, product coordinates on the equator. -/
def i1_realNormalProductEquatorHomeomorph (B : Type) [TopologicalSpace B] (d : ℕ) :
    {p : B × {x : Fin (d + 1) → ℝ | x ≠ 0} | Fin.tail p.2.1 ≠ 0} ≃ₜ
      ((B × {y : Fin d → ℝ | y ≠ 0}) × ℝ) :=
  (i1_productSecondSubsetHomeomorph B {x : Fin (d + 1) → ℝ | x ≠ 0}
    {x | Fin.tail x.1 ≠ 0}).trans
    (((Homeomorph.refl B).prodCongr
      ((i1_realNormalPuncturedEquatorForgetHomeomorph d).trans
        (i1_realNormalTailHomeomorph d))).trans
      (Homeomorph.prodAssoc B {y : Fin d → ℝ | y ≠ 0} ℝ).symm)

end HodgeLean.Foundations.BundleThom
