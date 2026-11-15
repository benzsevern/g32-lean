import HodgeLean.Foundations.BundleThom.RealNormalCapProjectionHelpers
import HodgeLean.Foundations.BundleThom.RealNormalCapIntersectionHelpers

/-! # Actual caps inside punctured normal space

HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.BundleThom

/-- Every actual real normal cap lies in the punctured normal space.
Source: Hatcher, Algebraic Topology, §2.2, the hemisphere cover of punctured Euclidean space. -/
theorem i1_realNormalCap_ne_zero (d : ℕ) (positive : Bool)
    (x : Fin (d + 1) → ℝ) (hx : x ∈ i1_realNormalCap d positive) : x ≠ 0 := by
  have hm : x ∈ i1_realNormalCap d true ∪ i1_realNormalCap d false := by
    cases positive
    · exact Or.inr hx
    · exact Or.inl hx
  rw [i1_realNormalCap_union] at hm
  exact hm

/-- Viewing a cap inside punctured space retains exactly its actual subspace topology.
Source: Hatcher, Algebraic Topology, §0 and §2.2, subspace topology of hemisphere domains. -/
def i1_realNormalPuncturedCapHomeomorph (d : ℕ) (positive : Bool) :
    {x : {x : Fin (d + 1) → ℝ | x ≠ 0} | x.1 ∈ i1_realNormalCap d positive} ≃ₜ
      i1_realNormalCap d positive where
  toFun := fun x => ⟨x.1.1, x.2⟩
  invFun := fun x => ⟨⟨x.1, i1_realNormalCap_ne_zero d positive x.1 x.2⟩, x.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- Each cap remains contractible as an actual subspace of punctured normal space.
Source: Hatcher, Algebraic Topology, §2.2, contractions of the punctured-space cover domains. -/
theorem i1_realNormalPuncturedCap_contractible (d : ℕ) (positive : Bool) :
    ContractibleSpace
      {x : {x : Fin (d + 1) → ℝ | x ≠ 0} | x.1 ∈ i1_realNormalCap d positive} := by
  letI := i1_realNormalCap_contractible d positive
  exact (i1_realNormalPuncturedCapHomeomorph d positive).contractibleSpace

end HodgeLean.Foundations.BundleThom
