import HodgeLean.Foundations.Program.G32Native.PELZariskiNormalizationExtension

noncomputable section
namespace HodgeLean.Foundations
open HodgeLean.Foundations.Program

/-- A subgroup containing an open neighborhood of the identity is open;
only continuity of left translations is needed. -/
theorem pel_subgroup_isOpen_of_patch {G : Type*} [Group G] [TopologicalSpace G]
    (hleft : ∀ a : G, Continuous (fun x : G => a * x))
    (H : Subgroup G) (U : Set G) (hU : IsOpen U) (hone : 1 ∈ U)
    (hUH : U ⊆ H) : IsOpen (H : Set G) := by
  have he : (H : Set G) = ⋃ h : H, (fun x : G => (h.val)⁻¹ * x) ⁻¹' U := by
    ext x
    constructor
    · intro hx
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by change x⁻¹ * x ∈ U; simpa only [inv_mul_cancel] using hone⟩
    · intro hx
      obtain ⟨h, hh⟩ := Set.mem_iUnion.mp hx
      have := H.mul_mem h.property (hUH hh)
      change x ∈ H
      simpa only [mul_inv_cancel_left] using this
  rw [he]
  exact isOpen_iUnion fun h => hU.preimage (hleft h.val⁻¹)

/-- To contain the Zariski identity component it suffices for a Zariski
closed subgroup to contain a relative open identity patch. -/
theorem pel_identityComponent_subset_of_open_patch {k : Type*} [Field k] {n : ℕ}
    (G : MatrixAlgGroup k n) (H : Subgroup (Matrix.GeneralLinearGroup (Fin n) k))
    (hH : @IsClosed _ (g1_zariski k n) (H : Set _))
    (U : Set G.carrier)
    (hU : @IsOpen _ (TopologicalSpace.induced (Subtype.val : G.carrier →
      Matrix.GeneralLinearGroup (Fin n) k) (g1_zariski k n)) U)
    (hone : (1 : G.carrier) ∈ U) (hUH : ∀ g ∈ U, g.val ∈ H) :
    g1_identityComponent G ⊆ (H : Set _) := by
  letI := g1_zariski k n
  let K : Subgroup G.carrier := H.comap G.carrier.subtype
  have hKc : IsClosed (K : Set G.carrier) := hH.preimage continuous_subtype_val
  have hleft : ∀ a : G.carrier, Continuous (fun x : G.carrier => a * x) := by
    intro a
    exact continuous_induced_rng.mpr
      ((g1_continuous_mul_left a.val).comp continuous_subtype_val)
  have hKo : IsOpen (K : Set G.carrier) :=
    pel_subgroup_isOpen_of_patch hleft K U hU hone hUH
  have hcomp := (show IsClopen (K : Set G.carrier) from ⟨hKc, hKo⟩).connectedComponent_subset
    K.one_mem
  intro g hg
  change g ∈ connectedComponentIn (G.carrier : Set _) 1 at hg
  rw [connectedComponentIn_eq_image G.carrier.one_mem] at hg
  obtain ⟨x, hx, rfl⟩ := hg
  exact hcomp hx

end HodgeLean.Foundations
