import HodgeLean.Adapters.NormalConeB4aGysinBridge2PieceGeneration

/-! Actual local reduction along a topologically open reduced immersion. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters Topology
namespace HodgeLean.Foundations.Program

/-- A reduced immersed piece whose underlying image is open gives the actual
reduction of every stalk on that image. -/
theorem s4_q3_reduced_open_piece_stalk_kernel
    {P K : Scheme} [IsReduced P] (ψ : P ⟶ K) [IsImmersion ψ]
    (hψ : IsOpenEmbedding ψ.base) (x : P) :
    RingHom.ker (ψ.stalkMap x).hom = nilradical (K.presheaf.stalk (ψ x)) := by
  apply le_antisymm
  · intro r hr
    exact a3b4g_isNilpotent_of_stalkMap_eq_zero ψ hψ x r hr
  · intro r hr
    change (ψ.stalkMap x).hom r = 0
    exact (show IsNilpotent ((ψ.stalkMap x).hom r) from
      (show IsNilpotent r from hr).map (ψ.stalkMap x).hom).eq_zero

end HodgeLean.Foundations.Program
