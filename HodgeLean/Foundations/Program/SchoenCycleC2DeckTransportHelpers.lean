import HodgeLean.Foundations.Program.SchoenCycleC2ComponentUniquenessHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2IsoPointHelpers
import HodgeLean.Foundations.Program.SchoenCycleC2AbsoluteTransportHelpers

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters
namespace HodgeLean.Foundations.Program

/-- The absolute class of a forward component translate is inverse pullback
of the original normalized component class. -/
theorem s2e_componentCycle_absolute_deck_transport
    {Q W : Over (Spec ↧ℂ)} [IsIntegral Q.left]
    [LocallyOfFiniteType W.hom] [QuasiCompact W.hom] [IsSeparated W.hom]
    (ι : Q ⟶ W) [IsClosedImmersion ι.left] (δ : W ⟶ W) [IsIso δ]
    (k : ℕ) (U : W.left.Opens) (hU : Set.range ι.left ⊆ U)
    (hsm : Smooth (U.ι ≫ W.hom))
    (hcodim : ∀ x ∈ (s2e_componentCycle ι ℚ).support, Order.coheight x = k)
    (c : s2e_supportedClass W (s2e_componentCycle ι ℚ) k)
    (c' : s2e_supportedClass W (s2e_componentCycle (ι ≫ δ) ℚ) k)
    (hc : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k c)
    (hc' : a3b4_IsCycleClass W.hom (s2e_componentCycle (ι ≫ δ) ℚ) k c') :
    s2e_classToAbsolute W (s2e_componentCycle (ι ≫ δ) ℚ) k c' =
      s2e_pullback ℚ (inv δ) (2 * k)
        (s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k c) := by
  letI : IsClosedImmersion (ι ≫ δ).left := by
    change IsClosedImmersion (ι.left ≫ δ.left)
    infer_instance
  have hf : Topology.IsOpenEmbedding (Point.map δ) :=
    (s2e_pointHomeomorphOfIso (asIso δ)).isOpenEmbedding
  let b := relativeCohomologyMap ℚ (2 * k) (s2e_componentOpenPairMap ι δ) c'
  have hb : a3b4_IsCycleClass W.hom (s2e_componentCycle ι ℚ) k b :=
    s2e_componentCycle_normalized_open_pullback ι δ hf k
      (fun r e he z => s2e_iso_holomorphicChart_forward W W δ r k e he z)
      b c' hc' rfl
  have heq : b = c := s2e_componentCycle_class_unique_of_smooth_open ι k U hU hsm hcodim b c hb hc
  have hAbs := s2e_componentOpenPairMap_absolute ι δ k c'
  change s2e_classToAbsolute W (s2e_componentCycle ι ℚ) k b =
    s2e_pullback ℚ δ (2 * k) (s2e_classToAbsolute W (s2e_componentCycle (ι ≫ δ) ℚ) k c') at hAbs
  rw [heq] at hAbs
  have hInv := congrArg (s2e_pullback ℚ (inv δ) (2 * k)) hAbs
  rw [s2e_pullback_inv_cancel] at hInv
  exact hInv.symm

end HodgeLean.Foundations.Program
