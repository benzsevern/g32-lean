import HodgeLean.Adapters.CyclePushforwardDimension
import HodgeLean.Adapters.KleimanExpectedCoheight

noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem retained_integral_dimension_formula (X : Over (Spec ↧ℂ))
    [IsIntegral X.left] [LocallyOfFiniteType X.hom] (x : X.left) :
    Order.height x + Order.coheight x = TopologicalSpace.dim X.left := by
  obtain ⟨_, n, hn, _⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  have hdim : TopologicalSpace.dim X.left = n := by
    rw [TopologicalSpace.dim_eq_krullDim, ← Order.height_top_eq_krullDim]
    change (Order.height (genericPoint X.left)).toNat = n
    rw [hn, ENat.toNat_natCast]
  rw [hdim]
  refine hc9k8_height_add_coheight_of_integral X.hom n (fun U hU hne => ?_) x
  have : Nonempty U := hne.to_subtype
  let p := genericPoint (Spec Γ(X.left, U))
  have hp : hU.fromSpec p = genericPoint X.left := genericPoint_eq_of_isOpenImmersion _
  obtain ⟨_, m, hm, htr⟩ := a1d_height_chart (X := X) (genericPoint X.left) U hU p hp
  obtain ⟨_, l, hl, htr'⟩ := a1d_height_eq_trdeg (X := X) (genericPoint X.left)
  have hmn : m = n := by
    have hml : m = l := by exact_mod_cast htr.symm.trans htr'
    have hln : l = n := by exact_mod_cast hl.symm.trans hn
    exact hml.trans hln
  have hheight : (Order.height p : WithBot ℕ∞) = ringKrullDim Γ(X.left, U) := by
    dsimp only [p]
    rw [hc9k8_height_spec, genericPoint_eq_bot_of_affine]
    change ringKrullDim (Γ(X.left, U) ⧸ (⊥ : Ideal Γ(X.left, U))) = _
    exact ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)
  rw [← hheight, hm, hmn]
  rfl

end HodgeLean.Foundations.QuotientDuality
