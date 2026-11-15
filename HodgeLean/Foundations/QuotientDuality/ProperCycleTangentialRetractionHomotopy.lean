import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupport

/-! # Actual tangential interpolation fixing a normal support fibre
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Interpolate the actual tangential retraction coordinates to the original tangential coordinates while retaining the literal normal coordinate.
Source: Hatcher, Algebraic Topology, section 0, straight-line homotopy in a real vector space.
HC no distance; AV milestone no distance. -/
def properCycle_tangential_retraction_homotopy
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (U : Set (E × Y)) (r : C(U, E)) :
    TopCat.Homotopy
      (TopCat.ofHom ⟨fun u : U => (r u, u.val.2), r.continuous.prodMk
        (continuous_snd.comp continuous_subtype_val)⟩ : TopCat.of U ⟶ TopCat.of (E × Y))
      (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) where
  toFun tu := ((1 - (tu.1 : ℝ)) • r tu.2 + (tu.1 : ℝ) • tu.2.val.1, tu.2.val.2)
  continuous_toFun := by fun_prop
  map_zero_left u := by
    change ((1 - (0 : ℝ)) • r u + (0 : ℝ) • u.val.1, u.val.2) = (r u, u.val.2)
    rw [sub_zero, one_smul, zero_smul, add_zero]
  map_one_left u := by
    change ((1 - (1 : ℝ)) • r u + (1 : ℝ) • u.val.1, u.val.2) = (u.val.1, u.val.2)
    rw [sub_self, zero_smul, one_smul, zero_add]

/-- If the tangential coordinates agree on the actual normal fibre, the entire interpolation preserves the original point complement.
Source: properCycle_tangential_retraction_homotopy; add_smul.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_retraction_homotopy_avoids_point
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (U : Set (E × Y)) (hU : (0, y) ∈ U)
    (r : C(U, E)) (hr : ∀ u : U, u.val.2 = y → r u = u.val.1)
    (t : unitInterval) (u : U) (hu : u ≠ ⟨(0, y), hU⟩) :
    properCycle_tangential_retraction_homotopy E Y U r (t, u) ≠ (0, y) := by
  intro he
  have hn : u.val.2 = y := congrArg Prod.snd he
  have ht := congrArg Prod.fst he
  change (1 - (t : ℝ)) • r u + (t : ℝ) • u.val.1 = 0 at ht
  rw [hr u hn, ← add_smul, sub_add_cancel, one_smul] at ht
  exact hu (Subtype.ext (Prod.ext ht hn))

end HodgeLean.Foundations.QuotientDuality
