import HodgeLean.Foundations.QuotientDuality.ProperCycleImageHeight

/-! # Proper images of smaller boundaries under actual generically finite maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual generically finite map cannot send a point of a proper source boundary to the generic target point.
Source: Hartshorne, Algebraic Geometry, exercise II.3.20; Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_generic_not_mem_image_boundary
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y)
    (hgeneric : f.left (genericPoint X.left) = genericPoint Y.left)
    (hdegree : 0 < a1p_degree f.left (genericPoint X.left))
    (B : Set X.left) (hB : genericPoint X.left ∉ B) :
    genericPoint Y.left ∉ f.left '' B := by
  rintro ⟨x, hxB, hfx⟩
  have hn : x ≠ genericPoint X.left := fun he => hB (he ▸ hxB)
  have hlt : x < genericPoint X.left := lt_iff_le_not_ge.mpr ⟨le_top, fun hge =>
    hn (((Scheme.le_iff_specializes.mp hge).antisymm
      (Scheme.le_iff_specializes.mp (show x ≤ genericPoint X.left from le_top))).eq)⟩
  obtain ⟨_, n, hnheight, _⟩ := a1d_height_eq_trdeg x
  have hstrict := Order.height_strictMono hlt (by rw [hnheight]; exact ENat.natCast_lt_top n)
  have he : Order.height (genericPoint Y.left) = Order.height (genericPoint X.left) := by
    rw [← hgeneric]
    exact (a1p_degree_pos_iff f _).mp hdegree
  have hle := properCycle_height_image_le f x
  rw [hfx, he] at hle
  exact (not_lt_of_ge hle) hstrict

end HodgeLean.Foundations.QuotientDuality
