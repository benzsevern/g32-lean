import HodgeLean.Foundations.Program.G32Native.UnionConormalAffineSchemeIdealEpi
import HodgeLean.Foundations.Program.G32Native.UnionConormalEpiNatIso
import HodgeLean.Foundations.AlgebraicGeometry.ConormalOpenComparison

/-! # Epic ideal comparison with an affine original ambient scheme -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open AlgebraicGeometry.Conormal

/-- Cartesian comparison of immersion ideals is epic when the original
ambient scheme is affine. -/
lemma unionConormal_idealMap_epi_of_affine_target
    {Q Q' W W' : Scheme.{0}} (i : Q ⟶ W) (i' : Q' ⟶ W')
    [IsClosedImmersion i] [IsClosedImmersion i'] [IsAffine W]
    (f : W' ⟶ W) (g : Q' ⟶ Q) (sq : IsPullback g i' i f) :
    Epi (idealPullbackMap i i' f g sq.w) := by
  apply unionConormal_epi_of_open_neighborhoods
  intro x
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (X := W')
    (U := ⊤) (x := x) (show x ∈ (⊤ : W'.Opens) from trivial)
  have : IsAffine V.toScheme := hV
  have sqV : IsPullback ((i' ⁻¹ᵁ V).ι ≫ g) (i' ∣_ V) i (V.ι ≫ f) :=
    (isPullback_morphismRestrict i' V).flip.paste_horiz sq
  have : Epi (idealPullbackMap i (i' ∣_ V) (V.ι ≫ f) ((i' ⁻¹ᵁ V).ι ≫ g) sqV.w) :=
    unionConormal_idealMap_epi_of_isAffine i (i' ∣_ V) (V.ι ≫ f) _ sqV
  have : IsIso (idealPullbackMap i' (i' ∣_ V) V.ι (i' ⁻¹ᵁ V).ι
      (morphismRestrict_ι i' V).symm) := idealPullbackMap_open_isIso i' V
  haveI := unionConormal_idealMap_map_epi_of_comp i i' (i' ∣_ V) f V.ι g
    (i' ⁻¹ᵁ V).ι sq.w (morphismRestrict_ι i' V).symm sqV.w
  exact ⟨V, hx, unionConormal_epi_map_of_natIso
    (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm
    (idealPullbackMap i i' f g sq.w)⟩

end HodgeLean.Foundations.Program.G32Native
