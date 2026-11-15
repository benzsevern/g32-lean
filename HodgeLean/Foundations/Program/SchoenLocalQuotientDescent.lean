import HodgeLean.Foundations.Program.SchoenInvariantOpenRefinements

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A restricted invariant map with image in an affine target open descends
through the actual quotient of its invariant affine source open. -/
theorem s2_invariantOpen_quotientDesc {X T : Scheme.{0}} [IsIntegral X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    (f : X ⟶ T) (hf : ∀ g : G, (ρ g).asIso.hom ≫ f = f)
    (U : X.Opens) (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty)
    (hInv : ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U)
    (V : T.Opens) (hV : IsAffineOpen V) (hUV : U ≤ f ⁻¹ᵁ V) :
    letI : IsAffine U.toScheme := hU
    letI := s2_schemeSectionAction U.toScheme G (s2_invariantOpenAction G ρ U hInv)
    ∃! d : Spec (CommRingCat.of (FixedPoints.subring Γ(U.toScheme, ⊤) G)) ⟶ T,
      s2_affineSchemeQuotientMap U.toScheme G (s2_invariantOpenAction G ρ U hInv) ≫ d =
        U.ι ≫ f := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine V.toScheme := hV
  haveI : Nonempty U := hne.to_subtype
  haveI : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  let ρU := s2_invariantOpenAction G ρ U hInv
  let fU := f.resLE V U hUV
  have hfu : ∀ g : G, (ρU g).asIso.hom ≫ fU = fU := by
    intro g
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
    change s2_invariantOpenMap U (ρ g).asIso.hom (hInv g).ge ≫ U.ι ≫ f = _
    rw [s2_invariantOpenMap_ι_assoc, hf g]
  obtain ⟨d, hd, _⟩ := s2_affineSchemeQuotientDesc G ρU fU hfu
  have hdf : s2_affineSchemeQuotientMap U.toScheme G ρU ≫ (d ≫ V.ι) = U.ι ≫ f := by
    rw [← Category.assoc, hd, Scheme.Hom.resLE_comp_ι]
  haveI := s2_affineSchemeQuotientMap_epi U.toScheme G ρU
  refine ⟨d ≫ V.ι, hdf, ?_⟩
  intro e he
  exact (cancel_epi (s2_affineSchemeQuotientMap U.toScheme G ρU)).mp (he.trans hdf.symm)

end HodgeLean.Foundations.Program
