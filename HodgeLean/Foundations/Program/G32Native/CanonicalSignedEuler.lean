import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalKernelGlobalEuler

/-! # Signed Euler on the retained projective component

The comparison input is the supported self-restriction output of U12.
The coordinate hyperplane and the projective identification remain fixed.
-/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.RealDefs
open HodgeLean.Foundations.Program.G32Native.EulerModel

namespace HodgeLean.Foundations.Program.G32Native

/-- Specialize the global normalized kernel calculation to the supplied immersion.
The comparison retains the actual global Thom class, with no scalar factor. -/
theorem canonicalSignedEuler
    {Q W₀ : Over (Spec ↧ℂ)}
    [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (hk : 0 < k)
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    [IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)).left]
    (ι : Q ⟶ W₀)
    (c : s2e_supportedClass W₀ (s2e_componentCycle ι ℚ) k)
    (hcomparison : s2e_normalEuler ι k c =
      s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) k
        (relativeCohomologyMap ℚ (2 * k) (normalComponentPointPairIso k eQ).inv
          (relativeCohomologyMap ℚ (2 * k) (projectiveNormalSectionPairMap k)
            (normalKernelGlobalThomClass k))))
    [IsIntegral (s2c_subscheme Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)).left]
    (cH : s2e_supportedClass Q (s2e_componentCycle
      (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1)
    (hcH : a3b4_IsCycleClass Q.hom _ 1 cH) :
    s2e_normalEuler ι k c = (-1 : ℚ) ^ k •
      s2e_hyperplanePower (TopCat.of (ComplexPoint Q))
        (s2e_classToAbsolute Q (s2e_componentCycle
          (s2c_subschemeι Q ((s2e_hyperplaneIdeal k).comap eQ.hom.left)) ℚ) 1 cH) k := by
  rw [hcomparison]
  exact normalKernelGlobalThomClass_hyperplane_sign Q k hk eQ cH hcH

#print axioms canonicalSignedEuler

/-- Native signed-Euler row for the same retained part and component.
The supported self-restriction comparison is an explicit input. -/
theorem canonicalSignedEuler_selected
    {J : Over (Spec ↧ℂ)} [GrpObj J] [IsCommMonObj J]
    [IsIntegral J.left] [Smooth J.hom] [IsProjective J.hom]
    {aut : g32p_G → (J ⟶ J)} {S : g32p_Supplier}
    (P : g32p_Part J aut S)
    (h : ℕ) (hh : 0 < h + 1) (hselected : h + 1 = 2 * P.k)
    {Q W₀ : Over (Spec ↧ℂ)}
    [IsIntegral W₀.left] [IsProjective W₀.hom]
    [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (P.k + 1)) (Spec ↧ℂ)))
    (ι : Q ⟶ W₀)
    (c : s2e_supportedClass W₀ (s2e_componentCycle ι ℚ) P.k)
    (hc : a3b4_IsCycleClass W₀.hom (s2e_componentCycle ι ℚ) P.k c)
    (hcomparison : ∀ (hpt : IsIntegral (s2c_subscheme Q
      ((s2e_s2b_intersectionIdeal P.k (Finset.univ.erase 0)).comap eQ.hom.left)).left),
      letI := hpt
      s2e_normalEuler ι P.k c =
      s2e_classToAbsolute Q (s2e_componentCycle (s2c_subschemeι Q
        ((s2e_s2b_intersectionIdeal P.k (Finset.univ.erase 0)).comap eQ.hom.left)) ℚ) P.k
        (relativeCohomologyMap ℚ (2 * P.k) (normalComponentPointPairIso P.k eQ).inv
          (relativeCohomologyMap ℚ (2 * P.k) (projectiveNormalSectionPairMap P.k)
            (normalKernelGlobalThomClass P.k)))) :
    let HI := (s2e_hyperplaneIdeal P.k).comap eQ.hom.left
    let QH := s2c_subscheme Q HI
    let jH := s2c_subschemeι Q HI
    ∃ (hH : IsIntegral QH.left),
      letI := hH
      ∃ cH, a3b4_IsCycleClass Q.hom (s2e_componentCycle jH ℚ) 1 cH ∧
        let H := relativeCohomologyToAbsolute ℚ _ 2 cH
        s2e_normalEuler ι P.k c = (-1 : ℚ) ^ P.k •
          s2e_hyperplanePower (TopCat.of (ComplexPoint Q)) H P.k := by
  have hk : 0 < P.k := by omega
  obtain ⟨hpt, _, _, _⟩ := coordinate_intersection_class Q P.k eQ
    (Finset.univ.erase 0) (by simp)
  letI := hpt
  obtain ⟨hH, cH, hcH⟩ := hyperplane_class Q P.k hk eQ
  letI := hH
  exact ⟨hH, cH, hcH, canonicalSignedEuler P.k hk eQ ι c (hcomparison hpt) cH hcH⟩

#print axioms canonicalSignedEuler_selected

end HodgeLean.Foundations.Program.G32Native
