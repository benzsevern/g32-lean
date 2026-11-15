import HodgeLean.Foundations.Program.SchoenCycleS3LinksProofs

/-! # S3 geometric links
Implication from coordinate ideals and coherent prefixes to residual restrictions
and intersection geometry over the complex base. HC no distance; AV milestone no distance.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Manifold AlgebraicGeometry.ComplexProjectiveSpace
open scoped BigOperators ContDiff
namespace HodgeLean.Foundations.Program

/-- Each coordinate ideal is locally free of rank one.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5, pp. 14–15;
Fulton, Intersection Theory, Appendix B; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_pair_cartier_on_slice
    (k : ℕ) (j : Fin (k + 1)) :
    ∀ x : ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      ∃ U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens,
        x ∈ U.1 ∧ Nonempty (((s2e_s2b_residueIdeal k j).ideal U)
          ≃ₗ[Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)] Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), U)) :=
  s2e_chain_pair_cartier_on_slice_aux k j

example := @s2e_chain_pair_cartier_on_slice

/-- Each unprocessed actual reduced branch retains its original coordinate ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5, pp. 14–15;
Fulton, Intersection Theory, Appendix B; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_unprocessed_pair_transverse
    (k r n : ℕ) (hn : n ≤ r) (ι : Fin r ↪ Fin (k + 1))
    (B : Fin (n + 1) → Over (Spec ↧ℂ))
    (b : ∀ i : Fin n, B i.succ ⟶ B i.castSucc)
    (D : ∀ i, Fin (2 * r) → (B i).left.IdealSheafData)
    (htransform : ∀ (i : Fin n) t,
      D i.succ t = s2c_strictTransform (b i).left (D i.castSucc t)
        (D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩))
    (hcartier : ∀ (i : Fin n) (x : (B i.succ).left),
      ∃ U : (B i.succ).left.affineOpens, x ∈ U.1 ∧
        Nonempty ((((D i.castSucc ⟨2 * i.val, by omega⟩ ⊔
          D i.castSucc ⟨2 * i.val + 1, by omega⟩).comap (b i).left).ideal U)
            ≃ₗ[Γ((B i.succ).left, U)] Γ((B i.succ).left, U)))
    (ℓ : ∀ i, Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)) ⟶ B i)
    (hfac : ∀ i : Fin n, ℓ i.succ ≫ b i = ℓ i.castSucc)
    (hresidue : ∀ j : Fin r,
      (D 0 ⟨2 * j.val, by omega⟩).comap (ℓ 0).left = s2e_s2b_residueIdeal k (ι j) ∧
      (D 0 ⟨2 * j.val + 1, by omega⟩).comap (ℓ 0).left = s2e_s2b_residueIdeal k (ι j)) :
    ∀ j : Fin r, n ≤ j.val →
      (D (Fin.last n) ⟨2 * j.val, by omega⟩).comap (ℓ (Fin.last n)).left =
        s2e_s2b_residueIdeal k (ι j) ∧
      (D (Fin.last n) ⟨2 * j.val + 1, by omega⟩).comap (ℓ (Fin.last n)).left =
        s2e_s2b_residueIdeal k (ι j) :=
  s2e_chain_unprocessed_pair_transverse_aux k r n hn ι B b D htransform hcartier ℓ hfac hresidue

example := @s2e_chain_unprocessed_pair_transverse

/-- The actual coordinate intersection has conormal rank T.card.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5, pp. 14–15;
Fulton, Intersection Theory, Appendix B; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_residue_conormal
    (k : ℕ) (T : Finset (Fin (k + 1))) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let I := s2e_s2b_intersectionIdeal k T
    ∀ x : (s2c_subscheme PP I).left,
      ∃ U : (s2c_subscheme PP I).left.Opens, x ∈ U ∧
        Nonempty (Scheme.Modules.restrict
          (s2c_conormal (s2c_subschemeι PP I).left) U.ι ≅
          (SheafOfModules.free (R := U.toScheme.ringCatSheaf) (Fin T.card) :
            U.toScheme.Modules)) :=
  s2e_chain_residue_conormal_aux k T

example := @s2e_chain_residue_conormal

/-- The coordinate intersection is projective space over the complex base.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5, pp. 14–15;
Fulton, Intersection Theory, Appendix B; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_residue_intersection_over_base
    (k : ℕ) (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) :
    Nonempty (s2c_subscheme
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
      (s2e_s2b_intersectionIdeal k T) ≅
      Over.mk (ProjectiveSpace.toBase (Fin (k - T.card + 1)) (Spec ↧ℂ))) :=
  s2e_chain_residue_intersection_over_base_aux k T hT

example := @s2e_chain_residue_intersection_over_base

/-- Transport an actual differential-locus ideal to its adapted coordinate ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemmas 2.4–2.5, pp. 14–15;
Fulton, Intersection Theory, Appendix B; Hartshorne, Algebraic Geometry, II.7. -/
theorem s2e_chain_adapted_residue_ideals
    (E C : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (k r : ℕ)
    [FiniteDimensional ℂ (b3_HolForm E C)]
    (hd : Module.finrank ℂ (b3_HolForm E C × (Fin r → ℂ)) = k + 1)
    (b : (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (b3_HolForm E C × (Fin r → ℂ)))
    (ι : Fin r ↪ Fin (k + 1)) (hb : ∀ v j, (b v).2 j = v (ι j)) :
    let PP := Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))
    let ep := s2e_finiteDimensionalProjectivePointEquiv
      (V := b3_HolForm E C × (Fin r → ℂ)) k hd
    let H : Fin r → PP.left.IdealSheafData := fun j =>
      Scheme.IdealSheafData.vanishingIdeal (TopologicalSpace.Closeds.closure
        (AlgebraicGeometry.Point.underlying ''
          {R : AlgebraicGeometry.ComplexPoint PP |
            ∃ (v : b3_HolForm E C × (Fin r → ℂ)) (hv : v ≠ 0),
              ep.symm R = Projectivization.mk ℂ v hv ∧ v.2 j = 0}))
    ∃ e : PP ≅ PP, ∀ j, (H j).comap e.hom.left = s2e_s2b_residueIdeal k (ι j) :=
  s2e_chain_adapted_residue_ideals_aux E C k r hd b ι hb

example := @s2e_chain_adapted_residue_ideals

end HodgeLean.Foundations.Program
