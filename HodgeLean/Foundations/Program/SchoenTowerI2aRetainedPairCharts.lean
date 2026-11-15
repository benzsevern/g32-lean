import HodgeLean.Foundations.Program.SchoenTowerI2aRetainedPairCoverage

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The retained blowup of two nonzero affine branch sections is covered by
their two actual Rees spectra, as open immersions over the original base.
Source: Hartshorne, Algebraic Geometry, II.7, Proposition 7.13. -/
theorem s2v_i2a_retained_pair_rees_charts
    (Q : Scheme.{0}) (R : Type) [CommRing R] [IsDomain R]
    (π : Spec (CommRingCat.of R) ⟶ Q) (B : Over Q)
    [IsIntegral B.left] [IsLocallyNoetherian B.left]
    (b : B ⟶ Over.mk π) (K : (Spec (CommRingCat.of R)).IdealSheafData)
    (huniv : ∀ (Z : Over Q) (h : Z ⟶ Over.mk π),
      (∀ p : Z.left, ∃ U : Z.left.affineOpens, p ∈ U.1 ∧
        Nonempty (((K.comap h.left).ideal U) ≃ₗ[Γ(Z.left, U)] Γ(Z.left, U))) →
      ∃! v : Z ⟶ B, v ≫ b = h)
    (hcartier : ∀ p : B.left, ∃ U : B.left.affineOpens, p ∈ U.1 ∧
      Nonempty (((K.comap b.left).ideal U) ≃ₗ[Γ(B.left, U)] Γ(B.left, U)))
    (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (hK : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {x, y}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom) :
    ∃ (gx : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {x, y}) x)) ⟶ B.left)
      (gy : Spec (CommRingCat.of (s2t_reesChart (Ideal.span {y, x}) y)) ⟶ B.left),
      IsOpenImmersion gx ∧ IsOpenImmersion gy ∧
      gx ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ∧
      gy ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) ∧
      ∀ p : B.left, p ∈ Set.range gx ∨ p ∈ Set.range gy := by
  have hKy : K.ideal ⟨⊤, isAffineOpen_top _⟩ =
      (Ideal.span {y, x}).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom := by
    simpa only [Set.pair_comm y x] using hK
  obtain ⟨gx, hgx, _⟩ := s2v_i2a_rees_chart_to_retained_blowup Q (Over.mk π) B b K huniv
    R π (𝟙 _) (Ideal.span {x, y}) x (Ideal.subset_span (by simp)) hx
    (by simpa using hK)
  obtain ⟨gy, hgy, _⟩ := s2v_i2a_rees_chart_to_retained_blowup Q (Over.mk π) B b K huniv
    R π (𝟙 _) (Ideal.span {y, x}) y (Ideal.subset_span (by simp)) hy
    (by simpa using hKy)
  have hxbase : gx.left ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
    simpa using congrArg (fun f => f.left) hgx
  have hybase : gy.left ≫ b.left = Spec.map (CommRingCat.ofHom (algebraMap R _)) := by
    simpa using congrArg (fun f => f.left) hgy
  exact ⟨gx.left, gy.left,
    s2v_i2a_retained_rees_open_immersion Q R π B b K huniv hcartier x y hx hK gx.left hxbase,
    s2v_i2a_retained_rees_open_immersion Q R π B b K huniv hcartier y x hy hKy gy.left hybase,
    hxbase, hybase,
    s2v_i2a_retained_pair_rees_cover Q R π B b K huniv hcartier x y hK gx.left gy.left hxbase hybase⟩

end HodgeLean.Foundations.Program
