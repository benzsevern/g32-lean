import HodgeLean.Foundations.Program.SchoenTowerAffineSpaceHom
import HodgeLean.Foundations.Program.SchoenInvariantQuotientEpi

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- A categorical symmetric quotient descends every invariant global section.
Source: SGA 1, Exposé V, §1, categorical quotient property applied to the affine line. -/
theorem s2t_quotient_section_desc (C P : Over (Spec ↧ℂ)) (n : ℕ)
    (π : g3_power C n ⟶ P)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (p : Γ((g3_power C n).left, ⊤))
    (hp : ∀ σ, (s2_permute C n σ).left.appTop p = p) :
    ∃ q : Γ(P.left, ⊤), π.left.appTop q = p := by
  let L : Over (Spec ↧ℂ) := Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
  let f : g3_power C n ⟶ L :=
    (s2t_affineSpaceOverHomEquiv (g3_power C n) (Fin 1)).symm (fun _ => p)
  have hf (i : Fin 1) : f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i) = p :=
    s2t_affineSpaceOverHomEquiv_symm_coord _ _ _ _
  have hinv : ∀ σ, s2_permute C n σ ≫ f = f := by
    intro σ
    apply (s2t_affineSpaceOverHomEquiv (g3_power C n) (Fin 1)).injective
    funext i
    change (s2_permute C n σ ≫ f).left.appTop (AffineSpace.coord (Spec ↧ℂ) i) =
      f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i)
    rw [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, hp]
  obtain ⟨d, hd, _⟩ := hquot L f hinv
  refine ⟨d.left.appTop (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1)), ?_⟩
  have he := congrArg (fun t : g3_power C n ⟶ L =>
    t.left.appTop (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1))) hd
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf] using he

/-- Pullback of sections through the specified categorical symmetric quotient is injective.
Source: SGA 1, Exposé V, §1, categorical quotient property applied to the affine line. -/
theorem s2t_quotient_sections_injective (C P : Over (Spec ↧ℂ)) (n : ℕ)
    (π : g3_power C n ⟶ P)
    (hinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f) :
    Function.Injective π.left.appTop := by
  letI : Epi π := s2_invariantQuotient_epi (s2_permute C n) π hinv hquot
  intro p q hpq
  let L : Over (Spec ↧ℂ) := Over.mk (complexAffineSpace (Fin 1) ↘ Spec ↧ℂ)
  let f : P ⟶ L := (s2t_affineSpaceOverHomEquiv P (Fin 1)).symm (fun _ => p)
  let g : P ⟶ L := (s2t_affineSpaceOverHomEquiv P (Fin 1)).symm (fun _ => q)
  have hf (i : Fin 1) : f.left.appTop (AffineSpace.coord (Spec ↧ℂ) i) = p :=
    s2t_affineSpaceOverHomEquiv_symm_coord _ _ _ _
  have hg (i : Fin 1) : g.left.appTop (AffineSpace.coord (Spec ↧ℂ) i) = q :=
    s2t_affineSpaceOverHomEquiv_symm_coord _ _ _ _
  have hfg : π ≫ f = π ≫ g := by
    apply (s2t_affineSpaceOverHomEquiv (g3_power C n) (Fin 1)).injective
    funext i
    change (π ≫ f).left.appTop (AffineSpace.coord (Spec ↧ℂ) i) =
      (π ≫ g).left.appTop (AffineSpace.coord (Spec ↧ℂ) i)
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      hf, hg]
    exact hpq
  have he := congrArg (fun t : P ⟶ L =>
    t.left.appTop (AffineSpace.coord (Spec ↧ℂ) (0 : Fin 1))) ((cancel_epi π).mp hfg)
  simpa only [hf, hg] using he

end HodgeLean.Foundations.Program
