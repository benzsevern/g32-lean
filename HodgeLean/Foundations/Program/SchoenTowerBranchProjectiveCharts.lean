import HodgeLean.Foundations.Program.SchoenTowerBranchAffine
import HodgeLean.Foundations.Program.SchoenTowerRetainedQuotientPullback
import HodgeLean.Foundations.Program.SchoenTowerPowerOpenRanges
import HodgeLean.Foundations.Program.SchoenTowerPowerAffine

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Foundations.Program

/-- The affine point-insertion immersion transports to a neighborhood in the retained projective quotient.
Source: Schoen (1988), printed p. 12; SGA 1, Exposé V, §1, invariant affine quotient charts. -/
theorem s2t_branch_projective_chart (C P B : Over (Spec ↧ℂ))
    [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    (n : ℕ) (U : C.left.Opens) (hU : IsAffineOpen U)
    (b : ComplexPoint (openScheme C U))
    (π : g3_power C n ⟶ P) (γ : g3_power C (n + 1) ⟶ B)
    (hπinv : ∀ σ, s2_permute C n σ ≫ π = π)
    (hπquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C n ⟶ T),
      (∀ σ, s2_permute C n σ ≫ f = f) → ∃! d : P ⟶ T, π ≫ d = f)
    (hγinv : ∀ σ, s2_permute C (n + 1) σ ≫ γ = γ)
    (hγquot : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (n + 1) ⟶ T),
      (∀ σ, s2_permute C (n + 1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) (ha : π ≫ a = s2c_branchInsertion C n (b ≫ openInclusion C U) ≫ γ) :
    ∃ V : B.left.Opens,
      γ.left ⁻¹' (V : Set B.left) = Set.range (s2_powerMap (openInclusion C U) (n + 1)).left ∧
      IsClosedImmersion (a.left ∣_ V) := by
  let D := openScheme C U
  let j := openInclusion C U
  letI : IsOpenImmersion j.left := inferInstanceAs (IsOpenImmersion U.ι)
  letI : IsAffine D.left := hU
  letI : Nonempty D.left := ⟨Point.underlying b⟩
  letI : IsIntegral D.left := isIntegral_of_isOpenImmersion j.left
  letI : Smooth D.hom := by change Smooth (j.left ≫ C.hom); infer_instance
  letI : IsAffine (terminal Scheme.{0}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.uniqueUpToIso terminalIsTerminal).inv
  letI (m : ℕ) : IsSeparated (terminal.from (g3_power C m).left) := by
    rw [← terminal.comp_from (g3_power C m).hom]
    infer_instance
  letI (m : ℕ) : IsAffine (g3_power D m).left := s2t_power_isAffine D m
  let ρP := s2_symmetricPowerAction D n
  let ρB := s2_symmetricPowerAction D (n + 1)
  let QP := s2t_affineQuotientOver (g3_power D n) (Equiv.Perm (Fin n)) ρP
  let QB := s2t_affineQuotientOver (g3_power D (n + 1)) (Equiv.Perm (Fin (n + 1))) ρB
  let qP := s2t_affineQuotientOverMap (g3_power D n) (Equiv.Perm (Fin n)) ρP
  let qB := s2t_affineQuotientOverMap (g3_power D (n + 1)) (Equiv.Perm (Fin (n + 1))) ρB
  letI : IsAffine QP.left := by dsimp [QP, s2t_affineQuotientOver]; infer_instance
  letI : IsAffine QB.left := by dsimp [QB, s2t_affineQuotientOver]; infer_instance
  have hiP : ∀ σ, s2_permute D n σ ≫ qP = qP :=
    s2t_affineQuotientOverMap_invariant (g3_power D n) (Equiv.Perm (Fin n)) ρP
  have hiB : ∀ σ, s2_permute D (n + 1) σ ≫ qB = qB :=
    s2t_affineQuotientOverMap_invariant (g3_power D (n + 1)) (Equiv.Perm (Fin (n + 1))) ρB
  have hqP : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power D n ⟶ T),
      (∀ σ, s2_permute D n σ ≫ f = f) → ∃! d : QP ⟶ T, qP ≫ d = f :=
    s2t_affineQuotientOverDesc (g3_power D n) (Equiv.Perm (Fin n)) ρP
  have hqB : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power D (n + 1) ⟶ T),
      (∀ σ, s2_permute D (n + 1) σ ≫ f = f) → ∃! d : QB ⟶ T, qB ≫ d = f :=
    s2t_affineQuotientOverDesc (g3_power D (n + 1)) (Equiv.Perm (Fin (n + 1))) ρB
  let jP := s2_powerMap j n
  let jB := s2_powerMap j (n + 1)
  letI : IsOpenImmersion jP.left := s2t_power_openImmersion D C j n
  letI : IsOpenImmersion jB.left := s2t_power_openImmersion D C j (n + 1)
  have heP (σ) : jP ≫ s2_permute C n σ = s2_permute D n σ ≫ jP :=
    s2t_powerMap_equivariant j n σ
  have heB (σ) : jB ≫ s2_permute C (n + 1) σ = s2_permute D (n + 1) σ ≫ jB :=
    s2t_powerMap_equivariant j (n + 1) σ
  obtain ⟨kP, hkP, _⟩ := hqP P (jP ≫ π) (by
    intro σ
    rw [← Category.assoc, ← heP, Category.assoc, hπinv])
  obtain ⟨kB, hkB, _⟩ := hqB B (jB ≫ γ) (by
    intro σ
    rw [← Category.assoc, ← heB, Category.assoc, hγinv])
  letI : IsOpenImmersion kP.left := s2t_retained_open_quotient
    (g3_power C n) (g3_power D n) QP P (Equiv.Perm (Fin n))
    (s2_symmetricPowerAction C n) ρP jP heP qP π hiP hqP hπinv hπquot kP hkP
  letI : IsOpenImmersion kB.left := s2t_retained_open_quotient
    (g3_power C (n + 1)) (g3_power D (n + 1)) QB B (Equiv.Perm (Fin (n + 1)))
    (s2_symmetricPowerAction C (n + 1)) ρB jB heB qB γ hiB hqB hγinv hγquot kB hkB
  have HP := s2t_retained_open_quotient_isPullback
    (g3_power C n) (g3_power D n) QP P (Equiv.Perm (Fin n))
    (s2_symmetricPowerAction C n) ρP jP heP qP π hiP hqP hπinv hπquot kP hkP
  have HB := s2t_retained_open_quotient_isPullback
    (g3_power C (n + 1)) (g3_power D (n + 1)) QB B (Equiv.Perm (Fin (n + 1)))
    (s2_symmetricPowerAction C (n + 1)) ρB jB heB qB γ hiB hqB hγinv hγquot kB hkB
  obtain ⟨d, hd, _⟩ := s2t_branch_descent D QP QB n b qP qB hqP hiB
  letI : IsClosedImmersion d.left :=
    s2t_branch_affine_immersion D QP QB n b qP qB hiP hqP hqB d hd
  letI : Epi qP := s2_invariantQuotient_epi (s2_permute D n) qP hiP hqP
  have hsq : d ≫ kB = kP ≫ a := by
    apply (cancel_epi qP).mp
    rw [← Category.assoc, hd, Category.assoc, hkB, ← Category.assoc,
      s2t_branchInsertion_powerMap, Category.assoc, ← ha, ← Category.assoc, ← Category.assoc, hkP]
  have hpreP : π.left ⁻¹' Set.range kP.left = Set.range jP.left := by
    have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback HP ⊤
    simp only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] at he
    exact congrArg (fun V : (g3_power C n).left.Opens => (V : Set (g3_power C n).left)) he.symm
  have hpreB : γ.left ⁻¹' Set.range kB.left = Set.range jB.left := by
    have he := IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback HB ⊤
    simp only [Scheme.Hom.preimage_top, Scheme.Hom.image_top_eq_opensRange] at he
    exact congrArg (fun V : (g3_power C (n + 1)).left.Opens =>
      (V : Set (g3_power C (n + 1)).left)) he.symm
  have hsπ := (s2t_retained_quotient_orbits (g3_power C n) P (Equiv.Perm (Fin n))
    (s2_symmetricPowerAction C n) π hπinv hπquot).1
  have hpre : a.left ⁻¹' Set.range kB.left = Set.range kP.left := by
    ext x
    obtain ⟨z, rfl⟩ := hsπ x
    have hz := congrArg (fun f : g3_power C n ⟶ B => f.left z) ha
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hz
    have h1 := congrArg (fun S : Set (g3_power C (n + 1)).left =>
      (s2c_branchInsertion C n (b ≫ j)).left z ∈ S) hpreB
    have h2 := congrArg (fun S : Set (g3_power C n).left => z ∈ S) hpreP
    have h3 := congrArg (fun S : Set (g3_power C n).left => z ∈ S)
      (s2t_branchInsertion_preimage_powerOpen C U n b)
    change a.left (π.left z) ∈ Set.range kB.left ↔ π.left z ∈ Set.range kP.left
    rw [hz]
    exact (h1.trans (h3.trans h2.symm)).to_iff
  have H : IsPullback d.left kP.left kB.left a.left := by
    apply IsOpenImmersion.isPullback d.left kP.left kB.left a.left
      (congrArg (fun f : QP ⟶ B => f.left) hsq).symm
    exact TopologicalSpace.Opens.ext hpre
  refine ⟨kB.left.opensRange, hpreB, ?_⟩
  apply (MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (morphismRestrictOpensRange a.left kB.left)).mpr
  rw [← H.flip.isoPullback_inv_snd]
  infer_instance

end HodgeLean.Foundations.Program
