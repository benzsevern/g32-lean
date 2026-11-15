import HodgeLean.Foundations.Program.SchoenCycleAffineIdealJets
import HodgeLean.Foundations.Program.SchoenCycleQuotientJets
import HodgeLean.Foundations.Program.SchoenCycleInvariantIdealJets
import HodgeLean.Foundations.Program.SchoenCycleStabilizerJets
import HodgeLean.Foundations.Program.SchoenCyclePointIdealStabilizer
import HodgeLean.Foundations.Program.SchoenCycleAffineStalkJets
import HodgeLean.Foundations.Program.SchoenCycleFixedStalkAction

/-! # Ideal membership in actual quotient affine jets -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A stabilizer-invariant finite jet in a stable ideal on an actual quotient chart descends within the contraction of that ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants and invariant affine section descent. -/
theorem s2e_quotient_stabilizer_ideal_jet_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U)
    (H : Subgroup G) (I : Ideal Γ(X.left, q.left ⁻¹ᵁ U)) [I.IsMaximal]
    (J : Ideal Γ(X.left, q.left ⁻¹ᵁ U))
    (N : ℕ) (b : Γ(X.left, q.left ⁻¹ᵁ U)) (hbJ : b ∈ J) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)
    (∀ g, ∀ r ∈ J, α g r ∈ J) →
    (∀ g, I.comap (α g).toRingHom = I ↔ g ∈ H) →
    (∀ g ∈ H, α g b - b ∈ I ^ N) →
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c ∈ J ∧
      (q.left.app U).hom c - b ∈ I ^ N := by
  classical
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  letI : Fintype G := Fintype.ofFinite G
  dsimp only
  intro hJ hstab hb
  obtain ⟨b', hbJ', hb', hcongr⟩ := s2e_maximal_stabilizer_ideal_jet_extension G Γ(X.left, W)
    (MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)) H I hstab J hJ N b hbJ hb
  have hi (u : G) : ((a u).left.appLE W W
      (s2e_step1_action_preimage X Y q (a u) (hinv u) U)).hom b' = b' := by
    have h := hb' u⁻¹
    change u⁻¹ • b' = b' at h
    change ((a ((u⁻¹)⁻¹)).left.appLE W W
      (s2e_step1_action_preimage X Y q (a ((u⁻¹)⁻¹)) (hinv ((u⁻¹)⁻¹)) U)).hom b' = b' at h
    simpa only [inv_inv] using h
  obtain ⟨c, hc, _⟩ := s2e_step1_invariant_affine_descent X Y G a ha1 hamul
    q hinv hquot U hU b' hi
  exact ⟨c, hc ▸ hbJ', hc ▸ hcongr⟩

/-- Jets in a stable ideal at an actual complex point descend within the contraction of that ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants; Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_quotient_complex_point_stabilizer_ideal_jet_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (H : Subgroup G)
    (x : AlgebraicGeometry.ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
    (hH : ∀ g, AlgebraicGeometry.Point.map (a g) x = x ↔ g ∈ H)
    (J : Ideal Γ(X.left, q.left ⁻¹ᵁ U))
    (N : ℕ) (b : Γ(X.left, q.left ⁻¹ᵁ U)) (hbJ : b ∈ J) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)
    let ε := s2e_step1_pointEvaluation X (q.left ⁻¹ᵁ U) x hx
    (∀ g, ∀ r ∈ J, α g r ∈ J) →
    (∀ g ∈ H, α g b - b ∈ RingHom.ker ε.toRingHom ^ N) →
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c ∈ J ∧
      (q.left.app U).hom c - b ∈ RingHom.ker ε.toRingHom ^ N := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)
  let ε := s2e_step1_pointEvaluation X W x hx
  let I := RingHom.ker ε.toRingHom
  have hsurj : Function.Surjective ε := by
    intro z
    exact ⟨algebraMap ℂ Γ(X.left, W) z, by
      simpa only [Algebra.algebraMap_self, RingHom.id_apply] using ε.commutes z⟩
  letI : I.IsMaximal := RingHom.ker_isMaximal_of_surjective ε.toRingHom hsurj
  have hW : IsAffineOpen W := hU.preimage q.left
  have hstab (g : G) : I.comap (α g).toRingHom = I ↔ g ∈ H := by
    have hs : I.comap (α g).toRingHom = I ↔ AlgebraicGeometry.Point.map (a g⁻¹) x = x :=
      s2e_quotient_point_ideal_stabilizer X Y G a ha1 hamul q hinv U hW x hx g
    exact hs.trans ((hH g⁻¹).trans H.inv_mem_iff)
  dsimp only
  intro hJ hb
  exact s2e_quotient_stabilizer_ideal_jet_descent X Y G a ha1 hamul q hinv hquot U hU H I J N b hbJ hJ hstab hb

/-- Stabilizer-invariant germs of sections in a stable ideal descend to quotient sections in the contraction of that ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_quotient_complex_point_stalk_ideal_jet_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (H : Subgroup G)
    (x : AlgebraicGeometry.ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
    (hclosed : IsClosed ({x.underlying} : Set X.left))
    (hH : ∀ g, AlgebraicGeometry.Point.map (a g) x = x ↔ g ∈ H)
    (J : Ideal Γ(X.left, q.left ⁻¹ᵁ U))
    (N : ℕ) (b : Γ(X.left, q.left ⁻¹ᵁ U)) (hbJ : b ∈ J) :
    letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
    letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
    letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
    let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)
    (∀ g, ∀ r ∈ J, α g r ∈ J) →
    (∀ g ∈ H, (X.left.presheaf.germ (q.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom
      (α g b - b) ∈ IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N) →
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c ∈ J ∧
      (X.left.presheaf.germ (q.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom
        ((q.left.app U).hom c - b) ∈
          IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  let α := MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)
  let ε := s2e_step1_pointEvaluation X W x hx
  let I := RingHom.ker ε.toRingHom
  have hW : IsAffineOpen W := hU.preimage q.left
  have hI : I = (hW.primeIdealOf ⟨x.underlying, hx trivial⟩).asIdeal :=
    s2e_pointEvaluation_kernel_primeIdealOf X W hW x hx
  have hmem (s : Γ(X.left, W)) :
      (X.left.presheaf.germ W x.underlying (hx trivial)).hom s ∈
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N ↔ s ∈ I ^ N := by
    rw [hI]
    exact s2e_affine_stalk_power_jet_mem_iff X.left W hW x.underlying (hx trivial) hclosed N s
  dsimp only
  intro hJ hb
  have hbI (g : G) (hg : g ∈ H) : α g b - b ∈ I ^ N := (hmem _).mp (hb g hg)
  obtain ⟨c, hcJ, hc⟩ := s2e_quotient_complex_point_stabilizer_ideal_jet_descent
    X Y G a ha1 hamul q hinv hquot U hU H x hx hH J N b hbJ hJ hbI
  exact ⟨c, hcJ, (hmem _).mpr hc⟩

/-- Every stabilizer-invariant finite stalk jet in a stable affine ideal descends within its actual contraction.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Mumford–Fogarty–Kirwan, Geometric Invariant Theory, 3rd ed., Chapter 1, §1,
finite quotient local invariants; Hartshorne, Algebraic Geometry, II.2 and II.5. -/
theorem s2e_quotient_invariant_stalk_ideal_jet_descent
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsIntegral Y.left]
    (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ u v, a (u * v) = a v ≫ a u)
    (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left]
    (hinv : ∀ u, a u ≫ q = q)
    (hquot : ∀ (T : Over (Spec ↧ℂ)) (v : X ⟶ T),
      (∀ u, a u ≫ v = v) → ∃! w : Y ⟶ T, q ≫ w = v)
    (U : Y.left.Opens) (hU : IsAffineOpen U) (H : Subgroup G)
    (x : AlgebraicGeometry.ComplexPoint X)
    (hx : ⊤ ≤ x.left ⁻¹ᵁ (q.left ⁻¹ᵁ U))
    (hclosed : IsClosed ({x.underlying} : Set X.left))
    (hH : ∀ g, AlgebraicGeometry.Point.map (a g) x = x ↔ g ∈ H)
    (J : Ideal Γ(X.left, q.left ⁻¹ᵁ U))
    (hJ : letI := s2e_step1_sectionAlgebra X (q.left ⁻¹ᵁ U)
      letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
      letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
      ∀ g, ∀ s ∈ J,
        (MulSemiringAction.toAlgAut G ℂ Γ(X.left, q.left ⁻¹ᵁ U)) g s ∈ J)
    (N : ℕ) (r : X.left.presheaf.stalk x.underlying)
    (hrJ : r ∈ J.map
      (X.left.presheaf.germ (q.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom)
    (hr : ∀ (g : G) (hg : g ∈ H),
      s2e_fixed_point_stalkPullback X.left (a g).left x.underlying
        (s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)) r - r ∈
        IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N) :
    ∃ c : Γ(Y.left, U), (q.left.app U).hom c ∈ J ∧
      (X.left.presheaf.germ (q.left ⁻¹ᵁ U) x.underlying (hx trivial)).hom
        ((q.left.app U).hom c) - r ∈
          IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N := by
  let W := q.left ⁻¹ᵁ U
  letI := s2e_step1_sectionAlgebra X W
  letI := s2e_step1_sectionAction X Y G a ha1 hamul q hinv U
  letI := s2e_step1_sectionAction_smulComm X Y G a ha1 hamul q hinv U
  have hfix (g : G) (hg : g ∈ H) : (a g).left x.underlying = x.underlying :=
    s2e_complex_point_fixed_underlying X (a g) x ((hH g).mpr hg)
  have hW : IsAffineOpen W := hU.preimage q.left
  obtain ⟨b, hbJ, hb⟩ := s2e_affine_ideal_stalk_jet_representative X.left W hW
    x.underlying (hx trivial) hclosed J N r hrJ
  have hb' := (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N).neg_mem hb
  rw [neg_sub] at hb'
  have hi (g : G) (hg : g ∈ H) :
      (X.left.presheaf.germ W x.underlying (hx trivial)).hom
        ((MulSemiringAction.toAlgAut G ℂ Γ(X.left, W)) g b - b) ∈
          IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N := by
    exact s2e_fixed_point_section_jet_invariant X.left (a g⁻¹).left x.underlying
      (hfix g⁻¹ (H.inv_mem hg)) W
      (s2e_step1_action_preimage X Y q (a g⁻¹) (hinv g⁻¹) U)
      (hx trivial) N r (hr g⁻¹ (H.inv_mem hg)) b hb'
  obtain ⟨c, hcJ, hc⟩ := s2e_quotient_complex_point_stalk_ideal_jet_descent X Y G a ha1 hamul
    q hinv hquot U hU H x hx hclosed hH J N b hbJ hJ hi
  refine ⟨c, hcJ, ?_⟩
  have hs := (IsLocalRing.maximalIdeal (X.left.presheaf.stalk x.underlying) ^ N).add_mem hc hb'
  rw [map_sub, sub_add_sub_cancel] at hs
  exact hs

end HodgeLean.Foundations.Program
