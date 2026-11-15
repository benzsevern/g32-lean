import HodgeLean.Foundations.Program.SchoenTowerI1aFiniteHelpers
import HodgeLean.Foundations.Program.SchoenTowerI1aInvariantTopology

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open scoped Pointwise
namespace HodgeLean.Foundations.Program

lemma s2v_i1ahi_chart_smulCommClass
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
    letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
    SMulCommClass G (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  constructor
  intro g c r
  change ((a g⁻¹).left.appLE U U _).hom (c.val * r) =
    c.val * ((a g⁻¹).left.appLE U U _).hom r
  rw [map_mul, c.property g⁻¹]

lemma s2v_i1ahi_chart_prime_action
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (g : G) (P : PrimeSpectrum Γ(X.left, U)) :
    letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
    g • P = (Spec.map ((a g).left.appLE U U (hiU g))) P := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  apply PrimeSpectrum.ext
  ext r
  change r ∈ g • P.asIdeal ↔ ((a g).left.appLE U U (hiU g)).hom r ∈ P.asIdeal
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  change ((a (g⁻¹)⁻¹).left.appLE U U _).hom r ∈ P.asIdeal ↔ _
  simp only [inv_inv]

lemma s2v_i1ahi_chart_fromSpec_action
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (g : G) (P : PrimeSpectrum Γ(X.left, U)) :
    letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
    hU.fromSpec (g • P) = (a g).left (hU.fromSpec P) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  rw [s2v_i1ahi_chart_prime_action X G a ha1 hamul U hiU g P]
  exact congrArg (fun f : Spec Γ(X.left, U) ⟶ X.left => f P)
    (hU.SpecMap_appLE_fromSpec (a g).left hU (hiU g))

lemma s2v_i1ahi_chart_image_fromSpec
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) (N : Set X.left) :
    s2v_i1a_affineQuotientMap X G a U hiU '' {x | U.ι x ∈ N} =
      PrimeSpectrum.comap (s2v_i1a_chartInvariants X G a U hiU).subtype ''
        (hU.fromSpec ⁻¹' N) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U.toSpecΓ x, ?_, rfl⟩
    change (U.toSpecΓ ≫ hU.fromSpec) x ∈ N
    rw [hU.toSpecΓ_fromSpec]
    exact hx
  · rintro ⟨P, hP, rfl⟩
    refine ⟨hU.isoSpec.inv P, hP, ?_⟩
    change (hU.isoSpec.inv ≫ U.toSpecΓ ≫
      Spec.map (CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype)) P = _
    rw [hU.isoSpec_inv_toSpecΓ_assoc]
    rfl

lemma s2v_i1ahi_chart_open_image
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (N : X.left.Opens) (hiN : ∀ g, N ≤ (a g).left ⁻¹ᵁ N) :
    IsOpen (s2v_i1a_affineQuotientMap X G a U hiU '' {x | U.ι x ∈ N}) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  letI := s2v_i1ahi_chart_isInvariant X G a ha1 hamul U hiU
  letI := s2v_i1ahi_chart_smulCommClass X G a ha1 hamul U hiU
  change IsOpen (s2v_i1a_affineQuotientMap X G a U hiU '' {x | U.ι x ∈ (N : Set X.left)})
  rw [s2v_i1ahi_chart_image_fromSpec X G a U hU hiU (N : Set X.left)]
  apply s2v_i1ahi_invariant_open_image (G := G) _ (N.isOpen.preimage hU.fromSpec.continuous)
  intro g P hP
  change hU.fromSpec (g • P) ∈ N
  rw [s2v_i1ahi_chart_fromSpec_action X G a ha1 hamul U hU hiU]
  exact hiN g hP

lemma s2v_i1ahi_chart_saturated_preimage
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (N : X.left.Opens) (hiN : ∀ g, N ≤ (a g).left ⁻¹ᵁ N) :
    s2v_i1a_affineQuotientMap X G a U hiU ⁻¹'
      (s2v_i1a_affineQuotientMap X G a U hiU '' {x | U.ι x ∈ N}) =
        {x | U.ι x ∈ N} := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  letI := s2v_i1ahi_chart_isInvariant X G a ha1 hamul U hiU
  letI := s2v_i1ahi_chart_smulCommClass X G a ha1 hamul U hiU
  have hstable (g : G) (P : PrimeSpectrum Γ(X.left, U))
      (hP : P ∈ hU.fromSpec ⁻¹' (N : Set X.left)) :
      g • P ∈ hU.fromSpec ⁻¹' (N : Set X.left) := by
    change hU.fromSpec (g • P) ∈ N
    rw [s2v_i1ahi_chart_fromSpec_action X G a ha1 hamul U hU hiU]
    exact hiN g hP
  have hs := s2v_i1ahi_invariant_open_saturation
    (A := s2v_i1a_chartInvariants X G a U hiU) (G := G)
    (hU.fromSpec ⁻¹' (N : Set X.left)) hstable
  change _ ⁻¹' (_ '' {x | U.ι x ∈ (N : Set X.left)}) = _
  rw [s2v_i1ahi_chart_image_fromSpec X G a U hU hiU (N : Set X.left)]
  ext x
  have hx := Set.ext_iff.mp hs (U.toSpecΓ x)
  change PrimeSpectrum.comap (s2v_i1a_chartInvariants X G a U hiU).subtype
      (U.toSpecΓ x) ∈ (PrimeSpectrum.comap (s2v_i1a_chartInvariants X G a U hiU).subtype ''
        (hU.fromSpec ⁻¹' (N : Set X.left))) ↔ hU.fromSpec (U.toSpecΓ x) ∈ N at hx
  refine hx.trans ?_
  change hU.fromSpec (U.toSpecΓ x) ∈ N ↔ U.ι x ∈ N
  rw [← Scheme.Hom.comp_apply, hU.toSpecΓ_fromSpec]

lemma s2v_i1ahi_chart_surjective
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) :
    Surjective (s2v_i1a_affineQuotientMap X G a U hiU) := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  letI := s2v_i1ahi_chart_isInvariant X G a ha1 hamul U hiU
  letI := Algebra.IsInvariant.isIntegral
    (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U) G
  haveI : IsIso U.toSpecΓ := by change IsIso hU.isoSpec.hom; infer_instance
  haveI : Surjective (Spec.map (CommRingCat.ofHom
      (s2v_i1a_chartInvariants X G a U hiU).subtype)) :=
    ⟨Algebra.IsIntegral.comap_surjective _ _⟩
  exact inferInstanceAs (Surjective (U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (s2v_i1a_chartInvariants X G a U hiU).subtype)))

lemma s2v_i1ahi_chart_scheme_point_orbit
    (X : Over (Spec ↧ℂ)) (G : Type) [Group G] [Finite G]
    (a : G → (X ⟶ X)) (ha1 : a 1 = 𝟙 X)
    (hamul : ∀ g h, a (g * h) = a h ≫ a g)
    (U : X.left.Opens) (hU : IsAffineOpen U)
    (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U)
    (x y : U.toScheme)
    (hxy : s2v_i1a_affineQuotientMap X G a U hiU x =
      s2v_i1a_affineQuotientMap X G a U hiU y) :
    ∃ g : G, (a g).left (U.ι x) = U.ι y := by
  letI := s2v_i1ahi_chartAction X G a ha1 hamul U hiU
  letI := (s2v_i1a_chartInvariants X G a U hiU).subtype.toAlgebra
  letI := s2v_i1ahi_chart_isInvariant X G a ha1 hamul U hiU
  letI := s2v_i1ahi_chart_smulCommClass X G a ha1 hamul U hiU
  have he : PrimeSpectrum.comap (algebraMap
      (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U)) (U.toSpecΓ x) =
    PrimeSpectrum.comap (algebraMap
      (s2v_i1a_chartInvariants X G a U hiU) Γ(X.left, U)) (U.toSpecΓ y) := hxy
  obtain ⟨g, hg⟩ := s2v_i1ahi_prime_fibre_orbit (G := G) (U.toSpecΓ x) (U.toSpecΓ y) he
  refine ⟨g, ?_⟩
  have hp := congrArg hU.fromSpec hg
  rw [s2v_i1ahi_chart_fromSpec_action X G a ha1 hamul U hU hiU] at hp
  have hu (t : U.toScheme) : hU.fromSpec (U.toSpecΓ t) = U.ι t :=
    congrArg (fun f : U.toScheme ⟶ X.left => f t) hU.toSpecΓ_fromSpec
  rw [hu x, hu y] at hp
  exact hp.symm

lemma s2v_i1ahi_chart_quotient_invariant
    (X : Over (Spec ↧ℂ)) (G : Type) (a : G → (X ⟶ X))
    (U : X.left.Opens) (hiU : ∀ g, U ≤ (a g).left ⁻¹ᵁ U) (g : G) :
    (a g).left.resLE U U (hiU g) ≫ s2v_i1a_affineQuotientMap X G a U hiU =
      s2v_i1a_affineQuotientMap X G a U hiU := by
  let j := CommRingCat.ofHom (s2v_i1a_chartInvariants X G a U hiU).subtype
  have he : j ≫ (a g).left.appLE U U (hiU g) = j := by
    ext r
    exact r.property g
  change (a g).left.resLE U U (hiU g) ≫ (U.toSpecΓ ≫ Spec.map j) =
    U.toSpecΓ ≫ Spec.map j
  rw [← Category.assoc, ← Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
    ← Spec.map_comp, he]

end HodgeLean.Foundations.Program
