import HodgeLean.Foundations.Program.SchoenQuotientOpenImmersions
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.CategoryTheory.Category.Preorder

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The concrete nonempty invariant affine open subschemes of a scheme action. -/
abbrev s2_InvariantAffineOpen (X : Scheme.{0}) (G : Type) [Group G] (ρ : G →* Aut X) :=
  {U : X.Opens // IsAffineOpen U ∧ (U : Set X).Nonempty ∧
    ∀ g : G, (ρ g).asIso.hom ⁻¹ᵁ U = U}

instance s2_invariantAffineOpen_isAffine (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) : IsAffine U.val.toScheme :=
  U.property.1

instance s2_invariantAffineOpen_isIntegral (X : Scheme.{0}) [IsIntegral X]
    (G : Type) [Group G] (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) :
    IsIntegral U.val.toScheme := by
  haveI : Nonempty U.val.toScheme := Set.nonempty_coe_sort.mpr U.property.2.1
  exact isIntegral_of_isOpenImmersion U.val.ι

/-- The original action restricted to an index open of the quotient diagram. -/
def s2_invariantAffineOpenAction (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) : G →* Aut U.val.toScheme :=
  s2_invariantOpenAction G ρ U.val U.property.2.2

/-- Intersection stays inside the invariant affine index on an integral scheme
with affine diagonal. -/
def s2_invariantAffineOpenInf (X : Scheme.{0}) [IsIntegral X]
    [IsAffineHom (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (G : Type) [Group G] (ρ : G →* Aut X) (U V : s2_InvariantAffineOpen X G ρ) :
    s2_InvariantAffineOpen X G ρ :=
  ⟨U.val ⊓ V.val, U.property.1.inf V.property.1,
    nonempty_preirreducible_inter U.val.isOpen V.val.isOpen U.property.2.1 V.property.2.1,
    by intro g; rw [Scheme.Hom.preimage_inf, U.property.2.2 g, V.property.2.2 g]⟩

/-- The invariant spectrum attached to one affine index open. -/
def s2_invariantAffineQuotientObj (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) : Scheme.{0} :=
  letI := s2_schemeSectionAction U.val.toScheme G (s2_invariantAffineOpenAction X G ρ U)
  Spec (CommRingCat.of (FixedPoints.subring Γ(U.val.toScheme, ⊤) G))

/-- Inclusion of invariant affine opens induces a map of their quotient charts. -/
def s2_invariantAffineQuotientMap (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U V : s2_InvariantAffineOpen X G ρ) (h : U ≤ V) :
    s2_invariantAffineQuotientObj X G ρ U ⟶ s2_invariantAffineQuotientObj X G ρ V :=
  s2_quotientComparison G (s2_invariantAffineOpenAction X G ρ U)
    (s2_invariantAffineOpenAction X G ρ V) (X.homOfLE h)
    (s2_invariantOpenAction_homOfLE G ρ U.val V.val h U.property.2.2 V.property.2.2)

/-- The quotient chart map of a reflexive inclusion is the identity. -/
theorem s2_invariantAffineQuotientMap_id (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) :
    s2_invariantAffineQuotientMap X G ρ U U le_rfl = 𝟙 _ := by
  unfold s2_invariantAffineQuotientMap
  simp only [Scheme.homOfLE_rfl, s2_quotientComparison_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Inclusion comparisons of invariant affine quotient charts compose. -/
theorem s2_invariantAffineQuotientMap_comp (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U V W : s2_InvariantAffineOpen X G ρ) (hUV : U ≤ V) (hVW : V ≤ W) :
    s2_invariantAffineQuotientMap X G ρ U V hUV ≫ s2_invariantAffineQuotientMap X G ρ V W hVW =
      s2_invariantAffineQuotientMap X G ρ U W (hUV.trans hVW) := by
  unfold s2_invariantAffineQuotientMap s2_quotientComparison
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  ext a
  exact congrArg (fun m : U.val.toScheme ⟶ W.val.toScheme => m.appTop a.val)
    (X.homOfLE_homOfLE hUV hVW)

/-- The diagram of invariant affine quotient charts ordered by inclusion. -/
def s2_invariantAffineDiagram (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) : s2_InvariantAffineOpen X G ρ ⥤ Scheme.{0} where
  obj := s2_invariantAffineQuotientObj X G ρ
  map {U V} h := s2_invariantAffineQuotientMap X G ρ U V h.le
  map_id U := s2_invariantAffineQuotientMap_id X G ρ U
  map_comp {U V W} f g := (s2_invariantAffineQuotientMap_comp X G ρ U V W f.le g.le).symm

/-- Every comparison in the integral source's quotient diagram is an open immersion. -/
instance s2_invariantAffineDiagram_map_openImmersion (X : Scheme.{0}) [IsIntegral X]
    (G : Type) [Group G] [Finite G] (ρ : G →* Aut X)
    {U V : s2_InvariantAffineOpen X G ρ} (i : U ⟶ V) :
    IsOpenImmersion ((s2_invariantAffineDiagram X G ρ).map i) :=
  s2_quotientComparison_openImmersion G (s2_invariantAffineOpenAction X G ρ U)
    (s2_invariantAffineOpenAction X G ρ V) (X.homOfLE i.le)
    (s2_invariantOpenAction_homOfLE G ρ U.val V.val i.le U.property.2.2 V.property.2.2)

/-- Restricting the action does not change its value as a point of the ambient scheme. -/
theorem s2_invariantAffineOpenAction_apply (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) (g : G) (x : U.val.toScheme) :
    ((s2_invariantAffineOpenAction X G ρ U g).asIso.hom x).val = (ρ g).asIso.hom x.val :=
  congrArg (fun f => f x) (s2_invariantOpenMap_ι U.val (ρ g).asIso.hom (U.property.2.2 g).ge)

/-- The actual affine quotient projection on one source index open. -/
def s2_invariantAffineProjection (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U : s2_InvariantAffineOpen X G ρ) :
    U.val.toScheme ⟶ s2_invariantAffineQuotientObj X G ρ U :=
  s2_affineSchemeQuotientMap U.val.toScheme G (s2_invariantAffineOpenAction X G ρ U)

/-- The source projections commute with every inclusion in the quotient chart diagram. -/
theorem s2_invariantAffineProjection_naturality (X : Scheme.{0}) (G : Type) [Group G]
    (ρ : G →* Aut X) (U V : s2_InvariantAffineOpen X G ρ) (h : U ≤ V) :
    s2_invariantAffineProjection X G ρ U ≫ s2_invariantAffineQuotientMap X G ρ U V h =
      X.homOfLE h ≫ s2_invariantAffineProjection X G ρ V :=
  s2_affineSchemeQuotientMap_naturality G (s2_invariantAffineOpenAction X G ρ U)
    (s2_invariantAffineOpenAction X G ρ V) (X.homOfLE h)
    (s2_invariantOpenAction_homOfLE G ρ U.val V.val h U.property.2.2 V.property.2.2)

end HodgeLean.Foundations.Program
