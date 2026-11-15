import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivisionHomotopy
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.Sheaf.Chain

/-! Subdivision on the actual relative-chain presheaf complex.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Apply relative subdivision simultaneously on every open support.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; subdivision of supported chains.
HC no distance; AV milestone no distance.
-/
def presheafSubdivision (X : TopCat.{0}) :
    singularChainPresheafComplex ℚ X ⟶ singularChainPresheafComplex ℚ X where
  f n :=
    { app U := (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
        ((relativeSubdivision (TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ)).f n)
      naturality {U V} i := by
        have h := congrArg (fun a => a.f n)
          (relativeSubdivision_naturality (supportInclusionPairMap X (leOfHom i.unop)))
        exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map) h }
  comm' i j hij := by
    obtain rfl := hij
    rw [singularChainPresheafComplex_d]
    apply NatTrans.ext
    funext U
    let P := TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ
    let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
    change F.map ((relativeSubdivision P).f (j + 1)) ≫
        F.map (((relativeChainFunctor ℚ).obj P).d (j + 1) j) =
      F.map (((relativeChainFunctor ℚ).obj P).d (j + 1) j) ≫ F.map ((relativeSubdivision P).f j)
    rw [← F.map_comp, ← F.map_comp]
    exact congrArg F.map ((relativeSubdivision P).comm (j + 1) j)


#print axioms presheafSubdivision
/-- The relative prism components form morphisms of the actual chain presheaves.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; supported subdivision prisms.
HC no distance; AV milestone no distance.
-/
def presheafSubdivisionPrism (X : TopCat.{0}) (i j : ℕ) :
    singularChainPresheaf ℚ X i ⟶ singularChainPresheaf ℚ X j where
  app U := (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
    (relativeSubdivisionPrism (TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ) i j)
  naturality {U V} f := by
    exact congrArg ((forget₂ (ModuleCat ℚ) AddCommGrpCat).map)
      (relativeSubdivisionPrism_naturality (supportInclusionPairMap X (leOfHom f.unop)) i j)

#print axioms presheafSubdivisionPrism
/-- The supported-chain presheaf subdivision is homotopic to the identity.
Source: Bredon, Sheaf Theory, second edition, V.9 and VI.12; supported subdivision prisms.
HC no distance; AV milestone no distance.
-/
def presheafSubdivisionHomotopy (X : TopCat.{0}) :
    Homotopy (presheafSubdivision X) (𝟙 (singularChainPresheafComplex ℚ X)) where
  hom := presheafSubdivisionPrism X
  zero i j hij := by
    apply NatTrans.ext
    funext U
    change (forget₂ (ModuleCat ℚ) AddCommGrpCat).map
      (relativeSubdivisionPrism (TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ) i j) = 0
    rw [relativeSubdivisionPrism_zero _ i j hij]
    exact Functor.map_zero (forget₂ (ModuleCat ℚ) AddCommGrpCat) _ _
  comm i := by
    cases i with
    | zero =>
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex,
        singularChainPresheafComplex_d, zero_add]
      apply NatTrans.ext
      funext U
      let P := TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ
      let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
      have h := (relativeSubdivisionHomotopy P).comm 0
      rw [Homotopy.dNext_zero_chainComplex, Homotopy.prevD_chainComplex, zero_add] at h
      change (relativeSubdivision P).f 0 = relativeSubdivisionPrism P 0 1 ≫
        ((relativeChainFunctor ℚ).obj P).d 1 0 + 𝟙 (((relativeChainFunctor ℚ).obj P).X 0) at h
      change F.map ((relativeSubdivision P).f 0) =
        F.map (relativeSubdivisionPrism P 0 1) ≫
          F.map (((relativeChainFunctor ℚ).obj P).d 1 0) +
            𝟙 (F.obj (((relativeChainFunctor ℚ).obj P).X 0))
      rw [← F.map_comp, ← F.map_id (((relativeChainFunctor ℚ).obj P).X 0), ← F.map_add]
      exact congrArg F.map h
    | succ n =>
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex,
        singularChainPresheafComplex_d, singularChainPresheafComplex_d]
      apply NatTrans.ext
      funext U
      let P := TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ
      let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
      have h := (relativeSubdivisionHomotopy P).comm (n + 1)
      rw [Homotopy.dNext_succ_chainComplex, Homotopy.prevD_chainComplex] at h
      change (relativeSubdivision P).f (n + 1) =
        ((relativeChainFunctor ℚ).obj P).d (n + 1) n ≫ relativeSubdivisionPrism P n (n + 1) +
        relativeSubdivisionPrism P (n + 1) (n + 2) ≫
          ((relativeChainFunctor ℚ).obj P).d (n + 2) (n + 1) +
            𝟙 (((relativeChainFunctor ℚ).obj P).X (n + 1)) at h
      change F.map ((relativeSubdivision P).f (n + 1)) =
        F.map (((relativeChainFunctor ℚ).obj P).d (n + 1) n) ≫
          F.map (relativeSubdivisionPrism P n (n + 1)) +
        F.map (relativeSubdivisionPrism P (n + 1) (n + 2)) ≫
          F.map (((relativeChainFunctor ℚ).obj P).d (n + 2) (n + 1)) +
            𝟙 (F.obj (((relativeChainFunctor ℚ).obj P).X (n + 1)))
      rw [← F.map_comp, ← F.map_comp,
        ← F.map_id (((relativeChainFunctor ℚ).obj P).X (n + 1)), ← F.map_add, ← F.map_add]
      exact congrArg F.map h


#print axioms presheafSubdivisionHomotopy
end HodgeLean.Foundations.RationalHomologyManifold
