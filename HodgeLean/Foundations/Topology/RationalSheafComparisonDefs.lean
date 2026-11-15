import HodgeLean.Foundations.Program.SingularGlobalPullback
import HodgeConjecture.Definitions.AlgebraicTopology.Support.SingularFlasqueModel
import HodgeConjecture.Definitions.AlgebraicGeometry.Cohomology.GlobalSections
import Mathlib.CategoryTheory.Abelian.Injective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Flat

/-! Rational singular and constant-sheaf comparison interfaces.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular
namespace HodgeLean.Topology.RationalSheafComparison

/-- The existing constant rational sheaf.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
abbrev constants (X : TopCat.{0}) :=
  (TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of ℚ)

/-- The fixed injective resolution already used by the singular resolution.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
abbrev resolution (X : TopCat.{0}) :=
  TopCat.Sheaf.ambientConstantInjectiveResolution X (AddCommGrpCat.of ℚ)

/-- Evaluation at the integer generator, with the source used by `Sheaf.H`.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def integerHomIso (X : TopCat.{0}) :
    preadditiveCoyoneda.obj (op ((TopCat.Sheaf.constantFunctor X).obj
      (AddCommGrpCat.of (ULift ℤ)))) ≅
      TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X :=
  NatIso.ofComponents (fun F =>
    (((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat isTerminalTop).homAddEquiv
      (AddCommGrpCat.of (ULift ℤ)) F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)).toAddCommGrpIso)
    (fun f => by ext g; rfl)

/-- The Hom complex for the integer generator is the global section complex.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def integerHomComplexIso (X : TopCat.{0})
    (K : CochainComplex (TopCat.Sheaf AddCommGrpCat X) ℤ) :
    CochainComplex.HomComplex
      ((CochainComplex.singleFunctor _ 0).obj
        ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of (ULift ℤ)))) K ≅
      TopCat.Sheaf.globalSectionsComplexInt X K :=
  letI : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  CochainComplex.HomComplex.fromSingleZeroIsoPreadditiveCoyoneda _ K ≪≫
    (NatIso.mapHomologicalComplex (integerHomIso X) ℤᵘᵖ).app K

/-- Global section cohomology of the chosen resolution computes the existing `Sheaf.H`.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def resolutionCohomologyEquiv (X : TopCat.{0}) (n : ℕ) :
    (TopCat.Sheaf.globalSectionsComplexInt X (resolution X).cochainComplex).homology
        (n : ℤ) ≃+ Sheaf.H (constants X) n :=
  (HomologicalComplex.homologyMapIso (integerHomComplexIso X
    (resolution X).cochainComplex) (n : ℤ)).symm.addCommGroupIsoToAddEquiv |>.trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ _ (n : ℤ)).trans
      (resolution X).extAddEquivCohomologyClass.symm)

/-- The ordinary rational cochain map through sheafification and the normalized resolution.
Source: Bredon, Sheaf Theory, second edition, II.4 and II.6. -/
def comparisonComplex (X : TopCat.{0})
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) :=
  HodgeLean.Foundations.Program.singularGlobalComparison X ≫
    ((TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
      (.up ℕ)).map (singularToConstantInjectiveResolution X hX)

/-- The canonical additive comparison, using the actual rational singular quotient.
Source: Bredon, Sheaf Theory, second edition, II.4, II.6 and III.1. -/
def comparison (X : TopCat.{0})
    (hX : ∀ (x : X) (U : Opens X), x ∈ U →
      ∃ V : Opens X, x ∈ V ∧ ContractibleSpace V ∧ V ≤ U) (n : ℕ) :
    Cohomology ℚ X n →+ Sheaf.H (constants X) n :=
  let Γ := (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).mapHomologicalComplex
    (.up ℕ)
  let G := Γ.obj (resolution X).cocomplex
  letI : (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive _
  (resolutionCohomologyEquiv X n).toAddMonoidHom.comp <|
    (HomologicalComplex.homologyMapIso
      (HomologicalComplex.mapExtendCanonicalIso
        (TopCat.Sheaf.IsFlasque.BoundedBelowComplex.globalSectionsFunctor X)
        (resolution X).cocomplex ComplexShape.embeddingUpNat) (n : ℤ)).inv.hom.comp <|
    ((G.extendHomologyIso ComplexShape.embeddingUpNat (j := n) rfl).inv.hom.comp <|
      (HomologicalComplex.homologyMap (comparisonComplex X hX) n).hom.comp
        (((SingularCochainComplex ℚ X).sc n).mapHomologyIso
          (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv.hom)

/-- Inverse image of a constant sheaf, via the actual two adjunctions.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def pullbackConstantsIso {X Y : TopCat.{0}} (f : X ⟶ Y) (A : AddCommGrpCat.{0}) :
    (TopCat.Sheaf.pullback AddCommGrpCat f).obj
      ((TopCat.Sheaf.constantFunctor Y).obj A) ≅
        (TopCat.Sheaf.constantFunctor X).obj A := by
  let adj : (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat ⋙
      TopCat.Sheaf.pullback AddCommGrpCat f) ⊣
      (sheafSections (Opens.grothendieckTopology X) AddCommGrpCat).obj (op ⊤) :=
    (constantSheafAdj _ AddCommGrpCat isTerminalTop).comp
      (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat f)
  exact (adj.leftAdjointUniq (constantSheafAdj _ AddCommGrpCat isTerminalTop)).app A

/-- Pullback on constant-sheaf cohomology from the actual inverse-image functor.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
def sheafPullback {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    Sheaf.H (constants Y) n →+ Sheaf.H (constants X) n :=
  letI : RepresentablyFlat (Opens.map f) := flat_of_preservesFiniteLimits (Opens.map f)
  letI : PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat f) :=
    Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      (Opens.map f) AddCommGrpCat (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)
  letI : (TopCat.Sheaf.pullback AddCommGrpCat f).Additive :=
    Functor.additive_of_preserves_binary_products _
  ((Abelian.Ext.mk₀ (pullbackConstantsIso f (AddCommGrpCat.of ℚ)).hom).postcomp
    ((TopCat.Sheaf.constantFunctor X).obj (AddCommGrpCat.of (ULift ℤ))) (add_zero n)).comp <|
    ((Abelian.Ext.mk₀ (pullbackConstantsIso f (AddCommGrpCat.of (ULift ℤ))).inv).precomp
      ((TopCat.Sheaf.pullback AddCommGrpCat f).obj (constants Y)) (zero_add n)).comp <|
    (TopCat.Sheaf.pullback AddCommGrpCat f).mapExtAddHom _ _ n

/-- Rational scalars act on the actual constant sheaf.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
abbrev scalar (X : TopCat.{0}) (a : ℚ) : constants X ⟶ constants X :=
  (TopCat.Sheaf.constantFunctor X).map (AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a))

/-- The coefficient endomorphism defines rational scalar multiplication.
Source: Bredon, Sheaf Theory, second edition, II.4, functoriality in coefficients. -/
instance cohomologySMul (X : TopCat.{0}) (n : ℕ) : SMul ℚ (Sheaf.H (constants X) n) :=
  ⟨fun a x => Sheaf.H.map (scalar X a) n x⟩

/-- The module structure comes from coefficient multiplication.
Source: Bredon, Sheaf Theory, second edition, II.4 and III.1;
AlgebraicTopology.Singular singular-cochain and constant-sheaf constructions. -/
instance cohomologyModule (X : TopCat.{0}) (n : ℕ) : Module ℚ (Sheaf.H (constants X) n) :=
  Module.ofMinimalAxioms
    (fun a x y => (Sheaf.H.map (scalar X a) n).map_add x y)
    (fun a b x => by
      change Sheaf.H.map (scalar X (a + b)) n x = _
      have h : scalar X (a + b) = scalar X a + scalar X b := by
        change (TopCat.Sheaf.constantFunctor X).map _ = _
        rw [AddMonoidHom.mulLeft_add]
        have h : AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a + AddMonoidHom.mulLeft b) =
            AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) +
              AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) := AddCommGrpCat.hom_ext rfl
        rw [h, Functor.map_add]
      rw [h, Sheaf.H.map_add_apply]; rfl)
    (fun a b x => by
      change Sheaf.H.map (scalar X (a * b)) n x = _
      have h : scalar X (a * b) = scalar X b ≫ scalar X a := by
        change (TopCat.Sheaf.constantFunctor X).map _ = _
        rw [AddMonoidHom.mulLeft_mul]
        have h : AddCommGrpCat.ofHom ((AddMonoidHom.mulLeft a).comp
            (AddMonoidHom.mulLeft b)) = AddCommGrpCat.ofHom (AddMonoidHom.mulLeft b) ≫
              AddCommGrpCat.ofHom (AddMonoidHom.mulLeft a) := AddCommGrpCat.hom_ext rfl
        rw [h, Functor.map_comp]
      rw [h, Sheaf.H.map_comp_apply]; rfl)
    (fun x => by
      change Sheaf.H.map (scalar X 1) n x = x
      have h : scalar X 1 = 𝟙 _ := by
        change (TopCat.Sheaf.constantFunctor X).map _ = _
        rw [AddMonoidHom.mulLeft_one]
        exact (TopCat.Sheaf.constantFunctor X).map_id _
      rw [h, Sheaf.H.map_id_apply])

end HodgeLean.Topology.RationalSheafComparison
