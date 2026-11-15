import HodgeLean.Foundations.RationalHomologyManifold.RelativeSubdivision

/-! The subdivision prism on relative singular chains.
HC no distance; AV milestone no distance.
-/

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Descend the actual rational prism through each relative-chain projection.
Source: Hatcher, Algebraic Topology, section 2.1, subdivision on relative chains.
HC no distance; AV milestone no distance.
-/
def relativeSubdivisionPrism (P : TopPair.{0}) (i j : ℕ) :
    ((relativeChainFunctor ℚ).obj P).X i ⟶ ((relativeChainFunctor ℚ).obj P).X j :=
  (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P i).desc
    (CokernelCofork.ofπ
      ((rationalSubdivisionHomotopy P.fst).hom i j ≫ (relativeChainProjection ℚ P).f j) (by
      have hn := rationalSubdivisionHomotopy_naturality P.map i j
      change ((chainPairFunctor ℚ).obj P).hom.f i ≫
          (rationalSubdivisionHomotopy P.fst).hom i j =
        (rationalSubdivisionHomotopy P.snd).hom i j ≫
          ((chainPairFunctor ℚ).obj P).hom.f j at hn
      have hz := congrArg (fun a => a.f j) (subspaceChainMap_relativeChainProjection ℚ P)
      change ((chainPairFunctor ℚ).obj P).hom.f j ≫ (relativeChainProjection ℚ P).f j = 0 at hz
      rw [← Category.assoc, hn, Category.assoc, hz, comp_zero]))

#print axioms relativeSubdivisionPrism
/-- Relative projection retains the literal rational prism on representatives.
Source: Hatcher, Algebraic Topology, section 2.1, relative subdivision prism.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionPrism_projection (P : TopPair.{0}) (i j : ℕ) :
    (relativeChainProjection ℚ P).f i ≫ relativeSubdivisionPrism P i j =
      (rationalSubdivisionHomotopy P.fst).hom i j ≫ (relativeChainProjection ℚ P).f j := by
  exact (Cofork.IsColimit.π_desc
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P i)
    (t := CokernelCofork.ofπ
      ((rationalSubdivisionHomotopy P.fst).hom i j ≫ (relativeChainProjection ℚ P).f j) _)).trans
        (CokernelCofork.π_ofπ _ _ _)

#print axioms relativeSubdivisionPrism_projection
/-- The descended prism has the required vanishing components away from the homotopy degree.
Source: Hatcher, Algebraic Topology, section 2.1, relative prism homotopy.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionPrism_zero (P : TopPair.{0}) (i j : ℕ)
    (hij : ¬(ComplexShape.down ℕ).Rel j i) : relativeSubdivisionPrism P i j = 0 := by
  apply Cofork.IsColimit.hom_ext
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P i)
  change (relativeChainProjection ℚ P).f i ≫ relativeSubdivisionPrism P i j =
    (relativeChainProjection ℚ P).f i ≫ 0
  rw [relativeSubdivisionPrism_projection, (rationalSubdivisionHomotopy P.fst).zero i j hij,
    zero_comp, comp_zero]

#print axioms relativeSubdivisionPrism_zero
/-- Projection intertwines the two differential terms of the relative prism.
Source: Hatcher, Algebraic Topology, section 2.1, chain homotopy identities.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionPrism_differential (P : TopPair.{0}) (i : ℕ) :
    (relativeChainProjection ℚ P).f i ≫
      (dNext i (relativeSubdivisionPrism P) + prevD i (relativeSubdivisionPrism P)) =
    (dNext i (rationalSubdivisionHomotopy P.fst).hom +
      prevD i (rationalSubdivisionHomotopy P.fst).hom) ≫
        (relativeChainProjection ℚ P).f i := by
  have hf : (fun a b => (relativeChainProjection ℚ P).f a ≫ relativeSubdivisionPrism P a b) =
      (fun a b => (rationalSubdivisionHomotopy P.fst).hom a b ≫
        (relativeChainProjection ℚ P).f b) := by
    funext a b
    exact relativeSubdivisionPrism_projection P a b
  calc
    _ = dNext i (fun a b => (relativeChainProjection ℚ P).f a ≫ relativeSubdivisionPrism P a b) +
        prevD i (fun a b => (relativeChainProjection ℚ P).f a ≫ relativeSubdivisionPrism P a b) := by
      rw [Preadditive.comp_add, ← dNext_comp_left, ← prevD_comp_left]
    _ = dNext i (fun a b => (rationalSubdivisionHomotopy P.fst).hom a b ≫
          (relativeChainProjection ℚ P).f b) +
        prevD i (fun a b => (rationalSubdivisionHomotopy P.fst).hom a b ≫
          (relativeChainProjection ℚ P).f b) := by rw [hf]
    _ = _ := by rw [dNext_comp_right, prevD_comp_right, Preadditive.add_comp]

#print axioms relativeSubdivisionPrism_differential
/-- The relative subdivision operator is chain homotopic to the identity through the descended prism.
Source: Hatcher, Algebraic Topology, section 2.1, relative subdivision homotopy.
HC no distance; AV milestone no distance.
-/
def relativeSubdivisionHomotopy (P : TopPair.{0}) :
    Homotopy (relativeSubdivision P) (𝟙 ((relativeChainFunctor ℚ).obj P)) where
  hom := relativeSubdivisionPrism P
  zero := relativeSubdivisionPrism_zero P
  comm i := by
    apply Cofork.IsColimit.hom_ext
      (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P i)
    change (relativeChainProjection ℚ P).f i ≫ (relativeSubdivision P).f i =
      (relativeChainProjection ℚ P).f i ≫
        (dNext i (relativeSubdivisionPrism P) + prevD i (relativeSubdivisionPrism P) +
          (𝟙 (((relativeChainFunctor ℚ).obj P).X i)))
    rw [Preadditive.comp_add, relativeSubdivisionPrism_differential]
    have hs := congrArg (fun a => a.f i) (relativeSubdivision_projection P)
    change (relativeChainProjection ℚ P).f i ≫ (relativeSubdivision P).f i =
      (rationalSubdivision P.fst).f i ≫ (relativeChainProjection ℚ P).f i at hs
    rw [hs, (rationalSubdivisionHomotopy P.fst).comm i]
    simp only [Preadditive.add_comp, HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

#print axioms relativeSubdivisionHomotopy
/-- Relative affine subdivision acts identically on actual relative singular homology.
Source: Hatcher, Algebraic Topology, section 2.1, invariance under subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivision_homology (P : TopPair.{0}) (n : ℕ) :
    HomologicalComplex.homologyMap (relativeSubdivision P) n =
      𝟙 _ := by
  simpa only [HomologicalComplex.homologyMap_id] using
    (relativeSubdivisionHomotopy P).homologyMap_eq n

#print axioms relativeSubdivision_homology
/-- Relative subdivision is a quasi-isomorphism of actual relative singular chains.
Source: Hatcher, Algebraic Topology, section 2.1, invariance under subdivision.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivision_quasiIso (P : TopPair.{0}) : QuasiIso (relativeSubdivision P) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, relativeSubdivision_homology]
  infer_instance

#print axioms relativeSubdivision_quasiIso
/-- The descended relative prism respects every map of topological pairs.
Source: Hatcher, Algebraic Topology, section 2.1, naturality of the relative prism.
HC no distance; AV milestone no distance.
-/
theorem relativeSubdivisionPrism_naturality {P Q : TopPair.{0}} (f : P ⟶ Q) (i j : ℕ) :
    ((relativeChainFunctor ℚ).map f).f i ≫ relativeSubdivisionPrism Q i j =
      relativeSubdivisionPrism P i j ≫ ((relativeChainFunctor ℚ).map f).f j := by
  let A := SSet.chainComplexMap (TopCat.toSSet.map f.hom.right) (ModuleCat.of ℚ ℚ)
  have hp := TopPair.Homotopy.relativeChainProjection_naturality (R := ℚ) f
  have hfi := congrArg (fun a => a.f i) hp
  have hfj := congrArg (fun a => a.f j) hp
  change (relativeChainProjection ℚ P).f i ≫ ((relativeChainFunctor ℚ).map f).f i =
    A.f i ≫ (relativeChainProjection ℚ Q).f i at hfi
  change (relativeChainProjection ℚ P).f j ≫ ((relativeChainFunctor ℚ).map f).f j =
    A.f j ≫ (relativeChainProjection ℚ Q).f j at hfj
  have hn : A.f i ≫ (rationalSubdivisionHomotopy Q.fst).hom i j =
      (rationalSubdivisionHomotopy P.fst).hom i j ≫ A.f j :=
    rationalSubdivisionHomotopy_naturality f.hom.right i j
  apply Cofork.IsColimit.hom_ext
    (TopPair.Homotopy.relativeChainProjectionComponentIsCokernel (R := ℚ) P i)
  change (relativeChainProjection ℚ P).f i ≫
      (((relativeChainFunctor ℚ).map f).f i ≫ relativeSubdivisionPrism Q i j) =
    (relativeChainProjection ℚ P).f i ≫
      (relativeSubdivisionPrism P i j ≫ ((relativeChainFunctor ℚ).map f).f j)
  calc
    _ = A.f i ≫ ((relativeChainProjection ℚ Q).f i ≫ relativeSubdivisionPrism Q i j) := by
      rw [← Category.assoc, hfi, Category.assoc]
    _ = A.f i ≫ ((rationalSubdivisionHomotopy Q.fst).hom i j ≫
        (relativeChainProjection ℚ Q).f j) := by rw [relativeSubdivisionPrism_projection]
    _ = (rationalSubdivisionHomotopy P.fst).hom i j ≫
        (A.f j ≫ (relativeChainProjection ℚ Q).f j) := by
      rw [← Category.assoc, hn, Category.assoc]
    _ = (rationalSubdivisionHomotopy P.fst).hom i j ≫
        ((relativeChainProjection ℚ P).f j ≫ ((relativeChainFunctor ℚ).map f).f j) := by rw [hfj]
    _ = _ := by rw [← Category.assoc, ← relativeSubdivisionPrism_projection, Category.assoc]

#print axioms relativeSubdivisionPrism_naturality
end HodgeLean.Foundations.RationalHomologyManifold
