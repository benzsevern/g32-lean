import HodgeLean.Adapters.LefschetzOneOneAlgebraicAbelian5SquareMaps

/-! # Reduced-equation pairs on the universal cover

These constructions are maps of actual pairs. The regular open retains the complement
of the zero set and removes only critical zeros. HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open AlgebraicTopology.Singular HodgeLean.RealDefs HodgeLean.Foundations
open Set Topology
namespace HodgeLean.Adapters

/-- The ambient affine space relative to the complement of an equation's zero set.
Source: Hatcher, *Algebraic Topology*, section 3.3, cohomology with supports. -/
def bh8_equationPair (n : ℕ) (f : (Fin n → ℂ) → ℂ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (Fin n → ℂ)) {p | f p ≠ 0}

example : (bh8_equationPair 1 (fun p ↦ p 0)).fst = TopCat.of (Fin 1 → ℂ) := rfl

/-- The complement of the critical zero set, including every point off the divisor.
Source: Griffiths--Harris, *Principles of Algebraic Geometry*, Chapter 0, analytic hypersurfaces. -/
def bh8_regularDomain (n : ℕ) (f : (Fin n → ℂ) → ℂ) : Set (Fin n → ℂ) :=
  {p | f p ≠ 0 ∨ fderiv ℂ f p ≠ 0}

example : (0 : Fin 1 → ℂ) ∈ bh8_regularDomain 1 (fun _ ↦ 1) :=
  Or.inl one_ne_zero

/-- The equation pair restricted away from critical zeros.
Source: Hatcher, section 3.3, restriction of relative cohomology. -/
def bh8_regularPair (n : ℕ) (f : (Fin n → ℂ) → ℂ) : TopPair :=
  TopPair.ofSubset (X := TopCat.of (bh8_regularDomain n f)) {p | f p ≠ 0}

example : (bh8_regularPair 1 (fun _ ↦ 1)).fst =
    TopCat.of (bh8_regularDomain 1 (fun _ ↦ 1)) := rfl

/-- Inclusion of the regular-domain pair in the full equation pair.
Source: functoriality of relative singular cohomology. -/
def bh8_regularInclusion (n : ℕ) (f : (Fin n → ℂ) → ℂ) :
    bh8_regularPair n f ⟶ bh8_equationPair n f :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩)
    (fun _ h ↦ h)

example (p : bh8_regularDomain 1 (fun _ ↦ 1)) :
    (TopPair.Hom.fst (bh8_regularInclusion 1 (fun _ ↦ 1))) p = p.val := rfl

/-- The equation itself as a map to the normal complex-line pair.
Source: Griffiths--Harris, Chapter 1, section 1, divisor local class. -/
def bh8_normalMap (n : ℕ) (f : (Fin n → ℂ) → ℂ) (hf : Continuous f) :
    bh8_equationPair n f ⟶ puncturedPair ℂ 1 :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨fun p _ ↦ f p, by fun_prop⟩)
    (by intro p hp he; exact hp (congrFun he 0))

example : (TopPair.Hom.fst (bh8_normalMap 1 (fun p ↦ p 0) (continuous_apply 0))) (0 : Fin 1 → ℂ) = (0 : Fin 1 → ℂ) := rfl

/-- The exponential cover as a map of component-support pairs.
Source: Birkenhake--Lange, *Complex Abelian Varieties*, second edition, section 1.3. -/
def bh8_coverMap
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x) :
    bh8_equationPair (dim X.left) f ⟶ neighborhoodSupportComplementPair
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X)) (cycleComponentSupport X x) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun p ↦ ⟨abelianExp X p, mem_univ _⟩,
      (continuous_abelianExp X).subtype_mk _⟩)
    (by intro p hp h; exact hp ((hs p).mpr h))

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (x : X.left) (f : (Fin (dim X.left) → ℂ) → ℂ)
    (hs : ∀ p, f p = 0 ↔ abelianExp X p ∈ bh4_componentSupport X x)
    (p : Fin (dim X.left) → ℂ) :
    ((TopPair.Hom.fst (bh8_coverMap X x f hs)) p).val = abelianExp X p := rfl

/-- The clamped disk map into the full equation pair.
Source: the stage-five square map and its checked boundary-avoidance lemma. -/
def bh8_diskToEquation
    (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] (f : (Fin (dim X.left) → ℂ) → ℂ)
    (l m : abelianPeriodLattice X) (z : Fin (dim X.left) → ℂ)
    (hnz : ∀ i : Fin 4, ∀ t ∈ Icc (0 : ℝ) 1, f (bh4_squareEdge X l m z i t) ≠ 0) :
    bh5_diskPair ⟶ bh8_equationPair (dim X.left) f :=
  TopPair.ofSubsetHom (TopCat.ofHom (bh5_squareMap (dim X.left) l m z)) (by
    intro q hq
    obtain ⟨i, t, ht, he⟩ := bh5_squareMap_outside X l m z q hq
    exact he ▸ hnz i t ht)

example (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left] [Smooth X.hom]
    [IsProjective X.hom] :
    (TopPair.Hom.fst (bh8_diskToEquation X (fun _ ↦ 1) 0 0 0 (fun _ _ _ ↦ one_ne_zero))) (0 : Fin 1 → ℂ) =
      (0 : Fin (dim X.left) → ℂ) := by
  change bh5_squareMap (dim X.left) 0 0 0 0 = 0
  simp [bh5_squareMap]

end HodgeLean.Adapters
