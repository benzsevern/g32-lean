import HodgeLean.Foundations.Program.G32Native.PELReferenceEndomorphisms

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII

variable (A B : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
  [GrpObj B] [IsCommMonObj B] [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
local instance : Module.Finite ℚ (HQ B 1) := (torusCohomology_cupProductOf B).finite
variable {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ B 1))
  (m : HQ B 1 ≃ₗ[ℚ] HQ A 1)
  (hGroup : g2_hodgeGroup (latticeHodgePieces A)
      (spec_latticeHodgePieces_isInternal A) (basis.map m) =
    g2_hodgeGroup (latticeHodgePieces B) (spec_latticeHodgePieces_isInternal B) basis)

/-- The geometric End⁰ transfer agrees with conjugation by the retained marking.
The marking need not preserve the individual Hodge planes.
Source: Mumford, Abelian Varieties, §§19, 22; Birkenhake–Lange, §1.2. -/
theorem referenceEnd0Equiv_apply (d : AbelianEnd0 B) (x : HQ B 1) :
    (abelianEnd0Action A
      (referenceEnd0Equiv A B (basis.map m) basis hGroup d)).unop (m x) =
      m ((abelianEnd0Action B d).unop x) := by
  have hh := referenceEnd0Equiv_matrix A B (basis.map m) basis hGroup d
  have he : (abelianEnd0Action A
      (referenceEnd0Equiv A B (basis.map m) basis hGroup d)).unop =
      m.conjAlgEquiv ℚ (abelianEnd0Action B d).unop := by
    apply (LinearMap.toMatrix (basis.map m) (basis.map m)).injective
    rw [hh]
    ext i j
    simp [LinearMap.toMatrix_apply, LinearEquiv.conjAlgEquiv_apply]
  rw [he]
  simp [LinearEquiv.conjAlgEquiv_apply]

/-- A reference adjoint equation transports to the actual target End⁰ action
when the same marking preserves the bilinear forms.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§5.2, 5.5, 9.6. -/
theorem referenceEnd0Equiv_rosati
    {D : Type*} [Ring D] [Algebra ℚ D] [Star D]
    (e : D →ₐ[ℚ] AbelianEnd0 B)
    (EA : LinearMap.BilinForm ℚ (HQ A 1)) (EB : LinearMap.BilinForm ℚ (HQ B 1))
    (hform : ∀ x y, EA (m x) (m y) = EB x y)
    (hadj : ∀ d x y, EB ((abelianEnd0Action B (e d)).unop x) y =
      EB x ((abelianEnd0Action B (e (star d))).unop y))
    (d : D) (x y : HQ A 1) :
    EA ((abelianEnd0Action A
      (referenceEnd0Equiv A B (basis.map m) basis hGroup (e d))).unop x) y =
      EA x ((abelianEnd0Action A
        (referenceEnd0Equiv A B (basis.map m) basis hGroup (e (star d)))).unop y) := by
  obtain ⟨x, rfl⟩ := m.surjective x
  obtain ⟨y, rfl⟩ := m.surjective y
  rw [referenceEnd0Equiv_apply, referenceEnd0Equiv_apply, hform, hform]
  exact hadj d x y

/-- The same quadratic generator is retained under an action-compatible marking.
Source: Birkenhake–Lange, Complex Abelian Varieties, §§5.5, 9.6. -/
theorem referenceEnd0Equiv_generator
    (u : AbelianEnd0 B) (JA : Module.End ℚ (HQ A 1)) (JB : Module.End ℚ (HQ B 1))
    (hu : JB = (abelianEnd0Action B u).unop)
    (hmark : ∀ x, m (JB x) = JA (m x)) :
    JA = (abelianEnd0Action A
      (referenceEnd0Equiv A B (basis.map m) basis hGroup u)).unop := by
  ext x
  obtain ⟨x, rfl⟩ := m.surjective x
  rw [referenceEnd0Equiv_apply, ← hu, hmark]

#print axioms referenceEnd0Equiv_apply
#print axioms referenceEnd0Equiv_rosati
#print axioms referenceEnd0Equiv_generator
end HodgeLean.Foundations.Program.GeneralTypeIII
