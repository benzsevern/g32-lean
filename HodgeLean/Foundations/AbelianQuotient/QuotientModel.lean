import HodgeLean.Foundations.AbelianQuotient.LatticeImage
import HodgeLean.Foundations.AbelianQuotient.PeriodProjector
import HodgeLean.Foundations.AbelianQuotient.PointMultiplication
import HodgeLean.Foundations.AbelianQuotient.ComplementMap

noncomputable section
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters HodgeLean.Foundations.Program
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- The lattice image of the difference map retains an algebraic target and its full period image. -/
theorem difference_lattice_factorization {A : Variety} (S : Subvariety A)
    (N : ℕ) (r : Hom A S.B)
    (hr : S.inclusion.hom ≫ r.hom = (multiplication S.B N).hom) :
    ∃ (B : Variety) (i : Hom B A) (q : Hom A B),
      q.hom ≫ i.hom = (complementMap S N r).hom ∧
      i.hom ≫ q.hom = (multiplication B N).hom ∧
      ∃ ψ : abelianPeriodLattice A.X →+ abelianPeriodLattice B.X,
        Function.Surjective ψ ∧ ∀ x l,
          abelianPeriod A.X (homPullback q.hom 1 x) l = abelianPeriod B.X x (ψ l) := by
  let e := complementMap S N r
  let eEnd : AbelianEnd A.X := ⟨e.hom, inferInstance⟩
  obtain ⟨φ, hφ⟩ := spec_abelianEndAction_period A.X eEnd
  have hφ' : ∀ x l, abelianPeriod A.X (homPullback e.hom 1 x) l =
      abelianPeriod A.X x (φ l) := by
    intro x l
    simpa only [abelianEndAction, complexPointPullback, homPullback] using hφ x l
  have hsq := lattice_square_of_hom_square A e φ hφ' N (complement_map_square S N r hr)
  obtain ⟨Q, hQ⟩ := exists_period_riemann_form A
  exact lattice_image_factorization A Q hQ eEnd φ hφ N hsq

end HodgeLean.Foundations.AbelianQuotient
