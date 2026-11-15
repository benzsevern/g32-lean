import HodgeLean.Foundations.RationalHomologyManifold.InitialCapTargetWindowTransport
import HodgeLean.Foundations.RationalHomologyManifold.GlobalTopBoundaryQuotient

/-! Actual incoming global cap-window epimorphy under total-degree transport.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits
open HodgeLean.Foundations.QuotientDuality
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual incoming initial cap-window component remains an epimorphism on global sections in any specified equal total degree.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; actual top boundary quotient with canonical degree transport.
HC no distance; AV milestone no distance.
-/
theorem initialCapTargetWindowComparisonOfEq_global_epi (X : TopCat.{0}) [CompactSpace X] [T2Space X]
    (t : FiniteTriangulation X) (N q : ℕ) (hN : N = q + 2) (o : LocalRationalOrientation X N) :
    Epi ((subdivisionGlobalSectionsFunctor X).map
      (initialCapTargetWindowComparisonOfEq X N q hN).τ₁) := by
  subst N
  let E := subdivisionGlobalSectionsFunctor X
  letI := subdivisionGlobal_top_pOpcycles_epi X t (q + 1) o
  change Epi (E.map (-(((subdivisionLimitSheafComplex X).XIsoOfEq rfl).inv ≫
    (subdivisionLimitSheafComplex X).pOpcycles (q + 2) ≫ (capTargetZeroTermIso X (q + 2)).inv)))
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_inv, Category.id_comp]
  rw [E.map_neg, E.map_comp]
  infer_instance

#print axioms initialCapTargetWindowComparisonOfEq_global_epi
end HodgeLean.Foundations.RationalHomologyManifold
