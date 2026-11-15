import HodgeLean.Foundations.Program.SchoenTransferQ3ComponentDomination
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorFiniteCoheight

/-! Generalization lifting and coheight for the retained open finite map. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.Adapters
open scoped Classical
namespace HodgeLean.Foundations.Program

/-- The generic component through a point lifts any target generalization
along an open map from a Noetherian scheme. -/
theorem s4_q3_generalizing_of_scheme_open
    {X W : Scheme} [IsNoetherian X] (q : X ⟶ W) (hq : IsOpenMap q) :
    GeneralizingMap q := by
  intro p x hxp
  let J := ccm3_inverseIdeal q x
  have hpJ : p ∈ J.support := by
    change p ∈ ((ccm3_primeIdeal W x).comap q).support
    rw [Scheme.IdealSheafData.support_comap]
    change q p ∈ ((ccm3_primeIdeal W x).support : Set W)
    rw [ccm3_primeIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact specializes_iff_mem_closure.mp hxp
  obtain ⟨w, hwp⟩ := J.range_subschemeι.symm.subset hpJ
  let C : irreducibleComponents J.subscheme :=
    ⟨irreducibleComponent w, irreducibleComponent_mem_irreducibleComponents w⟩
  let y := (genericPoints.ofComponent C).1
  have hy : closure ({y} : Set J.subscheme) = C := genericPoints.isGenericPoint_ofComponent C
  have hw : w ∈ closure ({y} : Set J.subscheme) := hy.symm ▸ mem_irreducibleComponent
  refine ⟨J.subschemeι y, ?_, s4_q3_inverse_component_dominates q hq x y
    (genericPoints.ofComponent C).2⟩
  have hh := (specializes_iff_mem_closure.mpr hw).map J.subschemeι.continuous
  simpa only [hwp] using hh

/-- Openness and discrete fibres give exact coheight preservation without a
flatness premise. -/
theorem s4_q3_coheight_eq_of_open_quasiFinite
    {X W : Scheme} [IsNoetherian X] (q : X ⟶ W) [LocallyQuasiFinite q]
    (hq : IsOpenMap q) (p : X) :
    Order.coheight p = Order.coheight (q p) := by
  apply Order.coheight_eq_of_strictMono q (s2v_l1b_divisor_quasi_finite_strictMono q)
  intro a b hab
  obtain ⟨a', haa', ha'b⟩ := s4_q3_generalizing_of_scheme_open q hq hab.le
  refine ⟨a', lt_iff_le_not_ge.mpr ⟨haa', ?_⟩, ha'b⟩
  intro hrev
  have he : a' = a := (haa'.antisymm (show Specializes a a' from hrev)).eq
  have heq : q a = b := by simpa only [he] using ha'b
  exact hab.ne heq

end HodgeLean.Foundations.Program
