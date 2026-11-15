import HodgeLean.Foundations.Program.CompensationAssemblyTraceModule
import HodgeConjecture.Lemmas.AlgebraicTopology.Singular.RelativeHomotopyInvariance

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
open scoped Topology
namespace HodgeLean.Foundations.Program

def cq_circleSection (X : TopCat.{0}) : X ⟶ TopCat.of (X × UnitAddCircle) :=
  TopCat.ofHom ⟨fun x => (x, 0), continuous_id.prodMk continuous_const⟩

def cq_circleLoopHomotopy (X : TopCat.{0}) :
    TopCat.Homotopy (cq_circleSection X) (cq_circleSection X) where
  toFun p := (p.2, ((p.1 : ℝ) : UnitAddCircle))
  continuous_toFun := by fun_prop
  map_zero_left x := by
    change (x, ((0 : ℝ) : UnitAddCircle)) = (x, 0)
    rw [AddCircle.coe_zero]
  map_one_left x := by
    change (x, ((1 : ℝ) : UnitAddCircle)) = (x, 0)
    rw [AddCircle.coe_period]

def cq_pairCircle (P : TopPair.{0}) : TopPair.{0} :=
  TopPair.of (cq_circleProductMap P.map)
    (P.isEmbedding_map.prodMap Topology.IsEmbedding.id)

def cq_pairCircleSection (P : TopPair.{0}) : P ⟶ cq_pairCircle P :=
  TopPair.ofHom (cq_circleSection P.fst) (cq_circleSection P.snd) (by
    apply ConcreteCategory.hom_ext
    intro p
    rfl)

def cq_pairCircleLoopHomotopy (P : TopPair.{0}) :
    TopPair.Homotopy (cq_pairCircleSection P) (cq_pairCircleSection P) where
  fst := cq_circleLoopHomotopy P.fst
  snd := cq_circleLoopHomotopy P.snd
  w := by
    apply ConcreteCategory.hom_ext
    intro p
    rfl

def cq_pairCircleChainHomotopy (P : TopPair.{0}) :
    _root_.Homotopy ((relativeChainFunctor ℚ).map (cq_pairCircleSection P))
      ((relativeChainFunctor ℚ).map (cq_pairCircleSection P)) :=
  TopPair.Homotopy.relativeChainHomotopy (R := ℚ) (cq_pairCircleLoopHomotopy P)

theorem cq_pairCircleChainHomotopy_boundary (P : TopPair.{0}) (n : ℕ) :
    dNext n (cq_pairCircleChainHomotopy P).hom + prevD n (cq_pairCircleChainHomotopy P).hom = 0 := by
  have h := (cq_pairCircleChainHomotopy P).comm n
  exact add_right_cancel (h.symm.trans (zero_add _).symm)

end HodgeLean.Foundations.Program
