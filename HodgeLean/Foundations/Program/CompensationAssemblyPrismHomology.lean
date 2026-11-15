import HodgeLean.Foundations.Program.CompensationAssemblyCirclePrism

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 10000
set_option maxRecDepth 2048
open CategoryTheory Limits HomologicalComplex
namespace HodgeLean.Foundations.Program

variable {C D : ChainComplex (ModuleCat ℚ) ℕ} {f : C ⟶ D}

theorem cq_selfHomotopy_boundary (H : Homotopy f f) (n : ℕ) :
    dNext n H.hom + prevD n H.hom = 0 := by
  have h := H.comm n
  exact add_right_cancel (h.symm.trans (zero_add _).symm)

theorem cq_selfHomotopy_cycles (H : Homotopy f f) (n : ℕ) :
    (C.iCycles n ≫ H.hom n (n + 1)) ≫ D.d (n + 1) n = 0 := by
  have h := cq_selfHomotopy_boundary H n
  rw [dNext_nat C D n H.hom,
    prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)] at h
  have h' := congrArg (fun k => C.iCycles n ≫ k) h
  simpa only [Preadditive.comp_add, Category.assoc, iCycles_d_assoc,
    zero_comp, zero_add, comp_zero] using h'

def cq_selfHomotopy_cycleMap (H : Homotopy f f) (n : ℕ) :
    C.cycles n ⟶ D.cycles (n + 1) :=
  D.liftCycles' (C.iCycles n ≫ H.hom n (n + 1)) n
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)
    (cq_selfHomotopy_cycles H n)

@[reassoc (attr := simp)]
theorem cq_selfHomotopy_cycleMap_i (H : Homotopy f f) (n : ℕ) :
    cq_selfHomotopy_cycleMap H n ≫ D.iCycles (n + 1) =
      C.iCycles n ≫ H.hom n (n + 1) := by
  exact D.liftCycles_i _ n ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl)) (cq_selfHomotopy_cycles H n)

theorem cq_selfHomotopy_successor_boundary (H : Homotopy f f) (n : ℕ) :
    C.d (n + 1) n ≫ H.hom n (n + 1) +
      H.hom (n + 1) (n + 2) ≫ D.d (n + 2) (n + 1) = 0 := by
  have h := cq_selfHomotopy_boundary H (n + 1)
  rw [dNext_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl),
    prevD_eq H.hom (show (ComplexShape.down ℕ).Rel (n + 2) (n + 1) from rfl)] at h
  exact h

theorem cq_selfHomotopy_cycleMap_boundary (H : Homotopy f f) (n : ℕ) :
    C.toCycles (n + 1) n ≫ cq_selfHomotopy_cycleMap H n ≫
      D.homologyπ (n + 1) = 0 := by
  have hb : C.d (n + 1) n ≫ H.hom n (n + 1) =
      (-H.hom (n + 1) (n + 2)) ≫ D.d (n + 2) (n + 1) := by
    rw [Preadditive.neg_comp]
    exact eq_neg_of_add_eq_zero_left (cq_selfHomotopy_successor_boundary H n)
  have he : C.toCycles (n + 1) n ≫ cq_selfHomotopy_cycleMap H n =
      D.liftCycles (C.d (n + 1) n ≫ H.hom n (n + 1)) n
        ((ComplexShape.down ℕ).next_eq' (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))
        (by rw [hb, Category.assoc, D.d_comp_d, comp_zero]) := by
    apply (cancel_mono (D.iCycles (n + 1))).1
    simp only [Category.assoc, cq_selfHomotopy_cycleMap_i,
      liftCycles_i, toCycles_i_assoc]
  rw [← Category.assoc, he]
  exact D.liftCycles_homologyπ_eq_zero_of_boundary _ n _ _ hb

def cq_selfHomotopy_homologyMap (H : Homotopy f f) (n : ℕ) :
    C.homology n ⟶ D.homology (n + 1) :=
  (C.homologyIsCokernel (n + 1) n ((ComplexShape.down ℕ).prev_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).desc
    (CokernelCofork.ofπ (cq_selfHomotopy_cycleMap H n ≫ D.homologyπ (n + 1))
      (cq_selfHomotopy_cycleMap_boundary H n))

@[reassoc (attr := simp)]
theorem cq_selfHomotopy_homologyMap_π (H : Homotopy f f) (n : ℕ) :
    C.homologyπ n ≫ cq_selfHomotopy_homologyMap H n =
      cq_selfHomotopy_cycleMap H n ≫ D.homologyπ (n + 1) := by
  exact (C.homologyIsCokernel (n + 1) n ((ComplexShape.down ℕ).prev_eq'
    (show (ComplexShape.down ℕ).Rel (n + 1) n from rfl))).fac _ WalkingParallelPair.one

theorem cq_selfHomotopy_homologyMap_naturality
    {C' D' : ChainComplex (ModuleCat ℚ) ℕ} {f' : C' ⟶ D'}
    (H : Homotopy f f) (H' : Homotopy f' f') (a : C ⟶ C') (b : D ⟶ D')
    (h : ∀ n, a.f n ≫ H'.hom n (n + 1) = H.hom n (n + 1) ≫ b.f (n + 1))
    (n : ℕ) :
    homologyMap a n ≫ cq_selfHomotopy_homologyMap H' n =
      cq_selfHomotopy_homologyMap H n ≫ homologyMap b (n + 1) := by
  have hc : cyclesMap a n ≫ cq_selfHomotopy_cycleMap H' n =
      cq_selfHomotopy_cycleMap H n ≫ cyclesMap b (n + 1) := by
    apply (cancel_mono (D'.iCycles (n + 1))).1
    simp only [Category.assoc, cq_selfHomotopy_cycleMap_i, cyclesMap_i,
      cyclesMap_i_assoc, cq_selfHomotopy_cycleMap_i_assoc]
    rw [h n]
  apply (cancel_epi (C.homologyπ n)).1
  simp only [homologyπ_naturality_assoc, Category.assoc,
    cq_selfHomotopy_homologyMap_π, cq_selfHomotopy_homologyMap_π_assoc,
    homologyπ_naturality_assoc]
  rw [← Category.assoc, hc, Category.assoc, homologyπ_naturality]

end HodgeLean.Foundations.Program
