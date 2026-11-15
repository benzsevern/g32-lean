import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenBasePreparation
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenCylinder
import HodgeLean.Foundations.Program.SchoenTowerHardtCad5OpenAssembly
import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Pre

/-! Adapted cylindrical partitions whose full-dimensional cells are open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_adapted_open_cad {n k : ℕ} (B : Fin k → s2v_t11b_Formula n) :
    ∃ P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin n))),
      (∀ i j, (P.cell i).realize ⊆ (B j).realize ∨ Disjoint (P.cell i).realize (B j).realize) ∧
      (∀ i, P.dim i = n → IsOpen (P.cell i).realize) := by
  classical
  induction n generalizing k with
  | zero =>
    obtain ⟨m, c, d, e, F, I, hn, hd, hc, hb, hF, hI, ha⟩ := s2v_hardt_cad4_adapted B
    let P : s2v_hardt_cad5_Partition (Set.univ : Set (EuclideanSpace ℝ (Fin 0))) :=
      { count := m, cell := c, dim := d, chart := e, forward := F, inverse := I
        nonempty := hn, disjoint := hd, cover := hc, bound := hb
        forward_eq := hF, inverse_eq := hI }
    exact ⟨P, ha, fun i _ => isOpen_discrete _⟩
  | succ n ih =>
    let atoms := Finset.univ.biUnion (fun j => (B j).atoms)
    let enum := (Fintype.equivFin {p // p ∈ atoms}).symm
    let P : Fin (Fintype.card {p // p ∈ atoms}) → Polynomial (MvPolynomial (Fin n) ℝ) :=
      fun j => MvPolynomial.finSuccEquiv ℝ n (enum j).val
    obtain ⟨b, C, hC, hdisj, hcover, hmarks, hzero, hlift⟩ :=
      s2v_hardt_cad4_pre_root_lift P (fun j : Fin 0 => Fin.elim0 j)
    choose r ψ hψ hm hr g band hg hb hbn hgn using hlift
    obtain ⟨Q, R, roots, hopen, hconn, hcont, hmono, hroot, hz, hs⟩ :=
      s2v_hardt_cad5_prepare_open_base ih P C hcover r ψ hψ hm g hg hzero hr
    have hatoms : ∀ j p, p ∈ (B j).atoms → ∃ l, MvPolynomial.finSuccEquiv ℝ n p = P l := by
      intro j p hp
      have hmem : p ∈ atoms := Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hp⟩
      refine ⟨(Fintype.equivFin {p // p ∈ atoms}) ⟨p, hmem⟩, ?_⟩
      simp only [P, enum, Equiv.symm_apply_apply]
    have localLift (i : Fin Q.count) :
        ∃ L : s2v_hardt_cad5_Partition
          {y : EuclideanSpace ℝ (Fin (n + 1)) | ∃ a : (Q.cell i).realize,
            ∀ v, y v.succ = a.val v},
          (∀ l j, (L.cell l).realize ⊆ (B j).realize ∨ Disjoint (L.cell l).realize (B j).realize) ∧
          (∀ l, L.dim l = n + 1 → IsOpen (L.cell l).realize) := by
      obtain ⟨graphs, hgraphs⟩ := s2v_hardt_cad2_section_formulas P (Q.cell i) (hconn i)
        (roots i) (hcont i) (hmono i) (hroot i) (Q.cell i) (fun _ h => h)
      exact s2v_hardt_cad5_lift_open_cylinder P Q i (hopen i) (roots i) (hcont i)
        (hmono i) graphs hgraphs (hz i) (hroot i) (hs i) B hatoms
    choose L hAdapt hOpen using localLift
    exact s2v_hardt_cad5_assemble_open_cylinders Q L B hAdapt hOpen

end HodgeLean.Foundations.Program
