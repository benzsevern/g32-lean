import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.TorusLocalLift

noncomputable section
open HodgeLean.Foundations.Program Filter
open scoped TensorProduct Manifold ContDiff Topology
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

variable {L : Type} [AddCommGroup L] [Module.Finite ℤ L]
  (F : Submodule ℂ (ℂ ⊗[ℤ] L))

/-- Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1. -/
def torusCoverHom : b5_V L F →+ b2_torus L F :=
  (QuotientAddGroup.mk' (b2_latticeMap L F).range).comp
    (b2_coord ((ℂ ⊗[ℤ] L) ⧸ F)).symm.toAddMonoidHom

theorem torusCoverHom_apply (v : b5_V L F) :
    torusCoverHom F v = b2_torusCover L F v := rfl


/-- Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1, local quotient charts. -/
theorem torus_sub_contMDiff {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C]
    [DiscreteTopology (b2_latticeMap L F).range]
    (f g : C → b2_torus L F)
    (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω f)
    (hg : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω g) :
    ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (fun x ↦ f x - g x) := by
  intro q
  obtain ⟨u, hu, heu⟩ := torus_localLift F f q (hf q)
  obtain ⟨v, hv, hev⟩ := torus_localLift F g q (hg q)
  have hh : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω
      (fun x ↦ b2_torusCover L F (u x - v x)) q :=
    (b2_torusCover_contMDiff F).contMDiffAt.comp q (hu.sub hv)
  apply hh.congr_of_eventuallyEq
  filter_upwards [heu, hev] with x hx hy
  exact (congrArg₂ (fun a b : b2_torus L F ↦ a - b) hx hy).trans
    ((torusCoverHom F).map_sub (u x) (v x)).symm


/-- Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1, local quotient charts. -/
theorem torus_sub_contMDiffAt {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C]
    [DiscreteTopology (b2_latticeMap L F).range]
    (f g : C → b2_torus L F) (q : C)
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω f q)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω g q) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (fun x ↦ f x - g x) q := by
  obtain ⟨u, hu, heu⟩ := torus_localLift F f q hf
  obtain ⟨v, hv, hev⟩ := torus_localLift F g q hg
  have hh : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω
      (fun x ↦ b2_torusCover L F (u x - v x)) q :=
    (b2_torusCover_contMDiff F).contMDiffAt.comp q (hu.sub hv)
  apply hh.congr_of_eventuallyEq
  filter_upwards [heu, hev] with x hx hy
  exact (congrArg₂ (fun a b : b2_torus L F ↦ a - b) hx hy).trans
    ((torusCoverHom F).map_sub (u x) (v x)).symm



/-- Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1, local quotient charts. -/
theorem torus_add_contMDiffAt {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C]
    [DiscreteTopology (b2_latticeMap L F).range]
    (f g : C → b2_torus L F) (q : C)
    (hf : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω f q)
    (hg : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω g q) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (fun x ↦ f x + g x) q := by
  have hn := torus_sub_contMDiffAt F (fun _ ↦ 0) g q contMDiffAt_const hg
  simpa only [zero_sub, sub_neg_eq_add] using
    torus_sub_contMDiffAt F f (fun x ↦ 0 - g x) q hf hn



/-- Source: Birkenhake–Lange, Complex Abelian Varieties, §1.1, local quotient charts. -/
theorem torus_sum_contMDiffAt {E C ι : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C]
    [DiscreteTopology (b2_latticeMap L F).range]
    (s : Finset ι) (f : ι → C → b2_torus L F) (q : C)
    (hf : ∀ i ∈ s, ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (f i) q) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (fun x ↦ ∑ i ∈ s, f i x) q := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using
        (contMDiffAt_const : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, b5_V L F) ω (fun _ : C ↦ (0 : b2_torus L F)) q)
  | @insert i s hi ih =>
      intro hf
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs := ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi] using
        torus_add_contMDiffAt F (f i) (fun x ↦ ∑ j ∈ s, f j x) q hfi hfs


end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
