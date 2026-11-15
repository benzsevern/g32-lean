import HodgeLean.Foundations.AnalyticDivisorAlgebraic18

noncomputable section
namespace HodgeLean.Foundations.AnalyticDivisorAlgebraic19

open Filter Set Topology
open HodgeLean.Foundations.AnalyticDivisorAlgebraic6
open HodgeLean.Foundations.AnalyticDivisorAlgebraic7
open HodgeLean.Foundations.AnalyticDivisorAlgebraic14

/-- Product-coordinate form of one-pair propagation. -/
theorem gaga19_pair_propagation_product_aux (n : ℕ) (p : (Fin n → ℂ) × ℂ)
    (F G : (Fin n → ℂ) × ℂ → ℂ)
    (hF : AnalyticAt ℂ F p) (hG : AnalyticAt ℂ G p)
    (hiF : IsIrreducibleAt F p) (hiG : IsIrreducibleAt G p)
    (hc : IsCoprimeAt F G p) :
    ∀ᶠ q in nhds p, IsCoprimeAt F G q ∧
      ∀ (k l : ℕ) (u v : (Fin n → ℂ) × ℂ → ℂ)
        (Q : Fin k → (Fin n → ℂ) × ℂ → ℂ)
        (R : Fin l → (Fin n → ℂ) × ℂ → ℂ)
        (d : Fin k → ℕ) (e : Fin l → ℕ),
        AnalyticAt ℂ u q → u q ≠ 0 → AnalyticAt ℂ v q → v q ≠ 0 →
        (∀ j, AnalyticAt ℂ (Q j) q ∧ IsIrreducibleAt (Q j) q ∧ 0 < d j) →
        (∀ j, AnalyticAt ℂ (R j) q ∧ IsIrreducibleAt (R j) q ∧ 0 < e j) →
        Pairwise (fun j j' ↦ IsCoprimeAt (Q j) (Q j') q) →
        Pairwise (fun j j' ↦ IsCoprimeAt (R j) (R j') q) →
        (F =ᶠ[nhds q] fun z ↦ u z * ∏ j, Q j z ^ d j) →
        (G =ᶠ[nhds q] fun z ↦ v z * ∏ j, R j z ^ e j) →
        ∀ j j', ¬ AreAssociatedAt (Q j) (R j') q := by
  let L : ((Fin n → ℂ) × ℂ) ≃L[ℂ] (Fin (n + 1) → ℂ) :=
    LinearEquiv.toContinuousLinearEquiv
      { toEquiv := (Equiv.prodComm _ _).trans
          (Fin.snocEquiv (fun _ : Fin (n + 1) ↦ ℂ))
        map_add' := by
          intro x y
          ext i
          exact Fin.lastCases (by simp) (fun j ↦ by simp) i
        map_smul' := by
          intro c x
          ext i
          exact Fin.lastCases (by simp) (fun j ↦ by simp) i }
  have hL (x : (Fin n → ℂ) × ℂ) : Tendsto L (nhds x) (nhds (L x)) :=
    L.continuous.continuousAt
  have hLi (x : Fin (n + 1) → ℂ) :
      Tendsto L.symm (nhds x) (nhds (L.symm x)) := L.symm.continuous.continuousAt
  have hLiL (x : (Fin n → ℂ) × ℂ) : Tendsto L.symm (nhds (L x)) (nhds x) := by
    simpa using hLi (L x)
  have hirr_iff (f : (Fin n → ℂ) × ℂ → ℂ) (x : (Fin n → ℂ) × ℂ) :
      IsIrreducibleAt (fun z ↦ f (L.symm z)) (L x) ↔ IsIrreducibleAt f x := by
    constructor
    · intro hf
      refine ⟨by simpa using hf.1, ?_⟩
      intro a b ha hb hab
      have ha' := ha.comp_of_eq (L.symm.analyticAt (L x)) (by simp)
      have hb' := hb.comp_of_eq (L.symm.analyticAt (L x)) (by simp)
      have hab' : (fun z ↦ f (L.symm z)) =ᶠ[nhds (L x)]
          fun z ↦ a (L.symm z) * b (L.symm z) :=
        (hLiL x).eventually hab |>.mono fun z hz ↦ by simpa using hz
      simpa using hf.2 (fun z ↦ a (L.symm z)) (fun z ↦ b (L.symm z)) ha' hb' hab'
    · intro hf
      refine ⟨by simpa using hf.1, ?_⟩
      intro a b ha hb hab
      have ha' := ha.comp_of_eq (L.analyticAt x) (by simp)
      have hb' := hb.comp_of_eq (L.analyticAt x) (by simp)
      have hab' : f =ᶠ[nhds x] fun y ↦ a (L y) * b (L y) := by
        filter_upwards [(hL x).eventually hab] with y hy
        simpa using hy
      exact hf.2 (fun y ↦ a (L y)) (fun y ↦ b (L y)) ha' hb' hab'
  have hcop_iff (f g : (Fin n → ℂ) × ℂ → ℂ) (x : (Fin n → ℂ) × ℂ) :
      IsCoprimeAt (fun z ↦ f (L.symm z)) (fun z ↦ g (L.symm z)) (L x) ↔
        IsCoprimeAt f g x := by
    constructor
    · intro hfg ⟨a, b, c, ha, hb, hc, ha0, hfb, hgc⟩
      apply hfg
      refine ⟨fun z ↦ a (L.symm z), fun z ↦ b (L.symm z), fun z ↦ c (L.symm z),
        ha.comp_of_eq (L.symm.analyticAt (L x)) (by simp),
        hb.comp_of_eq (L.symm.analyticAt (L x)) (by simp),
        hc.comp_of_eq (L.symm.analyticAt (L x)) (by simp), by simpa, ?_, ?_⟩
      · exact (hLiL x).eventually hfb |>.mono fun z hz ↦ by simpa using hz
      · exact (hLiL x).eventually hgc |>.mono fun z hz ↦ by simpa using hz
    · intro hfg ⟨a, b, c, ha, hb, hc, ha0, hfb, hgc⟩
      apply hfg
      refine ⟨fun y ↦ a (L y), fun y ↦ b (L y), fun y ↦ c (L y),
        ha.comp_of_eq (L.analyticAt x) (by simp), hb.comp_of_eq (L.analyticAt x) (by simp),
        hc.comp_of_eq (L.analyticAt x) (by simp),
        by simpa, ?_, ?_⟩
      · exact (hL x).eventually hfb |>.mono fun y hy ↦ by simpa using hy
      · exact (hL x).eventually hgc |>.mono fun y hy ↦ by simpa using hy
  have hassoc_iff (f g : (Fin n → ℂ) × ℂ → ℂ) (x : (Fin n → ℂ) × ℂ) :
      AreAssociatedAt (fun z ↦ f (L.symm z)) (fun z ↦ g (L.symm z)) (L x) ↔
        AreAssociatedAt f g x := by
    constructor
    · rintro ⟨u, hu, hu0, hfg⟩
      refine ⟨fun y ↦ u (L y), hu.comp_of_eq (L.analyticAt x) (by simp), by simpa, ?_⟩
      exact (hL x).eventually hfg |>.mono fun y hy ↦ by simpa using hy
    · rintro ⟨u, hu, hu0, hfg⟩
      refine ⟨fun z ↦ u (L.symm z),
        hu.comp_of_eq (L.symm.analyticAt (L x)) (by simp), by simpa, ?_⟩
      exact (hLiL x).eventually hfg |>.mono fun z hz ↦ by simpa using hz
  let F' : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ F (L.symm z)
  let G' : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ G (L.symm z)
  have hnear := AnalyticDivisorAlgebraic18.gaga18_pair_propagation (n + 1) (L p) F' G'
    (hF.comp_of_eq (L.symm.analyticAt (L p)) (by simp))
    (hG.comp_of_eq (L.symm.analyticAt (L p)) (by simp))
    ((hirr_iff F p).2 hiF) ((hirr_iff G p).2 hiG) ((hcop_iff F G p).2 hc)
  filter_upwards [(hL p).eventually hnear] with q hq
  refine ⟨(hcop_iff F G q).1 hq.1, ?_⟩
  intro k l u v Q R d e hu hu0 hv hv0 hQ hR hcQ hcR hfacF hfacG j j'
  let u' : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ u (L.symm z)
  let v' : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ v (L.symm z)
  let Q' (i : Fin k) : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ Q i (L.symm z)
  let R' (i : Fin l) : (Fin (n + 1) → ℂ) → ℂ := fun z ↦ R i (L.symm z)
  have hfacF' : F' =ᶠ[nhds (L q)] fun z ↦ u' z * ∏ i, Q' i z ^ d i :=
    (hLiL q).eventually hfacF |>.mono fun z hz ↦ by simpa [F', u', Q'] using hz
  have hfacG' : G' =ᶠ[nhds (L q)] fun z ↦ v' z * ∏ i, R' i z ^ e i :=
    (hLiL q).eventually hfacG |>.mono fun z hz ↦ by simpa [G', v', R'] using hz
  have hnot := hq.2 k l u' v' Q' R' d e
    (hu.comp_of_eq (L.symm.analyticAt (L q)) (by simp)) (by simpa [u'] using hu0)
    (hv.comp_of_eq (L.symm.analyticAt (L q)) (by simp)) (by simpa [v'] using hv0)
    (fun i ↦ ⟨(hQ i).1.comp_of_eq (L.symm.analyticAt (L q)) (by simp),
      (hirr_iff (Q i) q).2 (hQ i).2.1, (hQ i).2.2⟩)
    (fun i ↦ ⟨(hR i).1.comp_of_eq (L.symm.analyticAt (L q)) (by simp),
      (hirr_iff (R i) q).2 (hR i).2.1, (hR i).2.2⟩)
    (fun i j hij ↦ (hcop_iff (Q i) (Q j) q).2 (hcQ hij))
    (fun i j hij ↦ (hcop_iff (R i) (R j) q).2 (hcR hij)) hfacF' hfacG' j j'
  change ¬ AreAssociatedAt (fun z ↦ Q j (L.symm z))
    (fun z ↦ R j' (L.symm z)) (L q) at hnot
  exact (hassoc_iff (Q j) (R j') q).not.mp hnot

/-- Association to one common germ makes two analytic germs associated. -/
theorem gaga19_associated_of_common_right_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {A B C : E → ℂ} {q : E}
    (hAC : AreAssociatedAt A C q) (hBC : AreAssociatedAt B C q) :
    AreAssociatedAt A B q := by
  obtain ⟨u, hu, hu0, hAu⟩ := hAC
  obtain ⟨v, hv, hv0, hBv⟩ := hBC
  refine ⟨fun x ↦ u x * (v x)⁻¹, hu.mul (hv.inv hv0), mul_ne_zero hu0 (inv_ne_zero hv0), ?_⟩
  filter_upwards [hAu, hBv, hv.continuousAt.eventually_ne hv0] with x hAx hBx hvx
  rw [hAx, hBx]
  field_simp

end HodgeLean.Foundations.AnalyticDivisorAlgebraic19
