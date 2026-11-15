module

public import HodgeLean.Foundations.Program.SingularGlobalPullback

public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Nonzero natural scalars act injectively on the underlying homology of a rational complex. -/
theorem forgotten_rational_homology_nsmul_injective
    (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (d n : ℕ) (hd : d ≠ 0) :
    Function.Injective (fun x :
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homology n =>
      d • x) := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e := (K.sc n).mapHomologyIso F
  have hm : ∀ (V : ModuleCat.{0} ℚ), Function.Injective (fun x : V => d • x) := by
    intro V x y h
    have hq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
    have hs : (d : ℚ) • x = (d : ℚ) • y := by
      simpa only [Nat.cast_smul_eq_nsmul] using h
    have hi := congrArg (fun z : V => (d : ℚ)⁻¹ • z) hs
    simpa only [smul_smul, inv_mul_cancel₀ hq, one_smul] using hi
  intro x y h
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  have he := congrArg (fun z => e.hom z) h
  simp only [map_nsmul] at he
  exact hm (K.homology n) he

/-- Nonzero natural scalars act bijectively on underlying rational homology.
Source: Hatcher, Algebraic Topology, §3.1, rational cohomology as a vector space. -/
theorem forgotten_rational_homology_nsmul_bijective
    (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (d n : ℕ) (hd : d ≠ 0) :
    Function.Bijective (fun x :
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homology n =>
      d • x) := by
  refine ⟨forgotten_rational_homology_nsmul_injective K d n hd, ?_⟩
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let e := (K.sc n).mapHomologyIso F
  intro z
  let z' : K.homology n := e.hom z
  let w : K.homology n := (d : ℚ)⁻¹ • z'
  refine ⟨e.inv w, ?_⟩
  apply (ConcreteCategory.bijective_of_isIso e.hom).injective
  rw [map_nsmul]
  have he : e.hom (e.inv w) = w := by
    exact congrArg (fun v => v w) e.inv_hom_id
  rw [he]
  change d • ((d : ℚ)⁻¹ • z') = z'
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hdq, one_smul]

/-- Injectivity on underlying homology detects injectivity on rational homology. -/
theorem rational_homology_injective_of_forget
    {K M : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ M) (n : ℕ)
    (h : Function.Injective (HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map f) n)) :
    Function.Injective (HomologicalComplex.homologyMap f n) := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let eK := (K.sc n).mapHomologyIso F
  let eM := (M.sc n).mapHomologyIso F
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.up ℕ) n).map f) F
  intro x y hxy
  apply (ConcreteCategory.bijective_of_isIso eK.inv).injective
  apply h
  have he := congrArg (fun z => eM.inv z) hxy
  have hx := congrArg (fun v => v x) hn
  have hy := congrArg (fun v => v y) hn
  exact hx.symm.trans (he.trans hy)

/-- Fixed rational classes remain fixed under the natural underlying-group comparison.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of coefficient restriction. -/
theorem rational_homology_forget_fixed
    (K : CochainComplex (ModuleCat.{0} ℚ) ℕ) (g : K ⟶ K) (n : ℕ)
    (z : K.homology n) (hz : HomologicalComplex.homologyMap g n z = z) :
    let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
    let e := (K.sc n).mapHomologyIso F
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (.up ℕ)).map g) n (e.inv z) = e.inv z := by
  dsimp only
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.up ℕ) n).map g) F
  have h := (congrArg (fun v => v z) hn).symm
  exact h.trans (congrArg (fun w => ((K.sc n).mapHomologyIso F).inv w) hz)

/-- A lift of the underlying homology class gives a lift of the rational class.
Source: Hatcher, Algebraic Topology, §3.1, functoriality of coefficient restriction. -/
theorem rational_homology_lift_of_forget
    {K M : CochainComplex (ModuleCat.{0} ℚ) ℕ} (f : K ⟶ M) (n : ℕ)
    (z : M.homology n)
    (x : (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).obj K).homology n)
    (hx : HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map f) n x =
      ((M.sc n).mapHomologyIso (forget₂ (ModuleCat ℚ) AddCommGrpCat)).inv z) :
    ∃ y, HomologicalComplex.homologyMap f n y = z := by
  let F := forget₂ (ModuleCat ℚ) AddCommGrpCat
  let eK := (K.sc n).mapHomologyIso F
  let eM := (M.sc n).mapHomologyIso F
  let y : K.homology n := eK.hom x
  refine ⟨y, (ConcreteCategory.bijective_of_isIso eM.inv).injective ?_⟩
  have hn := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat ℚ) (.up ℕ) n).map f) F
  have hy : eK.inv y = x := congrArg (fun v => v x) eK.hom_inv_id
  have h := (congrArg (fun v => v y) hn).symm
  change HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat ℚ) AddCommGrpCat).mapHomologicalComplex (.up ℕ)).map f) n (eK.inv y) =
      eM.inv (HomologicalComplex.homologyMap f n y) at h
  rw [hy, hx] at h
  exact h.symm

end HodgeLean.Foundations.Program
