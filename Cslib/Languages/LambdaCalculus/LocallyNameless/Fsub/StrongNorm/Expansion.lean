/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.StrongNorm.Candidate

/-! # Strong normalization for System F-sub: head-expansion and subtyping soundness

Call-by-value head-expansion closure of the interpretation, semantic type substitution, and
soundness of subtyping in the model.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Fsub

open Relation
open scoped Ty Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- Weak head-expansion of an interpretation, via the candidate's `headExpand` field. -/
lemma interp_headExpand {ρ : Valuation Var} (hρ : ρ.IsValid) (δ : Ty Var) {t : Term Var}
    (lc : t.LC) (hnv : ¬ t.Value) (hred : ∀ t', t ⭢βᵛ t' → t' ∈ interp ρ δ) :
    t ∈ interp ρ δ :=
  (interp_candidate δ hρ).headExpand lc hnv hred

/-- Term-β head-expansion for the function space. -/
lemma interp_headExpand_abs {ρ : Valuation Var} {σ' : Ty Var} {σ τ : Ty Var} {M s : Term Var}
    (hρ : ρ.IsValid) (lc : (Term.abs σ' M).LC) (sσ : s ∈ interp ρ σ)
    (hbody : ∀ s', s' ∈ interp ρ σ → (M ^ᵗᵗ s') ∈ interp ρ τ) :
    Term.app (Term.abs σ' M) s ∈ interp ρ τ := by
  have candσ : Candidate (interp ρ σ) := interp_candidate σ hρ
  have sns : SN Term.Red s := candσ.sn sσ
  suffices h : ∀ s, SN Term.Red s → s ∈ interp ρ σ →
      Term.app (Term.abs σ' M) s ∈ interp ρ τ from h s sns sσ
  intro s sns
  induction sns with
  | intro s _ ih =>
    intro sσ
    refine interp_headExpand hρ τ (lc.app (candσ.lc sσ)) nofun ?_
    intro u hu
    cases hu with
    | appₗ _ r₁ => exact (value_no_red (.abs lc) r₁).elim
    | appᵣ _ r₂ => exact ih _ r₂ (candσ.red sσ r₂)
    | abs _ hv => exact hbody s sσ

/-- Type-β head-expansion for the universal. -/
lemma interp_headExpand_tabs {ρ : Valuation Var} {σ' : Ty Var} {δ : Ty Var} {M : Term Var}
    {τ' : Ty Var} (hρ : ρ.IsValid) (lc : (Term.tabs σ' M).LC) (lcτ : τ'.LC)
    (hbody : (M ^ᵗᵞ τ') ∈ interp ρ δ) :
    Term.tapp (Term.tabs σ' M) τ' ∈ interp ρ δ := by
  refine interp_headExpand hρ δ (lc.tapp lcτ) nofun ?_
  intro u hu
  cases hu with
  | tapp _ r₁ => exact (value_no_red (.tabs lc) r₁).elim
  | tabs _ _ => exact hbody

/-- `case` head-expansion on a left injection (value payload). -/
lemma interp_headExpand_case_inl {ρ : Valuation Var} {σ δ : Ty Var} {v N₂ N₃ : Term Var}
    (hρ : ρ.IsValid) (val : v.Value) (vσ : v ∈ interp ρ σ) (b₂ : N₂.body) (b₃ : N₃.body)
    (hbody : ∀ s', s' ∈ interp ρ σ → (N₂ ^ᵗᵗ s') ∈ interp ρ δ) :
    Term.case (Term.inl v) N₂ N₃ ∈ interp ρ δ := by
  refine interp_headExpand hρ δ (Term.body_case.mpr ⟨val.lc.inl, b₂, b₃⟩) nofun ?_
  intro u hu
  cases hu with
  | case r₁ _ _ => exact (value_no_red (.inl val) r₁).elim
  | case_inl _ _ _ => exact hbody v vσ

/-- `case` head-expansion on a right injection (value payload). -/
lemma interp_headExpand_case_inr {ρ : Valuation Var} {τ δ : Ty Var} {v N₂ N₃ : Term Var}
    (hρ : ρ.IsValid) (val : v.Value) (vτ : v ∈ interp ρ τ) (b₂ : N₂.body) (b₃ : N₃.body)
    (hbody : ∀ s', s' ∈ interp ρ τ → (N₃ ^ᵗᵗ s') ∈ interp ρ δ) :
    Term.case (Term.inr v) N₂ N₃ ∈ interp ρ δ := by
  refine interp_headExpand hρ δ (Term.body_case.mpr ⟨val.lc.inr, b₂, b₃⟩) nofun ?_
  intro u hu
  cases hu with
  | case r₁ _ _ => exact (value_no_red (.inr val) r₁).elim
  | case_inr _ _ _ => exact hbody v vτ

omit [HasFresh Var] in
/-- The interpretation commutes with opening at depth `k` by a free type variable. -/
lemma interp_openRec_fvar {ρ : Valuation Var} {τ : Ty Var} {X : Var} {S : Set (Term Var)} {k : ℕ}
    (nmem : X ∉ τ.fv) (hk : k ≤ ρ.bound.length) (hlc : τ.LcAt (k + 1)) :
    interp { ρ with bound := ρ.bound.insertIdx k S } τ
      = interp { ρ with free := Function.update ρ.free X S } (τ⟦k ↝ Ty.fvar X⟧ᵞ) := by
  induction τ generalizing ρ k with
  | top => rw [Ty.openRec, interp, interp]
  | bvar idx =>
    simp only [Ty.LcAt] at hlc
    rw [Ty.openRec]
    rcases lt_trichotomy idx k with hlt | heq | hgt
    · rw [if_neg (by omega), interp, interp, List.getElem?_insertIdx, if_pos hlt]
    · rw [heq, if_pos rfl, interp, interp, List.getElem?_insertIdx, if_pos hk]
      simp
    · omega
  | fvar Y => exact (Function.update_of_ne (a := Y) (a' := X) (by grind) S ρ.free).symm
  | arrow σ τ ihσ ihτ | sum σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlc
    rw [Ty.openRec, interp, interp, ihσ (by grind) hk hσ, ihτ (by grind) hk hτ]
  | all σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlc
    rw [Ty.openRec, interp, interp, ihσ (by grind) hk hσ]
    have key : ∀ T : Set (Term Var),
        interp { ρ with bound := T :: ρ.bound.insertIdx k S } τ
          = interp { ρ with bound := T :: ρ.bound, free := Function.update ρ.free X S }
              (τ⟦k + 1 ↝ Ty.fvar X⟧ᵞ) := by
      intro T
      have := ihτ (ρ := { ρ with bound := T :: ρ.bound }) (by grind) (by grind) hτ
      simpa only [List.insertIdx_succ_cons] using this
    simp only [key]

omit [HasFresh Var] in
/-- The interpretation commutes with opening the closest binder against a free type variable. -/
lemma interp_openTy_fvar {ρ : Valuation Var} {τ : Ty Var} {X : Var} {S : Set (Term Var)}
    (nmem : X ∉ τ.fv) (hlc : τ.LcAt 1) :
    interp { ρ with bound := S :: ρ.bound } τ
      = interp { ρ with free := Function.update ρ.free X S } (τ ^ᵞ Ty.fvar X) := by
  have := interp_openRec_fvar (ρ := ρ) (X := X) (S := S) nmem zero_le hlc
  simpa only [Ty.open', List.insertIdx_zero] using this

omit [DecidableEq Var] [HasFresh Var] in
/-- Inserting a candidate at a de Bruijn position past the body's depth is inert. -/
lemma interp_bound_irrel_at {ρ : Valuation Var} {τ : Ty Var} {S : Set (Term Var)} {k : ℕ}
    (hk : k ≤ ρ.bound.length) (hlc : τ.LcAt k) :
    interp { ρ with bound := ρ.bound.insertIdx k S } τ = interp ρ τ := by
  induction τ generalizing ρ k with
  | top => rw [interp, interp]
  | bvar idx =>
    simp only [Ty.LcAt] at hlc
    rw [interp, interp]
    simp only [List.getElem?_insertIdx, if_pos hlc]
  | fvar Y => rw [interp, interp]
  | arrow σ τ ihσ ihτ | sum σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlc
    rw [interp, interp, ihσ hk hσ, ihτ hk hτ]
  | all σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlc
    rw [interp, interp, ihσ hk hσ]
    have key : ∀ T : Set (Term Var),
        interp { ρ with bound := T :: ρ.bound.insertIdx k S } τ
          = interp { ρ with bound := T :: ρ.bound } τ := by
      intro T
      have := ihτ (ρ := { ρ with bound := T :: ρ.bound }) (by grind) hτ
      simpa only [List.insertIdx_succ_cons] using this
    simp only [key]

omit [DecidableEq Var] [HasFresh Var] in
/-- Pushing a candidate onto a body that is already closed (`LcAt 0`) is inert. -/
lemma interp_bound_irrel {ρ : Valuation Var} {τ : Ty Var} {S : Set (Term Var)} (hlc : τ.LcAt 0) :
    interp { ρ with bound := S :: ρ.bound } τ = interp ρ τ := by
  have h := interp_bound_irrel_at (ρ := ρ) (S := S) zero_le hlc
  rwa [List.insertIdx_zero] at h

omit [DecidableEq Var] [HasFresh Var] in
/-- Interpretation commutes with opening at depth `k` (semantic substitution at depth). -/
lemma interp_openRec {ρ : Valuation Var} {τ U : Ty Var} {k : ℕ}
    (hk : k ≤ ρ.bound.length) (hlcτ : τ.LcAt (k + 1)) (hlcU : U.LcAt 0) :
    interp { ρ with bound := ρ.bound.insertIdx k (interp ρ U) } τ = interp ρ (τ⟦k ↝ U⟧ᵞ) := by
  induction τ generalizing ρ k with
  | top => rw [Ty.openRec, interp, interp]
  | bvar idx =>
    simp only [Ty.LcAt] at hlcτ
    rw [Ty.openRec]
    rcases lt_trichotomy idx k with hlt | heq | hgt
    · rw [if_neg (by omega), interp, interp, List.getElem?_insertIdx, if_pos hlt]
    · rw [heq, if_pos rfl, interp, List.getElem?_insertIdx, if_neg (by omega), if_pos rfl,
        if_pos hk, Option.getD_some]
    · omega
  | fvar Y => rw [Ty.openRec, interp, interp]
  | arrow σ τ ihσ ihτ | sum σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlcτ
    rw [Ty.openRec, interp, interp, ihσ hk hσ, ihτ hk hτ]
  | all σ τ ihσ ihτ =>
    have ⟨hσ, hτ⟩ := hlcτ
    rw [Ty.openRec, interp, interp, ihσ hk hσ]
    have key : ∀ T : Set (Term Var),
        interp { ρ with bound := T :: ρ.bound.insertIdx k (interp ρ U) } τ
          = interp { ρ with bound := T :: ρ.bound } (τ⟦k + 1 ↝ U⟧ᵞ) := by
      intro T
      have h := ihτ (ρ := { ρ with bound := T :: ρ.bound }) (k := k + 1) (by grind) hτ
      rw [interp_bound_irrel (ρ := ρ) (S := T) hlcU] at h
      simpa only [List.insertIdx_succ_cons] using h
    simp only [key]

omit [DecidableEq Var] [HasFresh Var] in
/-- The semantic substitution lemma, powering the `tapp` case of the fundamental lemma. -/
lemma interp_openTy {ρ : Valuation Var} {τ U : Ty Var} (hlcτ : τ.LcAt 1) (hlcU : U.LcAt 0) :
    interp { ρ with bound := interp ρ U :: ρ.bound } τ = interp ρ (τ ^ᵞ U) := by
  have := interp_openRec (ρ := ρ) (U := U) zero_le hlcτ hlcU
  simpa only [Ty.open', List.insertIdx_zero] using this

/-- The body of a locally closed quantifier is closed up to depth one. -/
lemma Ty.lcAt_one_of_lc_all {σ τ : Ty Var} (h : (Ty.all σ τ).LC) : τ.LcAt 1 := by
  let .all L _ hτ := h
  have ⟨X, hX⟩ := fresh_exists (L ∪ τ.fv)
  exact Ty.lcAt_of_openRec (X := X) (Ty.lcAt_zero_of_lc (hτ X (by grind)))

/-- A candidate environment is coherent with a context when it respects every subtyping bound. -/
def Coherent (Γ : Env Var) (ρ : Valuation Var) : Prop :=
  ∀ {X σ}, Binding.sub σ ∈ Γ.dlookup X → ρ.free X ⊆ interp ρ σ

omit [HasFresh Var] in
/-- The extended environment updating a fresh free variable is valid. -/
lemma isValid_free_update {ρ : Valuation Var} {X : Var} {S : Set (Term Var)} (hρ : ρ.IsValid)
    (candS : Candidate S) :
    ({ ρ with free := Function.update ρ.free X S } : Valuation Var).IsValid := by
  refine ⟨fun Y => ?_, hρ.bound_rc⟩
  by_cases hY : Y = X
  · subst hY; simpa only [Function.update_self] using candS
  · simpa only [Function.update_of_ne hY] using hρ.free_rc Y

/-- Coherence extends to a fresh `sub` binding pointing at a candidate below its bound. -/
lemma coherent_free_update {Γ : Env Var} {ρ : Valuation Var} {X : Var} {σ : Ty Var}
    {S : Set (Term Var)} (cohρ : Coherent Γ ρ) (hΓwf : Env.Wf Γ) (hXΓ : X ∉ Context.dom Γ)
    (hXσ : X ∉ σ.fv) (hsub : S ⊆ interp ρ σ) :
    Coherent (⟨X, Binding.sub σ⟩ :: Γ) ({ ρ with free := Function.update ρ.free X S }) := by
  intro Y σ'' bind
  by_cases hYX : Y = X
  · subst hYX
    rw [List.dlookup_cons_eq] at bind
    have heqσ : σ'' = σ := by simpa only [Option.some.injEq, Binding.sub.injEq] using bind.symm
    subst heqσ
    rw [interp_free_update_nmem hXσ]
    intro s hs
    simp only [Function.update_self] at hs
    exact hsub hs
  · rw [List.dlookup_cons_ne (a := Y) Γ ⟨X, Binding.sub σ⟩ hYX] at bind
    have hnmem : X ∉ σ''.fv := (Ty.Wf.of_bind_sub hΓwf bind).nmem_fv hXΓ
    have hfreeY :
        ({ ρ with free := Function.update ρ.free X S } : Valuation Var).free Y = ρ.free Y :=
      Function.update_of_ne hYX S ρ.free
    rw [hfreeY, interp_free_update_nmem hnmem]
    exact cohρ bind

/-- Soundness of subtyping in the model: `Sub Γ σ τ` gives `interp ρ σ ⊆ interp ρ τ`. -/
lemma interp_sub_subset {Γ : Env Var} {σ τ : Ty Var} (sub : Sub Γ σ τ)
    {ρ : Valuation Var} (hρ : ρ.IsValid) (cohρ : Coherent Γ ρ) :
    interp ρ σ ⊆ interp ρ τ := by
  induction sub generalizing ρ with
  | top _ _ =>
    intro t ht
    exact ⟨interp_lc hρ ht, interp_sn hρ ht⟩
  | refl_tvar => exact fun t ht => ht
  | trans_tvar bind _ ih => exact fun t ht => ih hρ cohρ (cohρ bind ht)
  | arrow _ _ ihσ ihτ =>
    intro t ⟨lc, sn, hbody⟩
    refine ⟨lc, sn, ?_⟩
    intro s hs
    exact ihτ hρ cohρ (hbody s (ihσ hρ cohρ hs))
  | @all Γ σ σ' τ' τ L subσ subτ ihσ ihτ =>
    have ⟨wfΓ, wfLHS, wfRHS⟩ := Sub.wf Γ _ _ (Sub.all L subσ subτ)
    have lcτ' : τ'.LcAt 1 := Ty.lcAt_one_of_lc_all wfLHS.lc
    have lcτ : τ.LcAt 1 := Ty.lcAt_one_of_lc_all wfRHS.lc
    intro t ⟨lc, sn, hbody⟩
    refine ⟨lc, sn, ?_⟩
    intro S candS hsub U hU
    have hsub' : ∀ s ∈ S, s ∈ interp ρ σ' := fun s hs => ihσ hρ cohρ (hsub s hs)
    have hmem : Term.tapp t U ∈ interp { ρ with bound := S :: ρ.bound } τ' :=
      hbody S candS hsub' U hU
    have ⟨X, hX⟩ := fresh_exists (L ∪ σ.fv ∪ σ'.fv ∪ τ.fv ∪ τ'.fv ∪ Γ.dom)
    set ρ' : Valuation Var := { ρ with free := Function.update ρ.free X S }
    have hρ'valid : ρ'.IsValid := isValid_free_update hρ candS
    have hcoh' : Coherent (⟨X, Binding.sub σ⟩ :: Γ) ρ' :=
      coherent_free_update cohρ wfΓ (by grind) (by grind) hsub
    have hrw' : interp { ρ with bound := S :: ρ.bound } τ' = interp ρ' (τ' ^ᵞ Ty.fvar X) :=
      interp_openTy_fvar (by grind) lcτ'
    have hrw : interp { ρ with bound := S :: ρ.bound } τ = interp ρ' (τ ^ᵞ Ty.fvar X) :=
      interp_openTy_fvar (by grind) lcτ
    rw [hrw]
    rw [hrw'] at hmem
    exact ihτ X (by grind) hρ'valid hcoh' hmem
  | sum _ _ ihσ ihτ =>
    intro t ht
    induction ht with
    | inl hs => exact SumInterp.inl (ihσ hρ cohρ hs)
    | inr hs => exact SumInterp.inr (ihτ hρ cohρ hs)
    | neutral lc neu => exact SumInterp.neutral lc neu
    | red _ r ih => exact SumInterp.red ih r
    | headExpand lc hnv _ ih => exact SumInterp.headExpand lc hnv ih

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
