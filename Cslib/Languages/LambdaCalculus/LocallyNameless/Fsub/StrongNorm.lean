/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.StrongNorm.Substitution

/-! # Strong normalization for System F-sub

Strong normalization (call-by-value termination) for the polymorphic, subtyped λ-calculus with
sums, via Girard's reducibility candidates indexed by a de Bruijn candidate environment.

The call-by-value reduction `Term.Red` (`⭢βᵛ`) does not reduce under any binder, so every value is
already a normal form. Strong normalization is the statement that reduction of a well-typed term
terminates: `Typing Γ t τ → SN Term.Red t`.

`interp` recurses structurally on `Ty`: the impredicative universal type `∀<:σ. τ` is interpreted by
quantifying over the abstract space of reducibility candidates, pushing the chosen candidate onto a
de Bruijn-indexed `Valuation.bound` list rather than opening the body with a fresh free type
variable.

This file contains the fundamental lemma and the strong-normalization theorem.

## References

* [A. Chargueraud, *The Locally Nameless Representation*][Chargueraud2012]
* J.-Y. Girard, P. Taylor, Y. Lafont, *Proofs and Types* (reducibility candidates for System F)
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Fsub

open Relation
open scoped Ty Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- Semantic typing: the closed term lands in the interpretation of its type. -/
def entails (Γ : Env Var) (t : Term Var) (τ : Ty Var) : Prop :=
  ∀ (ρ : Valuation Var) (γ : Context Var (Term Var)),
    ρ.IsValid → Coherent Γ ρ → TmEnvLC γ → entailsContext Γ ρ γ → multiSubstTm γ t ∈ interp ρ τ

/-- Semantic typing threaded with a type-substitution context, for the induction. -/
def entails' (Γ : Env Var) (t : Term Var) (τ : Ty Var) : Prop :=
  ∀ (ρ : Valuation Var) (θ : Context Var (Ty Var)) (γ : Context Var (Term Var)),
    ρ.IsValid → Coherent Γ ρ → TyEnvLC θ → TmEnvLC γ → entailsContext Γ ρ γ →
      multiSubstTm γ (multiSubstTy θ t) ∈ interp ρ τ

/-- Opening the closed body at any element of the domain interpretation stays in the codomain. -/
lemma interp_open_body {Γ : Env Var} {t : Term Var} {σ τ : Ty Var} {L : Finset Var}
    {ρ : Valuation Var} {θ : Context Var (Ty Var)} {γ : Context Var (Term Var)}
    (hρ : ρ.IsValid) (cohρ : Coherent Γ ρ) (hθ : TyEnvLC θ) (hγ : TmEnvLC γ)
    (subok : entailsContext Γ ρ γ)
    (ih : ∀ x ∉ L, entails' (⟨x, Binding.ty σ⟩ :: Γ) (t ^ᵗᵗ Term.fvar x) τ)
    {s' : Term Var} (hs' : s' ∈ interp ρ σ) :
    (multiSubstTm γ (multiSubstTy θ t)) ^ᵗᵗ s' ∈ interp ρ τ := by
  have hs'lc : s'.LC := interp_lc hρ hs'
  have ⟨x, hx⟩ := fresh_exists
    (L ∪ Context.dom Γ ∪ γ.keys.toFinset ∪ tmEnvFv γ ∪ t.fvTm)
  have hxL : x ∉ L := by grind
  have hxk : x ∉ (γ.keys.toFinset : Finset Var) := by grind
  have hxfv : x ∉ tmEnvFv γ := by grind
  have hxt : x ∉ t.fvTm := by grind
  have hih := ih x hxL ρ θ (γ ++ [⟨x, s'⟩]) hρ (coherent_cons_ty cohρ) hθ
    (tmCtxLc_snoc hγ hs'lc) (entailsContext_snoc subok hs' hxk hxfv)
  rwa [multiSubstTy_openTm _ _ _ hθ, multiSubstTy_fvar,
    multiSubstTm_open_var hs'lc hγ hxfv hxk (by rw [multiSubstTy_fvTm]; exact hxt)] at hih

/-- The closing substitution of an abstraction's body is locally closed under any type-subst. -/
lemma multiSubst_abs_lc {Γ : Env Var} {t₁ : Term Var} {σ τ : Ty Var} {L : Finset Var}
    {θ : Context Var (Ty Var)} {γ : Context Var (Term Var)}
    (d : ∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ Term.fvar x) τ)
    (hθ : TyEnvLC θ) (hγ : TmEnvLC γ) :
    (Term.abs (Ty.multiSubst θ σ) (multiSubstTm γ (multiSubstTy θ t₁))).LC := by
  have ⟨_, hlc, _⟩ := (Typing.abs L d).wf
  have h0 := multiSubstTy_lc θ hlc hθ
  rw [multiSubstTy_abs] at h0
  have h1 := multiSubstTm_lc γ h0 hγ
  rwa [multiSubstTm_abs] at h1

/-- Lifting the abstraction case of soundness. -/
lemma compat_abs {Γ : Env Var} {t₁ : Term Var} {σ τ : Ty Var} {L : Finset Var}
    (d : ∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ Term.fvar x) τ)
    (ih : ∀ x ∉ L, entails' (⟨x, Binding.ty σ⟩ :: Γ) (t₁ ^ᵗᵗ Term.fvar x) τ) :
    entails' Γ (Term.abs σ t₁) (Ty.arrow σ τ) := by
  intro ρ θ γ hρ cohρ hθ hγ subok
  rw [multiSubstTy_abs, multiSubstTm_abs]
  have hlcabs := multiSubst_abs_lc d hθ hγ
  exact ⟨hlcabs, sn_value (Term.Value.abs hlcabs),
    fun s hs => interp_headExpand_abs hρ hlcabs hs
      (fun s' hs' => interp_open_body hρ cohρ hθ hγ subok ih hs')⟩

/-- The closing substitution of a type-abstraction's body is locally closed. -/
lemma multiSubst_tabs_lc {Γ : Env Var} {t₁ : Term Var} {σ τ : Ty Var} {L : Finset Var}
    {θ : Context Var (Ty Var)} {γ : Context Var (Term Var)}
    (d : ∀ X ∉ L, Typing (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ Ty.fvar X) (τ ^ᵞ Ty.fvar X))
    (hθ : TyEnvLC θ) (hγ : TmEnvLC γ) :
    (Term.tabs (Ty.multiSubst θ σ) (multiSubstTm γ (multiSubstTy θ t₁))).LC := by
  have ⟨_, hlc, _⟩ := (Typing.tabs L d).wf
  have h0 := multiSubstTy_lc θ hlc hθ
  rw [multiSubstTy_tabs] at h0
  have h1 := multiSubstTm_lc γ h0 hγ
  rwa [multiSubstTm_tabs] at h1

/-- The validating substitution survives a fresh free-variable update of the environment. -/
lemma entailsContext_free_update {Γ : Env Var} {ρ : Valuation Var} {γ : Context Var (Term Var)}
    {X : Var} {σ : Ty Var} {S : Set (Term Var)} (subok : entailsContext Γ ρ γ) (hΓwf : Env.Wf Γ)
    (hXΓ : X ∉ Context.dom Γ) :
    entailsContext (⟨X, Binding.sub σ⟩ :: Γ) ({ ρ with free := Function.update ρ.free X S }) γ := by
  intro y σ'' bind
  rw [List.dlookup_cons_ne (a := y) Γ ⟨X, Binding.sub σ⟩ (by
    intro rfl
    rw [List.dlookup_cons_eq] at bind
    cases bind)] at bind
  have hnmem : X ∉ σ''.fv := (Ty.Wf.of_bind_ty hΓwf bind).nmem_fv hXΓ
  rw [interp_free_update_nmem hnmem]
  exact subok bind

/-- Lifting the type-abstraction case of soundness. -/
lemma compat_tabs {Γ : Env Var} {t₁ : Term Var} {σ τ : Ty Var} {L : Finset Var}
    (d : ∀ X ∉ L, Typing (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ Ty.fvar X) (τ ^ᵞ Ty.fvar X))
    (ih : ∀ X ∉ L, entails' (⟨X, Binding.sub σ⟩ :: Γ) (t₁ ^ᵗᵞ Ty.fvar X) (τ ^ᵞ Ty.fvar X)) :
    entails' Γ (Term.tabs σ t₁) (Ty.all σ τ) := by
  intro ρ θ γ hρ cohρ hθ hγ subok
  rw [multiSubstTy_tabs, multiSubstTm_tabs]
  set M₀ : Term Var := multiSubstTy θ t₁
  set M : Term Var := multiSubstTm γ M₀
  have hlctabs := multiSubst_tabs_lc d hθ hγ
  refine ⟨hlctabs, sn_value (Term.Value.tabs hlctabs), ?_⟩
  intro S candS hsub U hU
  refine interp_headExpand_tabs (hρ.extend_bound candS) hlctabs hU ?_
  have ⟨X, hX⟩ := fresh_exists
    (L ∪ Context.dom Γ ∪ γ.keys.toFinset ∪ tmEnvFv γ ∪ t₁.fvTm ∪ σ.fv ∪ τ.fv ∪ M.fvTm
      ∪ M₀.fvTy ∪ θ.keys.toFinset)
  simp only [Finset.mem_union, not_or] at hX
  have ⟨⟨⟨⟨⟨⟨⟨⟨⟨hXL, hXΓ⟩, hXk⟩, hXfv⟩, hXt₁⟩, hXσ⟩, hXτ⟩, hXMtm⟩, hXM₀ty⟩, hXθkeys⟩ := hX
  have ⟨_, _, hwfτ⟩ := (Typing.tabs L d).wf
  have hτlc : τ.LcAt 1 := Ty.lcAt_one_of_lc_all hwfτ.lc
  have hΓwf : Env.Wf Γ := by let .sub h _ _ := (d X hXL).wf.left; exact h
  have hXθk : ∀ Y V, ⟨Y, V⟩ ∈ θ → Y ≠ X := by
    intro Y V hYV rfl
    exact hXθkeys (by simp [List.mem_keys_of_mem hYV])
  have hθ' : TyEnvLC (θ ++ [⟨X, U⟩]) := by
    intro Y V hY
    rcases List.mem_append.mp hY with h | h
    · exact hθ Y V h
    · simp only [List.mem_singleton] at h; cases h; exact hU
  have hih := ih X hXL { ρ with free := Function.update ρ.free X S } (θ ++ [⟨X, U⟩]) γ
    (isValid_free_update hρ candS) (coherent_free_update cohρ hΓwf hXΓ hXσ hsub) hθ' hγ
    (entailsContext_free_update subok hΓwf hXΓ)
  rwa [multiSubstTy_snoc, multiSubstTy_openTy _ _ _ hθ,
    Ty.multiSubst_fvar_nmem _ hXθk,
    (Term.openTy_substTy_intro M₀ U hXM₀ty).symm,
    multiSubstTm_openTy _ _ _ hγ, (interp_openTy_fvar hXτ hτlc).symm] at hih

/-- The closing substitution of a binder body is a `body` term. -/
lemma multiSubst_branch_body {Γ : Env Var} {tᵢ : Term Var} {σ' δ : Ty Var} {L : Finset Var}
    {θ : Context Var (Ty Var)} {γ : Context Var (Term Var)}
    (dᵢ : ∀ x ∉ L, Typing (⟨x, Binding.ty σ'⟩ :: Γ) (tᵢ ^ᵗᵗ Term.fvar x) δ)
    (hθ : TyEnvLC θ) (hγ : TmEnvLC γ) :
    (multiSubstTm γ (multiSubstTy θ tᵢ)).body := by
  refine ⟨L ∪ Context.dom Γ ∪ γ.keys.toFinset ∪ tmEnvFv γ ∪ tᵢ.fvTm, fun y hy => ?_⟩
  have hyL : y ∉ L := by grind
  have hyk : y ∉ (γ.keys.toFinset : Finset Var) := by grind
  have ⟨_, hlcbody, _⟩ := (dᵢ y hyL).wf
  have h0 := multiSubstTy_lc θ hlcbody hθ
  rw [multiSubstTy_openTm _ _ _ hθ, multiSubstTy_fvar] at h0
  have h1 := multiSubstTm_lc γ h0 hγ
  rwa [multiSubstTm_openTm _ _ _ hγ, multiSubstTm_fvar_eq hyk] at h1

/-- Lifting the `let`-binding case of soundness. -/
lemma compat_let {Γ : Env Var} {t₁ t₂ : Term Var} {σ τ : Ty Var} {L : Finset Var}
    (d₂ : ∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ Term.fvar x) τ)
    (ih₁ : entails' Γ t₁ σ)
    (ih₂ : ∀ x ∉ L, entails' (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ Term.fvar x) τ) :
    entails' Γ (Term.let' t₁ t₂) τ := by
  intro ρ θ γ hρ cohρ hθ hγ subok
  rw [multiSubstTy_let, multiSubstTm_let]
  set N : Term Var := multiSubstTm γ (multiSubstTy θ t₂)
  have hMmem : multiSubstTm γ (multiSubstTy θ t₁) ∈ interp ρ σ := ih₁ ρ θ γ hρ cohρ hθ hγ subok
  have hNbody : N.body := multiSubst_branch_body d₂ hθ hγ
  have hbody : ∀ s', s' ∈ interp ρ σ → (N ^ᵗᵗ s') ∈ interp ρ τ :=
    fun s' hs' => interp_open_body hρ cohρ hθ hγ subok ih₂ hs'
  suffices h : ∀ M, SN Term.Red M → M ∈ interp ρ σ →
      Term.let' M N ∈ interp ρ τ from
    h _ (interp_sn hρ hMmem) hMmem
  intro M snM
  induction snM with
  | intro M _ ih =>
    intro hMmem
    refine interp_headExpand hρ τ (Term.body_let.mpr ⟨interp_lc hρ hMmem, hNbody⟩) nofun ?_
    intro u hu
    cases hu with
    | let_bind r hb =>
      exact ih _ r ((interp_candidate σ hρ).red hMmem r)
    | let_body hv hb =>
      exact hbody M hMmem

/-- Lifting the sum-elimination case of soundness. -/
lemma compat_case {Γ : Env Var} {t₁ t₂ t₃ : Term Var} {σ τ δ : Ty Var} {L : Finset Var}
    (d₂ : ∀ x ∉ L, Typing (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ Term.fvar x) δ)
    (d₃ : ∀ x ∉ L, Typing (⟨x, Binding.ty τ⟩ :: Γ) (t₃ ^ᵗᵗ Term.fvar x) δ)
    (ih₁ : entails' Γ t₁ (Ty.sum σ τ))
    (ih₂ : ∀ x ∉ L, entails' (⟨x, Binding.ty σ⟩ :: Γ) (t₂ ^ᵗᵗ Term.fvar x) δ)
    (ih₃ : ∀ x ∉ L, entails' (⟨x, Binding.ty τ⟩ :: Γ) (t₃ ^ᵗᵗ Term.fvar x) δ) :
    entails' Γ (Term.case t₁ t₂ t₃) δ := by
  intro ρ θ γ hρ cohρ hθ hγ subok
  rw [multiSubstTy_case, multiSubstTm_case]
  have hMmem : multiSubstTm γ (multiSubstTy θ t₁) ∈ interp ρ (Ty.sum σ τ) :=
    ih₁ ρ θ γ hρ cohρ hθ hγ subok
  have hN₂body : (multiSubstTm γ (multiSubstTy θ t₂)).body := multiSubst_branch_body d₂ hθ hγ
  have hN₃body : (multiSubstTm γ (multiSubstTy θ t₃)).body := multiSubst_branch_body d₃ hθ hγ
  have hbody₂ : ∀ s', s' ∈ interp ρ σ →
      ((multiSubstTm γ (multiSubstTy θ t₂)) ^ᵗᵗ s') ∈ interp ρ δ :=
    fun s' hs' => interp_open_body hρ cohρ hθ hγ subok ih₂ hs'
  have hbody₃ : ∀ s', s' ∈ interp ρ τ →
      ((multiSubstTm γ (multiSubstTy θ t₃)) ^ᵗᵗ s') ∈ interp ρ δ :=
    fun s' hs' => interp_open_body hρ cohρ hθ hγ subok ih₃ hs'
  set N₂ : Term Var := multiSubstTm γ (multiSubstTy θ t₂)
  set N₃ : Term Var := multiSubstTm γ (multiSubstTy θ t₃)
  clear_value N₂ N₃
  suffices h : ∀ M, SN Term.Red M → M ∈ interp ρ (Ty.sum σ τ) →
      Term.case M N₂ N₃ ∈ interp ρ δ from
    h _ (interp_sn hρ hMmem) hMmem
  intro M snM
  induction snM with
  | intro M _ ih =>
    intro hMmem
    have hMsum : SumInterp (interp ρ σ) (interp ρ τ) M := hMmem
    by_cases hval : M.Value
    · rcases SumInterp.value_form hMsum .refl hval with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · let .inl hv := hval
        exact interp_headExpand_case_inl hρ hv
          (SumInterp.inl_mem (interp_candidate σ hρ) (interp_candidate τ hρ) hMsum)
          hN₂body hN₃body hbody₂
      · let .inr hv := hval
        exact interp_headExpand_case_inr hρ hv
          (SumInterp.inr_mem (interp_candidate σ hρ) (interp_candidate τ hρ) hMsum)
          hN₂body hN₃body hbody₃
    · refine interp_headExpand hρ δ
        (Term.body_case.mpr ⟨(interp_candidate (Ty.sum σ τ) hρ).lc hMmem, hN₂body, hN₃body⟩)
        nofun ?_
      intro u hu
      cases hu with
      | case r _ _ => exact ih _ r (SumInterp.red hMsum r)
      | case_inl hv _ _ => exact absurd (hv.inl) hval
      | case_inr hv _ _ => exact absurd (hv.inr) hval

/-- The fundamental lemma, strengthened with substitution contexts for the induction. -/
lemma soundness' {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) :
    entails' Γ t τ := by
  induction der with
  | var _ bind =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    rw [multiSubstTy_fvar]
    exact subok bind
  | app _ _ ih₁ ih₂ =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    rw [multiSubstTy_app, multiSubstTm_app]
    have ⟨_, _, hbody⟩ := ih₁ ρ θ γ hρ cohρ hθ hγ subok
    exact hbody _ (ih₂ ρ θ γ hρ cohρ hθ hγ subok)
  | sub _ sub ih =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    exact interp_sub_subset sub hρ cohρ (ih ρ θ γ hρ cohρ hθ hγ subok)
  | abs _ d ih => exact compat_abs d ih
  | tabs _ d ih => exact compat_tabs d ih
  | tapp d sub ih =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    rw [multiSubstTy_tapp, multiSubstTm_tapp]
    have ⟨_, _, hFbody⟩ := ih ρ θ γ hρ cohρ hθ hγ subok
    have ⟨_, hwfσ', _⟩ := Sub.wf _ _ _ sub
    have hσ'lc := hwfσ'.lc
    have ⟨_, _, hwfall⟩ := d.wf
    have hmem := hFbody _ (interp_candidate _ hρ)
      (fun _ hs => interp_sub_subset sub hρ cohρ hs) _ (Ty.multiSubst_lc θ hσ'lc hθ)
    rwa [interp_openTy (Ty.lcAt_one_of_lc_all hwfall.lc)
      (Ty.lcAt_zero_of_lc hσ'lc)] at hmem
  | let' _ _ d₂ ih₁ ih₂ => exact compat_let d₂ ih₁ ih₂
  | inl _ _ ih =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    rw [multiSubstTy_inl, multiSubstTm_inl]
    exact SumInterp.inl (ih ρ θ γ hρ cohρ hθ hγ subok)
  | inr _ _ ih =>
    intro ρ θ γ hρ cohρ hθ hγ subok
    rw [multiSubstTy_inr, multiSubstTm_inr]
    exact SumInterp.inr (ih ρ θ γ hρ cohρ hθ hγ subok)
  | case _ _ d₂ d₃ ih₁ ih₂ ih₃ => exact compat_case d₂ d₃ ih₁ ih₂ ih₃

/-- The fundamental lemma: every well-typed term is semantically well-typed. -/
lemma soundness {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) : entails Γ t τ := by
  intro ρ γ hρ cohρ hγlc subok
  have h := soundness' der ρ [] γ hρ cohρ nofun hγlc subok
  simpa only [multiSubstTy] using h

/-- The canonical candidate environment of a context, assigning to each type variable the
interpretation of its subtyping bound. -/
def Env.valuation : Env Var → Valuation Var
  | [] => Valuation.empty
  | ⟨X, Binding.sub β⟩ :: Γ =>
    let ρ := Env.valuation Γ
    { ρ with free := Function.update ρ.free X (interp ρ β) }
  | ⟨_, Binding.ty _⟩ :: Γ => Env.valuation Γ

/-- The canonical candidate environment of a well-formed context is valid. -/
lemma Env.valuation_isValid {Γ : Env Var} (wf : Γ.Wf) : (Env.valuation Γ).IsValid := by
  induction wf with
  | empty => exact Valuation.empty_isValid
  | sub _ _ _ ih => exact isValid_free_update ih (interp_candidate _ ih)
  | ty _ _ _ ih => simpa only [Env.valuation] using ih

/-- The canonical candidate environment of a well-formed context is coherent with it. -/
lemma Env.valuation_coherent {Γ : Env Var} (wf : Γ.Wf) : Coherent Γ (Env.valuation Γ) := by
  induction wf with
  | empty => nofun
  | sub wfΓ wfβ hY ih => exact coherent_free_update ih wfΓ hY (wfβ.nmem_fv hY) subset_rfl
  | ty _ _ _ ih => exact coherent_cons_ty ih

/-- Every well-typed term is strongly normalizing under call-by-value reduction. -/
theorem strong_norm {Γ : Env Var} {t : Term Var} {τ : Ty Var} (der : Typing Γ t τ) :
    SN Term.Red t := by
  have wfΓ : Γ.Wf := der.wf.1
  have hρ := Env.valuation_isValid wfΓ
  have h := soundness der (Env.valuation Γ) [] hρ (Env.valuation_coherent wfΓ) nofun
    (by intro x σ _; exact (interp_candidate σ hρ).neutral Term.LC.var (Neutral.fvar x))
  exact interp_sn hρ h

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
