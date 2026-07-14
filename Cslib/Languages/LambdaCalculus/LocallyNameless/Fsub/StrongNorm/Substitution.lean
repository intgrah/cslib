/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/

module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.StrongNorm.Expansion

/-! # Strong normalization for System F-sub: closing substitution

Iterated term and type substitution closing a term over a context of assignments, sum-interpretation
inversion, and the validating-substitution and empty-environment infrastructure.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Fsub

open Relation
open scoped Ty Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- Iterated term substitution closing a term over a context of term assignments. -/
def multiSubstTm : Context Var (Term Var) → Term Var → Term Var
  | [], t => t
  | ⟨x, s⟩ :: γ, t => multiSubstTm γ (t[x := s])

section
omit [HasFresh Var]

@[scoped grind =]
lemma multiSubstTm_app (γ : Context Var (Term Var)) (t₁ t₂ : Term Var) :
    multiSubstTm γ (Term.app t₁ t₂) = Term.app (multiSubstTm γ t₁) (multiSubstTm γ t₂) := by
  induction γ generalizing t₁ t₂ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_abs (γ : Context Var (Term Var)) (σ : Ty Var) (t : Term Var) :
    multiSubstTm γ (Term.abs σ t) = Term.abs σ (multiSubstTm γ t) := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_tabs (γ : Context Var (Term Var)) (σ : Ty Var) (t : Term Var) :
    multiSubstTm γ (Term.tabs σ t) = Term.tabs σ (multiSubstTm γ t) := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_tapp (γ : Context Var (Term Var)) (t : Term Var) (σ : Ty Var) :
    multiSubstTm γ (Term.tapp t σ) = Term.tapp (multiSubstTm γ t) σ := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_let (γ : Context Var (Term Var)) (t₁ t₂ : Term Var) :
    multiSubstTm γ (Term.let' t₁ t₂) = Term.let' (multiSubstTm γ t₁) (multiSubstTm γ t₂) := by
  induction γ generalizing t₁ t₂ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_inl (γ : Context Var (Term Var)) (t : Term Var) :
    multiSubstTm γ (Term.inl t) = Term.inl (multiSubstTm γ t) := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_inr (γ : Context Var (Term Var)) (t : Term Var) :
    multiSubstTm γ (Term.inr t) = Term.inr (multiSubstTm γ t) := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTm_case (γ : Context Var (Term Var)) (t₁ t₂ t₃ : Term Var) :
    multiSubstTm γ (Term.case t₁ t₂ t₃)
      = Term.case (multiSubstTm γ t₁) (multiSubstTm γ t₂) (multiSubstTm γ t₃) := by
  induction γ generalizing t₁ t₂ t₃ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

end

/-- Iterated type substitution on a type. -/
def Ty.multiSubst : Context Var (Ty Var) → Ty Var → Ty Var
  | [], σ => σ
  | ⟨X, U⟩ :: θ, σ => Ty.multiSubst θ (σ[X := U])

/-- Iterated type-in-term substitution on a term. -/
def multiSubstTy : Context Var (Ty Var) → Term Var → Term Var
  | [], t => t
  | ⟨X, U⟩ :: θ, t => multiSubstTy θ (t[X := U])

/-- All assigned types in a type-substitution context are locally closed. -/
def TyEnvLC (θ : Context Var (Ty Var)) : Prop := ∀ X U, ⟨X, U⟩ ∈ θ → U.LC

omit [DecidableEq Var] [HasFresh Var] in
lemma TyEnvLC.head {X : Var} {U : Ty Var} {θ : Context Var (Ty Var)}
    (h : TyEnvLC (⟨X, U⟩ :: θ)) : U.LC := h X U (by simp)

omit [DecidableEq Var] [HasFresh Var] in
lemma TyEnvLC.tail {X : Var} {U : Ty Var} {θ : Context Var (Ty Var)}
    (h : TyEnvLC (⟨X, U⟩ :: θ)) : TyEnvLC θ := fun Y V hV => h Y V (by simp [hV])

section
omit [HasFresh Var]

@[scoped grind =]
lemma multiSubstTy_app (θ : Context Var (Ty Var)) (t₁ t₂ : Term Var) :
    multiSubstTy θ (Term.app t₁ t₂) = Term.app (multiSubstTy θ t₁) (multiSubstTy θ t₂) := by
  induction θ generalizing t₁ t₂ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_tapp (θ : Context Var (Ty Var)) (t : Term Var) (σ : Ty Var) :
    multiSubstTy θ (Term.tapp t σ) = Term.tapp (multiSubstTy θ t) (Ty.multiSubst θ σ) := by
  induction θ generalizing t σ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_abs (θ : Context Var (Ty Var)) (σ : Ty Var) (t : Term Var) :
    multiSubstTy θ (Term.abs σ t) = Term.abs (Ty.multiSubst θ σ) (multiSubstTy θ t) := by
  induction θ generalizing σ t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_tabs (θ : Context Var (Ty Var)) (σ : Ty Var) (t : Term Var) :
    multiSubstTy θ (Term.tabs σ t) = Term.tabs (Ty.multiSubst θ σ) (multiSubstTy θ t) := by
  induction θ generalizing σ t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_let (θ : Context Var (Ty Var)) (t₁ t₂ : Term Var) :
    multiSubstTy θ (Term.let' t₁ t₂) = Term.let' (multiSubstTy θ t₁) (multiSubstTy θ t₂) := by
  induction θ generalizing t₁ t₂ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_inl (θ : Context Var (Ty Var)) (t : Term Var) :
    multiSubstTy θ (Term.inl t) = Term.inl (multiSubstTy θ t) := by
  induction θ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_inr (θ : Context Var (Ty Var)) (t : Term Var) :
    multiSubstTy θ (Term.inr t) = Term.inr (multiSubstTy θ t) := by
  induction θ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_case (θ : Context Var (Ty Var)) (t₁ t₂ t₃ : Term Var) :
    multiSubstTy θ (Term.case t₁ t₂ t₃)
      = Term.case (multiSubstTy θ t₁) (multiSubstTy θ t₂) (multiSubstTy θ t₃) := by
  induction θ generalizing t₁ t₂ t₃ with
  | nil => rfl
  | cons hd tl ih => exact ih ..

@[scoped grind =]
lemma multiSubstTy_fvar (θ : Context Var (Ty Var)) (x : Var) :
    multiSubstTy θ (Term.fvar x) = Term.fvar x := by
  induction θ generalizing x with
  | nil => rfl
  | cons hd tl ih => exact ih ..

lemma multiSubstTy_snoc (θ : Context Var (Ty Var)) (X : Var) (U : Ty Var) (t : Term Var) :
    multiSubstTy (θ ++ [⟨X, U⟩]) t = (multiSubstTy θ t)[X := U] := by
  induction θ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

lemma Ty.multiSubst_fvar_nmem (θ : Context Var (Ty Var)) {X : Var}
    (nmem : ∀ Y U, ⟨Y, U⟩ ∈ θ → Y ≠ X) : Ty.multiSubst θ (Ty.fvar X) = Ty.fvar X := by
  induction θ generalizing X with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨Y, U⟩ := hd
    simp only [Ty.multiSubst]
    have hne : X ≠ Y := (nmem Y U (by simp)).symm
    have hfvar : ((Ty.fvar X)[Y := U] : Ty Var) = Ty.fvar X := by
      rw [← Ty.subst_def]; simp only [Ty.subst, if_neg hne]
    rw [hfvar]
    exact ih fun Z V hZ => nmem Z V (by simp [hZ])

end

/-- Iterated type substitution commutes with term opening. -/
lemma multiSubstTy_openTm (θ : Context Var (Ty Var)) (t s : Term Var) (hθ : TyEnvLC θ) :
    multiSubstTy θ (t ^ᵗᵗ s) = (multiSubstTy θ t) ^ᵗᵗ (multiSubstTy θ s) := by
  induction θ generalizing t s with
  | nil => rfl
  | cons hd tl ih =>
    simp only [multiSubstTy]
    rw [Term.openTm_substTy]
    exact ih _ _ hθ.tail

/-- Iterated type substitution commutes with type opening of a term, using local closure. -/
lemma multiSubstTy_openTy (θ : Context Var (Ty Var)) (t : Term Var) (V : Ty Var) (hθ : TyEnvLC θ) :
    multiSubstTy θ (t ^ᵗᵞ V) = (multiSubstTy θ t) ^ᵗᵞ (Ty.multiSubst θ V) := by
  induction θ generalizing t V with
  | nil => rfl
  | cons hd tl ih =>
    simp only [multiSubstTy]
    rw [Term.openTy_substTy _ _ hθ.head]
    exact ih _ _ hθ.tail

omit [HasFresh Var] in
lemma multiSubstTy_fvTm (θ : Context Var (Ty Var)) (t : Term Var) :
    (multiSubstTy θ t).fvTm = t.fvTm := by
  induction θ generalizing t with
  | nil => rfl
  | cons hd tl ih =>
    simp only [multiSubstTy]
    induction t <;> grind

lemma Ty.multiSubst_lc (θ : Context Var (Ty Var)) {σ : Ty Var} (hlc : σ.LC) (hθ : TyEnvLC θ) :
    (Ty.multiSubst θ σ).LC := by
  induction θ generalizing σ with
  | nil => exact hlc
  | cons hd tl ih =>
    let ⟨X, _⟩ := hd
    exact ih (Ty.subst_lc hlc hθ.head X) hθ.tail

lemma multiSubstTy_lc (θ : Context Var (Ty Var)) {t : Term Var} (hlc : t.LC) (hθ : TyEnvLC θ) :
    (multiSubstTy θ t).LC := by
  induction θ generalizing t with
  | nil => exact hlc
  | cons hd tl ih =>
    let ⟨X, _⟩ := hd
    exact ih (Term.substTy_lc hlc hθ.head X) hθ.tail

/-- All assigned terms in a term-substitution context are locally closed. -/
def TmEnvLC (γ : Context Var (Term Var)) : Prop := ∀ x s, ⟨x, s⟩ ∈ γ → s.LC

omit [DecidableEq Var] [HasFresh Var] in
lemma TmEnvLC.tail {x : Var} {s : Term Var} {γ : Context Var (Term Var)}
    (h : TmEnvLC (⟨x, s⟩ :: γ)) : TmEnvLC γ := fun y t ht => h y t (by simp [ht])

omit [HasFresh Var] in
lemma multiSubstTm_snoc (γ : Context Var (Term Var)) (x : Var) (s t : Term Var) :
    multiSubstTm (γ ++ [⟨x, s⟩]) t = (multiSubstTm γ t)[x := s] := by
  induction γ generalizing t with
  | nil => rfl
  | cons hd tl ih => exact ih ..

lemma multiSubstTm_openTm (γ : Context Var (Term Var)) (t s : Term Var) (hγ : TmEnvLC γ) :
    multiSubstTm γ (t ^ᵗᵗ s) = (multiSubstTm γ t) ^ᵗᵗ (multiSubstTm γ s) := by
  induction γ generalizing t s with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨x, u⟩ := hd
    simp only [multiSubstTm]
    rw [Term.openTm_substTm _ _ (hγ x u (by simp))]
    exact ih _ _ hγ.tail

lemma multiSubstTm_openTy (γ : Context Var (Term Var)) (t : Term Var) (U : Ty Var)
    (hγ : TmEnvLC γ) :
    multiSubstTm γ (t ^ᵗᵞ U) = (multiSubstTm γ t) ^ᵗᵞ U := by
  induction γ generalizing t U with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨x, u⟩ := hd
    simp only [multiSubstTm]
    rw [Term.openTy_substTm t U (hγ x u (by simp)) x]
    exact ih _ _ hγ.tail

omit [HasFresh Var] in
lemma multiSubstTm_fvar_nmem (γ : Context Var (Term Var)) {x : Var}
    (nmem : ∀ y s, ⟨y, s⟩ ∈ γ → y ≠ x) : multiSubstTm γ (Term.fvar x) = Term.fvar x := by
  induction γ generalizing x with
  | nil => rfl
  | cons hd tl ih =>
    let ⟨y, u⟩ := hd
    simp only [multiSubstTm]
    have hne : x ≠ y := (nmem y u (by simp)).symm
    have hfvar : ((Term.fvar x)[y := u] : Term Var) = Term.fvar x := by
      simp only [Term.substTm_def.symm, Term.substTm, if_neg hne]
    rw [hfvar]
    exact ih fun z s hz => nmem z s (by simp [hz])

lemma multiSubstTm_lc (γ : Context Var (Term Var)) {t : Term Var} (hlc : t.LC) (hγ : TmEnvLC γ) :
    (multiSubstTm γ t).LC := by
  induction γ generalizing t with
  | nil => exact hlc
  | cons hd tl ih =>
    let ⟨x, s⟩ := hd
    exact ih (Term.substTm_lc hlc (hγ x s (by simp)) x) hγ.tail

/-- The free term variables occurring in the values of a term-substitution context. -/
def tmEnvFv (γ : Context Var (Term Var)) : Finset Var :=
  (γ.map (fun ⟨_, t⟩ => t.fvTm)).foldr (· ∪ ·) ∅

omit [HasFresh Var] in
lemma multiSubstTm_fvar_eq {γ : Context Var (Term Var)} {x : Var}
    (hdom : x ∉ (γ.keys.toFinset : Finset Var)) : multiSubstTm γ (Term.fvar x) = Term.fvar x := by
  apply multiSubstTm_fvar_nmem
  intro y s hy rfl
  exact hdom (by simp [List.mem_keys_of_mem hy])

omit [HasFresh Var] in
lemma fvTm_substTm_subset {x : Var} {s t : Term Var} {y : Var}
    (hy : y ∈ Term.fvTm (t[x:=s])) : y ∈ t.fvTm ∨ y ∈ s.fvTm := by
  induction t <;> grind

omit [HasFresh Var] in
lemma nmem_fvTm_multiSubstTm {γ : Context Var (Term Var)} {t : Term Var} {x : Var}
    (ht : x ∉ t.fvTm) (hγ : x ∉ tmEnvFv γ) : x ∉ (multiSubstTm γ t).fvTm := by
  induction γ generalizing t with
  | nil => exact ht
  | cons hd tl ih =>
    let ⟨_, s⟩ := hd
    have ⟨hs, htl⟩ : x ∉ s.fvTm ∧ x ∉ tmEnvFv tl := by
      simpa only [tmEnvFv, List.map_cons, List.foldr_cons, Finset.mem_union, not_or] using hγ
    exact ih (fun hmem => (fvTm_substTm_subset hmem).elim ht hs) htl

/-- A neutral term never reduces (in any number of steps) to a left injection. -/
lemma neutral_not_red_inl {t v : Term Var} (neu : Neutral t) (hred : t ↠βᵛ Term.inl v) : False := by
  induction hred using ReflTransGen.head_induction_on with
  | refl => cases neu
  | head r _ ih => exact ih (neu.step r)

/-- A neutral term never reduces (in any number of steps) to a right injection. -/
lemma neutral_not_red_inr {t v : Term Var} (neu : Neutral t) (hred : t ↠βᵛ Term.inr v) : False := by
  induction hred using ReflTransGen.head_induction_on with
  | refl => cases neu
  | head r _ ih => exact ih (neu.step r)

/-- A neutral term never reduces (in any number of steps) to a value. -/
lemma neutral_red_star_not_value {t v : Term Var} (neu : Neutral t) (hred : t ↠βᵛ v)
    (hval : v.Value) : False := by
  induction hred using ReflTransGen.head_induction_on with
  | refl => exact neu.not_value hval
  | head r _ ih => exact ih (neu.step r)

omit [DecidableEq Var] [HasFresh Var] in
/-- Forward closure of a candidate along multi-step reduction. -/
lemma Candidate.red_star {A : Set (Term Var)} (candA : Candidate A)
    {s v : Term Var} (hs : s ∈ A) (hred : s ↠βᵛ v) : v ∈ A := by
  induction hred with
  | refl => exact hs
  | tail _ r ih => exact candA.red ih r

/-- The payload of a left injection reachable in a sum interpretation lies in the left candidate. -/
lemma SumInterp.inl_red {A B : Set (Term Var)}
    (candA : Candidate A) (_candB : Candidate B) :
    ∀ {e : Term Var}, SumInterp A B e → ∀ {v : Term Var}, (e ↠βᵛ Term.inl v) → v ∈ A := by
  intro e h
  induction h with
  | inl hs =>
    intro v hred
    exact candA.red_star hs (Term.Red.inl_star_inv hred)
  | inr _ =>
    intro v hred
    have ⟨w, hw, _⟩ := Term.Red.inr_star_shape hred rfl
    exact absurd hw (by simp)
  | neutral _ neu =>
    intro v hred
    exact (neutral_not_red_inl neu hred).elim
  | red _ r ih =>
    intro v hred
    exact ih (hred.head r)
  | headExpand lc hnv _ ih =>
    intro v hred
    rcases hred.cases_head with h | ⟨w, r, hrest⟩
    · subst h
      refine candA.headExpand (by cases lc; assumption) (fun hv => hnv (hv.inl)) ?_
      intro u ru
      exact ih (Term.inl u) ru.inl .refl
    · exact ih w r hrest

/-- The payload of a right injection in a sum interpretation lies in the right candidate. -/
lemma SumInterp.inr_red {A B : Set (Term Var)}
    (_candA : Candidate A) (candB : Candidate B) :
    ∀ {e : Term Var}, SumInterp A B e → ∀ {v : Term Var}, (e ↠βᵛ Term.inr v) → v ∈ B := by
  intro e h
  induction h with
  | inl _ =>
    intro v hred
    have ⟨w, hw, _⟩ := Term.Red.inl_star_shape hred rfl
    exact absurd hw (by simp)
  | inr hs =>
    intro v hred
    exact candB.red_star hs (Term.Red.inr_star_inv hred)
  | neutral _ neu =>
    intro v hred
    exact (neutral_not_red_inr neu hred).elim
  | red _ r ih =>
    intro v hred
    exact ih (hred.head r)
  | headExpand lc hnv _ ih =>
    intro v hred
    rcases hred.cases_head with h | ⟨w, r, hrest⟩
    · subst h
      refine candB.headExpand (by cases lc; assumption) (fun hv => hnv (hv.inr)) ?_
      intro u ru
      exact ih u.inr ru.inr .refl
    · exact ih w r hrest

/-- The payload of a left injection in a sum interpretation lies in the left candidate. -/
lemma SumInterp.inl_mem {A B : Set (Term Var)} {v : Term Var}
    (candA : Candidate A) (candB : Candidate B)
    (h : SumInterp A B v.inl) : v ∈ A :=
  SumInterp.inl_red candA candB h .refl

/-- The payload of a right injection in a sum interpretation lies in the right candidate. -/
lemma SumInterp.inr_mem {A B : Set (Term Var)} {v : Term Var}
    (candA : Candidate A) (candB : Candidate B)
    (h : SumInterp A B v.inr) : v ∈ B :=
  SumInterp.inr_red candA candB h .refl

/-- Any value reachable from a member of a sum interpretation is a left or right injection. -/
lemma SumInterp.value_form {A B : Set (Term Var)} :
    ∀ {e : Term Var}, SumInterp A B e → ∀ {v : Term Var}, (e ↠βᵛ v) → v.Value →
      (∃ s, v = Term.inl s) ∨ (∃ s, v = Term.inr s) := by
  intro e h
  induction h with
  | inl _ =>
    intro v hred hval
    obtain ⟨w, rfl, _⟩ := Term.Red.inl_star_shape hred rfl
    exact Or.inl ⟨w, rfl⟩
  | inr _ =>
    intro v hred hval
    obtain ⟨w, rfl, _⟩ := Term.Red.inr_star_shape hred rfl
    exact Or.inr ⟨w, rfl⟩
  | neutral _ neu =>
    intro v hred hval
    exact (neutral_red_star_not_value neu hred hval).elim
  | red _ r ih =>
    intro v hred hval
    exact ih (hred.head r) hval
  | headExpand _ hnv _ ih =>
    intro v hred hval
    rcases hred.cases_head with h | ⟨w, r, hrest⟩
    · subst h; exact absurd hval hnv
    · exact ih w r hrest hval

/-- A closing substitution commutes with opening at a fresh variable. -/
lemma multiSubstTm_open_var {γ : Context Var (Term Var)} {t s : Term Var} {x : Var}
    (_hs : s.LC) (hγ : TmEnvLC γ) (hxγ : x ∉ tmEnvFv γ)
    (hxk : x ∉ (γ.keys.toFinset : Finset Var)) (hxt : x ∉ t.fvTm) :
    multiSubstTm (γ ++ [⟨x, s⟩]) (t ^ᵗᵗ Term.fvar x) = (multiSubstTm γ t) ^ᵗᵗ s := by
  have hxM : x ∉ (multiSubstTm γ t).fvTm := nmem_fvTm_multiSubstTm hxt hxγ
  rw [multiSubstTm_snoc, multiSubstTm_openTm _ _ _ hγ, multiSubstTm_fvar_eq hxk,
    ← Term.openTm_substTm_intro (multiSubstTm γ t) s hxM]

/-- A term-substitution validates a context (each variable in its type's interpretation). -/
def entailsContext (Γ : Env Var) (ρ : Valuation Var) (γ : Context Var (Term Var)) : Prop :=
  ∀ {x σ}, Binding.ty σ ∈ Γ.dlookup x → multiSubstTm γ (Term.fvar x) ∈ interp ρ σ

omit [DecidableEq Var] [HasFresh Var] in
/-- Extending a locally closed term-substitution with a locally closed assignment. -/
lemma tmCtxLc_snoc {γ : Context Var (Term Var)} {x : Var} {s : Term Var}
    (hγ : TmEnvLC γ) (hs : s.LC) : TmEnvLC (γ ++ [⟨x, s⟩]) := by
  intro y u hy
  rcases List.mem_append.mp hy with h | h
  · exact hγ y u h
  · cases List.mem_singleton.mp h; exact hs

omit [HasFresh Var] in
/-- Coherence is about `sub` bindings, so a `ty` binding may be prepended freely. -/
lemma coherent_cons_ty {Γ : Env Var} {ρ : Valuation Var} {x : Var} {σ : Ty Var}
    (cohρ : Coherent Γ ρ) : Coherent (⟨x, Binding.ty σ⟩ :: Γ) ρ := by
  intro Y σ'' bind
  rw [List.dlookup_cons_ne (a := Y) Γ ⟨x, Binding.ty σ⟩ (by
    intro rfl; rw [List.dlookup_cons_eq] at bind; cases bind)] at bind
  exact cohρ bind

omit [HasFresh Var] in
/-- Extending a validating substitution with a fresh assignment in the interpretation. -/
lemma entailsContext_snoc {Γ : Env Var} {ρ : Valuation Var} {γ : Context Var (Term Var)}
    {x : Var} {s : Term Var} {σ : Ty Var} (subok : entailsContext Γ ρ γ) (hs : s ∈ interp ρ σ)
    (hxk : x ∉ (γ.keys.toFinset : Finset Var)) (hxfv : x ∉ tmEnvFv γ) :
    entailsContext (⟨x, Binding.ty σ⟩ :: Γ) ρ (γ ++ [⟨x, s⟩]) := by
  intro y σ'' bind
  by_cases hyx : y = x
  · subst hyx
    rw [List.dlookup_cons_eq] at bind
    obtain rfl : σ'' = σ := by simpa only [Option.some.injEq, Binding.ty.injEq] using bind.symm
    rw [multiSubstTm_snoc, multiSubstTm_fvar_eq hxk]
    have : ((Term.fvar y)[y := s] : Term Var) = s := by
      rw [← Term.substTm_def]; simp only [Term.substTm, if_pos]
    rw [this]; exact hs
  · rw [List.dlookup_cons_ne (a := y) Γ ⟨x, Binding.ty σ⟩ hyx] at bind
    rw [multiSubstTm_snoc]
    have hnmem : x ∉ (multiSubstTm γ (Term.fvar y)).fvTm :=
      nmem_fvTm_multiSubstTm
        (by simp only [Term.fvTm, Finset.mem_singleton]; exact fun h => hyx h.symm) hxfv
    rw [(Term.substTm_fresh hnmem s).symm]
    exact subok bind

/-- The empty candidate environment, maximal everywhere, validating the empty context. -/
def Valuation.empty : Valuation Var := { bound := [], free _ := maximalSet }

/-- The empty candidate environment is valid. -/
lemma Valuation.empty_isValid : (Valuation.empty (Var := Var)).IsValid where
  free_rc _ := maximalCand
  bound_rc S hS := by simp [Valuation.empty] at hS

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
