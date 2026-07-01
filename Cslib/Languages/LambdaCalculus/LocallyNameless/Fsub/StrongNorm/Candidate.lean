/-
Copyright (c) 2026 Jeremy Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Chen
-/

module

public import Cslib.Foundations.Relation.Confluence
public import Cslib.Languages.LambdaCalculus.LocallyNameless.Fsub.Typing

/-! # Strong normalization for System F-sub: reducibility candidates

Type size, local closure at depth, call-by-value strong-normalization building blocks, reducibility
candidates, the type-variable valuation, and the Girard interpretation.
-/

@[expose] public section

set_option linter.unusedDecidableInType false

namespace Cslib

universe u

namespace LambdaCalculus.LocallyNameless.Fsub

open Relation
open scoped Ty Term

variable {Var : Type u} [DecidableEq Var] [HasFresh Var]

/-- Local closure of a type up to de Bruijn depth `k` (`LcAt 0` is full local closure). -/
@[scoped grind =]
def Ty.LcAt : Ty Var → ℕ → Prop
  | .top, _ => True
  | .bvar i, k => i < k
  | .fvar _, _ => True
  | .arrow σ τ, k => σ.LcAt k ∧ τ.LcAt k
  | .all σ τ, k => σ.LcAt k ∧ τ.LcAt (k + 1)
  | .sum σ τ, k => σ.LcAt k ∧ τ.LcAt k

omit [DecidableEq Var] [HasFresh Var] in
/-- Opening at depth `k` with a free variable lowers an `LcAt k` body to `LcAt (k + 1)`. -/
lemma Ty.lcAt_of_openRec {σ : Ty Var} {X : Var} {k : ℕ}
    (h : (σ⟦k ↝ Ty.fvar X⟧ᵞ).LcAt k) : σ.LcAt (k + 1) := by
  induction σ generalizing k <;> grind

/-- A locally closed type is closed at every depth, in particular `LcAt 0`. -/
lemma Ty.lcAt_zero_of_lc {σ : Ty Var} (h : σ.LC) : σ.LcAt 0 := by
  induction h with
  | all L _ _ _ ih => grind [fresh_exists <| free_union Var, lcAt_of_openRec]
  | _ => grind

omit [DecidableEq Var] [HasFresh Var] in
/-- Strong normalization lifts through a left injection. -/
lemma sn_inl {t : Term Var} (h : SN Term.Red t) : SN Term.Red (Term.inl t) := by
  induction h with
  | intro _ _ ih =>
    refine SN.intro fun u hu => ?_
    cases hu with
    | inl r => exact ih _ r

omit [DecidableEq Var] [HasFresh Var] in
/-- Strong normalization lifts through a right injection. -/
lemma sn_inr {t : Term Var} (h : SN Term.Red t) : SN Term.Red (Term.inr t) := by
  induction h with
  | intro _ _ ih =>
    refine SN.intro fun u hu => ?_
    cases hu with
    | inr r => exact ih _ r

omit [DecidableEq Var] [HasFresh Var] in
/-- A value admits no reduction. -/
lemma value_no_red {t t' : Term Var} (v : t.Value) (r : t ⭢βᵛ t') : False := by
  induction v generalizing t' with
  | abs => cases r
  | tabs => cases r
  | inl _ ih => cases r with | inl r => exact ih r
  | inr _ ih => cases r with | inr r => exact ih r

omit [DecidableEq Var] [HasFresh Var] in
/-- A value is irreducible, hence strongly normalizing. -/
lemma sn_value {t : Term Var} (val : t.Value) : SN Term.Red t := by
  induction val with
  | abs _ => exact SN.intro nofun
  | tabs _ => exact SN.intro nofun
  | inl _ ih => exact sn_inl ih
  | inr _ ih => exact sn_inr ih

/-- A call-by-value neutral term: locally closed, not a value, and stuck at the head. -/
inductive Neutral : Term Var → Prop
  | fvar (x : Var) : Neutral (Term.fvar x)
  | app {t₁ t₂ : Term Var} : Neutral t₁ → SN Term.Red t₂ → t₂.LC → Neutral (Term.app t₁ t₂)
  | tapp {t₁ : Term Var} {σ : Ty Var} : Neutral t₁ → σ.LC → Neutral (Term.tapp t₁ σ)
  | let' {t₁ t₂ : Term Var} : Neutral t₁ → t₂.body → Neutral (Term.let' t₁ t₂)
  | case {t₁ t₂ t₃ : Term Var} : Neutral t₁ → t₂.body → t₃.body → Neutral (Term.case t₁ t₂ t₃)

omit [HasFresh Var] in
/-- Neutral terms are locally closed. -/
lemma Neutral.lc {t : Term Var} (h : Neutral t) : t.LC := by
  induction h with
  | fvar x => exact .var
  | app _ _ hlc ih => exact ih.app hlc
  | tapp _ hσ ih => exact ih.tapp hσ
  | let' _ hbody ih => have ⟨L, hL⟩ := hbody; exact ih.let' L hL
  | case _ hb2 hb3 ih =>
      have ⟨L2, hL2⟩ := hb2
      have ⟨L3, hL3⟩ := hb3
      exact ih.case (L2 ∪ L3) (fun x hx => hL2 x (by grind)) (fun x hx => hL3 x (by grind))

omit [DecidableEq Var] [HasFresh Var] in
/-- A neutral term is not a value. -/
lemma Neutral.not_value {t : Term Var} (h : Neutral t) (v : t.Value) : False := by
  cases h <;> cases v

/-- Neutral terms are preserved by reduction. -/
lemma Neutral.step {t t' : Term Var} (h : Neutral t) (r : t ⭢βᵛ t') : Neutral t' := by
  induction h generalizing t' with
  | fvar x => cases r
  | app hn hsn hlc ih =>
    cases r with
    | appₗ _ r₁ => exact .app (ih r₁) hsn hlc
    | appᵣ _ r₂ => exact .app hn (hsn.of_rel r₂) r₂.lc.right
    | abs => cases hn
  | tapp hn hσ ih =>
    cases r with
    | tapp _ r₁ => exact .tapp (ih r₁) hσ
    | tabs => cases hn
  | let' hn hbody ih =>
    cases r with
    | let_bind r₁ _ => exact .let' (ih r₁) hbody
    | let_body v _ => exact (hn.not_value v).elim
  | case hn hb₂ hb₃ ih =>
    cases r with
    | case r₁ _ _ => exact .case (ih r₁) hb₂ hb₃
    | case_inl => cases hn
    | case_inr => cases hn

/-- Neutral terms are strongly normalizing: the head reduces only at the head, and the
value-headed reduction of each frame is impossible since the head is neutral. -/
lemma sn_neutral {t : Term Var} (h : Neutral t) : SN Term.Red t := by
  induction h with
  | fvar _ => exact SN.intro nofun
  | app hn _ _ ih =>
    induction ih with
    | intro _ _ ih =>
      refine SN.intro fun u hu => ?_
      cases hu with
      | appₗ _ r₁ => exact ih _ r₁ (hn.step r₁)
      | appᵣ hv _ => cases hn <;> cases hv
      | abs hv _ => cases hn
  | tapp hn _ ih =>
    induction ih with
    | intro _ _ ih =>
      refine SN.intro fun u hu => ?_
      cases hu with
      | tapp _ r₁ => exact ih _ r₁ (hn.step r₁)
      | tabs hv _ => cases hn
  | let' hn _ ih =>
    induction ih with
    | intro _ _ ih =>
      refine SN.intro fun u hu => ?_
      cases hu with
      | let_bind r₁ _ => exact ih _ r₁ (hn.step r₁)
      | let_body hv _ => cases hn <;> cases hv
  | case hn _ _ ih =>
    induction ih with
    | intro _ _ ih =>
      refine SN.intro fun u hu => ?_
      cases hu with
      | case r₁ _ _ => exact ih _ r₁ (hn.step r₁)
      | case_inl hv _ _ => cases hn
      | case_inr hv _ _ => cases hn

/-- A reducibility candidate, adapted to call-by-value reduction. -/
@[scoped grind]
structure Cand (S : Set (Term Var)) : Prop where
  lc {t} : t ∈ S → t.LC
  sn {t} : t ∈ S → SN Term.Red t
  fwd {t t'} : t ∈ S → t ⭢βᵛ t' → t' ∈ S
  neutral {t} : t.LC → Neutral t → t ∈ S
  expand {t} : t.LC → ¬ t.Value → (∀ t', t ⭢βᵛ t' → t' ∈ S) → t ∈ S

/-- The maximal candidate: every locally closed strongly normalizing term. -/
def maximalSet : Set (Term Var) := { t | t.LC ∧ SN Term.Red t }

/-- The maximal set is a candidate. -/
lemma maximalCand : Cand (maximalSet (Var := Var)) := by
  refine ⟨fun ⟨h, _⟩ => h, fun ⟨_, h⟩ => h, ?_, ?_, ?_⟩
  · intro t t' ⟨hlc, hsn⟩ hr
    exact ⟨hr.lc.right, hsn.of_rel hr⟩
  · exact fun hlc hn => ⟨hlc, sn_neutral hn⟩
  · intro t hlc _ hred
    exact ⟨hlc, SN.intro fun u hu => (hred u hu).right⟩

/-- A candidate environment: a candidate per bound (de Bruijn) and per free type variable. -/
structure SemEnv (Var : Type u) where
  /-- A candidate for each bound (de Bruijn) type variable, innermost first. -/
  bound : List (Set (Term Var))
  /-- A candidate for each free type variable. -/
  free : Var → Set (Term Var)

/-- A candidate environment is valid when every assigned set is a reducibility candidate. -/
structure SemEnv.IsValid (ρ : SemEnv Var) : Prop where
  /-- Every free-variable assignment is a candidate. -/
  free_rc : ∀ X, Cand (ρ.free X)
  /-- Every bound-variable assignment is a candidate. -/
  bound_rc : ∀ S ∈ ρ.bound, Cand S

omit [DecidableEq Var] [HasFresh Var] in
/-- Pushing a candidate onto the bound list preserves validity. -/
lemma SemEnv.IsValid.extend_bound {ρ : SemEnv Var} {S : Set (Term Var)}
    (hρ : ρ.IsValid) (hS : Cand S) : { ρ with bound := S :: ρ.bound }.IsValid where
  free_rc := hρ.free_rc
  bound_rc := by
    intro S' hS'
    rcases List.mem_cons.mp hS' with h | h
    · exact h ▸ hS
    · exact hρ.bound_rc S' h

/-- The interpretation of a sum type, as the least candidate containing the injections. -/
inductive SumInterp (A B : Set (Term Var)) : Term Var → Prop
  | inl {s : Term Var} : s ∈ A → SumInterp A B (Term.inl s)
  | inr {s : Term Var} : s ∈ B → SumInterp A B (Term.inr s)
  | neutral {t : Term Var} : t.LC → Neutral t → SumInterp A B t
  | fwd {t t' : Term Var} : SumInterp A B t → t ⭢βᵛ t' → SumInterp A B t'
  | expand {t : Term Var} : t.LC → ¬t.Value → (∀ t', t ⭢βᵛ t' → SumInterp A B t') →
      SumInterp A B t

/-- The Girard interpretation of a type as a reducibility candidate over a candidate environment. -/
def interp (ρ : SemEnv Var) : Ty Var → Set (Term Var)
  | .top => maximalSet
  | .bvar i => ρ.bound[i]?.getD maximalSet
  | .fvar X => ρ.free X
  | .arrow σ τ =>
      { t | t.LC ∧ SN Term.Red t ∧ ∀ s, s ∈ interp ρ σ → Term.app t s ∈ interp ρ τ }
  | .sum σ τ => SumInterp (interp ρ σ) (interp ρ τ)
  | .all σ τ =>
      { t | t.LC ∧ SN Term.Red t ∧
          ∀ S : Set (Term Var), Cand S → (∀ s ∈ S, s ∈ interp ρ σ) → ∀ U : Ty Var, U.LC →
            Term.tapp t U ∈ interp { ρ with bound := S :: ρ.bound } τ }

/-- Every interpretation is a reducibility candidate, by structural induction on the type. -/
lemma interp_cand {ρ : SemEnv Var} (τ : Ty Var) (hρ : ρ.IsValid) : Cand (interp ρ τ) := by
  induction τ generalizing ρ with
  | top => rw [interp]; exact maximalCand
  | bvar i =>
    rw [interp]
    cases h : ρ.bound[i]? with
    | none => simpa only [Option.getD_none] using maximalCand
    | some S => simpa only [Option.getD_some] using hρ.bound_rc S (List.mem_of_getElem? h)
  | fvar X => rw [interp]; exact hρ.free_rc X
  | arrow σ τ ihσ ihτ =>
    have candσ : Cand (interp ρ σ) := ihσ hρ
    have candτ : Cand (interp ρ τ) := ihτ hρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ⟨lc, _⟩
      exact lc
    · intro t ⟨_, sn, _⟩
      exact sn
    · intro t t' ⟨_, sn, hbody⟩ r
      refine ⟨r.lc.right, sn.of_rel r, ?_⟩
      intro s hs
      exact candτ.fwd (hbody s hs) (r.appₗ (candσ.lc hs))
    · intro t lc neu
      refine ⟨lc, sn_neutral neu, ?_⟩
      intro s hs
      exact candτ.neutral (lc.app (candσ.lc hs))
        (Neutral.app neu (candσ.sn hs) (candσ.lc hs))
    · intro t lc hnv hred
      have hsn : SN Term.Red t := SN.intro fun u hu => have ⟨_, sn, _⟩ := hred u hu; sn
      refine ⟨lc, hsn, ?_⟩
      intro s hs
      refine candτ.expand (lc.app (candσ.lc hs)) nofun ?_
      intro u hu
      cases hu with
      | appₗ _ r₁ => have ⟨_, _, hbody⟩ := hred _ r₁; exact hbody s hs
      | appᵣ hv _ => exact (hnv hv).elim
      | abs hab _ => exact (hnv (.abs hab)).elim
  | sum σ τ ihσ ihτ =>
    have candσ : Cand (interp ρ σ) := ihσ hρ
    have candτ : Cand (interp ρ τ) := ihτ hρ
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ht
      induction ht with
      | inl hs => exact (candσ.lc hs).inl
      | inr hs => exact (candτ.lc hs).inr
      | neutral lc _ => exact lc
      | fwd _ r ih => exact r.lc.right
      | expand lc hnv hred => exact lc
    · intro t ht
      induction ht with
      | inl hs => exact sn_inl (candσ.sn hs)
      | inr hs => exact sn_inr (candτ.sn hs)
      | neutral _ neu => exact sn_neutral neu
      | fwd hh r ih => exact ih.of_rel r
      | expand lc hnv hred ih => exact SN.intro fun u hu => ih u hu
    · intro t t'; exact SumInterp.fwd
    · intro t; exact SumInterp.neutral
    · intro t; exact SumInterp.expand
  | all σ τ ihσ ihτ =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro t ⟨lc, _⟩
      exact lc
    · intro t ⟨_, sn, _⟩
      exact sn
    · intro t t' ⟨_, sn, hbody⟩ r
      refine ⟨r.lc.right, sn.of_rel r, ?_⟩
      intro S candS hsub U hU
      exact (ihτ (hρ.extend_bound candS)).fwd (hbody S candS hsub U hU) (r.tapp hU)
    · intro t lc neu
      refine ⟨lc, sn_neutral neu, ?_⟩
      intro S candS hsub U hU
      exact (ihτ (hρ.extend_bound candS)).neutral (lc.tapp hU) (Neutral.tapp neu hU)
    · intro t lc hnv hred
      have hsn : SN Term.Red t := SN.intro fun u hu => have ⟨_, sn, _⟩ := hred u hu; sn
      refine ⟨lc, hsn, ?_⟩
      intro S candS hsub U hU
      refine (ihτ (hρ.extend_bound candS)).expand (lc.tapp hU) nofun ?_
      intro u hu
      cases hu with
      | tapp _ r₁ => have ⟨_, _, hbody⟩ := hred _ r₁; exact hbody S candS hsub U hU
      | tabs hab _ => exact (hnv (.tabs hab)).elim

/-- Members of an interpretation are locally closed. -/
lemma interp_lc {ρ : SemEnv Var} {τ : Ty Var} {t : Term Var}
    (hρ : ρ.IsValid) (mem : t ∈ interp ρ τ) : t.LC :=
  (interp_cand τ hρ).lc mem

/-- Members of an interpretation are strongly normalizing. -/
lemma interp_sn {ρ : SemEnv Var} {τ : Ty Var} {t : Term Var}
    (hρ : ρ.IsValid) (mem : t ∈ interp ρ τ) : SN Term.Red t :=
  (interp_cand τ hρ).sn mem

omit [HasFresh Var] in
/-- Updating the free assignment at a variable absent from a type's free variables is inert. -/
lemma interp_free_update_nmem {ρ : SemEnv Var} {τ : Ty Var} {X : Var} {C : Set (Term Var)}
    (nmem : X ∉ τ.fv) :
    interp { ρ with free := Function.update ρ.free X C } τ = interp ρ τ := by
  induction τ generalizing ρ with
  | top => rw [interp, interp]
  | bvar i => rw [interp, interp]
  | fvar Y =>
    exact Function.update_of_ne (a := Y) (a' := X) (by grind) C ρ.free
  | arrow σ τ ihσ ihτ =>
    rw [interp, interp, ihσ (by grind), ihτ (by grind)]
  | sum σ τ ihσ ihτ =>
    rw [interp, interp, ihσ (by grind), ihτ (by grind)]
  | all σ τ ihσ ihτ =>
    rw [interp, interp]
    have hσ := ihσ (ρ := ρ) (by grind)
    have key : ∀ S : Set (Term Var),
        interp { ρ with bound := S :: ρ.bound, free := Function.update ρ.free X C } τ
          = interp { ρ with bound := S :: ρ.bound } τ :=
      fun S => ihτ (ρ := { ρ with bound := S :: ρ.bound }) (by grind)
    simp only [hσ, key]

end LambdaCalculus.LocallyNameless.Fsub

end Cslib
