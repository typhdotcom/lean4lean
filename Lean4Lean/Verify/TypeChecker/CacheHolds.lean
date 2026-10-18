import Lean4Lean.Verify.TypeChecker.Learned

/-!
# Cached facts at their levels

A cache entry records its result with the level of the facts it rests on and the id of that
level's scope. While that scope is open, the entry asserts its fact at its level (`Holds`): in
every context extending the level's context that admits the context it was learned in. These are
the invariants the caches keep when a scope's end no longer discards what was learned in it.
-/

namespace Lean4Lean.TypeChecker
open Lean hiding Environment Exception
open Kernel

variable {κ ν : Type} [BEq κ] [Hashable κ]

/-- Every current entry of `cache`, labelled by `lab`, holds as `P` says, at its level. -/
def LabHolds (c : VContext) (s : State) (cache : Std.HashMap κ ν) (lab : ν → Nat × Nat)
    (P : κ → ν → MLCtx → Prop) : Prop :=
  ∀ ⦃k : κ⦄ ⦃v : ν⦄, cache[k]? = some v → Scopes.valid s.scopeIds (lab v).1 (lab v).2 = true →
    Holds c s.scopeFV c.top s.ngen (lab v).1 (P k v)

/-- Every entry of `cache` records the id of a scope the name generator had made, or `0`. -/
def LabIds (s : State) (cache : Std.HashMap κ ν) (lab : ν → Nat × Nat) : Prop :=
  ∀ ⦃k : κ⦄ ⦃v : ν⦄, cache[k]? = some v → (lab v).2 ≤ s.ngen.idx

theorem LabHolds.empty {c : VContext} {s : State} {lab : ν → Nat × Nat} {P} :
    LabHolds c s ({} : Std.HashMap κ ν) lab P := fun _ _ h => by simp at h

theorem LabIds.empty {s : State} {lab : ν → Nat × Nat} :
    LabIds s ({} : Std.HashMap κ ν) lab := fun _ _ h => by simp at h

/-- A current entry's fact holds in the context it is looked up in, if the ceiling keeps it. -/
theorem LabHolds.now {c : VContext} {s : State} {cache : Std.HashMap κ ν} {lab P} {k : κ} {v : ν}
    (H : LabHolds c s cache lab P) (hS : ScopeShape c.mlctx s.scopeFV c.ceiling c.top)
    (hm : cache[k]? = some v) (hv : Scopes.valid s.scopeIds (lab v).1 (lab v).2 = true)
    (hc : c.ceiling.all ((lab v).1 ≤ ·)) : P k v c.mlctx :=
  (H hm hv).now hS hc

/-- A run that made none of the context's variables keeps what the caches assert. -/
theorem LabHolds.mono {c : VContext} {s s' : State} {cache : Std.HashMap κ ν} {lab P}
    (H : LabHolds c s cache lab P) (hids : s'.scopeIds = s.scopeIds) (hfv : s'.scopeFV = s.scopeFV)
    (hg : s.ngen ≤ s'.ngen) (hk : Keeps c.lctx s.ngen s'.ngen) : LabHolds c s' cache lab P := by
  intro k v hm hv
  rw [hids] at hv; rw [hfv]
  exact (H hm hv).mono hg hk

theorem LabIds.mono {s s' : State} {cache : Std.HashMap κ ν} {lab : ν → Nat × Nat}
    (H : LabIds s cache lab) (hg : s.ngen ≤ s'.ngen) : LabIds s' cache lab :=
  fun _ _ hm => Nat.le_trans (H hm) hg.idx_le

/-- Inserting an entry whose fact holds keeps what the cache asserts. -/
theorem LabHolds.insert [EquivBEq κ] [LawfulHashable κ] {c : VContext} {s : State}
    {cache : Std.HashMap κ ν} {lab P} {k : κ} {v : ν}
    (H : LabHolds c s cache lab P)
    (hv : ∀ k', (k == k') = true → Scopes.valid s.scopeIds (lab v).1 (lab v).2 = true →
      Holds c s.scopeFV c.top s.ngen (lab v).1 (P k' v)) :
    LabHolds c s (cache.insert k v) lab P := by
  intro k' v' hm hval
  rw [Std.HashMap.getElem?_insert] at hm
  split at hm
  · rename_i e; cases hm; exact hv k' e hval
  · exact H hm hval

theorem LabIds.insert [EquivBEq κ] [LawfulHashable κ] {s : State} {cache : Std.HashMap κ ν} {lab : ν → Nat × Nat} {k : κ} {v : ν}
    (H : LabIds s cache lab) (hv : (lab v).2 ≤ s.ngen.idx) : LabIds s (cache.insert k v) lab := by
  intro k' v' hm
  rw [Std.HashMap.getElem?_insert] at hm
  split at hm
  · cases hm; exact hv
  · exact H hm

/-- A label current after a scope is opened, with an id the name generator had made before, was
current before. -/
theorem valid_push_of_lt {ids : Scopes} {x l id : Nat} (hid : id < x)
    (h : Scopes.valid (ids.push x) l id = true) : Scopes.valid ids l id = true := by
  simp only [Scopes.valid_def, Bool.or_eq_true, beq_iff_eq] at h ⊢
  refine h.imp_right fun h => ?_
  rw [Array.getElem?_push] at h
  split at h
  · cases h; omega
  · exact h

/-- A label current with the scopes `ids` is current with more scopes opened. -/
theorem valid_push_of_valid {ids : Scopes} {x l id : Nat}
    (h : Scopes.valid ids l id = true) : Scopes.valid (ids.push x) l id = true := by
  simp only [Scopes.valid_def, Bool.or_eq_true, beq_iff_eq] at h ⊢
  refine h.imp_right fun h => ?_
  have hl := (Array.getElem?_eq_some_iff.1 h).1
  rw [Array.getElem?_push_lt hl, ← Array.getElem?_eq_getElem hl]; exact h

/-- A current label is at most the number of open scopes. -/
theorem le_of_valid {ids : Scopes} {l id : Nat} (h : Scopes.valid ids l id = true) :
    l ≤ ids.size := by
  simp only [Scopes.valid_def, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · omega
  · have := (Array.getElem?_eq_some_iff.1 h).1; omega

/-- Opening the scope of a fresh variable keeps what the caches assert. -/
theorem LabHolds.enter {c c' : VContext} {s : State} {cache : Std.HashMap κ ν} {lab P}
    (H : LabHolds c s cache lab P) (hI : LabIds s cache lab)
    (hS : ScopeShape c.mlctx s.scopeFV c.ceiling c.top)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under ⟨s.ngen.curr⟩ = c.mlctx)
    (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (ht : c'.top = c.top)
    (hnew : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → fv = ⟨s.ngen.curr⟩)
    (hfresh : c.lctx.find? ⟨s.ngen.curr⟩ = none) :
    LabHolds c' s.enter cache lab P := by
  intro k v hm hvalid
  have hv0 : Scopes.valid s.scopeIds (lab v).1 (lab v).2 = true :=
    valid_push_of_lt (Nat.lt_succ_of_le (hI hm)) hvalid
  have := (H hm hv0).push hS hb hx hv hl hc (fun fv a b => by
      rw [hnew fv a b]; exact s.ngen.not_reserves_self) NameGenerator.LE.next
    (Keeps.next hfresh)
  rw [ht]; exact this

/-- Opening a scope keeps the entries' ids made. -/
theorem LabIds.enter {s : State} {cache : Std.HashMap κ ν} {lab : ν → Nat × Nat}
    (H : LabIds s cache lab) : LabIds s.enter cache lab :=
  H.mono NameGenerator.LE.next

/-- Closing a scope keeps what the caches assert at the levels still open. -/
theorem LabHolds.exit {c c' : VContext} {s₀ s₁ : State} {x : FVarId}
    {cache : Std.HashMap κ ν} {lab P}
    (H : LabHolds c' s₁ cache lab P) (hS : ScopeShape c.mlctx s₀.scopeFV c.ceiling c.top)
    (hfv : s₁.scopeFV = s₀.scopeFV.push x) (hids : ∃ i, s₁.scopeIds = s₀.scopeIds.push i)
    (hsz : s₀.scopeFV.size = s₀.scopeIds.size)
    (hb : c.mlctx.Below c'.mlctx) (hx : c'.mlctx.under x = c.mlctx)
    (hv : c'.venv = c.venv) (hl : c'.lparams = c.lparams) (hc : c'.ceiling = c.ceiling)
    (ht : c'.top = c.top)
    (hmade : ∀ fv ∈ c'.vlctx.fvars, fv ∉ c.vlctx.fvars → s₁.ngen.Reserves fv) :
    LabHolds c (s₀.popScope s₁) cache lab P := by
  intro k v hm hvalid
  obtain ⟨i, hi⟩ := hids
  have hvalid' : Scopes.valid s₁.scopeIds (lab v).1 (lab v).2 = true :=
    hi ▸ valid_push_of_valid hvalid
  have hle : (lab v).1 ≤ s₀.scopeFV.size := hsz ▸ le_of_valid hvalid
  have H' := H hm hvalid'
  rw [hfv] at H'
  rw [← ht] at hS
  have R := H'.pop hS hle hb hx hv hl hc hmade
  rw [ht] at R; exact R

/-- What the caches assert carries over to a context a computation is run again in: one extending
the level-`lab₀` context, admitting `c` with the name generator past the computation, and setting
aside the levels above `lab₀` among the open ones. -/
theorem LabHolds.transfer {c c₂ : VContext} {s : State} {g : NameGenerator} {lab₀ : Nat}
    {cache : Std.HashMap κ ν} {lab P}
    (H : LabHolds c s cache lab P) (hS : ScopeShape c.mlctx s.scopeFV c.ceiling c.top)
    (hvis : c.ceiling.all (lab₀ ≤ ·))
    (hv : c₂.venv = c.venv) (hlp : c₂.lparams = c.lparams)
    (hb : (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab₀).Below c₂.mlctx)
    (htop : (levelCtx c.mlctx s.scopeFV c.ceiling c.top lab₀).Below
      (levelCtx c₂.mlctx s.scopeFV c₂.ceiling c₂.top lab₀))
    (hvis₂ : ∀ l, l < lab₀ → c₂.ceiling.all (l < ·))
    (hcut : ∀ l, l ≤ s.scopeIds.size → lab₀ < l → c₂.ceiling.all (l ≤ ·) = false)
    (ha : Admits c.lctx g c₂.lctx) (hg : s.ngen ≤ g) (hk : Keeps c.lctx s.ngen g) :
    LabHolds c₂ s cache lab P := by
  intro k v hm hvalid
  rcases Nat.lt_or_ge lab₀ (lab v).1 with hl | hl
  · intro hc; rw [hcut _ (le_of_valid hvalid) hl] at hc; cases hc
  · exact (H hm hvalid).transfer hS hl hvis hv hlp hb htop hvis₂ ha hg hk

end Lean4Lean.TypeChecker
