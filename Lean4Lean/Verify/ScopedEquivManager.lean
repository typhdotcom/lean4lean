import Lean4Lean.ScopedEquivManager

/-!
# The scoped union-find is sound for any leveled equivalence

`ScopedEquivManager` answers queries by following links whose scope is open. Whatever a link of
level `l` asserts, as a relation `R l` on nodes that is an equivalence and grows with the level, a
query answers only what the current links prove. Termination of the walks is by fuel, so nothing
here depends on the links being acyclic.
-/

namespace Lean4Lean.ScopedEquivManager
open Lean

/-- A relation on nodes at each level, closed under the steps a union-find takes. -/
structure LRel (R : Nat → Nat → Nat → Prop) : Prop where
  refl : R 0 a a
  symm : R l a b → R l b a
  trans : R l₁ a b → R l₂ b c → R (max l₁ l₂) a c
  mono : l₁ ≤ l₂ → R l₁ a b → R l₂ a b

/-- Every current link asserts its relation at its level. -/
def WF (m : ScopedEquivManager) (ids : Scopes) (R : Nat → Nat → Nat → Prop) : Prop :=
  ∀ n p, m.parent[n]? = some p → p ≠ n → m.linkOK ids n = true → R (m.lvl[n]?.getD 0) n p

variable {m : ScopedEquivManager} {ids : Scopes} {R : Nat → Nat → Nat → Prop}

theorem rootL.go_spec (hR : LRel R) (wf : m.WF ids R) :
    ∀ k n l l₀, R l₀ n₀ n → l₀ ≤ l → rootL.go m ids k n l = (r, l') → R l' n₀ r ∧ l ≤ l'
  | 0, n, l, l₀, h, hl, e => by cases e; exact ⟨hR.mono hl h, Nat.le_refl _⟩
  | k+1, n, l, l₀, h, hl, e => by
    simp only [rootL.go] at e
    split at e
    · cases e; exact ⟨hR.mono hl h, Nat.le_refl _⟩
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_false] at hc
      have hp : m.parent[n]? = some (m.parent[n]?.getD n) := by
        cases h' : m.parent[n]? with
        | none => simp [h'] at hc
        | some p => rfl
      have hl' := wf n _ hp hc.1 hc.2
      have := hR.trans h hl'
      obtain ⟨h1, h2⟩ := rootL.go_spec hR wf k _ _ _ this
        (by omega) e
      exact ⟨h1, Nat.le_trans (Nat.le_max_left _ _) h2⟩

theorem rootL_spec (hR : LRel R) (wf : m.WF ids R) (e : m.rootL ids n = (r, l)) : R l n r :=
  (rootL.go_spec hR wf _ n 0 0 hR.refl (Nat.le_refl _) e).1

/-- A connection the union-find reports is in the relation, at the level it reports. -/
theorem connLevel_spec (hR : LRel R) (wf : m.WF ids R) (e : m.connLevel ids n1 n2 = some l) :
    R l n1 n2 := by
  unfold connLevel at e
  split at e
  · rename_i h; cases e; simp only [beq_iff_eq] at h; subst h; exact hR.refl
  · generalize e1 : m.rootL ids n1 = p1 at e
    generalize e2 : m.rootL ids n2 = p2 at e
    obtain ⟨r1, l1⟩ := p1; obtain ⟨r2, l2⟩ := p2
    simp only at e
    split at e <;> cases e
    rename_i h; simp only [beq_iff_eq] at h; subst h
    exact hR.trans (rootL_spec hR wf e1) (hR.symm (rootL_spec hR wf e2))

theorem toNode_parent (e : Expr) :
    ((toNode e).run m).2.parent = m.parent ∨
      (((toNode e).run m).2.parent = m.parent.push m.parent.size ∧
       ((toNode e).run m).2.lvl = m.lvl.push 0 ∧ ((toNode e).run m).2.sid = m.sid.push 0) := by
  simp only [toNode, StateT.run]
  split
  · exact .inl rfl
  · exact .inr ⟨rfl, rfl, rfl⟩

theorem toNode_WF (e : Expr) (wf : m.WF ids R) (hl : m.lvl.size = m.parent.size)
    (hs : m.sid.size = m.parent.size) : ((toNode e).run m).2.WF ids R := by
  intro n p hp hne hok
  cases h : m.toNodeMap[e]? with
  | some r =>
    simp only [toNode, StateT.run, h] at hp hok ⊢
    exact wf n p hp hne hok
  | none =>
    simp only [toNode, StateT.run, h, linkOK] at hp hok ⊢
    rw [Array.getElem?_push] at hp
    split at hp
    · cases hp; subst_vars; exact absurd rfl hne
    · have hlt : n < m.parent.size := (Array.getElem?_eq_some_iff.1 hp).1
      have h1 : (m.lvl.push 0)[n]? = m.lvl[n]? := by
        rw [Array.getElem?_push]; split
        · omega
        · rfl
      have h2 : (m.sid.push 0)[n]? = m.sid[n]? := by
        rw [Array.getElem?_push]; split
        · omega
        · rfl
      simp only [h1, h2] at hok ⊢
      exact wf n p hp hne hok

/-- The arrays have one entry per node. -/
structure Sized (m : ScopedEquivManager) : Prop where
  lvl : m.lvl.size = m.parent.size
  sid : m.sid.size = m.parent.size

theorem toNode_sized (e : Expr) (h : m.Sized) : ((toNode e).run m).2.Sized := by
  simp only [toNode, StateT.run]
  split
  · exact h
  · exact ⟨by simp [h.lvl], by simp [h.sid]⟩

theorem link_sized (h : m.Sized) : (m.link ids a b l).Sized :=
  ⟨by simp [link, h.lvl], by simp [link, h.sid]⟩

theorem link_WF (wf : m.WF ids R) (sz : m.Sized) (hR : R l a b) (h : a < m.parent.size) :
    (m.link ids a b l).WF ids R := by
  intro n p hp hne hok
  have hl : a < m.lvl.size := sz.lvl ▸ h
  have hs : a < m.sid.size := sz.sid ▸ h
  simp only [link, linkOK, Array.set!] at hp hok ⊢
  by_cases e : n = a
  · subst e
    rw [Array.getElem?_setIfInBounds_self_of_lt h] at hp
    rw [Array.getElem?_setIfInBounds_self_of_lt hl] at hok ⊢
    cases hp; exact hR
  · rw [Array.getElem?_setIfInBounds_ne (Ne.symm e)] at hp
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm e)] at hok ⊢
    rw [Array.getElem?_setIfInBounds_ne (Ne.symm e)] at hok
    exact wf n p hp hne hok

theorem merge_sized (h : m.Sized) : (m.merge ids n1 n2 l).Sized := by
  unfold merge
  dsimp only
  split
  · exact h
  · split
    · exact link_sized h
    · split
      · exact link_sized h
      · exact ⟨by simp [link, h.lvl], by simp [link, h.sid]⟩

/-- Recording an equivalence that holds keeps the union-find sound. -/
theorem merge_WF (hR : LRel R) (wf : m.WF ids R) (sz : m.Sized) (h : R l n1 n2) :
    (m.merge ids n1 n2 l).WF ids R := by
  unfold merge
  generalize e1 : m.rootL ids n1 = p1
  generalize e2 : m.rootL ids n2 = p2
  obtain ⟨r1, l1⟩ := p1; obtain ⟨r2, l2⟩ := p2
  have h1 := rootL_spec hR wf e1
  have h2 := rootL_spec hR wf e2
  -- the roots are related at the link's level
  have h12 : R (max l (max l1 l2)) r1 r2 := by
    have := hR.trans (hR.trans (hR.symm h1) h) h2
    exact hR.mono (by omega) this
  dsimp only
  split
  · exact wf
  · rename_i hc
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hc
    obtain ⟨⟨-, hr1⟩, hr2⟩ := hc
    split
    · exact link_WF wf sz h12 hr1
    · split
      · exact link_WF wf sz (hR.symm h12) hr2
      · intro n p hp hne hok
        exact link_WF wf sz h12 hr1 n p hp hne hok

/-- A union-find sound for one stack of scopes and relation is sound for another, when every link
current in the second was current in the first and asserts the second relation too. Opening a
scope with a fresh id, and closing one, are such changes. -/
theorem WF.mono {ids' : Scopes} {R' : Nat → Nat → Nat → Prop} (wf : m.WF ids R)
    (H : ∀ n p, m.linkOK ids' n = true → m.linkOK ids n = true ∧
      (R (m.lvl[n]?.getD 0) n p → R' (m.lvl[n]?.getD 0) n p)) :
    m.WF ids' R' := fun n p hp hne hok =>
  let ⟨h1, h2⟩ := H n p hok; h2 (wf n p hp hne h1)

theorem Scopes.valid_pop {ids : Scopes} {l i : Nat} (h : Scopes.valid ids.pop l i = true) :
    ids.valid l i = true := by
  simp only [Scopes.valid, Bool.or_eq_true, beq_iff_eq] at h ⊢
  refine h.imp_right fun h => ?_
  rw [Array.getElem?_pop] at h
  split at h
  · exact h
  · cases h

theorem Scopes.labelId_of_valid {ids : Scopes} {l i : Nat} (h : ids.valid l i = true)
    (hl : l ≠ 0) : ids.labelId l = i := by
  simp only [Scopes.valid, Bool.or_eq_true, beq_iff_eq] at h
  simp only [Scopes.labelId, beq_iff_eq, hl, ↓reduceIte]
  rcases h with h | h
  · exact absurd h hl
  · simp [h]

end Lean4Lean.ScopedEquivManager
