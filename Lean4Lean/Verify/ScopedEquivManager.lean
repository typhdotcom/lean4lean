import Lean4Lean.ScopedEquivManager
import Std.Data.HashMap.Lemmas
import Lean4Lean.Verify.Expr

/-!
# The scoped union-find is sound for any leveled equivalence

`ScopedEquivManager` answers queries by following links whose scope is open. Whatever a link of
level `l` asserts, as a relation `R l` on nodes that is an equivalence and grows with the level, a
query answers only what the current links prove. Termination of the walks is by fuel, so nothing
here depends on the links being acyclic.
-/

namespace Lean4Lean.ScopedEquivManager
open Lean

/-- A relation on the nodes `D` at each level, closed under the steps a union-find takes. -/
structure LRel (D : Nat → Prop) (R : Nat → Nat → Nat → Prop) : Prop where
  refl : D a → R 0 a a
  symm : R l a b → R l b a
  trans : D b → R l₁ a b → R l₂ b c → R (max l₁ l₂) a c
  mono : l₁ ≤ l₂ → R l₁ a b → R l₂ a b

/-- Every current link asserts its relation at its level. -/
def WF (m : ScopedEquivManager) (ids : Scopes) (R : Nat → Nat → Nat → Prop) : Prop :=
  ∀ n p, m.parent[n]? = some p → p ≠ n → m.linkOK ids n = true → R (m.lvl[n]?.getD 0) n p

/-- Links lead from nodes of `D` to nodes of `D`. -/
def Closed (m : ScopedEquivManager) (D : Nat → Prop) : Prop :=
  ∀ n p, m.parent[n]? = some p → D n → D p

variable {m : ScopedEquivManager} {ids : Scopes} {R : Nat → Nat → Nat → Prop} {D : Nat → Prop}

theorem rootL.go_spec (hR : LRel D R) (wf : m.WF ids R) (hD : m.Closed D) :
    ∀ k n l l₀, D n → R l₀ n₀ n → l₀ ≤ l → rootL.go m ids k n l = (r, l') →
      D r ∧ R l' n₀ r ∧ l ≤ l'
  | 0, n, l, l₀, hn, h, hl, e => by cases e; exact ⟨hn, hR.mono hl h, Nat.le_refl _⟩
  | k+1, n, l, l₀, hn, h, hl, e => by
    simp only [rootL.go] at e
    split at e
    · cases e; exact ⟨hn, hR.mono hl h, Nat.le_refl _⟩
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', not_or,
        Bool.not_eq_false] at hc
      have hp : m.parent[n]? = some (m.parent[n]?.getD n) := by
        cases h' : m.parent[n]? with
        | none => simp [h'] at hc
        | some p => rfl
      have hl' := wf n _ hp hc.1 hc.2
      have := hR.trans hn h hl'
      obtain ⟨h0, h1, h2⟩ := rootL.go_spec hR wf hD k _ _ _ (hD _ _ hp hn) this
        (by omega) e
      exact ⟨h0, h1, Nat.le_trans (Nat.le_max_left _ _) h2⟩

theorem rootL_spec (hR : LRel D R) (wf : m.WF ids R) (hD : m.Closed D) (hn : D n)
    (e : m.rootL ids n = (r, l)) : D r ∧ R l n r :=
  let ⟨h0, h1, _⟩ := rootL.go_spec hR wf hD _ n 0 0 hn (hR.refl hn) (Nat.le_refl _) e; ⟨h0, h1⟩

/-- A connection the union-find reports is in the relation, at the level it reports. -/
theorem connLevel_spec (hR : LRel D R) (wf : m.WF ids R) (hD : m.Closed D) (h1 : D n1)
    (h2 : D n2) (e : m.connLevel ids n1 n2 = some l) : R l n1 n2 := by
  unfold connLevel at e
  split at e
  · rename_i h; cases e; simp only [beq_iff_eq] at h; subst h; exact hR.refl h1
  · generalize e1 : m.rootL ids n1 = p1 at e
    generalize e2 : m.rootL ids n2 = p2 at e
    obtain ⟨r1, l1⟩ := p1; obtain ⟨r2, l2⟩ := p2
    simp only at e
    split at e <;> cases e
    rename_i h; simp only [beq_iff_eq] at h; subst h
    have ⟨d1, r1⟩ := rootL_spec hR wf hD h1 e1
    exact hR.trans d1 r1 (hR.symm (rootL_spec hR wf hD h2 e2).2)

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
theorem merge_WF (hR : LRel D R) (wf : m.WF ids R) (hD : m.Closed D) (sz : m.Sized)
    (d1 : D n1) (d2 : D n2) (h : R l n1 n2) :
    (m.merge ids n1 n2 l).WF ids R := by
  unfold merge
  generalize e1 : m.rootL ids n1 = p1
  generalize e2 : m.rootL ids n2 = p2
  obtain ⟨r1, l1⟩ := p1; obtain ⟨r2, l2⟩ := p2
  have ⟨dr1, h1⟩ := rootL_spec hR wf hD d1 e1
  have ⟨dr2, h2⟩ := rootL_spec hR wf hD d2 e2
  -- the roots are related at the link's level
  have h12 : R (max l (max l1 l2)) r1 r2 := by
    have := hR.trans d2 (hR.trans d1 (hR.symm h1) h) h2
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

/-! ### Terms -/

/-- The relation on nodes that a relation on terms induces through the node map. -/
def NodeRel (m : ScopedEquivManager) (E : Nat → Expr → Expr → Prop) (l i j : Nat) : Prop :=
  ∀ e₁ e₂, m.toNodeMap[e₁]? = some i → m.toNodeMap[e₂]? = some j → E l e₁ e₂

/-- A relation on terms at each level, closed under what `isEquiv` concludes from. -/
structure ERel (E : Nat → Expr → Expr → Prop) : Prop where
  beq : (e₁ == e₂) = true → E 0 e₁ e₂
  symm : E l e₁ e₂ → E l e₂ e₁
  trans : E l₁ e₁ e₂ → E l₂ e₂ e₃ → E (max l₁ l₂) e₁ e₃
  mono : l₁ ≤ l₂ → E l₁ e₁ e₂ → E l₂ e₁ e₂
  app : E l₁ f₁ f₂ → E l₂ a₁ a₂ → E (max l₁ l₂) (.app f₁ a₁) (.app f₂ a₂)
  lam : E l₁ d₁ d₂ → E l₂ b₁ b₂ → E (max l₁ l₂) (.lam n₁ d₁ b₁ i₁) (.lam n₂ d₂ b₂ i₂)
  forallE : E l₁ d₁ d₂ → E l₂ b₁ b₂ →
    E (max l₁ l₂) (.forallE n₁ d₁ b₁ i₁) (.forallE n₂ d₂ b₂ i₂)
  letE : E l₁ t₁ t₂ → E l₂ v₁ v₂ → E l₃ b₁ b₂ →
    E (max (max l₁ l₂) l₃) (.letE n₁ t₁ v₁ b₁ x₁) (.letE n₂ t₂ v₂ b₂ x₂)
  mdata : E l e₁ e₂ → E l (.mdata d₁ e₁) (.mdata d₂ e₂)
  proj : E l e₁ e₂ → E l (.proj s i e₁) (.proj s i e₂)

/-- What the scoped equivalence manager keeps: one node per term up to `==`, and every current
link in the relation its terms induce. -/
structure WFE (m : ScopedEquivManager) (ids : Scopes) (E : Nat → Expr → Expr → Prop) : Prop where
  sized : m.Sized
  parent_lt : ∀ (n p : Nat), m.parent[n]? = some p → p < m.parent.size
  dom {i} : i < m.parent.size ↔ ∃ e : Expr, m.toNodeMap[e]? = some i
  inj {e₁ e₂ : Expr} {i : Nat} : m.toNodeMap[e₁]? = some i → m.toNodeMap[e₂]? = some i →
    (e₁ == e₂) = true
  links : m.WF ids (NodeRel m E)

theorem WFE.closed (wf : m.WFE ids E) : m.Closed (· < m.parent.size) :=
  fun n p h _ => wf.parent_lt n p h

theorem WFE.lrel (hE : ERel E) (wf : m.WFE ids E) :
    LRel (· < m.parent.size) (NodeRel m E) where
  refl _ _ _ h1 h2 := hE.beq (wf.inj h1 h2)
  symm h _ _ h1 h2 := hE.symm (h _ _ h2 h1)
  trans hb h1 h2 e₁ e₃ a1 a3 :=
    let ⟨e₂, a2⟩ := wf.dom.1 hb
    hE.trans (h1 e₁ e₂ a1 a2) (h2 e₂ e₃ a2 a3)
  mono hl h e₁ e₂ a1 a2 := hE.mono hl (h e₁ e₂ a1 a2)

/-- Nodes keep the terms they were made for. -/
def LE (m₁ m₂ : ScopedEquivManager) : Prop :=
  ∀ {e : Expr} {i : Nat}, m₁.toNodeMap[e]? = some i → m₂.toNodeMap[e]? = some i

theorem LE.rfl : LE m m := id
theorem LE.trans {m₁ m₂ m₃ : ScopedEquivManager} (h1 : LE m₁ m₂) (h2 : LE m₂ m₃) : LE m₁ m₃ :=
  fun h => h2 (h1 h)

theorem toNode_spec (wf : m.WFE ids E) (e : Expr) :
    ((toNode e).run m).2.WFE ids E ∧ LE m ((toNode e).run m).2 ∧
      ((toNode e).run m).2.toNodeMap[e]? = some ((toNode e).run m).1 := by
  cases h : m.toNodeMap[e]? with
  | some r => simp only [toNode, StateT.run, h]; exact ⟨wf, fun h => h, trivial⟩
  | none =>
    simp only [toNode, StateT.run, h]
    have hfresh {e' : Expr} (h' : (e == e') = true) : m.toNodeMap[e']? = none := by
      rw [← Std.HashMap.getElem?_congr h']; exact h
    have hold {e' : Expr} {i} (h' : m.toNodeMap[e']? = some i) : (e == e') = false := by
      cases eq : (e == e') with
      | false => rfl
      | true => rw [hfresh eq] at h'; cases h'
    have hget (e' : Expr) : (m.toNodeMap.insert e m.parent.size)[e']? =
        if (e == e') = true then some m.parent.size else m.toNodeMap[e']? := by
      rw [Std.HashMap.getElem?_insert]
    have hlt {e' : Expr} {i} (h' : m.toNodeMap[e']? = some i) : i < m.parent.size :=
      wf.dom.2 ⟨_, h'⟩
    refine ⟨{ sized := ?_, parent_lt := ?_, dom := ?_, inj := ?_, links := ?_ },
      fun h' => by rw [hget, hold h']; exact h', by rw [hget, if_pos BEq.rfl]⟩
    · exact ⟨by simp [wf.sized.lvl], by simp [wf.sized.sid]⟩
    · intro n p hp
      simp only [Array.size_push]
      rw [Array.getElem?_push] at hp
      split at hp
      · cases hp; omega
      · exact Nat.lt_succ_of_lt (wf.parent_lt n p hp)
    · intro i
      simp only [Array.size_push]
      constructor
      · intro hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · obtain ⟨e', h'⟩ := wf.dom.1 hi
          exact ⟨e', by rw [hget, hold h']; exact h'⟩
        · exact ⟨e, by rw [hget, if_pos BEq.rfl]⟩
      · rintro ⟨e', h'⟩
        rw [hget] at h'
        split at h'
        · cases h'; exact Nat.lt_succ_self _
        · exact Nat.lt_succ_of_lt (hlt h')
    · intro e₁ e₂ i h1 h2
      rw [hget] at h1 h2
      split at h1 <;> split at h2
      · rename_i a1 a2; exact BEq.trans (BEq.symm a1) a2
      · cases h1; exact absurd (hlt h2) (Nat.lt_irrefl _)
      · cases h2; exact absurd (hlt h1) (Nat.lt_irrefl _)
      · exact wf.inj h1 h2
    · intro n p hp hne hok
      rw [Array.getElem?_push] at hp
      split at hp
      · cases hp; rename_i h; exact absurd h.symm hne
      · rename_i hn
        have hnl : n < m.parent.size := (Array.getElem?_eq_some_iff.1 hp).1
        have h1 : (m.lvl.push 0)[n]? = m.lvl[n]? := by
          rw [Array.getElem?_push]; split
          · rw [wf.sized.lvl] at *; omega
          · rfl
        have h2 : (m.sid.push 0)[n]? = m.sid[n]? := by
          rw [Array.getElem?_push]; split
          · rw [wf.sized.sid] at *; omega
          · rfl
        simp only [linkOK, h1, h2] at hok ⊢
        intro e₁ e₂ a1 a2
        have hp' := wf.parent_lt n p hp
        rw [hget] at a1 a2
        split at a1
        · cases a1; omega
        split at a2
        · cases a2; omega
        exact wf.links n p hp hne hok e₁ e₂ a1 a2

theorem merge_toNodeMap : (m.merge ids n1 n2 l).toNodeMap = m.toNodeMap := by
  unfold merge; dsimp only
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

theorem merge_parent_size : (m.merge ids n1 n2 l).parent.size = m.parent.size := by
  unfold merge; dsimp only
  split
  · rfl
  · split
    · simp [link]
    · split <;> simp [link]

theorem link_parent_lt (h : ∀ (n p : Nat), m.parent[n]? = some p → p < m.parent.size)
    (hb : b < m.parent.size) :
    ∀ (n p : Nat), (m.link ids a b l).parent[n]? = some p → p < (m.link ids a b l).parent.size := by
  intro n p hp
  simp only [link, Array.set!, Array.size_setIfInBounds] at hp ⊢
  rw [Array.getElem?_setIfInBounds] at hp
  split at hp
  · split at hp
    · cases hp; exact hb
    · cases hp
  · exact h n p hp

theorem merge_WFE (hE : ERel E) (wf : m.WFE ids E) (d1 : n1 < m.parent.size)
    (d2 : n2 < m.parent.size) (h : NodeRel m E l n1 n2) : (m.merge ids n1 n2 l).WFE ids E := by
  have hT := merge_toNodeMap (m := m) (ids := ids) (n1 := n1) (n2 := n2) (l := l)
  have hS := merge_parent_size (m := m) (ids := ids) (n1 := n1) (n2 := n2) (l := l)
  have hN : NodeRel (m.merge ids n1 n2 l) E = NodeRel m E := by
    funext l i j; simp only [NodeRel, hT]
  refine { sized := merge_sized wf.sized, parent_lt := ?_, dom := ?_, inj := ?_, links := ?_ }
  · unfold merge; dsimp only
    split
    · exact wf.parent_lt
    · rename_i hc
      simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, not_or, Nat.not_le] at hc
      obtain ⟨⟨-, hr1⟩, hr2⟩ := hc
      split
      · exact link_parent_lt wf.parent_lt hr2
      · split
        · exact link_parent_lt wf.parent_lt hr1
        · intro n p hp
          exact link_parent_lt (ids := ids) (l := max l (max (m.rootL ids n1).2 (m.rootL ids n2).2))
            wf.parent_lt hr2 n p hp
  · intro i; rw [hS, hT]; exact wf.dom
  · intro e₁ e₂ i h1 h2; rw [hT] at h1 h2; exact wf.inj h1 h2
  · rw [hN]; exact merge_WF (wf.lrel hE) wf.links wf.closed wf.sized d1 d2 h

/-- A computation on the manager keeps it sound and its nodes, and ends in `P`. -/
def SWF (ids : Scopes) (E : Nat → Expr → Expr → Prop) (m : ScopedEquivManager)
    (x : StateM ScopedEquivManager α) (P : α → ScopedEquivManager → Prop) : Prop :=
  m.WFE ids E → ∀ a m', x.run m = (a, m') → m'.WFE ids E ∧ LE m m' ∧ P a m'

protected theorem SWF.pure {P : α → ScopedEquivManager → Prop} (H : P a m) :
    SWF ids E m (pure a) P := by
  rintro wf _ _ ⟨⟩; exact ⟨wf, LE.rfl, H⟩

protected theorem SWF.bind {x : StateM ScopedEquivManager β} {f : β → StateM ScopedEquivManager γ}
    {P Q} (h1 : SWF ids E m x P) (h2 : ∀ a m', LE m m' → P a m' → SWF ids E m' (f a) Q) :
    SWF ids E m (x >>= f) Q := by
  intro wf a m₁
  simp only [bind, StateT.run, StateT.bind]
  generalize e : x m = r; obtain ⟨b, m₂⟩ := r
  intro eq
  have ⟨wf₂, a1, a2⟩ := h1 wf b m₂ e
  have ⟨wf₃, b1, b2⟩ := h2 _ _ a1 a2 wf₂ _ _ eq
  exact ⟨wf₃, a1.trans b1, b2⟩

protected theorem SWF.mono {x : StateM ScopedEquivManager β} {P Q}
    (h1 : SWF ids E m x P) (h2 : ∀ a m', LE m m' → P a m' → Q a m') : SWF ids E m x Q :=
  fun wf a m' e => let ⟨w, l, p⟩ := h1 wf a m' e; ⟨w, l, h2 _ _ l p⟩

protected theorem SWF.stateWF {x : StateM ScopedEquivManager β} {P}
    (H : m.WFE ids E → SWF ids E m x P) : SWF ids E m x P := fun h => H h h

theorem toNode.SWF (e : Expr) :
    SWF ids E m (toNode e) fun n m' => m'.toNodeMap[e]? = some n := by
  intro wf a m' eq
  have := toNode_spec wf e
  simp only [StateT.run] at eq this
  rw [eq] at this
  exact this

theorem get.SWF : SWF ids E m get fun a m' => a = m' := by
  rintro wf _ _ ⟨⟩; exact ⟨wf, LE.rfl, rfl⟩

theorem modifyMerge.SWF (hE : ERel E) {n1 n2 l} (H : m.WFE ids E → n1 < m.parent.size ∧
    n2 < m.parent.size ∧ NodeRel m E l n1 n2) :
    SWF ids E m (modify (·.merge ids n1 n2 l)) fun _ _ => True := by
  rintro wf _ _ ⟨⟩
  obtain ⟨d1, d2, h⟩ := H wf
  exact ⟨merge_WFE hE wf d1 d2 h, fun h => by
    show (m.merge ids n1 n2 l).toNodeMap[_]? = _; rw [merge_toNodeMap]; exact h, trivial⟩

/-- A relation between two terms is one between their nodes. -/
theorem WFE.nodeRel (hE : ERel E) (wf : m.WFE ids E) (h1 : m.toNodeMap[e₁]? = some n1)
    (h2 : m.toNodeMap[e₂]? = some n2) (h : E l e₁ e₂) : NodeRel m E l n1 n2 := by
  intro e₁' e₂' a1 a2
  have := hE.trans (hE.trans (hE.beq (wf.inj a1 h1)) h) (hE.beq (wf.inj h2 a2))
  exact hE.mono (by omega) this

theorem both.SWF {x : StateM ScopedEquivManager (Option Nat)}
    {y : Unit → StateM ScopedEquivManager (Option Nat)} {P Q : Nat → Prop}
    (h1 : SWF ids E m x fun r _ => ∀ l, r = some l → P l)
    (h2 : ∀ {m}, SWF ids E m (y ()) fun r _ => ∀ l, r = some l → Q l) :
    SWF ids E m (both x y) fun r _ => ∀ l, r = some l → ∃ a b, l = max a b ∧ P a ∧ Q b := by
  unfold both
  refine h1.bind fun r _ _ hr => ?_
  cases r with
  | none => exact .pure nofun
  | some a =>
    refine h2.bind fun r' _ _ hr' => ?_
    cases r' with
    | none => exact .pure nofun
    | some b => exact .pure fun _ e => by cases e; exact ⟨a, b, rfl, hr a rfl, hr' b rfl⟩

/-- An equivalence the manager reports holds at the level it reports. -/
theorem isEquiv.SWF (hE : ERel E) {lv : Expr → Nat} {m : ScopedEquivManager} {useHash : Bool}
    {e₁ e₂ : Expr} :
    SWF ids E m (isEquiv ids lv useHash e₁ e₂) fun r _ => ∀ l, r = some l → E l e₁ e₂ := by
  unfold isEquiv
  split
  · rename_i h; exact .pure fun _ e => by cases e; rw [ptrEqExpr_eq h]; exact hE.beq BEq.rfl
  split
  · exact .pure nofun
  split
  · rename_i h; refine .pure fun l e => ?_
    simp only [Bool.and_eq_true, Expr.isBVar] at h
    split at h <;> cases h.1; split at h <;> cases h.2
    simp only [Expr.bvarIdx!, beq_iff_eq, Option.ite_none_right_eq_some,
      Option.some.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact hE.beq BEq.rfl
  refine (toNode.SWF e₁).bind fun n1 _ _ a1 => (toNode.SWF e₂).bind fun n2 _ le₂ b1 => ?_
  refine get.SWF.bind fun m₀ _ le₃ h₀ => ?_
  cases h₀
  refine .stateWF fun wf => ?_
  replace a1 := le₃ (le₂ a1)
  replace b1 := le₃ b1
  have d1 : n1 < m₀.parent.size := wf.dom.2 ⟨_, a1⟩
  have d2 : n2 < m₀.parent.size := wf.dom.2 ⟨_, b1⟩
  split
  · rename_i l hl
    refine .pure fun l' e => ?_
    cases e
    exact connLevel_spec (wf.lrel hE) wf.links wf.closed d1 d2 hl _ _ a1 b1
  -- the structural cases end by recording the equivalence found
  have fin {m} (le : LE m₀ m) {r : Option Nat} (H : ∀ l, r = some l → E l e₁ e₂) :
      ScopedEquivManager.SWF ids E m (do
        let some l := r | return none
        modify (·.merge ids n1 n2 (max l (max (lv e₁) (lv e₂))))
        return some l) fun r _ => ∀ l, r = some l → E l e₁ e₂ := by
    cases r with
    | none => exact .pure nofun
    | some l =>
      refine (modifyMerge.SWF hE fun wf' => ⟨wf'.dom.2 ⟨_, le a1⟩, wf'.dom.2 ⟨_, le b1⟩,
        wf'.nodeRel hE (le a1) (le b1) (hE.mono (by omega) (H l rfl))⟩).bind fun _ _ _ _ => ?_
      exact .pure fun _ e => by cases e; exact H l rfl
  have leaf {X : Option Nat} (H : ∀ l, X = some l → E l e₁ e₂) :
      ScopedEquivManager.SWF ids E m₀ (do let result ← pure X; match result with
        | some l => do
          modify fun x => x.merge ids n1 n2 (max l (max (lv e₁) (lv e₂)))
          pure (some l)
        | _ => pure none) fun r _ => ∀ l, r = some l → E l e₁ e₂ :=
    SWF.bind (P := fun r _ => r = X) (.pure rfl) fun r _ le hr => by subst hr; exact fin le H
  have eqv {X : Option Nat} (H : X = some 0 ∨ X = none) (H' : X = some 0 → e₁ = e₂) :
      ∀ l, X = some l → E l e₁ e₂ := by
    intro l e; rcases H with h | h <;> rw [h] at e <;> cases e
    obtain rfl := H' h; exact hE.beq BEq.rfl
  have ite0 {c : Bool} : (if c = true then some 0 else none) = some 0 ∨
      (if c = true then some 0 else none) = none := by split <;> simp
  have rec2 {x : StateM ScopedEquivManager (Option Nat)} {y : Unit → StateM ScopedEquivManager (Option Nat)}
      {P Q : Nat → Prop} (h1 : ScopedEquivManager.SWF ids E m₀ x fun r _ => ∀ l, r = some l → P l)
      (h2 : ∀ {m}, ScopedEquivManager.SWF ids E m (y ()) fun r _ => ∀ l, r = some l → Q l)
      (H : ∀ a b, P a → Q b → E (max a b) e₁ e₂) :
      ScopedEquivManager.SWF ids E m₀ (do let result ← both x y; match result with
        | some l => do
          modify fun x => x.merge ids n1 n2 (max l (max (lv e₁) (lv e₂)))
          pure (some l)
        | _ => pure none) fun r _ => ∀ l, r = some l → E l e₁ e₂ :=
    (both.SWF h1 h2).bind fun r _ le hr => fin le fun l e => by
      obtain ⟨a, b, rfl, ha, hb⟩ := hr l e; exact H a b ha hb
  dsimp only
  split
  · exact leaf (eqv ite0 fun h => by
      split at h <;> cases h
      rename_i h; simp only [Bool.and_eq_true, beq_iff_eq] at h; rw [h.1, h.2])
  · exact leaf (eqv ite0 fun h => by
      split at h <;> cases h; rename_i h; simp only [beq_iff_eq] at h; rw [h])
  · exact leaf (eqv ite0 fun h => by
      split at h <;> cases h; rename_i h; simp only [beq_iff_eq] at h; rw [h])
  · exact leaf (eqv ite0 fun h => by
      split at h <;> cases h; rename_i h; simp only [beq_iff_eq] at h; rw [h])
  · exact leaf (eqv ite0 fun h => by
      split at h <;> cases h; rename_i h; simp only [beq_iff_eq] at h; rw [h])
  · exact rec2 (isEquiv.SWF hE) (isEquiv.SWF hE) fun _ _ => hE.app
  · exact rec2 (isEquiv.SWF hE) (isEquiv.SWF hE) fun _ _ => hE.lam
  · exact (isEquiv.SWF (useHash := useHash) (lv := lv) hE).bind fun r _ le hr =>
      fin le fun l e => hE.mdata (hr l e)
  · exact rec2 (isEquiv.SWF hE) (isEquiv.SWF hE) fun _ _ => hE.forallE
  · split
    · rename_i h
      simp only [Bool.and_eq_true, beq_iff_eq] at h; obtain ⟨rfl, rfl⟩ := h
      exact (isEquiv.SWF (useHash := useHash) (lv := lv) hE).bind fun r _ le hr =>
        fin le fun l e => hE.proj (hr l e)
    · exact (SWF.pure (P := fun r _ => r = none) rfl).bind fun r _ le hr => by
        subst hr; exact fin (r := none) le fun _ e => by cases e
  · refine (both.SWF (both.SWF (isEquiv.SWF hE) (isEquiv.SWF hE)) (isEquiv.SWF hE)).bind fun r _ le hr =>
      fin le fun l e => ?_
    obtain ⟨a, b, rfl, ⟨a', b', rfl, ha, hb⟩, hc⟩ := hr l e
    exact hE.letE ha hb hc
  · exact leaf nofun

/-- Recording an equivalence that holds at its level keeps the manager sound. -/
theorem addEquiv.SWF (hE : ERel E) {lv : Expr → Nat} (h : E l e₁ e₂) :
    SWF ids E m (addEquiv ids lv e₁ e₂ l) fun _ _ => True := by
  unfold addEquiv
  refine (toNode.SWF e₁).bind fun n1 _ _ a1 => (toNode.SWF e₂).bind fun n2 _ le₂ b1 => ?_
  exact modifyMerge.SWF hE fun wf => ⟨wf.dom.2 ⟨_, le₂ a1⟩, wf.dom.2 ⟨_, b1⟩,
    wf.nodeRel hE (le₂ a1) b1 (hE.mono (by omega) h)⟩

theorem WFE.empty : ({} : ScopedEquivManager).WFE ids E where
  sized := ⟨rfl, rfl⟩
  parent_lt _ _ h := by simp at h
  dom := by simp
  inj h := by simp at h
  links _ _ h := by simp at h

end Lean4Lean.ScopedEquivManager
