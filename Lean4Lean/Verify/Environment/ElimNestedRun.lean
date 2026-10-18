import Lean4Lean.Verify.Environment.Checker
import Lean4Lean.Verify.Environment.ElimNested
import Lean4Lean.Verify.Support.Basic
import Lean4Lean.Theory.Typing.Nested

/-!
# Eliminating nested occurrences

What `ElimNestedInductive.run` produces from a block, at the level of `Expr`s:

* the parameters it opens from the first type (`Opens`), as `res.params` in `res.lctx`;
* the block's own types, with each constructor's type opened at fresh parameters, its nested
  occurrences replaced (`Replaced`), and closed again;
* an auxiliary type per entry of `res.aux2nested`, created from an earlier type `J` at the
  occurrence's levels and parameters (`Created`), its constructors processed the same way.
-/

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

/-! ### Telescopes -/

/-- The body of `e` under its first `n` binders, which are literal `forallE`s. -/
def peel : Nat → Expr → Option Expr
  | 0, e => some e
  | n + 1, .forallE _ _ b _ => peel n b
  | _ + 1, _ => none

/-- `e` with the body under its first `n` literal binders replaced by `b`. -/
def setBody : Nat → Expr → Expr → Expr
  | 0, _, b => b
  | n + 1, .forallE nm d e bi, b => .forallE nm d (setBody n e b) bi
  | _ + 1, e, _ => e

theorem peel_setBody : ∀ {n e b}, (peel n e).isSome → peel n (setBody n e b) = some b
  | 0, _, _, _ => rfl
  | n + 1, .forallE .., _, h => peel_setBody (n := n) h
  | _ + 1, .bvar .., _, h | _ + 1, .fvar .., _, h | _ + 1, .mvar .., _, h
  | _ + 1, .sort .., _, h | _ + 1, .const .., _, h | _ + 1, .app .., _, h
  | _ + 1, .lam .., _, h | _ + 1, .letE .., _, h | _ + 1, .lit .., _, h
  | _ + 1, .mdata .., _, h | _ + 1, .proj .., _, h => by simp [peel] at h

/-- The fresh names `n` calls of `mkFreshId` return from `g`. -/
def freshIds (g : NameGenerator) : Nat → List FVarId
  | 0 => []
  | n + 1 => ⟨g.curr⟩ :: freshIds g.next n

/-- `g` after `n` calls of `mkFreshId`. -/
def advance (g : NameGenerator) : Nat → NameGenerator
  | 0 => g
  | n + 1 => advance g.next n

theorem le_advance : ∀ {g : NameGenerator} {n}, g ≤ advance g n
  | _, 0 => NameGenerator.LE.rfl
  | _, _ + 1 => NameGenerator.LE.next.trans le_advance

theorem freshIds_reserves : ∀ {g : NameGenerator} {n x}, x ∈ freshIds g n →
    (advance g n).Reserves x ∧ ¬g.Reserves x
  | g, n + 1, x, h => by
    simp only [freshIds, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨NameGenerator.Reserves.mono (le_advance (g := g.next))
        NameGenerator.next_reserves_self,
        NameGenerator.not_reserves_self⟩
    · obtain ⟨h1, h2⟩ := freshIds_reserves (g := g.next) h
      refine ⟨h1, fun h3 => h2 (h3.mono NameGenerator.LE.next)⟩

theorem freshIds_nodup : ∀ {g : NameGenerator} {n}, (freshIds g n).Nodup
  | _, 0 => .nil
  | g, n + 1 => by
    refine List.nodup_cons.2 ⟨fun h => ?_, freshIds_nodup⟩
    exact (freshIds_reserves (g := g.next) h).2 NameGenerator.next_reserves_self

theorem freshIds_length : ∀ {g : NameGenerator} {n}, (freshIds g n).length = n
  | _, 0 => rfl
  | _, _ + 1 => congrArg (· + 1) freshIds_length

/-- `withParams.loop` opening the binders of `ty`, from `lctx`, as the local declarations `xs`. -/
inductive Opens : LocalContext → Expr → List FVarId → LocalContext → Expr → Prop
  | nil : Opens lctx ty [] lctx ty
  | cons {lctx : LocalContext} {x : FVarId} {nm : Name} {dom : Expr} {bi : BinderInfo}
      {body : Expr} {xs : List FVarId} {lctx' : LocalContext} {ty' : Expr} :
    Opens (lctx.mkLocalDecl x nm dom bi) (body.instantiate1 (.fvar x)) xs lctx' ty' →
    Opens lctx (.forallE nm dom body bi) (x :: xs) lctx' ty'

theorem peel_instantiate1 {a : Expr} : ∀ {m e k B}, peel m e = some B →
    peel m (Expr.instantiate1' e a k) = some (Expr.instantiate1' B a (k + m))
  | 0, _, _, _, h => by cases h; rfl
  | m + 1, .forallE .., k, B, h => by
    simp only [Expr.instantiate1', peel] at h ⊢
    rw [peel_instantiate1 h, Nat.add_right_comm]; rfl
  | _ + 1, .bvar .., _, _, h | _ + 1, .fvar .., _, _, h | _ + 1, .mvar .., _, _, h
  | _ + 1, .sort .., _, _, h | _ + 1, .const .., _, _, h | _ + 1, .app .., _, _, h
  | _ + 1, .lam .., _, _, h | _ + 1, .letE .., _, _, h | _ + 1, .lit .., _, _, h
  | _ + 1, .mdata .., _, _, h | _ + 1, .proj .., _, _, h => by simp [peel] at h

theorem peel_instantiate1_fvar {x : FVarId} : ∀ {m e k},
    peel m (Expr.instantiate1' e (.fvar x) k) = (peel m e).map (Expr.instantiate1' · (.fvar x) (k + m))
  | 0, _, _ => rfl
  | m + 1, .forallE .., k => by
    simp only [Expr.instantiate1', peel]
    rw [peel_instantiate1_fvar, Nat.add_right_comm]; rfl
  | _ + 1, .bvar i, k => by
    simp only [Expr.instantiate1']
    split <;> [rfl; split <;> rfl]
  | _ + 1, .fvar .., _ | _ + 1, .mvar .., _ | _ + 1, .sort .., _ | _ + 1, .const .., _
  | _ + 1, .app .., _ | _ + 1, .lam .., _ | _ + 1, .letE .., _ | _ + 1, .lit .., _
  | _ + 1, .mdata .., _ | _ + 1, .proj .., _ => rfl

/-- Only the free variables a term mentions, constrained by `P`. -/
abbrev FVOnly (P : FVarId → Prop) : Supp := ⟨P, fun _ => True, fun _ => True⟩

theorem abstract_instantiate1 {x : FVarId} {e : Expr} {k}
    (h : e.SuppIn (FVOnly (· ≠ x))) : (Expr.instantiate1' e (.fvar x) k).abstract1 x k = e := by
  induction e generalizing k with simp_all [Expr.instantiate1', Expr.abstract1, Expr.SuppIn]
  | bvar i =>
    split <;> [skip; split]
    · simp [Expr.abstract1, *]
    · simp [Expr.abstract1, Expr.liftLooseBVars', *]
    · obtain _|i := i <;> simp [Expr.abstract1] <;> omega
  | fvar v' => exact Ne.symm h

theorem SuppIn.peel {S : Supp} : ∀ {m e B}, peel m e = some B → Expr.SuppIn S e →
    Expr.SuppIn S B
  | 0, _, _, h, he => by cases h; exact he
  | m + 1, .forallE .., B, h, he => SuppIn.peel (m := m) h he.2
  | _ + 1, .bvar .., _, h, _ | _ + 1, .fvar .., _, h, _ | _ + 1, .mvar .., _, h, _
  | _ + 1, .sort .., _, h, _ | _ + 1, .const .., _, h, _ | _ + 1, .app .., _, h, _
  | _ + 1, .lam .., _, h, _ | _ + 1, .letE .., _, h, _ | _ + 1, .lit .., _, h, _
  | _ + 1, .mdata .., _, h, _ | _ + 1, .proj .., _, h, _ => by simp [ElimNestedInductive.peel] at h

/-- Opening a telescope at fresh variables and abstracting them again gives back its body. -/
theorem Opens.peel {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ty.SuppIn (FVOnly (· ≠ x))) :
    ElimNestedInductive.peel xs.length ty = some (ty'.abstractList xs) := by
  induction H with
  | nil => rfl
  | @cons lctx x nm dom bi body xs lctx' ty' _ ih =>
    rw [List.nodup_cons] at hnd
    have hb : body.SuppIn (FVOnly (· ≠ x)) := (hx x (.head _)).2
    have ih := ih hnd.2 fun y hy => by
      simp only [Expr.instantiate1_eq]
      exact Expr.SuppIn.instantiate1 (a := .fvar x) (S := FVOnly (· ≠ y)) (show x ≠ y from fun h => hnd.1 (h ▸ hy)) (hx y (.tail _ hy)).2
    simp only [Expr.instantiate1_eq, peel_instantiate1_fvar, Nat.zero_add] at ih
    obtain ⟨B, hB, e⟩ := Option.map_eq_some_iff.1 ih
    simp only [List.length_cons, ElimNestedInductive.peel, hB, Expr.abstractList]
    rw [← Expr.abstract1_abstractList' (List.nodup_cons.2 hnd), Nat.zero_add, ← e,
      abstract_instantiate1 (SuppIn.peel hB hb)]

theorem setBody_abstract1 {x : FVarId} {W : Expr} : ∀ {m e k}, (peel m e).isSome →
    e.SuppIn (FVOnly (· ≠ x)) →
    Expr.abstract1 x (setBody m (Expr.instantiate1' e (.fvar x) k) W) k =
      setBody m e (Expr.abstract1 x W (k + m))
  | 0, _, _, _, _ => rfl
  | m + 1, .forallE nm d b bi, k, h, he => by
    simp only [Expr.instantiate1', setBody, Expr.abstract1]
    rw [abstract_instantiate1 he.1, setBody_abstract1 (m := m) h he.2, Nat.add_right_comm]; rfl
  | _ + 1, .bvar .., _, h, _ | _ + 1, .fvar .., _, h, _ | _ + 1, .mvar .., _, h, _
  | _ + 1, .sort .., _, h, _ | _ + 1, .const .., _, h, _ | _ + 1, .app .., _, h, _
  | _ + 1, .lam .., _, h, _ | _ + 1, .letE .., _, h, _ | _ + 1, .lit .., _, h, _
  | _ + 1, .mdata .., _, h, _ | _ + 1, .proj .., _, h, _ => by simp [peel] at h

theorem _root_.Lean.LocalContext.find?_mkLocalDecl_self {lctx : LocalContext} (h : lctx.WF)
    (hn : lctx.find? fv = none) :
    (lctx.mkLocalDecl fv nm ty bi).find? fv = some (.cdecl lctx.decls.size fv nm ty bi .default) := by
  rw [(h.mkLocalDecl hn).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList]
  simp [LocalDecl.fvarId]

theorem _root_.Lean.LocalContext.find?_mkLocalDecl_ne {lctx : LocalContext} (h : lctx.WF)
    (hn : lctx.find? fv = none) {y : FVarId} (hy : fv ≠ y) :
    (lctx.mkLocalDecl fv nm ty bi).find? y = lctx.find? y := by
  rw [(h.mkLocalDecl hn).find?_eq_find?_toList, LocalContext.mkLocalDecl_toList,
    h.find?_eq_find?_toList]
  have : (y == fv) = false := by simpa using Ne.symm hy
  simp only [List.find?_cons, LocalDecl.fvarId, this]

/-- What opening a telescope adds to the local context. -/
theorem Opens.lctx {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') (hW : lctx.WF)
    (hfr : ∀ x ∈ xs, lctx.find? x = none) (hnd : xs.Nodup) :
    lctx'.WF ∧ (∀ y, y ∉ xs → lctx'.find? y = lctx.find? y) ∧
      ∀ x ∈ xs, ∃ d, lctx'.find? x = some d := by
  induction H with
  | nil => exact ⟨hW, fun _ _ => rfl, nofun⟩
  | @cons lctx x nm dom bi body xs lctx' ty' _ ih =>
    rw [List.nodup_cons] at hnd
    have hx := hfr x (.head _)
    have hW' := hW.mkLocalDecl (name := nm) (ty := dom) (bi := bi) (kind := .default) hx
    have hfr' : ∀ y ∈ xs, (lctx.mkLocalDecl x nm dom bi).find? y = none := fun y hy => by
      rw [LocalContext.find?_mkLocalDecl_ne hW hx (fun e => hnd.1 (e ▸ hy))]
      exact hfr y (.tail _ hy)
    obtain ⟨h1, h2, h3⟩ := ih hW' hfr' hnd.2
    refine ⟨h1, fun y hy => ?_, fun y hy => ?_⟩
    · rw [h2 y (fun h => hy (.tail _ h)),
        LocalContext.find?_mkLocalDecl_ne hW hx (fun e => hy (e ▸ .head _))]
    · rcases List.mem_cons.1 hy with rfl | hy
      · rw [h2 _ hnd.1, LocalContext.find?_mkLocalDecl_self hW hx]; exact ⟨_, rfl⟩
      · exact h3 y hy

/-- The variables a closed telescope is opened at are declared at closed types. -/
theorem Opens.closed {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') (hW : lctx.WF)
    (hfr : ∀ x ∈ xs, lctx.find? x = none) (hnd : xs.Nodup) (hty : ty.looseBVarRange' = 0) :
    ty'.looseBVarRange' = 0 ∧ ∀ x ∈ xs, ∃ d, lctx'.find? x = some d ∧ d.Closed := by
  induction H with
  | nil => exact ⟨hty, nofun⟩
  | @cons lctx x nm dom bi body xs lctx' ty' H ih =>
    rw [List.nodup_cons] at hnd
    have hx := hfr x (.head _)
    have hW' := hW.mkLocalDecl (name := nm) (ty := dom) (bi := bi) (kind := .default) hx
    have hfr' : ∀ y ∈ xs, (lctx.mkLocalDecl x nm dom bi).find? y = none := fun y hy => by
      rw [LocalContext.find?_mkLocalDecl_ne hW hx (fun e => hnd.1 (e ▸ hy))]
      exact hfr y (.tail _ hy)
    simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hty
    have hb : (body.instantiate1 (.fvar x)).looseBVarRange' = 0 := by
      rw [Expr.instantiate1_eq]
      have := Expr.instantiate1'_looseBVarRange (e := body) (a := .fvar x) (n := 0) (k := 0)
        (by omega) (by simp [Expr.looseBVarRange'])
      omega
    obtain ⟨h1, h2⟩ := ih hW' hfr' hnd.2 hb
    obtain ⟨-, h3, -⟩ := H.lctx hW' hfr' hnd.2
    refine ⟨h1, fun y hy => ?_⟩
    rcases List.mem_cons.1 hy with h | hy
    · exact ⟨.cdecl lctx.decls.size x nm dom bi .default,
        by rw [h, h3 _ hnd.1, LocalContext.find?_mkLocalDecl_self hW hx], hty.1⟩
    · exact h2 y hy

/-- Closing the variables a telescope was opened at puts back its binders, around any body. -/
theorem Opens.mkForall {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') (hW : lctx.WF)
    (hfr : ∀ x ∈ xs, lctx.find? x = none) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ty.SuppIn (FVOnly (· ≠ x))) (hty : ty.looseBVarRange' = 0) (Z : Expr)
    (hZ : Z.looseBVarRange' = 0) :
    lctx'.mkForall ⟨xs.map .fvar⟩ Z = setBody xs.length ty (Z.abstractList xs) := by
  rw [LocalContext.mkForall, LocalContext.mkBinding_eq]
  obtain ⟨-, hsome⟩ := H.closed hW hfr hnd hty
  induction H with
  | nil => simp [setBody, Expr.abstractList]
  | @cons lctx x nm dom bi body xs lctx' ty' H ih =>
    rw [List.nodup_cons] at hnd
    have hx' := hfr x (.head _)
    have hW' := hW.mkLocalDecl (name := nm) (ty := dom) (bi := bi) (kind := .default) hx'
    have hfr' : ∀ y ∈ xs, (lctx.mkLocalDecl x nm dom bi).find? y = none := fun y hy => by
      rw [LocalContext.find?_mkLocalDecl_ne hW hx' (fun e => hnd.1 (e ▸ hy))]
      exact hfr y (.tail _ hy)
    have hb : body.SuppIn (FVOnly (· ≠ x)) := (hx x (.head _)).2
    have ih := ih hW' hfr' hnd.2 (fun y hy => by
      simp only [Expr.instantiate1_eq]
      exact Expr.SuppIn.instantiate1 (a := .fvar x) (S := FVOnly (· ≠ y)) (show x ≠ y from fun h => hnd.1 (h ▸ hy)) (hx y (.tail _ hy)).2)
      (by
        simp only [Expr.looseBVarRange', Nat.max_eq_zero_iff] at hty
        rw [Expr.instantiate1_eq]
        have := Expr.instantiate1'_looseBVarRange (e := body) (a := .fvar x) (n := 0) (k := 0)
          (by omega) (by simp [Expr.looseBVarRange'])
        omega)
      (fun y hy => hsome y (.tail _ hy))
    have hpeel := H.peel hnd.2 (fun y hy => by
      simp only [Expr.instantiate1_eq]
      exact Expr.SuppIn.instantiate1 (a := .fvar x) (S := FVOnly (· ≠ y)) (show x ≠ y from fun h => hnd.1 (h ▸ hy)) (hx y (.tail _ hy)).2)
    simp only [Expr.instantiate1_eq, peel_instantiate1_fvar] at hpeel
    have hps : (ElimNestedInductive.peel xs.length body).isSome := by
      cases h : ElimNestedInductive.peel xs.length body <;> simp_all
    obtain ⟨-, h2, -⟩ := H.lctx hW' hfr' hnd.2
    have hfx : lctx'.find? x = some (.cdecl lctx.decls.size x nm dom bi .default) := by
      rw [h2 _ hnd.1, LocalContext.find?_mkLocalDecl_self hW hx']
    rw [LocalContext.mkBindingList_cons hZ (fun y hy => hsome y (.tail _ hy))
      (List.nodup_cons.2 hnd), ih]
    simp only [LocalContext.mkBindingList1, hfx, Expr.abstractList, Bool.false_eq_true,
      if_false, List.length_cons, setBody]
    simp only [Expr.instantiate1_eq]
    have e := Expr.abstract1_abstractList' (e := Z) (k := 0) (List.nodup_cons.2 hnd)
    rw [Nat.zero_add] at e
    rw [setBody_abstract1 hps hb, Nat.zero_add, e, Expr.abstract'_nil]

/-! ### Hoare triples -/

/-- Run from a state satisfying `P`, `x` ends in one satisfying `Q` of its result. -/
def Triple (env : Environment) (P : State → Prop) (x : M α) (Q : α → State → Prop) : Prop :=
  ∀ s a s', x env s = .ok (a, s') → P s → Q a s'

namespace Triple
variable {env : Environment}

theorem bind {x : M α} {f : α → M β} {P Q R} (h1 : Triple env P x Q)
    (h2 : ∀ a, Triple env (Q a) (f a) R) : Triple env P (x >>= f) R := by
  intro s b s' h hp
  obtain ⟨a, s₁, h₁, h₂⟩ := bind_ok h
  exact h2 a s₁ b s' h₂ (h1 s a s₁ h₁ hp)

theorem pure {a : α} {P : State → Prop} {Q} (h : ∀ s, P s → Q a s) :
    Triple env P (Pure.pure a : M α) Q := by
  rintro s _ _ ⟨⟩ hp; exact h s hp

theorem get {P Q} (h : ∀ s, P s → Q s s) : Triple env P (MonadState.get : M State) Q := by
  rintro s _ _ ⟨⟩ hp; exact h s hp

theorem read {P Q} (h : ∀ s, P s → Q env s) :
    Triple env P (MonadReader.read : M Environment) Q := by
  rintro s _ _ ⟨⟩ hp; exact h s hp

theorem modify {f : State → State} {P Q} (h : ∀ s, P s → Q ⟨⟩ (f s)) :
    Triple env P (_root_.modify f : M PUnit) Q := by
  rintro s _ _ ⟨⟩ hp; exact h s hp

theorem throw {e : Exception} {P Q} : Triple env P (MonadExcept.throw e : M α) Q := by
  rintro _ _ _ ⟨⟩

theorem default [Inhabited α] {P Q} (h : ∀ s, P s → Q Inhabited.default s) :
    Triple env P (Inhabited.default : M α) Q := by
  rintro s _ _ ⟨⟩ hp; exact h s hp

theorem liftExcept {x : Except Exception α} {P Q} (h : ∀ a s, x = .ok a → P s → Q a s) :
    Triple env P (liftM x : M α) Q := by
  intro s a s' h1 hp
  cases hx : x with
  | error => rw [hx] at h1; cases h1
  | ok a' => rw [hx] at h1; cases h1; exact h _ _ hx hp

theorem mono {x : M α} {P P' Q Q'} (H : Triple env P x Q) (hP : ∀ s, P' s → P s)
    (hQ : ∀ a s, Q a s → Q' a s) : Triple env P' x Q' :=
  fun s a s' h hp => hQ _ _ (H s a s' h (hP _ hp))

theorem forIn_list {l : List β} {init : σ} {body : β → σ → M (ForInStep σ)}
    {I : σ → State → Prop}
    (h : ∀ b ∈ l, ∀ r, Triple env (I r) (body b r) fun st => I (stepVal st)) :
    Triple env (I init) (forIn l init body) I := by
  induction l generalizing init with
  | nil => exact Triple.pure fun _ h => h
  | cons b l ih =>
    rw [List.forIn_cons]
    refine Triple.bind (h b (.head _) init) fun r => ?_
    cases r with
    | done a => exact Triple.pure fun _ h => h
    | yield a => exact ih (fun b hb => h b (.tail _ hb))

end Triple

/-- The states a successful `mapM` passes through. -/
inductive Chain (env : Environment) (f : β → M γ) : List β → List γ → State → State → Prop
  | nil : Chain env f [] [] s s
  | cons : f b env s = .ok (c, s₁) → Chain env f l cs s₁ s' → Chain env f (b :: l) (c :: cs) s s'

theorem mapM_ok {env : Environment} {f : β → M γ} :
    ∀ {l : List β} {s cs s'}, l.mapM f env s = .ok (cs, s') → Chain env f l cs s s'
  | [], s, cs, s', h => by cases h; exact .nil
  | b :: l, s, cs, s', h => by
    rw [List.mapM_cons] at h
    obtain ⟨c, s₁, h1, h⟩ := bind_ok h
    obtain ⟨cs', s₂, h2, h⟩ := bind_ok h
    cases h
    exact .cons h1 (mapM_ok h2)

theorem mkFreshId_eq {env : Environment} {s : State} :
    (mkFreshId : M Name) env s = .ok (s.ngen.curr, { s with ngen := s.ngen.next }) := rfl

theorem withParams.loop_open {env : Environment} {k : LocalContext → Expr → Array Expr → M α} :
    ∀ n lctx type params s a s', withParams.loop k lctx type params n env s = .ok (a, s') →
      ∃ lctx' ty', Opens lctx type (freshIds s.ngen n) lctx' ty' ∧
        k lctx' ty' (params ++ ((freshIds s.ngen n).map .fvar).toArray) env
          { s with ngen := advance s.ngen n } = .ok (a, s')
  | 0, lctx, type, params, s, a, s', h => by
    rw [withParams.loop] at h; exact ⟨_, _, .nil, by simpa [freshIds, advance] using h⟩
  | n + 1, lctx, type, params, s, a, s', h => by
    unfold withParams.loop at h
    split at h
    · obtain ⟨_, s₁, hf, h⟩ := bind_ok h
      rw [mkFreshId_eq] at hf; cases hf
      obtain ⟨lctx', ty', ho, hk⟩ := withParams.loop_open n _ _ _ _ _ _ h
      refine ⟨lctx', ty', .cons ho, ?_⟩
      simpa [freshIds, advance] using hk
    · cases h

/-! ### Replacing nested occurrences -/

/-- `replaceParams` when its sizes agree: `e`, opened at the constructor's parameters `As`, at the
block's parameters `params` instead. -/
def replaceParamsVal (params : Array Expr) (e : Expr) (As : Array Expr) : Expr := (e.abstract As).instantiateRev params

theorem replaceParams_eq {params As : Array Expr} (h : As.size = params.size) (e : Expr)
    {env : Environment} {s : State} :
    replaceParams params e As env s = .ok (replaceParamsVal params e As, s) := by
  unfold replaceParams; simp only [h, beq_self_eq_true, ↓reduceIte]; rfl

/-- The auxiliary type `T` that `replaceIfNested` creates, under the key `K`, while processing a
constructor opened at `As` in `lctx`: the earlier type `J` of the occurrence, its first `nI`
arguments being its parameters, instantiated at the occurrence's levels and parameters. -/
def Created (env : Environment) (lctx : LocalContext) (params As : Array Expr) (K : Expr)
    (T : InductiveType) : Prop :=
  ∃ J Ls args nI Jv v, K = replaceParamsVal params (mkAppRange (.const J Ls) 0 nI args) As ∧
    env.find? J = some (.inductInfo Jv) ∧ nI ≤ args.size ∧
    (∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0) ∧
    (∀ a ∈ args, a.SuppIn (FVOnly (.fvar · ∈ As))) ∧
    instantiateForallParams (Jv.type.instantiateLevelParams Jv.levelParams Ls) nI args = .ok v ∧
    T.type = lctx.mkForall As v ∧ env.contains T.name = false ∧
    List.Forall₂ (fun Jc c => c.name = Jc.replacePrefix J T.name ∧ ∃ ci v', env.find? Jc = some ci ∧
        instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams Ls) nI args =
          .ok v' ∧ c.type = lctx.mkForall As v')
      Jv.ctors T.ctors ∧
    ∃ I Iv, env.find? I = some (.inductInfo Iv) ∧ J ∈ Iv.all ∧ nI = Iv.numParams

/-- `s'` is `s` with auxiliary types added that were created while processing a constructor
opened at `As` in `lctx`. -/
def Extends (env : Environment) (lctx : LocalContext) (params As : Array Expr) (s s' : State) :
    Prop :=
  s'.lvls = s.lvls ∧ s'.ngen = s.ngen ∧ ∃ new : List ((Expr × Name) × InductiveType),
    s'.nestedAux.toList = s.nestedAux.toList ++ new.map (·.1) ∧
    s'.newTypes.toList = s.newTypes.toList ++ new.map (·.2) ∧
    ∀ p ∈ new, p.2.name = p.1.2 ∧ Created env lctx params As p.1.1 p.2

theorem Extends.refl {env lctx params As} {s : State} : Extends env lctx params As s s :=
  ⟨rfl, rfl, [], by simp, by simp, nofun⟩

theorem Extends.trans {env lctx params As} {s₁ s₂ s₃ : State}
    (h₁ : Extends env lctx params As s₁ s₂) (h₂ : Extends env lctx params As s₂ s₃) :
    Extends env lctx params As s₁ s₃ := by
  obtain ⟨a1, b1, n1, c1, d1, e1⟩ := h₁
  obtain ⟨a2, b2, n2, c2, d2, e2⟩ := h₂
  refine ⟨a2.trans a1, b2.trans b1, n1 ++ n2, by simp [c1, c2], by simp [d1, d2], ?_⟩
  intro p hp; rcases List.mem_append.1 hp with h | h
  · exact e1 p h
  · exact e2 p h

theorem Extends.sub {env lctx params As} {s s' : State} (h : Extends env lctx params As s s') :
    s.nestedAux.toList ⊆ s'.nestedAux.toList := by
  obtain ⟨-, -, _, h, -⟩ := h; rw [h]; exact List.subset_append_left _ _

/-- `Y` is the nested occurrence `e` replaced, by the auxiliary type recorded in `pairs` under a
key agreeing with the occurrence's at the block's parameters, applied to the constructor's
parameters `As` and the occurrence's remaining arguments. -/
def NodeRep (pairs : List (Expr × Name)) (lvls : List Level) (params As : Array Expr)
    (e Y : Expr) : Prop :=
  ∃ I Ls args nI K aux, e = mkAppN (.const I Ls) args ∧ nI ≤ args.size ∧
    (∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0) ∧ (K, aux) ∈ pairs ∧
    (K == replaceParamsVal params (mkAppRange (.const I Ls) 0 nI args) As) ∧
    Y = mkAppRange (mkAppN (.const aux lvls) As) nI args.size args

theorem NodeRep.mono {pairs pairs' : List (Expr × Name)} {lvls params As e Y}
    (h : NodeRep pairs lvls params As e Y) (hp : pairs ⊆ pairs') :
    NodeRep pairs' lvls params As e Y :=
  let ⟨I, Ls, args, nI, K, aux, h1, h2, h3, h4, h5, h6⟩ := h
  ⟨I, Ls, args, nI, K, aux, h1, h2, h3, hp h4, h5, h6⟩

/-- `Y` is `e` with some subterms `e'` replaced by `Y'` such that `Rep e' Y'`, as
`Expr.replaceNoCacheT` does. -/
inductive Replaced (Rep : Expr → Expr → Prop) : Expr → Expr → Prop
  | node : Rep e Y → Replaced Rep e Y
  | refl : Replaced Rep e e
  | app : Replaced Rep f f' → Replaced Rep a a' → Replaced Rep (.app f a) (.app f' a')
  | lam : Replaced Rep d d' → Replaced Rep b b' →
    Replaced Rep (.lam n d b bi) (.lam n d' b' bi)
  | forallE : Replaced Rep d d' → Replaced Rep b b' →
    Replaced Rep (.forallE n d b bi) (.forallE n d' b' bi)
  | letE : Replaced Rep t t' → Replaced Rep v v' → Replaced Rep b b' →
    Replaced Rep (.letE n t v b nd) (.letE n t' v' b' nd)
  | mdata : Replaced Rep b b' → Replaced Rep (.mdata m b) (.mdata m b')
  | proj : Replaced Rep b b' → Replaced Rep (.proj s i b) (.proj s i b')

theorem Replaced.mono {Rep Rep' : Expr → Expr → Prop} (H : Replaced Rep e Y)
    (h : ∀ e Y, Rep e Y → Rep' e Y) : Replaced Rep' e Y := by
  induction H with
  | node h' => exact .node (h _ _ h')
  | refl => exact .refl
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | lam _ _ ih1 ih2 => exact .lam ih1 ih2
  | forallE _ _ ih1 ih2 => exact .forallE ih1 ih2
  | letE _ _ _ ih1 ih2 ih3 => exact .letE ih1 ih2 ih3
  | mdata _ ih => exact .mdata ih
  | proj _ ih => exact .proj ih

theorem forIn_looseBVars {env : Environment} {args : Array Expr}
    {body : Nat → Bool × Bool → M (ForInStep (Bool × Bool))}
    (hbody : ∀ i r s st s', body i r env s = .ok (st, s') →
      s' = s ∧ ∃ b, st = .yield (b, r.2 || args[i]!.hasLooseBVars)) :
    ∀ {l : List Nat} {init s r s'}, forIn l init body env s = .ok (r, s') →
      s' = s ∧ (r.2 = false → init.2 = false ∧ ∀ i ∈ l, args[i]!.hasLooseBVars = false)
  | [], init, s, r, s', h => by cases h; exact ⟨rfl, fun h => ⟨h, nofun⟩⟩
  | i :: l, init, s, r, s', h => by
    rw [List.forIn_cons] at h
    obtain ⟨st, s₁, h1, h⟩ := bind_ok h
    obtain ⟨rfl, b, rfl⟩ := hbody _ _ _ _ _ h1
    obtain ⟨rfl, ih⟩ := forIn_looseBVars hbody h
    refine ⟨rfl, fun hr => ?_⟩
    obtain ⟨h2, h3⟩ := ih hr
    simp only [Bool.or_eq_false_iff] at h2
    exact ⟨h2.1, fun j hj => (List.mem_cons.1 hj).elim (· ▸ h2.2) (h3 j)⟩

theorem isNestedInductiveApp?_spec {env : Environment} {e : Expr} {s r s'}
    (h : isNestedInductiveApp? e env s = .ok (r, s')) :
    s' = s ∧ ∀ ci, r = some ci → ∃ fn ls, e.getAppFn = .const fn ls ∧
      env.find? fn = some (.inductInfo ci) ∧ ci.numParams ≤ e.getAppArgs.size ∧
      ∀ i < ci.numParams, e.getAppArgs[i]!.looseBVarRange' = 0 := by
  unfold isNestedInductiveApp? at h
  dsimp only at h
  split at h
  · cases h; exact ⟨rfl, nofun⟩
  generalize hfn : e.getAppFn = F at h
  cases F with
  | bvar | fvar | mvar | sort | app | lam | forallE | letE | lit | mdata | proj =>
    cases h; exact ⟨rfl, nofun⟩
  | const fn ls =>
    dsimp only at h
    obtain ⟨_, s₁, h1, h2⟩ := bind_ok h
    cases h1
    clear h
    generalize hci : env.find? fn = C at h2
    rcases C with _ | ⟨_ | _ | _ | _ | _ | ci | _ | _⟩
    all_goals try (cases h2; exact ⟨rfl, nofun⟩)
    · dsimp only at h2
      have h := h2; clear h2
      split at h
      · cases h; exact ⟨rfl, nofun⟩
      · rename_i hle
        obtain ⟨st, s₂, h1, h3⟩ := bind_ok h
        clear h
        rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h1
        obtain ⟨hs2, hl⟩ := forIn_looseBVars (args := e.getAppArgs) (fun i r s st s' h => by
          split at h <;>
          · obtain ⟨_, s₁, h1, h⟩ := bind_ok h
            cases h1
            split at h <;> (cases h; exact ⟨rfl, _, congrArg _ (Prod.ext rfl (by simp_all))⟩)) h1
        subst hs2
        split at h3
        · cases h3; exact ⟨rfl, nofun⟩
        · split at h3
          · obtain ⟨_, _, h1, _⟩ := bind_ok h3; cases h1
          · cases h3
            rename_i hl2
            refine ⟨rfl, fun ci' e' => ?_⟩
            cases e'
            refine ⟨fn, ls, rfl, hci, by omega, fun i hi => ?_⟩
            have := (hl (by simpa using hl2)).2 i (by simp; omega)
            simpa [Expr.hasLooseBVars] using this

theorem Chain.pres {env : Environment} {f : β → M γ} {R : β → γ → Prop}
    (hf : ∀ b st c st', f b env st = .ok (c, st') → st' = st ∧ R b c) :
    ∀ {l cs st st'}, Chain env f l cs st st' → st' = st ∧ List.Forall₂ R l cs := by
  intro l cs st st' H
  induction H with
  | nil => exact ⟨rfl, .nil⟩
  | cons h1 _ ih =>
    obtain ⟨rfl, h⟩ := hf _ _ _ _ h1
    exact ⟨ih.1, .cons h ih.2⟩

theorem mkUniqueName.loop_spec {n : Name} {env : Environment} {s : State}
    (i : Nat) (fuel : UInt64) {a s'} (h : mkUniqueName.loop n env s i fuel = .ok (a, s')) :
    env.contains a = false ∧ s'.nestedAux = s.nestedAux ∧ s'.newTypes = s.newTypes ∧
      s'.lvls = s.lvls ∧ s'.ngen = s.ngen := by
  rw [mkUniqueName.loop] at h
  split at h
  · split at h
    · cases h
    · exact mkUniqueName.loop_spec (i + 1) (fuel - 1) h
  · cases h; rename_i h; exact ⟨by simpa using h, rfl, rfl, rfl, rfl⟩
termination_by fuel.toNat
decreasing_by
  rename_i h
  have : fuel.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.1 (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _
    (by simpa [UInt64.le_iff_toNat_le] using Nat.one_le_iff_ne_zero.2 this)]
  simp; omega

theorem mkUniqueName_spec {n : Name} {env : Environment} {s : State} {a s'}
    (h : mkUniqueName n env s = .ok (a, s')) :
    env.contains a = false ∧ s'.nestedAux = s.nestedAux ∧ s'.newTypes = s.newTypes ∧
      s'.lvls = s.lvls ∧ s'.ngen = s.ngen := mkUniqueName.loop_spec _ _ h

theorem liftM_ok {x : Except Exception α} {env : Environment} {s : State} {a s'}
    (h : (liftM x : M α) env s = .ok (a, s')) : x = .ok a ∧ s' = s := by
  cases hx : x with
  | error => rw [hx] at h; cases h
  | ok a' => rw [hx] at h; cases h; exact ⟨rfl, rfl⟩

theorem get_ok {env : Environment} {n : Name} {ci : ConstantInfo}
    (h : env.get n = .ok ci) : env.find? n = some ci := by
  unfold Environment.get at h; split at h <;> cases h; assumption

theorem mkAppN_eq_mkAppList (f : Expr) (args : Array Expr) :
    mkAppN f args = Expr.mkAppList f args.toList := by
  rw [Expr.mkAppList_eq_foldl, Array.foldl_toList]; rfl

theorem replaceIfNested_spec {env : Environment} {lctx : LocalContext} {params As : Array Expr}
    (hAs : As.size = params.size) {e : Expr} (hfv : e.SuppIn (FVOnly (.fvar · ∈ As))) {s r s'}
    (h : replaceIfNested lctx params As e env s = .ok (r, s')) :
    Extends env lctx params As s s' ∧
      ∀ Y, r = some Y → NodeRep s'.nestedAux.toList s.lvls params As e Y := by
  unfold replaceIfNested at h
  obtain ⟨r₀, s₁, h1, h⟩ := bind_ok h
  obtain ⟨rfl, hI⟩ := isNestedInductiveApp?_spec h1
  rcases r₀ with _ | I_val
  · cases h; exact ⟨.refl, nofun⟩
  obtain ⟨fn, ls, hfn, hci, hle, hlb⟩ := hI _ rfl
  dsimp only at h
  rw [Expr.withApp_eq, hfn] at h
  dsimp only at h
  have he : e = mkAppN (.const fn ls) e.getAppArgs := by
    rw [mkAppN_eq_mkAppList, ← hfn, Expr.getAppArgs_toList, Expr.mkAppList_getAppArgsList]
  rw [if_pos hle] at h
  obtain ⟨Ip, s₂, h2, h⟩ := bind_ok h
  rw [replaceParams_eq hAs] at h2; cases h2
  obtain ⟨st, s₃, h3, h⟩ := bind_ok h
  cases h3
  generalize hfs : Array.findSome? _ s₁.nestedAux = F at h
  rcases F with _ | auxI
  · obtain ⟨env', s₄, h4, h⟩ := bind_ok h
    cases h4
    obtain ⟨res, s₅, h5, h⟩ := bind_ok h
    -- what the loop over the earlier type's block keeps
    let LI (result : Option Expr) (st : State) : Prop :=
      Extends env lctx params As s₁ st ∧
        ∀ Y, result = some Y → NodeRep st.nestedAux.toList s₁.lvls params As e Y
    have hloop : LI res s₅ := by
      refine Triple.forIn_list (I := LI) ?_ s₁ res s₅ h5 ⟨.refl, nofun⟩
      intro J_name hJmem result st x st' hb ⟨hE, hY⟩
      · 
        obtain ⟨ci, s₆, h6, hb⟩ := bind_ok hb
        obtain ⟨hg, hs6⟩ := liftM_ok h6
        subst s₆
        rcases ci with _ | _ | _ | _ | _ | J_info | _ | _
        case inductInfo =>
          obtain ⟨auxJ, s₇, h7, hb1⟩ := bind_ok hb
          obtain ⟨hfresh, hn7, ht7, hl7, hg7⟩ := mkUniqueName_spec h7
          obtain ⟨v, s₈, h8, hb2⟩ := bind_ok hb1
          obtain ⟨hv, hs8⟩ := liftM_ok h8
          subst s₈
          obtain ⟨JAs', s₉, h9, hb3⟩ := bind_ok hb2
          rw [replaceParams_eq hAs] at h9; cases h9
          obtain ⟨_, s₁₀, h10, hb4⟩ := bind_ok hb3
          cases h10
          -- the auxiliary type, and the state with it recorded
          have hfin {result' : Option Expr} {cs s₁₂} {T₀ : InductiveType} {K : Expr}
              (hcs : List.Forall₂ (fun Jc (c : Constructor) =>
                c.name = Jc.replacePrefix J_name auxJ ∧ ∃ ci v', env.find? Jc = some ci ∧
                  instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams ls)
                    I_val.numParams e.getAppArgs = .ok v' ∧ c.type = lctx.mkForall As v')
                J_info.ctors cs)
              (hT₀ : T₀ = { name := auxJ, type := lctx.mkForall As v, ctors := cs })
              (hK : K = replaceParamsVal params (mkAppRange (.const J_name ls) 0 I_val.numParams
                  e.getAppArgs) As)
              (hst : x = .yield result') (hs : st' = { s₁₂ with newTypes := s₁₂.newTypes.push T₀ })
              (hs₁₂ : s₁₂ = { s₇ with nestedAux := s₇.nestedAux.push (K, auxJ) })
              (hres : ∀ Y, result' = some Y → result = some Y ∨
                (J_name = fn ∧ Y = mkAppRange (mkAppN (.const auxJ s₁.lvls) As) I_val.numParams
                  e.getAppArgs.size e.getAppArgs)) :
              LI (stepVal x) st' := by
            subst hst hs hs₁₂
            have hE' : Extends env lctx params As st
                { s₇ with nestedAux := s₇.nestedAux.push (K, auxJ), newTypes := s₇.newTypes.push T₀ } := by
              refine ⟨hl7, hg7, [((K, auxJ), T₀)], by simp [hn7], by simp [ht7], ?_⟩
              simp only [List.mem_singleton]
              rintro _ rfl
              subst hT₀ hK
              exact ⟨rfl, J_name, ls, e.getAppArgs, I_val.numParams, J_info, v, rfl, get_ok hg, hle,
                fun i hi a ha => by have := hlb i hi; rwa [getElem!_def, ha] at this,
                hfv.getAppArgs, hv, rfl, hfresh, hcs, fn, I_val, hci, hJmem, rfl⟩
            refine ⟨hE.trans hE', fun Y hYr => ?_⟩
            have hsub := hE'.sub
            rcases hres Y hYr with hY' | ⟨rfl, rfl⟩
            · exact (hY Y hY').mono hsub
            · exact ⟨J_name, ls, e.getAppArgs, I_val.numParams, K, auxJ, hfn ▸ he, hle,
                fun i hi a ha => by have := hlb i hi; rwa [getElem!_def, ha] at this,
                by simp, by subst hK; exact Expr.eqv_refl _, rfl⟩
          split at hb4
          · rename_i hJ
            obtain ⟨st₁, s₁₁, h11, hb5⟩ := bind_ok hb4
            cases h11
            obtain ⟨cs, s₁₂, h12, hb6⟩ := bind_ok hb5
            obtain ⟨hs12, hcs⟩ := Chain.pres (R := fun Jc (c : Constructor) =>
              c.name = Jc.replacePrefix J_name auxJ ∧ ∃ ci v', env.find? Jc = some ci ∧
                instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams ls)
                  I_val.numParams e.getAppArgs = .ok v' ∧ c.type = lctx.mkForall As v')
              (fun Jc st c st' h => by
              obtain ⟨ci, s₆, h6, h⟩ := bind_ok h
              obtain ⟨hg, hs6⟩ := liftM_ok h6
              subst s₆
              obtain ⟨v', s₇', h7, h⟩ := bind_ok h
              obtain ⟨hv, hs7⟩ := liftM_ok h7
              subst s₇'
              cases h
              exact ⟨rfl, rfl, ci, v', get_ok hg, hv, rfl⟩) (mapM_ok h12)
            obtain ⟨_, s₁₃, h13, hb7⟩ := bind_ok hb6
            cases h13; cases hb7
            refine hfin hcs rfl rfl rfl (by rw [hs12]) rfl fun Y hY => ?_
            cases hY
            exact .inr ⟨by simpa using hJ, by simp only [hl7, hE.1]⟩
          · obtain ⟨cs, s₁₂, h12, hb6⟩ := bind_ok hb4
            obtain ⟨hs12, hcs⟩ := Chain.pres (R := fun Jc (c : Constructor) =>
              c.name = Jc.replacePrefix J_name auxJ ∧ ∃ ci v', env.find? Jc = some ci ∧
                instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams ls)
                  I_val.numParams e.getAppArgs = .ok v' ∧ c.type = lctx.mkForall As v')
              (fun Jc st c st' h => by
              obtain ⟨ci, s₆, h6, h⟩ := bind_ok h
              obtain ⟨hg, hs6⟩ := liftM_ok h6
              subst s₆
              obtain ⟨v', s₇', h7, h⟩ := bind_ok h
              obtain ⟨hv, hs7⟩ := liftM_ok h7
              subst s₇'
              cases h
              exact ⟨rfl, rfl, ci, v', get_ok hg, hv, rfl⟩) (mapM_ok h12)
            obtain ⟨_, s₁₃, h13, hb7⟩ := bind_ok hb6
            cases h13; cases hb7
            exact hfin hcs rfl rfl rfl (by rw [hs12]) rfl fun Y hY => .inl hY
        all_goals
          obtain ⟨_, s₇, h7, hb⟩ := bind_ok hb
          cases h7; cases hb
          exact ⟨hE, hY⟩
    split at h
    · cases h; exact hloop
    · cases h; exact ⟨hloop.1, nofun⟩
  · cases h
    refine ⟨.refl, fun Y hY => ?_⟩; cases hY
    obtain ⟨⟨K, aux⟩, hmem, hK⟩ := Array.exists_of_findSome?_eq_some hfs
    simp only at hK
    split at hK <;> cases hK
    rename_i hKe
    exact ⟨fn, ls, e.getAppArgs, I_val.numParams, K, auxI, he, hle, fun i hi a ha => by
      have := hlb i hi; rwa [getElem!_def, ha] at this, Array.mem_toList_iff.2 hmem, hKe, rfl⟩

theorem replaceAllNested_spec {env : Environment} {lctx : LocalContext} {params As : Array Expr}
    (hAs : As.size = params.size) : ∀ (e : Expr) {s Y s'},
    e.SuppIn (FVOnly (.fvar · ∈ As)) →
    replaceAllNested lctx params As e env s = .ok (Y, s') →
    Extends env lctx params As s s' ∧
      Replaced (NodeRep s'.nestedAux.toList s.lvls params As) e Y := by
  intro e
  unfold replaceAllNested Expr.replaceM
  induction e with
  | bvar | fvar | mvar | sort | const | lit =>
    intro s Y s' hfv h
    unfold Expr.replaceNoCacheT at h
    obtain ⟨r, s₁, hf, h⟩ := bind_ok h
    obtain ⟨E, hr⟩ := replaceIfNested_spec hAs hfv hf
    cases r with
    | some Y' => cases h; exact ⟨E, .node (hr _ rfl)⟩
    | none => cases h; exact ⟨E, .refl⟩
  | app f a ih1 ih2 =>
    intro s Y s' hfv h
    unfold Expr.replaceNoCacheT at h
    obtain ⟨r, s₁, hf, h⟩ := bind_ok h
    obtain ⟨E, hr⟩ := replaceIfNested_spec hAs hfv hf
    cases r with
    | some Y' => cases h; exact ⟨E, .node (hr _ rfl)⟩
    | none =>
      obtain ⟨f', s₂, h1, h⟩ := bind_ok h
      obtain ⟨a', s₃, h2, h⟩ := bind_ok h
      cases h
      obtain ⟨E1, R1⟩ := ih1 hfv.1 h1
      obtain ⟨E2, R2⟩ := ih2 hfv.2 h2
      have lv1 := E.1; have lv2 := E1.1
      refine ⟨E.trans (E1.trans E2), ?_⟩
      simp only [Expr.updateApp!]
      refine .app (R1.mono fun _ _ h => ?_) (R2.mono fun _ _ h => ?_)
      · rw [lv1] at h; exact h.mono E2.sub
      · rw [lv2, lv1] at h; exact h
  | lam n d b bi ih1 ih2 | forallE n d b bi ih1 ih2 =>
    intro s Y s' hfv h
    unfold Expr.replaceNoCacheT at h
    obtain ⟨r, s₁, hf, h⟩ := bind_ok h
    obtain ⟨E, hr⟩ := replaceIfNested_spec hAs hfv hf
    cases r with
    | some Y' => cases h; exact ⟨E, .node (hr _ rfl)⟩
    | none =>
      obtain ⟨d', s₂, h1, h⟩ := bind_ok h
      obtain ⟨b', s₃, h2, h⟩ := bind_ok h
      cases h
      obtain ⟨E1, R1⟩ := ih1 hfv.1 h1
      obtain ⟨E2, R2⟩ := ih2 hfv.2 h2
      have lv1 := E.1; have lv2 := E1.1
      refine ⟨E.trans (E1.trans E2), ?_⟩
      first
      | (simp only [Expr.updateLambdaE!, Expr.updateLambda!]
         refine .lam (R1.mono fun _ _ h => ?_) (R2.mono fun _ _ h => ?_))
      | (simp only [Expr.updateForallE!, Expr.updateForall!]
         refine .forallE (R1.mono fun _ _ h => ?_) (R2.mono fun _ _ h => ?_))
      · rw [lv1] at h; exact h.mono E2.sub
      · rw [lv2, lv1] at h; exact h
  | letE n t v b nd ih1 ih2 ih3 =>
    intro s Y s' hfv h
    unfold Expr.replaceNoCacheT at h
    obtain ⟨r, s₁, hf, h⟩ := bind_ok h
    obtain ⟨E, hr⟩ := replaceIfNested_spec hAs hfv hf
    cases r with
    | some Y' => cases h; exact ⟨E, .node (hr _ rfl)⟩
    | none =>
      obtain ⟨t', s₂, h1, h⟩ := bind_ok h
      obtain ⟨v', s₃, h2, h⟩ := bind_ok h
      obtain ⟨b', s₄, h3, h⟩ := bind_ok h
      cases h
      obtain ⟨E1, R1⟩ := ih1 hfv.1 h1
      obtain ⟨E2, R2⟩ := ih2 hfv.2.1 h2
      obtain ⟨E3, R3⟩ := ih3 hfv.2.2 h3
      have lv1 := E.1; have lv2 := E1.1; have lv3 := E2.1
      refine ⟨E.trans (E1.trans (E2.trans E3)), ?_⟩
      simp only [Expr.updateLet!]
      refine .letE (R1.mono fun _ _ h => ?_) (R2.mono fun _ _ h => ?_) (R3.mono fun _ _ h => ?_)
      · rw [lv1] at h; exact h.mono (E2.sub.trans E3.sub)
      · rw [lv2, lv1] at h; exact h.mono E3.sub
      · rw [lv3, lv2, lv1] at h; exact h
  | mdata m b ih | proj _ _ b ih =>
    intro s Y s' hfv h
    unfold Expr.replaceNoCacheT at h
    obtain ⟨r, s₁, hf, h⟩ := bind_ok h
    obtain ⟨E, hr⟩ := replaceIfNested_spec hAs hfv hf
    cases r with
    | some Y' => cases h; exact ⟨E, .node (hr _ rfl)⟩
    | none =>
      obtain ⟨b', s₂, h1, h⟩ := bind_ok h
      cases h
      obtain ⟨E1, R1⟩ := ih hfv h1
      have lv1 := E.1
      refine ⟨E.trans E1, ?_⟩
      first
      | (simp only [Expr.updateMData!]; refine .mdata (R1.mono fun _ _ h => ?_))
      | (simp only [Expr.updateProj!]; refine .proj (R1.mono fun _ _ h => ?_))
      rw [lv1] at h; exact h

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem Opens.suppIn {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') :
    ∀ {P : FVarId → Prop}, ty.SuppIn (FVOnly P) → ty'.SuppIn (FVOnly fun x => P x ∨ x ∈ xs) := by
  induction H with
  | nil =>
    intro P h
    exact Expr.SuppIn.mono (S := FVOnly P) (S' := FVOnly fun x => P x ∨ x ∈ [])
      ⟨fun _ h => Or.inl h, fun _ => id, fun _ => id⟩ h
  | @cons lctx x nm dom bi body xs lctx' ty' _ ih =>
    intro P h
    have h1 : (body.instantiate1 (.fvar x)).SuppIn (FVOnly fun y => P y ∨ y = x) := by
      rw [Expr.instantiate1_eq]
      exact Expr.SuppIn.instantiate1 (S := FVOnly fun y => P y ∨ y = x) (a := .fvar x) (Or.inr rfl)
        (Expr.SuppIn.mono (S := FVOnly P) (S' := FVOnly fun y => P y ∨ y = x)
          ⟨fun _ h => Or.inl h, fun _ => id, fun _ => id⟩ h.2)
    refine Expr.SuppIn.mono (S := FVOnly fun y => (P y ∨ y = x) ∨ y ∈ xs)
      (S' := FVOnly fun y => P y ∨ y ∈ x :: xs)
      ⟨fun y hy => ?_, fun _ => id, fun _ => id⟩ (ih h1)
    rcases hy with (hy | rfl) | hy
    · exact Or.inl hy
    · exact Or.inr (.head _)
    · exact Or.inr (.tail _ hy)

/-- The constructor `ctorStep` processes, opened at fresh parameters, with its nested occurrences
replaced, closed again. -/
theorem ctorStep_spec {env : Environment} {nparams : Nat} {params : Array Expr} {ctor : Constructor}
    {s c s'} (hP : params.size = nparams) (hc : ctor.type.SuppIn (FVOnly fun _ => False))
    (h : ctorStep nparams params ctor env s = .ok (c, s')) :
    ∃ lctx body Y, Opens {} ctor.type (freshIds s.ngen nparams) lctx body ∧
      body.SuppIn (FVOnly (· ∈ freshIds s.ngen nparams)) ∧
      Extends env lctx params ((freshIds s.ngen nparams).map .fvar).toArray
        { s with ngen := advance s.ngen nparams } s' ∧
      Replaced (NodeRep s'.nestedAux.toList s.lvls params
        ((freshIds s.ngen nparams).map .fvar).toArray) body Y ∧
      c.name = ctor.name ∧
      c.type = lctx.mkForall ((freshIds s.ngen nparams).map .fvar).toArray Y := by
  unfold ctorStep withParams at h
  obtain ⟨lctx, body, ho, hk⟩ := withParams.loop_open _ _ _ _ _ _ _ h
  simp only [List.size_toArray, List.length_map, freshIds_length, Array.empty_append,
    beq_self_eq_true, ↓reduceIte] at hk
  obtain ⟨Y, s₁, h1, hk⟩ := bind_ok hk
  cases hk
  have hfv : body.SuppIn (FVOnly (· ∈ freshIds s.ngen nparams)) :=
    Expr.SuppIn.mono (S := FVOnly fun x => False ∨ x ∈ freshIds s.ngen nparams)
      (S' := FVOnly (· ∈ freshIds s.ngen nparams))
      ⟨fun _ h => Or.resolve_left h id, fun _ => id, fun _ => id⟩ (ho.suppIn hc)
  obtain ⟨E, R⟩ := replaceAllNested_spec (by simp [hP, freshIds_length]) body
    (Expr.SuppIn.mono (S := FVOnly (· ∈ freshIds s.ngen nparams))
      (S' := FVOnly (.fvar · ∈ ((freshIds s.ngen nparams).map Expr.fvar).toArray))
      ⟨fun x hx => by simpa using hx, fun _ => id, fun _ => id⟩ hfv) h1
  exact ⟨lctx, body, Y, ho, hfv, E, R, rfl, rfl⟩

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

theorem forIn_peel : ∀ {l : List Nat} {e r : Expr}, forIn (m := Except Exception) l e
      (fun _ e => match e with
        | .forallE _ _ body _ => pure (ForInStep.yield body)
        | _ => do throw illFormed; pure (ForInStep.yield e)) = .ok r →
      peel l.length e = some r
  | [], e, r, h => by cases h; rfl
  | i :: l, e, r, h => by
    rw [List.forIn_cons] at h
    cases e with
    | forallE => exact forIn_peel (l := l) h
    | _ => cases h

theorem instantiateForallParams_ok {e : Expr} {hi : Nat} {ps : Array Expr} {v}
    (h : instantiateForallParams e hi ps = .ok v) :
    ∃ b, peel hi e = some b ∧ v = b.instantiateRevRange 0 hi ps := by
  unfold instantiateForallParams at h
  dsimp only at h
  rw [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  generalize hf : forIn (m := Except Exception) (ρ := List Nat) _ e _ = F at h
  rcases F with _ | b
  · cases h
  · cases h
    refine ⟨b, ?_, rfl⟩
    have := forIn_peel hf
    simpa [Std.Legacy.Range.size] using this

theorem _root_.Lean.Level.LParamsIn.true {l : Level} : l.LParamsIn fun _ => True := by
  induction l <;> simp_all [Level.LParamsIn]

theorem SuppIn.instantiateLevelParams {P : FVarId → Prop} {e : Expr} {ps ls}
    (h : e.SuppIn (FVOnly P)) : (e.instantiateLevelParams ps ls).SuppIn (FVOnly P) := by
  rw [Expr.instantiateLevelParams_eq]
  generalize (!ps.isEmpty && !ls.isEmpty) = red
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', Expr.SuppIn, Level.LParamsIn.true]

theorem instantiateLevelParams_looseBVarRange (e : Expr) (ps ls) :
    (e.instantiateLevelParams ps ls).looseBVarRange' = e.looseBVarRange' := by
  rw [Expr.instantiateLevelParams_eq]
  generalize (!ps.isEmpty && !ls.isEmpty) = red
  induction e <;> simp_all [Expr.instantiateLevelParamsCore', Expr.looseBVarRange']

theorem SuppIn.setBody {S : Supp} {b : Expr} (hb : b.SuppIn S) :
    ∀ {n e}, e.SuppIn S → (setBody n e b).SuppIn S
  | 0, _, _ => hb
  | n + 1, .forallE .., h => ⟨h.1, SuppIn.setBody hb (n := n) h.2⟩
  | _ + 1, .bvar .., h | _ + 1, .fvar .., h | _ + 1, .mvar .., h | _ + 1, .sort .., h
  | _ + 1, .const .., h | _ + 1, .app .., h | _ + 1, .lam .., h | _ + 1, .letE .., h
  | _ + 1, .lit .., h | _ + 1, .mdata .., h | _ + 1, .proj .., h => h

theorem _root_.Lean.LocalContext.find?_empty {x : FVarId} : ({} : LocalContext).find? x = none := by
  exact LocalContext.WF.nil.find?_eq_find?_toList.trans rfl

/-- Closing a telescope opened at `xs` over a body mentioning only `xs` leaves no free
variable. -/
theorem abstract1_looseBVarRange {x : FVarId} : ∀ {e : Expr} {k},
    (Expr.abstract1 x e k).looseBVarRange' ≤ max (e.looseBVarRange' + 1) (k + 1) := by
  intro e; induction e with
  | bvar i => intro k; simp only [Expr.abstract1, Expr.looseBVarRange']; split <;> omega
  | fvar v => intro k; simp only [Expr.abstract1]; split <;> simp [Expr.looseBVarRange']
  | app f a ihf iha =>
    intro k; simp only [Expr.abstract1, Expr.looseBVarRange']
    have := @ihf k; have := @iha k; omega
  | lam n t b bi iht ihb | forallE n t b bi iht ihb =>
    intro k; simp only [Expr.abstract1, Expr.looseBVarRange']
    have := @iht k; have := @ihb (k + 1); omega
  | letE n t v b bi iht ihv ihb =>
    intro k; simp only [Expr.abstract1, Expr.looseBVarRange']
    have := @iht k; have := @ihv k; have := @ihb (k + 1); omega
  | mdata m e ih | proj s i e ih => intro k; simp only [Expr.abstract1, Expr.looseBVarRange']; exact ih
  | _ => intro k; simp [Expr.abstract1, Expr.looseBVarRange']

theorem abstractList_looseBVarRange : ∀ {xs : List FVarId} {e : Expr},
    (Expr.abstractList e xs).looseBVarRange' ≤ e.looseBVarRange' + xs.length
  | [], _ => by simp
  | x :: xs, e => by
    simp only [Expr.abstractList, List.length_cons]
    have := abstractList_looseBVarRange (xs := xs) (e := Expr.abstract1 x e 0)
    have := abstract1_looseBVarRange (x := x) (e := e) (k := 0)
    omega

theorem peel_looseBVarRange : ∀ {n e b k}, peel n e = some b → e.looseBVarRange' ≤ k →
    b.looseBVarRange' ≤ k + n
  | 0, _, _, _, h, he => by cases h; exact he
  | n + 1, .forallE _ _ body _, b, k, h, he => by
    simp only [peel] at h; simp only [Expr.looseBVarRange', Nat.max_le] at he
    have := peel_looseBVarRange (e := body) (k := k + 1) h (by omega); omega
  | _ + 1, .bvar .., _, _, h, _ | _ + 1, .fvar .., _, _, h, _ | _ + 1, .mvar .., _, _, h, _
  | _ + 1, .sort .., _, _, h, _ | _ + 1, .const .., _, _, h, _ | _ + 1, .app .., _, _, h, _
  | _ + 1, .lam .., _, _, h, _ | _ + 1, .letE .., _, _, h, _ | _ + 1, .lit .., _, _, h, _
  | _ + 1, .mdata .., _, _, h, _ | _ + 1, .proj .., _, _, h, _ => by simp [peel] at h

theorem setBody_looseBVarRange {b : Expr} : ∀ {n e k}, e.looseBVarRange' ≤ k →
    b.looseBVarRange' ≤ k + n → (setBody n e b).looseBVarRange' ≤ k
  | 0, _, _, _, hb => hb
  | n + 1, .forallE _ d body _, k, he, hb => by
    simp only [setBody, Expr.looseBVarRange', Nat.max_le] at he ⊢
    have := setBody_looseBVarRange (b := b) (e := body) (n := n) (k := k + 1) (by omega)
      (by omega)
    exact ⟨he.1, by omega⟩
  | _ + 1, .bvar .., _, he, _ | _ + 1, .fvar .., _, he, _ | _ + 1, .mvar .., _, he, _
  | _ + 1, .sort .., _, he, _ | _ + 1, .const .., _, he, _ | _ + 1, .app .., _, he, _
  | _ + 1, .lam .., _, he, _ | _ + 1, .letE .., _, he, _ | _ + 1, .lit .., _, he, _
  | _ + 1, .mdata .., _, he, _ | _ + 1, .proj .., _, he, _ => he

/-- Closing a closed telescope opened at `xs` over a closed body mentioning only `xs` leaves no
free variable and no loose one. -/
theorem Opens.mkForall_closed {ty xs lctx body} (H : Opens {} ty xs lctx body) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, ty.SuppIn (FVOnly (· ≠ x))) (hty : ty.SuppIn (FVOnly fun _ => False))
    (hcl : ty.looseBVarRange' = 0)
    {Z : Expr} (hZ : Z.SuppIn (FVOnly (· ∈ xs))) (hZc : Z.looseBVarRange' = 0) :
    (lctx.mkForall (xs.map .fvar).toArray Z).SuppIn (FVOnly fun _ => False) ∧
      (lctx.mkForall (xs.map .fvar).toArray Z).looseBVarRange' = 0 := by
  have : (xs.map Expr.fvar).toArray = ⟨xs.map .fvar⟩ := rfl
  rw [this, H.mkForall .nil (fun _ _ => LocalContext.find?_empty) hnd hx hcl Z hZc]
  refine ⟨SuppIn.setBody ?_ hty, Nat.le_zero.1 (setBody_looseBVarRange (Nat.le_of_eq hcl) ?_)⟩
  · exact Expr.SuppIn.abstractList (S := FVOnly fun _ => False)
      (Expr.SuppIn.mono (S := FVOnly (· ∈ xs)) (S' := ⟨fun x => False ∨ x ∈ xs, fun _ => True,
        fun _ => True⟩) ⟨fun _ h => Or.inr h, fun _ => id, fun _ => id⟩ hZ)
  · have := abstractList_looseBVarRange (xs := xs) (e := Z); omega

theorem forall₂_mem_right {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {b}, b ∈ l₂ → ∃ a ∈ l₁, R a b
  | _, _, .cons h _, _, .head _ => ⟨_, .head _, h⟩
  | _, _, .cons _ t, _, .tail _ hb => let ⟨a, ha, h⟩ := forall₂_mem_right t hb; ⟨a, .tail _ ha, h⟩

/-- Every constant of `env` has a type without free variables, as the types of a translated
environment do. -/
def EnvClosed (env : Environment) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ci.type.SuppIn (FVOnly fun _ => False) ∧ ci.type.looseBVarRange' = 0

theorem instantiateForallParams_suppIn {e : Expr} {hi : Nat} {args : Array Expr} {v}
    {P : FVarId → Prop} (h : instantiateForallParams e hi args = .ok v)
    (he : e.SuppIn (FVOnly P)) (ha : ∀ a ∈ args, a.SuppIn (FVOnly P)) :
    v.SuppIn (FVOnly P) := by
  obtain ⟨b, hb, rfl⟩ := instantiateForallParams_ok h
  exact (SuppIn.peel hb he).instantiateRevRange ha

/-- A type with no free or loose variables in its type or its constructors' types. -/
def TypeClosed (T : InductiveType) : Prop :=
  T.type.SuppIn (FVOnly fun _ => False) ∧ T.type.looseBVarRange' = 0 ∧
    ∀ c ∈ T.ctors, c.type.SuppIn (FVOnly fun _ => False) ∧ c.type.looseBVarRange' = 0

/-- The types an auxiliary type is created with mention no free or loose variable. -/
theorem Created.closed {env : Environment} (henv : EnvClosed env) {cty xs lctx body}
    (H : Opens {} cty xs lctx body) (hnd : xs.Nodup) (hx : ∀ x ∈ xs, cty.SuppIn (FVOnly (· ≠ x)))
    (hty : cty.SuppIn (FVOnly fun _ => False)) (htc : cty.looseBVarRange' = 0) {params K T₀}
    (hC : Created env lctx params (xs.map .fvar).toArray K T₀) :
    TypeClosed T₀ := by
  obtain ⟨J, Ls, args, nI, Jv, v, -, hJ, hnI, hlb, hargs, hv, hT, -, hcs, -⟩ := hC
  have hargs' : ∀ a ∈ args, a.SuppIn (FVOnly (· ∈ xs)) := fun a ha =>
    Expr.SuppIn.mono (S := FVOnly (.fvar · ∈ (xs.map Expr.fvar).toArray)) (S' := FVOnly (· ∈ xs))
      ⟨fun _ h => by simpa using h, fun _ => id, fun _ => id⟩ (hargs a ha)
  have hcl {ci : ConstantInfo} {v'} (hci : ci.type.SuppIn (FVOnly fun _ => False))
      (h : instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams Ls) nI args =
        .ok v') : v'.SuppIn (FVOnly (· ∈ xs)) :=
    instantiateForallParams_suppIn h (SuppIn.instantiateLevelParams (Expr.SuppIn.mono
      (S := FVOnly fun _ => False) (S' := FVOnly (· ∈ xs))
      ⟨fun _ h => False.elim h, fun _ => id, fun _ => id⟩ hci)) hargs'
  have hlc {ci : ConstantInfo} {v'} (hci : ci.type.looseBVarRange' = 0)
      (h : instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams Ls) nI args =
        .ok v') : v'.looseBVarRange' = 0 := by
    obtain ⟨b, hb, rfl⟩ := instantiateForallParams_ok h
    have hb' := peel_looseBVarRange (k := 0) hb (Nat.le_of_eq
      ((instantiateLevelParams_looseBVarRange _ _ _).trans hci))
    have hex : ∀ a ∈ (args.extract 0 nI).toList, a.looseBVarRange' = 0 := by
      intro a ha
      rw [Array.toList_extract] at ha
      simp [List.extract] at ha
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
      exact hlb i (by simp at hi; omega) _ (by simp [List.getElem_take])
    rw [Expr.instantiateRevRange_eq, Expr.instantiateRev_eq_instantiateList
      (fun a ha => hex a (Array.mem_toList_iff.2 ha))]
    have := Expr.instantiateList_looseBVarRange (n := 0) (k := 0) (e := b)
      (as := (args.extract 0 nI).toList.reverse) (by simp; omega)
      (fun a ha => Nat.le_of_eq (hex a (List.mem_reverse.1 ha)))
    omega
  have hcons {n : Name} {ci : ConstantInfo} {v'} (h1 : env.find? n = some ci)
      (h2 : instantiateForallParams (ci.type.instantiateLevelParams ci.levelParams Ls) nI args =
        .ok v') :=
    H.mkForall_closed hnd hx hty htc (hcl (henv _ ci h1).1 h2) (hlc (henv _ ci h1).2 h2)
  refine ⟨hT ▸ (hcons hJ hv).1, hT ▸ (hcons hJ hv).2, fun c hc => ?_⟩
  obtain ⟨Jc, -, ⟨-, ci, v', hci, hv', hct⟩⟩ := forall₂_mem_right hcs hc
  exact hct ▸ hcons hci hv'



/-- The auxiliary type `p.2`, recorded under the key `p.1.1` and the name `p.1.2`: created while
processing a constructor of type `cty`, opened at the fresh variables `xs` in `lctx`. -/
def AuxMade (env : Environment) (params : Array Expr) (nparams : Nat)
    (p : (Expr × Name) × InductiveType) : Prop :=
  p.2.name = p.1.2 ∧ ∃ cty xs lctx body, Opens {} cty xs lctx body ∧ xs.length = nparams ∧
    xs.Nodup ∧ (∀ x ∈ xs, cty.SuppIn (FVOnly (· ≠ x))) ∧ (∀ x ∈ xs, .fvar x ∉ params) ∧
    cty.SuppIn (FVOnly fun _ => False) ∧ cty.looseBVarRange' = 0 ∧
    Created env lctx params (xs.map .fvar).toArray p.1.1 p.2

/-- The constructor `c₀` as `run` leaves it: opened at fresh variables `xs`, its nested occurrences
replaced by auxiliary types recorded in `pairs`, and closed again. -/
def CtorDone (pairs : List (Expr × Name)) (lvls : List Level) (params : Array Expr)
    (nparams : Nat) (c₀ c : Constructor) : Prop :=
  c.name = c₀.name ∧ ∃ xs lctx body Y, Opens {} c₀.type xs lctx body ∧ xs.length = nparams ∧
    xs.Nodup ∧ (∀ x ∈ xs, c₀.type.SuppIn (FVOnly (· ≠ x))) ∧ (∀ x ∈ xs, .fvar x ∉ params) ∧
    body.SuppIn (FVOnly (· ∈ xs)) ∧
    Replaced (NodeRep pairs lvls params (xs.map .fvar).toArray) body Y ∧
    c.type = lctx.mkForall (xs.map .fvar).toArray Y

/-- The type `T₀` as `run` leaves it: its constructors processed. -/
def TypeDone (pairs : List (Expr × Name)) (lvls : List Level) (params : Array Expr)
    (nparams : Nat) (T₀ T : InductiveType) : Prop :=
  T.name = T₀.name ∧ T.type = T₀.type ∧ List.Forall₂ (CtorDone pairs lvls params nparams) T₀.ctors T.ctors

theorem CtorDone.mono {pairs pairs' : List (Expr × Name)} {lvls params nparams c₀ c}
    (H : CtorDone pairs lvls params nparams c₀ c) (h : pairs ⊆ pairs') :
    CtorDone pairs' lvls params nparams c₀ c :=
  let ⟨h0, xs, lctx, body, Y, h1, h2, h3, h4, h5, h6, h7, h8⟩ := H
  ⟨h0, xs, lctx, body, Y, h1, h2, h3, h4, h5, h6, h7.mono fun _ _ h' => h'.mono h, h8⟩

theorem TypeDone.mono {pairs pairs' : List (Expr × Name)} {lvls params nparams T₀ T}
    (H : TypeDone pairs lvls params nparams T₀ T) (h : pairs ⊆ pairs') :
    TypeDone pairs' lvls params nparams T₀ T :=
  ⟨H.1, H.2.1, Lean4Lean.List.Forall₂.imp (fun _ _ H' => H'.mono h) H.2.2⟩

/-- How `run`'s state grows while it processes constructors. -/
def Grows (env : Environment) (params : Array Expr) (nparams : Nat) (s s' : State) : Prop :=
  s'.lvls = s.lvls ∧ s.ngen ≤ s'.ngen ∧ ∃ new : List ((Expr × Name) × InductiveType),
    s'.nestedAux.toList = s.nestedAux.toList ++ new.map (·.1) ∧
    s'.newTypes.toList = s.newTypes.toList ++ new.map (·.2) ∧
    ∀ p ∈ new, AuxMade env params nparams p ∧ TypeClosed p.2

theorem Grows.refl {env params nparams} {s : State} : Grows env params nparams s s :=
  ⟨rfl, NameGenerator.LE.rfl, [], by simp, by simp, nofun⟩

theorem Grows.trans {env params nparams} {s₁ s₂ s₃ : State} (h₁ : Grows env params nparams s₁ s₂)
    (h₂ : Grows env params nparams s₂ s₃) : Grows env params nparams s₁ s₃ := by
  obtain ⟨a1, b1, n1, c1, d1, e1⟩ := h₁
  obtain ⟨a2, b2, n2, c2, d2, e2⟩ := h₂
  refine ⟨a2.trans a1, b1.trans b2, n1 ++ n2, by simp [c1, c2], by simp [d1, d2], ?_⟩
  intro p hp; rcases List.mem_append.1 hp with h | h
  · exact e1 p h
  · exact e2 p h

theorem Grows.sub {env params nparams} {s s' : State} (h : Grows env params nparams s s') :
    s.nestedAux.toList ⊆ s'.nestedAux.toList := by
  obtain ⟨-, -, _, h, -⟩ := h; rw [h]; exact List.subset_append_left _ _

/-- The fvars `params` stand for are reserved. -/
def ParamsReserved (g : NameGenerator) (params : Array Expr) : Prop :=
  ∀ p ∈ params, ∃ x, p = .fvar x ∧ g.Reserves x

theorem ctorStep_grows {env : Environment} (henv : EnvClosed env) {nparams : Nat}
    {params : Array Expr} {ctor : Constructor} {s c s'} (hP : params.size = nparams)
    (hpr : ParamsReserved s.ngen params) (hc : ctor.type.SuppIn (FVOnly fun _ => False))
    (hcl : ctor.type.looseBVarRange' = 0)
    (h : ctorStep nparams params ctor env s = .ok (c, s')) :
    Grows env params nparams s s' ∧ CtorDone s'.nestedAux.toList s.lvls params nparams ctor c := by
  obtain ⟨lctx, body, Y, ho, hfv, E, R, hn, hty⟩ := ctorStep_spec hP hc h
  have hnd := freshIds_nodup (g := s.ngen) (n := nparams)
  have hx : ∀ x ∈ freshIds s.ngen nparams, ctor.type.SuppIn (FVOnly (· ≠ x)) := fun x _ =>
    Expr.SuppIn.mono (S := FVOnly fun _ => False) (S' := FVOnly (· ≠ x))
      ⟨fun _ h => False.elim h, fun _ => id, fun _ => id⟩ hc
  have hpx : ∀ x ∈ freshIds s.ngen nparams, .fvar x ∉ params := by
    intro x hx hp
    obtain ⟨y, hy, hr⟩ := hpr _ hp
    cases hy
    exact (freshIds_reserves hx).2 hr
  obtain ⟨hl, hg, new, h1, h2, h3⟩ := E
  refine ⟨⟨hl, ?_, new, h1, h2, fun p hp => ?_⟩, hn, _, lctx, body, Y, ho, freshIds_length, hnd, hx,
    hpx, hfv, R, hty⟩
  · rw [hg]; exact le_advance
  · obtain ⟨hp1, hp2⟩ := h3 p hp
    exact ⟨⟨hp1, _, _, lctx, body, ho, freshIds_length, hnd, hx, hpx, hc, hcl, hp2⟩,
      Created.closed henv ho hnd hx hc hcl hp2⟩

theorem ctors_grows {env : Environment} (henv : EnvClosed env) {nparams : Nat}
    {params : Array Expr} (hP : params.size = nparams) :
    ∀ {cs₀ cs s s'}, Chain env (ctorStep nparams params) cs₀ cs s s' →
      ParamsReserved s.ngen params →
      (∀ c ∈ cs₀, c.type.SuppIn (FVOnly fun _ => False) ∧ c.type.looseBVarRange' = 0) →
      Grows env params nparams s s' ∧
        List.Forall₂ (CtorDone s'.nestedAux.toList s.lvls params nparams) cs₀ cs := by
  intro cs₀ cs s s' H
  induction H with
  | nil => exact fun _ _ => ⟨.refl, .nil⟩
  | cons h1 _ ih =>
    intro hpr hc
    obtain ⟨G1, D1⟩ := ctorStep_grows henv hP hpr (hc _ (.head _)).1 (hc _ (.head _)).2 h1
    obtain ⟨G2, D2⟩ := ih (fun p hp => let ⟨x, h, hr⟩ := hpr p hp; ⟨x, h, hr.mono G1.2.1⟩)
      fun c hc' => hc c (.tail _ hc')
    refine ⟨G1.trans G2, .cons (D1.mono G2.sub) ?_⟩
    rw [G1.1] at D2; exact D2

/-- What `run.loop` keeps, before its `i`th type: the types so far processed, the rest as given or
created, and the auxiliary types recorded in order with the keys their occurrences gave. -/
def LoopInv (env : Environment) (lparams : List Name) (types : List InductiveType)
    (nparams : Nat) (params : Array Expr) (i : Nat) (s : State) : Prop :=
  s.lvls = lparams.map .param ∧ params.size = nparams ∧ ParamsReserved s.ngen params ∧
  ∃ auxs, List.Forall₂ (fun e T => AuxMade env params nparams (e, T)) s.nestedAux.toList auxs ∧
    (∀ T ∈ types ++ auxs, TypeClosed T) ∧ i ≤ (types ++ auxs).length ∧
    ∃ dones, s.newTypes.toList = dones ++ (types ++ auxs).drop i ∧
      List.Forall₂ (TypeDone s.nestedAux.toList (lparams.map .param) params nparams)
        ((types ++ auxs).take i) dones

theorem forall₂_app {R : α → β → Prop} :
    ∀ {l₁ l₂ l₃ l₄}, List.Forall₂ R l₁ l₂ → List.Forall₂ R l₃ l₄ → List.Forall₂ R (l₁ ++ l₃) (l₂ ++ l₄)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h t, h' => .cons h (forall₂_app t h')

theorem forall₂_append_map {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ R l₁ l₂) {new : List γ} {f : γ → α} {g : γ → β} (hn : ∀ x ∈ new, R (f x) (g x)) :
    List.Forall₂ R (l₁ ++ new.map f) (l₂ ++ new.map g) := by
  induction h with
  | nil =>
    simp only [List.nil_append]
    induction new with
    | nil => exact .nil
    | cons x new ih => exact .cons (hn x (.head _)) (ih fun y hy => hn y (.tail _ hy))
  | cons h _ ih => exact .cons h ih

theorem run.loop_inv {env : Environment} (henv : EnvClosed env) {lparams : List Name}
    {types : List InductiveType} {nparams : Nat} {lctx : LocalContext} {params : Array Expr} :
    ∀ (fuel i : Nat) (s : State) (res : Result) (s' : State),
      run.loop nparams lctx params i fuel env s = .ok (res, s') →
      LoopInv env lparams types nparams params i s →
      ∃ sf, LoopInv env lparams types nparams params sf.newTypes.size sf ∧
        res.nparams = params.size ∧ res.lctx = lctx ∧ res.params = params ∧
        res.aux2nested = sf.nestedAux.foldl (fun m (e, n) => m.insert n e) {} ∧
        res.types = sf.newTypes.toList
  | 0, i, s, res, s', h, _ => by rw [run.loop] at h; cases h
  | fuel + 1, i, s, res, s', h, hI => by
    rw [run.loop, bind_apply] at h
    rw [show (MonadState.get : M State) env s = .ok (s, s) from rfl] at h
    dsimp only at h
    split at h
    · rename_i hi
      obtain ⟨ctors, s₁, hv, h⟩ := bind_ok h
      obtain ⟨_, s₂, hm, h⟩ := bind_ok h
      cases hm
      refine run.loop_inv henv fuel (i + 1) _ res s' h ?_
      obtain ⟨hl, hP, hpr, auxs, hA, hcl, hle, dones, hnt, hD⟩ := hI
      have hlen : dones.length = i := by
        rw [← List.Forall₂.length_eq hD, List.length_take]; omega
      have hi' : i < (types ++ auxs).length := by
        have := congrArg List.length hnt
        simp only [Array.length_toList, List.length_append, List.length_drop, hlen] at this
        have : i < s.newTypes.size := hi
        simp only [List.length_append] at hle ⊢
        omega
      have hi'' := hi'
      simp only [List.length_append] at hi''
      obtain ⟨T, rest, hTr⟩ : ∃ T rest, (types ++ auxs).drop i = T :: rest := by
        cases h : (types ++ auxs).drop i with
        | nil => have := congrArg List.length h; simp at this; omega
        | cons T rest => exact ⟨T, rest, rfl⟩
      have hT : s.newTypes[i] = T := by
        have h1 : s.newTypes.toList[i]? = some T := by rw [hnt, hTr, ← hlen]; simp
        exact Option.some_inj.1 (by rw [← Array.getElem?_eq_getElem, ← Array.getElem?_toList, h1])
      have hdrop : (types ++ auxs).drop (i + 1) = rest := by
        rw [← List.drop_drop, hTr]; rfl
      have htake : (types ++ auxs).take (i + 1) = (types ++ auxs).take i ++ [T] := by
        rw [List.take_add_one, List.getElem?_eq_some_iff.2 ⟨hi', ?_⟩]; · rfl
        have := congrArg (·[0]?) hTr; simp at this; exact (List.getElem?_eq_some_iff.1 this).2
      simp only [List.length_append] at hi'
      have hTmem : T ∈ types ++ auxs := List.mem_of_mem_drop (hTr ▸ List.mem_cons_self ..)
      rw [hT] at hv
      obtain ⟨G, hcs⟩ := ctors_grows henv hP (mapM_ok hv) hpr (hcl T hTmem).2.2
      obtain ⟨hl1, hg1, new, hn1, ht1, hnew⟩ := G
      refine ⟨by simp [hl1, hl], hP, fun p hp => let ⟨x, h, hr⟩ := hpr p hp; ⟨x, h, hr.mono hg1⟩,
        auxs ++ new.map (·.2), ?_, ?_, ?_, dones ++ [{ T with ctors := ctors }], ?_, ?_⟩
      · simp only [hn1]
        exact forall₂_append_map hA fun p hp => (hnew p hp).1
      · intro T' hT'
        simp only [← List.append_assoc, List.mem_append, List.mem_map] at hT'
        rcases hT' with hT' | ⟨p, hp, rfl⟩
        · exact hcl T' (List.mem_append.2 hT')
        · exact (hnew p hp).2
      · simp; omega
      · simp only [Array.toList_setIfInBounds, Array.set!_eq_setIfInBounds, ht1, hnt, hTr]
        rw [← List.append_assoc, List.drop_append_of_le_length (by simp; omega), hdrop]
        rw [List.append_assoc, List.set_append_right _ _ (by omega)]
        simp [hlen, hT]
      · rw [← List.append_assoc, List.take_append_of_le_length (by simp; omega), htake]
        refine forall₂_app ?_ (.cons ?_ .nil)
        · rw [hn1]
          exact Lean4Lean.List.Forall₂.imp (fun _ _ h => h.mono (List.subset_append_left _ _)) hD
        · refine ⟨rfl, rfl, ?_⟩
          rw [hl] at hcs; simpa [hn1, hT] using hcs
    · rename_i hi
      cases h
      have hsz : i = s.newTypes.size := by
        obtain ⟨-, -, -, auxs, -, -, hle, dones, hnt, hD⟩ := hI
        have h1 := congrArg List.length hnt
        have h2 := List.Forall₂.length_eq hD
        simp only [Array.length_toList, List.length_append, List.length_drop, List.length_take]
          at h1 h2 hle
        omega
      exact ⟨s, hsz ▸ hI, rfl, rfl, rfl, rfl, rfl⟩

/-- What eliminating nested occurrences produces, from a block whose types mention no free
variable, in an environment whose constants do not either:
* the parameters, opened from the first type's leading binders at fresh variables in `res.lctx`;
* the block's own types and then the auxiliary types `auxs`, each created for the occurrence
  recorded under its name in `res.aux2nested` (`AuxMade`), and every one of them processed
  (`TypeDone`): its constructors opened at fresh variables, their nested occurrences replaced by
  the auxiliary types `pairs` records, and closed again. -/
theorem run_spec {env : Environment} (henv : EnvClosed env) {fuel nparams : Nat}
    {types : List InductiveType} {lparams : List Name} (hT : ∀ T ∈ types, TypeClosed T)
    {res : Result}
    (h : (run fuel nparams types env).run' { lvls := lparams.map .param, newTypes := types.toArray }
      = .ok res) :
    ∃ I rest, types = I :: rest ∧ ∃ xs body, Opens {} I.type xs res.lctx body ∧
      xs.length = nparams ∧ xs.Nodup ∧ res.params = (xs.map .fvar).toArray ∧
      res.nparams = nparams ∧
      ∃ auxs pairs, List.Forall₂ (fun e T => AuxMade env res.params nparams (e, T)) pairs auxs ∧
        res.aux2nested = pairs.foldl (fun m (e, n) => m.insert n e) {} ∧
        (∀ T ∈ types ++ auxs, TypeClosed T) ∧
        List.Forall₂ (TypeDone pairs (lparams.map .param) res.params nparams) (types ++ auxs)
          res.types := by
  obtain ⟨⟨res', s'⟩, h1, h2⟩ : ∃ p, run fuel nparams types env
      { lvls := lparams.map .param, newTypes := types.toArray } = .ok p ∧ p.1 = res := by
    revert h; unfold StateT.run'
    cases run fuel nparams types env _ <;> simp [Functor.map, Except.map]
  subst h2
  unfold run at h1
  split at h1
  · rename_i I rest
    obtain ⟨lctx, ty, ho, hk⟩ := withParams.loop_open _ _ _ _ _ _ _ h1
    simp only [Array.empty_append] at hk
    obtain ⟨sf, hI, hn, hl, hp, ha, ht⟩ := run.loop_inv (types := I :: rest) (lparams := lparams)
      henv fuel 0 _ _ _ hk ⟨rfl, by simp [freshIds_length], fun p hp => by
        simp only [List.mem_toArray, List.mem_map] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨x, rfl, (freshIds_reserves hx).1⟩, [], by exact .nil, by simpa using hT,
        Nat.zero_le _, [], by simp, .nil⟩
    obtain ⟨-, -, -, auxs, hA, hcl, hle, dones, hnt, hD⟩ := hI
    refine ⟨I, rest, rfl, _, ty, hl ▸ ho, freshIds_length, freshIds_nodup, hp, ?_, auxs,
      sf.nestedAux.toList, hp ▸ hA, ?_, hcl, ?_⟩
    · rw [hn]; simp [freshIds_length]
    · rw [ha, Array.foldl_toList]
    · have hsz : sf.newTypes.size = (I :: rest ++ auxs).length := by
        have h1 := congrArg List.length hnt
        have h2 := List.Forall₂.length_eq hD
        simp only [Array.length_toList, List.length_append, List.length_drop, List.length_take]
          at h1 h2 hle ⊢
        omega
      rw [ht, hnt, hsz, List.drop_length, List.append_nil]
      rw [hsz, List.take_length] at hD
      dsimp only; rw [hp]; exact hD
  · cases h1

/-! ### Restoring -/

/-- The map `run` builds from its records. -/
def auxMap (pairs : List (Expr × Name)) : NameMap Expr :=
  pairs.foldl (fun m (e, n) => m.insert n e) {}

/-- `NameMap` as the tree map it is. -/
abbrev TM := Std.TreeMap Name Expr Name.quickCmp

theorem tm_get?_insert {m : TM} {n a : Name} {e : Expr} :
    (m.insert n e).get? a = if n = a then some e else m.get? a := by
  rw [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert, Std.TreeMap.get?_eq_getElem?]
  by_cases h : n = a
  · subst h; simp
  · rw [if_neg, if_neg h]; rw [Std.LawfulBEqCmp.compare_eq_iff_beq]; simpa using h

theorem foldl_insert_get?_of_not_mem {a : Name} : ∀ {pairs : List (Expr × Name)} {m : TM},
    a ∉ pairs.map (·.2) →
    (pairs.foldl (fun m (e, n) => m.insert n e) m).get? a = m.get? a
  | [], _, _ => rfl
  | (e, n) :: pairs, m, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, foldl_insert_get?_of_not_mem h.2, tm_get?_insert, if_neg (Ne.symm h.1)]

theorem auxMap_find? {pairs : List (Expr × Name)} (hnd : (pairs.map (·.2)).Nodup) {N : Expr}
    {a : Name} (h : (N, a) ∈ pairs) : (auxMap pairs).find? a = some N := by
  show (pairs.foldl (fun (m : TM) (e, n) => m.insert n e) {}).get? a = some N
  generalize ({} : TM) = m
  induction pairs generalizing m with
  | nil => cases h
  | cons p pairs ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldl_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [foldl_insert_get?_of_not_mem hnd.1, tm_get?_insert, if_pos rfl]
    · exact ih hnd.2 h _

theorem foldl_insert_contains {c : Name} : ∀ {pairs : List (Expr × Name)} {m : TM},
    (pairs.foldl (fun m (e, n) => m.insert n e) m).contains c →
    m.contains c ∨ c ∈ pairs.map (·.2)
  | [], _, h => .inl h
  | (e, n) :: pairs, m, h => by
    rw [List.foldl_cons] at h
    rcases foldl_insert_contains h with h | h
    · rw [Std.TreeMap.contains_insert] at h
      rcases Bool.or_eq_true _ _ ▸ h with h | h
      · have h' : n.quickCmp c = .eq := by simpa using h
        rw [Std.LawfulBEqCmp.compare_eq_iff_beq] at h'; simp at h'; exact .inr (by simp [h'])
      · exact .inl h
    · exact .inr (List.mem_cons_of_mem _ h)

theorem auxMap_contains {pairs : List (Expr × Name)} {c : Name}
    (h : (auxMap pairs).contains c) : c ∈ pairs.map (·.2) := by
  rcases foldl_insert_contains (m := ({} : TM)) h with h | h
  · simp at h
  · exact h

/-- The variables `bvar (d + n - 1), …, bvar d`: parameters abstracted at depth `d`. -/
def bvs : Nat → Nat → List Expr
  | 0, _ => []
  | n + 1, d => .bvar (d + n) :: bvs n d

theorem bvs_length : ∀ {n d : Nat}, (bvs n d).length = n
  | 0, _ => rfl
  | _ + 1, _ => congrArg (· + 1) bvs_length

theorem abstractList_mkAppList {xs : List FVarId} {d : Nat} :
    ∀ {f : Expr} {as : List Expr}, (Expr.mkAppList f as).abstractList xs d =
      Expr.mkAppList (f.abstractList xs d) (as.map (·.abstractList xs d))
  | f, [] => rfl
  | f, a :: as => by
    simp only [Expr.mkAppList, List.map_cons]
    rw [abstractList_mkAppList]
    congr 1
    simp only [Expr.abstractList_eq_foldl]
    induction xs generalizing f a <;> simp_all [Expr.abstract1]

theorem abstractList_bvar {i d : Nat} (h : d ≤ i) :
    ∀ {xs : List FVarId}, (Expr.bvar i).abstractList xs d = .bvar (i + xs.length)
  | [] => rfl
  | x :: xs => by
    simp only [Expr.abstractList, Expr.abstract1, if_neg (Nat.not_lt.2 h)]
    rw [abstractList_bvar (Nat.le_succ_of_le h)]; simp; omega

theorem abstractList_fvar_not_mem {y : FVarId} :
    ∀ {xs : List FVarId} {d}, y ∉ xs → (Expr.fvar y).abstractList xs d = .fvar y
  | [], _, _ => rfl
  | x :: xs, d, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [Expr.abstractList, Expr.abstract1, show (x == y) = false by simpa using Ne.symm h.1]
    exact abstractList_fvar_not_mem h.2

theorem abstractList_fvars {d : Nat} :
    ∀ {xs : List FVarId}, xs.Nodup →
      (xs.map Expr.fvar).map (fun e : Expr => e.abstractList xs d) = bvs xs.length d
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.nodup_cons] at h
    simp only [List.map_cons, Expr.abstractList, Expr.abstract1, beq_self_eq_true, ↓reduceIte,
      List.length_cons, bvs]
    rw [abstractList_bvar (Nat.le_refl _)]
    congr 1
    rw [← abstractList_fvars h.2, List.map_map, List.map_map]
    refine List.map_congr_left fun y hy => ?_
    simp only [Function.comp, Expr.abstract1]
    rw [if_neg (by simpa using fun (e : x = y) => h.1 (e ▸ hy))]

/-- Instantiating at fresh variables and abstracting them again is the identity. -/
theorem abstractList_instantiateList_fvars : ∀ (n : Nat) {ps : List FVarId} {E : Expr},
    ps.length = n → ps.Nodup → E.SuppIn (FVOnly (· ∉ ps)) →
    (E.instantiateList (ps.map .fvar).reverse).abstractList ps = E
  | 0, ps, E, hn, _, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn; rfl
  | n + 1, ps, E, hn, hnd, hE => by
    obtain ⟨qs, p, rfl⟩ : ∃ qs p, ps = qs ++ [p] :=
      by simpa using (List.eq_nil_or_concat ps).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hn
    rw [List.nodup_append] at hnd
    have hp : p ∉ qs := fun h => hnd.2.2 _ h _ (.head _) rfl
    simp only [List.map_append, List.map_cons, List.map_nil, List.reverse_append,
      List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      Expr.instantiateList, Expr.abstractList_append, Expr.abstractList]
    rw [abstractList_instantiateList_fvars n hn hnd.1]
    · exact abstract_instantiate1 (Expr.SuppIn.mono (S := FVOnly (· ∉ qs ++ [p]))
        (S' := FVOnly (· ≠ p)) ⟨fun _ h e => h (e ▸ by simp), fun _ => id, fun _ => id⟩ hE)
    · exact Expr.SuppIn.instantiate1 (S := FVOnly (· ∉ qs)) (a := .fvar p) hp
        (Expr.SuppIn.mono (S := FVOnly (· ∉ qs ++ [p])) (S' := FVOnly (· ∉ qs))
          ⟨fun _ h h' => h (by simp [h']), fun _ => id, fun _ => id⟩ hE)

theorem abstract1_liftLooseBVars {x : FVarId} {δ : Nat} : ∀ {e : Expr} {s k}, s ≤ k →
    Expr.abstract1 x (e.liftLooseBVars' s δ) (k + δ) = (Expr.abstract1 x e k).liftLooseBVars' s δ := by
  intro e
  induction e with
  | bvar i =>
    intro s k h
    by_cases h1 : i < s <;> by_cases h2 : i < k <;>
      simp [h1, h2, Expr.abstract1, Expr.liftLooseBVars'] <;> (try split) <;> omega
  | fvar v =>
    intro s k h
    simp only [Expr.liftLooseBVars', Expr.abstract1]
    split
    · simp [Expr.liftLooseBVars']; omega
    · rfl
  | lam _ d b _ ih1 ih2 | forallE _ d b _ ih1 ih2 =>
    intro s k h
    simp only [Expr.liftLooseBVars', Expr.abstract1]
    rw [ih1 h, Nat.add_right_comm, ih2 (Nat.succ_le_succ h)]
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro s k h
    simp only [Expr.liftLooseBVars', Expr.abstract1]
    rw [ih1 h, ih2 h, Nat.add_right_comm, ih3 (Nat.succ_le_succ h)]
  | app f a ih1 ih2 =>
    intro s k h; simp only [Expr.liftLooseBVars', Expr.abstract1]; rw [ih1 h, ih2 h]
  | mdata _ e ih | proj _ _ e ih =>
    intro s k h; simp only [Expr.liftLooseBVars', Expr.abstract1]; rw [ih h]
  | mvar | sort | const | lit => intros; rfl

theorem abstractList_liftLooseBVars {δ : Nat} : ∀ {xs : List FVarId} {e : Expr} {s k}, s ≤ k →
    (e.liftLooseBVars' s δ).abstractList xs (k + δ) =
      (e.abstractList xs k).liftLooseBVars' s δ
  | [], _, _, _, _ => rfl
  | x :: xs, e, s, k, h => by
    simp only [Expr.abstractList]
    rw [abstract1_liftLooseBVars h, abstractList_liftLooseBVars h]

/-- A term mentioning no loose variable, abstracted at depth `d`: its abstraction at the top,
lifted. -/
theorem abstractList_closed {xs : List FVarId} {e : Expr} (h : e.looseBVarRange' = 0) (d : Nat) :
    e.abstractList xs d = (e.abstractList xs 0).liftLooseBVars' 0 d := by
  have := abstractList_liftLooseBVars (xs := xs) (e := e) (s := 0) (k := 0) (δ := d) (Nat.le_refl _)
  rwa [Nat.zero_add, Expr.liftLooseBVars_eq_self (by omega)] at this

theorem replaceNoCache_id {f : Expr → Option Expr} (hf : ∀ t, f t = none ∨ f t = some t) :
    ∀ e : Expr, e.replaceNoCache f = e := by
  intro e
  induction e with
  | bvar i => unfold Expr.replaceNoCache; rcases hf (.bvar i) with h | h <;> simp [h]
  | fvar i => unfold Expr.replaceNoCache; rcases hf (.fvar i) with h | h <;> simp [h]
  | mvar i => unfold Expr.replaceNoCache; rcases hf (.mvar i) with h | h <;> simp [h]
  | sort i => unfold Expr.replaceNoCache; rcases hf (.sort i) with h | h <;> simp [h]
  | const c ls => unfold Expr.replaceNoCache; rcases hf (.const c ls) with h | h <;> simp [h]
  | lit i => unfold Expr.replaceNoCache; rcases hf (.lit i) with h | h <;> simp [h]
  | app f' a ih1 ih2 =>
    unfold Expr.replaceNoCache; rcases hf (.app f' a) with h | h <;> simp [h, ih1, ih2, Expr.updateApp!]
  | lam n d b bi ih1 ih2 =>
    unfold Expr.replaceNoCache; rcases hf (.lam n d b bi) with h | h <;>
      simp [h, ih1, ih2, Expr.updateLambdaE!, Expr.updateLambda!]
  | forallE n d b bi ih1 ih2 =>
    unfold Expr.replaceNoCache; rcases hf (.forallE n d b bi) with h | h <;>
      simp [h, ih1, ih2, Expr.updateForallE!, Expr.updateForall!]
  | letE n t v b nd ih1 ih2 ih3 =>
    unfold Expr.replaceNoCache; rcases hf (.letE n t v b nd) with h | h <;>
      simp [h, ih1, ih2, ih3, Expr.updateLet!]
  | mdata m b ih =>
    unfold Expr.replaceNoCache; rcases hf (.mdata m b) with h | h <;> simp [h, ih, Expr.updateMData!]
  | proj s' i b ih =>
    unfold Expr.replaceNoCache; rcases hf (.proj s' i b) with h | h <;> simp [h, ih, Expr.updateProj!]

theorem substLevelParams_id {s : Name → Option Level} (hs : ∀ n, (s n).getD (.param n) = .param n) :
    ∀ u : Level, Result.substLevelParams s u = u := by
  intro u; induction u <;> simp_all [Result.substLevelParams]

/-- Instantiating the level parameters by themselves, without simplifying, changes nothing. -/
theorem instantiateLevelParamsRaw_self {ps : List Name} (e : Expr) :
    Result.instantiateLevelParamsRaw e ps (ps.map .param) = e := by
  have hs : ∀ n, (List.lookup n (ps.zip (ps.map Level.param))).getD (.param n) = .param n := by
    intro n
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.lookup_cons]
      split
      · rename_i h; simp at h; simp [h]
      · exact ih
  unfold Result.instantiateLevelParamsRaw
  rw [Expr.replace_eq]
  refine replaceNoCache_id (fun t => ?_) e
  split
  · right; congr 2; exact List.map_id'' (substLevelParams_id hs) _
  · right; rw [substLevelParams_id hs]
  · left; rfl

open Result in
/-- The function `restoreNested` replaces with. -/
def restoreFn (r : Result) (env' : Environment) (lparams : List Name) (auxRec : NameMap Name)
    (t : Expr) : Option Expr := do
  if let .const c ls := t then
    if let some recName := auxRec.find? c then
      return .const recName ls
  let (c, n) ← spineHead? t
  if n != r.nparams || !(r.aux2nested.contains c || (r.getNestedIfAuxCtor env' c).isSome) then
    none
  let (_, ls, args) ← constSpine? t
  let inst (nested : Expr) :=
    (instantiateLevelParamsRaw (nested.abstract r.params) lparams ls).instantiateRev args
  if let some nested := r.aux2nested.find? c then
    return inst nested
  let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
  let .const I_c I_ls := (inst nested).getAppFn | none
  return mkAppN (.const (c.replacePrefix auxI_name I_c) I_ls) (inst nested).getAppArgs

theorem restoreNested_eq {r : Result} {env' : Environment} {lparams : List Name} {e : Expr}
    {auxRec : NameMap Name} :
    r.restoreNested env' lparams e auxRec = e.replaceNoCache (restoreFn r env' lparams auxRec) := by
  unfold Result.restoreNested; rw [Expr.replace_eq]; rfl

/-- `c` is none of the names restoring replaces. -/
def NotAux (r : Result) (env' : Environment) (auxRec : NameMap Name) (c : Name) : Prop :=
  auxRec.find? c = none ∧ r.aux2nested.contains c = false ∧ (r.getNestedIfAuxCtor env' c).isSome = false

/-- Only the constants a term mentions, constrained by `P`. -/
abbrev ConstOnly (P : Name → Prop) : Supp := ⟨fun _ => True, fun _ => True, P⟩

theorem spineHead?_suppIn {S : Supp} : ∀ {t : Expr} {c n}, Result.spineHead? t = some (c, n) →
    t.SuppIn S → S.const c
  | .const .., _, _, h, ht => by cases h; exact ht.1
  | .app f _, c, n, h, ht => by
    simp only [Result.spineHead?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', n'⟩, h, e⟩ := h; cases e
    exact spineHead?_suppIn h ht.1
  | .bvar .., _, _, h, _ | .fvar .., _, _, h, _ | .mvar .., _, _, h, _ | .sort .., _, _, h, _
  | .lam .., _, _, h, _ | .forallE .., _, _, h, _ | .letE .., _, _, h, _ | .lit .., _, _, h, _
  | .mdata .., _, _, h, _ | .proj .., _, _, h, _ => by simp [Result.spineHead?] at h

theorem restoreFn_none {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {t : Expr} (ht : t.SuppIn (ConstOnly (NotAux r env' auxRec))) :
    restoreFn r env' lparams auxRec t = none := by
  have hc : ∀ c n, Result.spineHead? t = some (c, n) → NotAux r env' auxRec c :=
    fun c n h => spineHead?_suppIn h ht
  unfold restoreFn
  cases hs : Result.spineHead? t with
  | none =>
    cases t <;> simp_all [Result.spineHead?]
  | some p =>
    obtain ⟨c, n⟩ := p
    obtain ⟨h1, h2, h3⟩ := hc c n hs
    cases t <;> simp_all [Result.spineHead?]

theorem replaceNoCache_id_of {S : Supp} {f : Expr → Option Expr}
    (hf : ∀ t, t.SuppIn S → f t = none) : ∀ e : Expr, e.SuppIn S → e.replaceNoCache f = e := by
  intro e he
  induction e with
  | bvar | fvar | mvar | sort | const | lit => unfold Expr.replaceNoCache; simp [hf _ he]
  | app f' a ih1 ih2 =>
    unfold Expr.replaceNoCache; simp [hf _ he, ih1 he.1, ih2 he.2, Expr.updateApp!]
  | lam n d b bi ih1 ih2 =>
    unfold Expr.replaceNoCache
    simp [hf _ he, ih1 he.1, ih2 he.2, Expr.updateLambdaE!, Expr.updateLambda!]
  | forallE n d b bi ih1 ih2 =>
    unfold Expr.replaceNoCache
    simp [hf _ he, ih1 he.1, ih2 he.2, Expr.updateForallE!, Expr.updateForall!]
  | letE n t v b nd ih1 ih2 ih3 =>
    unfold Expr.replaceNoCache
    simp [hf _ he, ih1 he.1, ih2 he.2.1, ih3 he.2.2, Expr.updateLet!]
  | mdata m b ih =>
    unfold Expr.replaceNoCache; simp [hf _ he, ih he, Expr.updateMData!]
  | proj s' i b ih =>
    unfold Expr.replaceNoCache; simp [hf _ he, ih he, Expr.updateProj!]

theorem restore_id {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {e : Expr} (he : e.SuppIn (ConstOnly (NotAux r env' auxRec))) :
    e.replaceNoCache (restoreFn r env' lparams auxRec) = e :=
  replaceNoCache_id_of (fun _ ht => restoreFn_none ht) e he

theorem spineHead?_mkAppList {c : Name} :
    ∀ {xs : List Expr} {f : Expr} {k}, Result.spineHead? f = some (c, k) →
      Result.spineHead? (Expr.mkAppList f xs) = some (c, k + xs.length)
  | [], _, _, h => h
  | x :: xs, f, k, h => by
    simp only [Expr.mkAppList, List.length_cons]
    rw [spineHead?_mkAppList (c := c) (f := .app f x) (k := k + 1) (by simp [Result.spineHead?, h])]
    simp [Nat.add_assoc, Nat.add_comm 1]

theorem spineHead?_const_mkAppList {c : Name} {ls : List Level} {xs : List Expr} :
    Result.spineHead? (Expr.mkAppList (.const c ls) xs) = some (c, xs.length) := by
  simpa using spineHead?_mkAppList (c := c) (xs := xs) (f := .const c ls) (k := 0) rfl

theorem constSpine?_mkAppList {c : Name} {ls : List Level} :
    ∀ {xs : List Expr} {f : Expr} {acc}, Result.constSpine? f = some (c, ls, acc) →
      Result.constSpine? (Expr.mkAppList f xs) = some (c, ls, acc ++ xs.toArray)
  | [], _, _, h => by simpa using h
  | x :: xs, f, acc, h => by
    simp only [Expr.mkAppList]
    rw [constSpine?_mkAppList (c := c) (ls := ls) (f := .app f x) (acc := acc.push x)
      (by simp [Result.constSpine?, h])]
    simp

theorem constSpine?_const_mkAppList {c : Name} {ls : List Level} {xs : List Expr} :
    Result.constSpine? (Expr.mkAppList (.const c ls) xs) = some (c, ls, xs.toArray) := by
  simpa using constSpine?_mkAppList (c := c) (ls := ls) (xs := xs) (f := .const c ls) (acc := #[]) rfl

theorem tm_contains_of_get? {m : TM} {c : Name} {N : Expr} (h : m.get? c = some N) :
    m.contains c = true := by
  rw [Std.TreeMap.contains_eq_isSome_getElem?, ← Std.TreeMap.get?_eq_getElem?, h]; rfl

theorem restoreFn_spine {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {t : Expr} {c : Name} {n : Nat} {ls : List Level} {args : Array Expr}
    (hc : ∀ c' ls', t = .const c' ls' → auxRec.find? c' = none)
    (hs : Result.spineHead? t = some (c, n)) (hcs : Result.constSpine? t = some (c, ls, args))
    (hn : n = r.nparams) {N : Expr} (hN : r.aux2nested.find? c = some N) :
    restoreFn r env' lparams auxRec t = some
      ((Result.instantiateLevelParamsRaw (N.abstract r.params) lparams ls).instantiateRev args) := by
  have hcon : r.aux2nested.contains c = true := by
    exact tm_contains_of_get? (m := r.aux2nested) hN
  unfold restoreFn
  cases t with
  | const c' ls' =>
    simp only [hc c' ls' rfl]
    simp_all
  | _ => simp_all

theorem restoreFn_long {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {f a : Expr} {c : Name} {n : Nat}
    (hs : Result.spineHead? (.app f a) = some (c, n)) (hn : n ≠ r.nparams) :
    restoreFn r env' lparams auxRec (.app f a) = none := by
  unfold restoreFn
  simp_all

/-- Restoring an auxiliary constant applied to the parameters' worth of arguments and more: the
occurrence it stands for, at those arguments, applied to the rest. -/
theorem restore_spine {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {aux : Name} {lvls : List Level} {N : Expr} {Bs : List Expr}
    (hBs : Bs.length = r.nparams) (hN : r.aux2nested.find? aux = some N)
    (hR : auxRec.find? aux = none) :
    ∀ (n : Nat) (Rs : List Expr), Rs.length = n →
      (∀ R ∈ Rs, R.SuppIn (ConstOnly (NotAux r env' auxRec))) →
      (Expr.mkAppList (.const aux lvls) (Bs ++ Rs)).replaceNoCache (restoreFn r env' lparams auxRec) =
        Expr.mkAppList ((Result.instantiateLevelParamsRaw (N.abstract r.params) lparams lvls).instantiateRev
          Bs.toArray) Rs
  | 0, Rs, hn, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hn
    rw [List.append_nil]
    unfold Expr.replaceNoCache
    rw [restoreFn_spine (n := Bs.length) (ls := lvls) (args := Bs.toArray) ?_
      spineHead?_const_mkAppList constSpine?_const_mkAppList hBs hN]
    · rfl
    · intro c' ls' h
      have := congrArg Result.spineHead? h
      rw [spineHead?_const_mkAppList] at this
      simp [Result.spineHead?] at this
      rw [← this.1]; exact hR
  | n + 1, Rs, hn, hRs => by
    obtain ⟨Qs, R, rfl⟩ : ∃ Qs R, Rs = Qs ++ [R] :=
      by simpa using (List.eq_nil_or_concat Rs).resolve_left (by rintro rfl; simp at hn)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hn
    rw [← List.append_assoc, Expr.mkAppList_append, Expr.mkAppList_append]
    simp only [Expr.mkAppList]
    unfold Expr.replaceNoCache
    rw [restoreFn_long (c := aux) (n := (Bs ++ Qs).length + 1)]
    · simp only [Expr.updateApp!]
      rw [← Expr.mkAppList_append, restore_spine hBs hN hR n Qs hn
        (fun R hR' => hRs R (List.mem_append_left _ hR')), restore_id (hRs R (by simp))]
      simp [Expr.mkAppList_append]
    · have := spineHead?_mkAppList (c := aux) (xs := Bs ++ Qs ++ [R]) (f := .const aux lvls) (k := 0) rfl
      simp only [Expr.mkAppList_append, Expr.mkAppList, List.length_append, List.length_singleton,
        Nat.zero_add] at this
      rw [this]; simp
    · simp; omega

theorem abstract1_eqv {x : FVarId} {e₁ e₂ : Expr} {k} :
    e₁ == e₂ → Expr.abstract1 x e₁ k == Expr.abstract1 x e₂ k := by
  simp [(· == ·)]; induction e₁ generalizing e₂ k
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [Expr.abstract1, Expr.eqv']
  all_goals intros; subst_vars; try simp [*]
  all_goals split <;> simp [Expr.eqv']

theorem abstractList_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) :
    ∀ {xs : List FVarId} {k}, Expr.abstractList e₁ xs k == Expr.abstractList e₂ xs k
  | [], _ => h
  | _ :: _, _ => abstractList_eqv (abstract1_eqv h)

theorem abstract'_eqv {xs : List FVarId} {e₁ e₂ : Expr} {k} :
    e₁ == e₂ → Expr.abstract' e₁ xs k == Expr.abstract' e₂ xs k := by
  simp [(· == ·)]; induction e₁ generalizing e₂ k
  all_goals
    cases e₂ <;> try change false = _ → _; rintro ⟨⟩
    simp [Expr.abstract', Expr.eqv']
  all_goals intros; subst_vars; try simp [*]
  all_goals split <;> simp [Expr.eqv']

theorem mkAppList_eqv {f₁ f₂ : Expr} (h : f₁ == f₂) :
    ∀ {as : List Expr}, Expr.mkAppList f₁ as == Expr.mkAppList f₂ as
  | [] => h
  | a :: _ => mkAppList_eqv (f₁ := .app f₁ a) (f₂ := .app f₂ a) (by
      have h1 : f₁.eqv' f₂ = true := by simpa [(· == ·)] using h
      have h2 : a.eqv' a = true := by simpa [(· == ·)] using Expr.eqv_refl a
      simp [(· == ·), Expr.eqv', h1, h2])

theorem looseBVarRange_abstract1 {x : FVarId} : ∀ {e : Expr} {k m},
    e.looseBVarRange' ≤ m → k ≤ m → (Expr.abstract1 x e k).looseBVarRange' ≤ m + 1 := by
  intro e
  induction e with
  | bvar i =>
    intro k m h hk
    simp only [Expr.abstract1, Expr.looseBVarRange'] at h ⊢
    split <;> omega
  | fvar v =>
    intro k m h hk
    simp only [Expr.abstract1]
    split <;> simp only [Expr.looseBVarRange'] <;> omega
  | app f a ih1 ih2 =>
    intro k m h hk; simp only [Expr.abstract1, Expr.looseBVarRange', Nat.max_le] at h ⊢
    exact ⟨ih1 h.1 hk, ih2 h.2 hk⟩
  | lam _ d b _ ih1 ih2 | forallE _ d b _ ih1 ih2 =>
    intro k m h hk; simp only [Expr.abstract1, Expr.looseBVarRange', Nat.max_le] at h ⊢
    refine ⟨ih1 h.1 hk, ?_⟩
    have := ih2 (k := k + 1) (m := m + 1) (by omega) (by omega); omega
  | letE _ t v b _ ih1 ih2 ih3 =>
    intro k m h hk; simp only [Expr.abstract1, Expr.looseBVarRange', Nat.max_le] at h ⊢
    refine ⟨⟨ih1 h.1.1 hk, ih2 h.1.2 hk⟩, ?_⟩
    have := ih3 (k := k + 1) (m := m + 1) (by omega) (by omega); omega
  | mdata _ e ih | proj _ _ e ih =>
    intro k m h hk; simp only [Expr.abstract1, Expr.looseBVarRange'] at h ⊢; exact ih h hk
  | mvar | sort | const | lit => intros; simp [Expr.abstract1, Expr.looseBVarRange']

theorem looseBVarRange_abstractList : ∀ {xs : List FVarId} {e : Expr} {m},
    e.looseBVarRange' ≤ m → (Expr.abstractList e xs 0).looseBVarRange' ≤ m + xs.length
  | [], _, _, h => h
  | x :: xs, e, m, h => by
    have := looseBVarRange_abstractList (xs := xs) (e := Expr.abstract1 x e 0) (m := m + 1)
      (looseBVarRange_abstract1 (k := 0) (m := m) h (Nat.zero_le _))
    simp only [Expr.abstractList, List.length_cons]; omega

/-- Instantiating the variables of a term by the variables at depth `d` lifts it by `d`. What
`Expr.instantiateRev` does at runtime; see the report on `instantiate_eq`. -/
def InstantiateBVars : Prop :=
  ∀ (E : Expr) (n d : Nat), E.looseBVarRange' ≤ n → E.instantiateRev (bvs n d).toArray = E.liftLooseBVars' 0 d

theorem bvs_reverse_getElem : ∀ {n d j : Nat} (h : j < (bvs n d).reverse.length),
    (bvs n d).reverse[j] = .bvar (d + j)
  | 0, _, _, h => by simp [bvs] at h
  | n + 1, d, j, h => by
    simp only [bvs, List.reverse_cons]
    have hl : (bvs n d).reverse.length = n := by simp [bvs_length]
    by_cases hj : j < n
    · rw [List.getElem_append_left (by omega)]; exact bvs_reverse_getElem _
    · have : j < n + 1 := by simpa [bvs, bvs_length] using h
      rw [List.getElem_append_right (by omega)]; simp; omega

theorem instantiate'_bvs {n d : Nat} : ∀ {E : Expr} {k},
    E.looseBVarRange' ≤ n + k → E.instantiate' (bvs n d).reverse k = E.liftLooseBVars' k d := by
  intro E; induction E with
  | bvar i =>
    intro k h; simp only [Expr.looseBVarRange'] at h
    simp only [Expr.instantiate', Expr.liftLooseBVars']
    by_cases hik : i < k
    · simp [hik]
    · have hl : i - k < (bvs n d).reverse.length := by simp [bvs_length]; omega
      rw [if_neg hik, dif_pos hl, bvs_reverse_getElem]
      simp [Expr.liftLooseBVars', hik]; omega
  | app f a ihf iha =>
    intro k h; simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [Expr.instantiate', Expr.liftLooseBVars', ihf h.1, iha h.2]
  | lam _ t b _ iht ihb | forallE _ t b _ iht ihb =>
    intro k h; simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [Expr.instantiate', Expr.liftLooseBVars', iht h.1, ihb (k := k + 1) (by omega)]
  | letE _ t v b _ iht ihv ihb =>
    intro k h; simp only [Expr.looseBVarRange', Nat.max_le] at h
    simp only [Expr.instantiate', Expr.liftLooseBVars', iht h.1.1, ihv h.1.2,
      ihb (k := k + 1) (by omega)]
  | mdata _ e ih | proj _ _ e ih =>
    intro k h; simp only [Expr.looseBVarRange'] at h
    simp only [Expr.instantiate', Expr.liftLooseBVars', ih h]
  | _ => intro k _; rfl

theorem instantiateBVars : InstantiateBVars := fun E n d h => by
  rw [Expr.instantiateRev_eq_instantiate']
  simpa using instantiate'_bvs (d := d) (k := 0) (E := E) (by omega)

section
variable {f f' a a' d d' b b' t t' v v' e e' : Expr}

theorem eqv_app' (h1 : f == f') (h2 : a == a') : Expr.app f a == .app f' a' := by
  simp only [(· == ·), Expr.eqv_eq] at *; simp [Expr.eqv', h1, h2]
theorem eqv_lam' {n bi} (h1 : d == d') (h2 : b == b') : Expr.lam n d b bi == .lam n d' b' bi := by
  simp only [(· == ·), Expr.eqv_eq] at *; simp [Expr.eqv', h1, h2]
theorem eqv_forallE' {n bi} (h1 : d == d') (h2 : b == b') :
    Expr.forallE n d b bi == .forallE n d' b' bi := by
  simp only [(· == ·), Expr.eqv_eq] at *; simp [Expr.eqv', h1, h2]
theorem eqv_letE' {n nd} (h1 : t == t') (h2 : v == v') (h3 : b == b') :
    Expr.letE n t v b nd == .letE n t' v' b' nd := by
  simp only [(· == ·), Expr.eqv_eq] at *; simp [Expr.eqv', h1, h2, h3]
theorem eqv_proj' {s i} (h : e == e') : Expr.proj s i e == .proj s i e' := by
  simp only [(· == ·), Expr.eqv_eq] at *; simp [Expr.eqv', h]
theorem eqv_mdata' {m} (h : e == e') : Expr.mdata m e == .mdata m e' := by
  have := Expr.eqv_refl (.mdata m e)
  simp only [(· == ·), Expr.eqv_eq] at *; simp_all [Expr.eqv']
end

theorem looseBVarRange_mkAppList {m : Nat} : ∀ {f : Expr} {as : List Expr},
    f.looseBVarRange' ≤ m → (∀ a ∈ as, a.looseBVarRange' ≤ m) →
    (Expr.mkAppList f as).looseBVarRange' ≤ m
  | _, [], hf, _ => hf
  | f, a :: as, hf, ha => looseBVarRange_mkAppList (f := .app f a) (as := as)
      (by simp only [Expr.looseBVarRange', Nat.max_le]; exact ⟨hf, ha a (.head _)⟩)
      fun b hb => ha b (.tail _ hb)

theorem le_looseBVarRange_mkAppList : ∀ {f : Expr} {as : List Expr},
    f.looseBVarRange' ≤ (Expr.mkAppList f as).looseBVarRange' ∧
      ∀ a ∈ as, a.looseBVarRange' ≤ (Expr.mkAppList f as).looseBVarRange'
  | _, [] => ⟨Nat.le_refl _, nofun⟩
  | f, a :: as => by
    have ⟨h1, h2⟩ := le_looseBVarRange_mkAppList (f := .app f a) (as := as)
    simp only [Expr.looseBVarRange', Nat.max_le] at h1
    refine ⟨by simp only [Expr.mkAppList]; omega, fun b hb => ?_⟩
    rcases List.mem_cons.1 hb with rfl | hb
    · simp only [Expr.mkAppList]; omega
    · exact h2 b hb

/-- A replacement by the auxiliary applications at the constructor's parameters introduces no
loose variable. -/
theorem Replaced.looseBVarRange_le {pairs : List (Expr × Name)} {lvls : List Level}
    {params : Array Expr} {xs : List FVarId} {e Y : Expr}
    (R : Replaced (NodeRep pairs lvls params (xs.map .fvar).toArray) e Y) :
    Y.looseBVarRange' ≤ e.looseBVarRange' := by
  induction R with
  | node h =>
    obtain ⟨I, Ls, args, nI, K, aux, rfl, hnI, -, -, -, rfl⟩ := h
    have htd : args.toList = args.toList.take nI ++ args.toList.drop nI ++ [] := by simp
    rw [Expr.mkAppRange_eq (args := args) htd (by simp [Nat.min_eq_left hnI]) (by simp),
      mkAppN_eq_mkAppList, mkAppN_eq_mkAppList]
    have hle := (le_looseBVarRange_mkAppList (f := .const I Ls) (as := args.toList)).2
    exact looseBVarRange_mkAppList (looseBVarRange_mkAppList (by simp [Expr.looseBVarRange'])
      (by simp [Expr.looseBVarRange'])) (fun a ha => hle a (List.mem_of_mem_drop ha))
  | refl => exact Nat.le_refl _
  | app _ _ ih1 ih2 | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    simp only [Expr.looseBVarRange']; omega
  | letE _ _ _ ih1 ih2 ih3 => simp only [Expr.looseBVarRange']; omega
  | mdata _ ih | proj _ ih => exact ih

theorem abstractList_const {xs : List FVarId} {d : Nat} {c : Name} {ls : List Level} :
    (Expr.const c ls).abstractList xs d = .const c ls := by
  induction xs <;> simp_all [Expr.abstractList, Expr.abstract1]

theorem instantiateRev_eqv {e₁ e₂ : Expr} (h : e₁ == e₂) (as : Array Expr) :
    e₁.instantiateRev as == e₂.instantiateRev as := by
  simp only [Expr.instantiateRev_eq_instantiate']; exact Expr.instantiate'_eqv h

/-- Restoring a replaced nested occurrence, abstracted with the constructor's parameters, gives
the occurrence back. -/
theorem restore_node {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {pairs : List (Expr × Name)} {ps xs : List FVarId}
    (hmap : r.aux2nested = auxMap pairs) (hnd : (pairs.map (·.2)).Nodup)
    (hpar : r.params = (ps.map .fvar).toArray) (hps : ps.Nodup) (hnp : r.nparams = xs.length)
    (hxs : xs.Nodup) (hpl : ps.length = xs.length)
    (hrec : ∀ c ∈ pairs.map (·.2), auxRec.find? c = none) (hinst : InstantiateBVars)
    {I : Name} {Ls : List Level} {args : Array Expr} {nI : Nat} {K : Expr} {aux : Name}
    (hnI : nI ≤ args.size) (hlb : ∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0)
    (hmem : (K, aux) ∈ pairs)
    (hK : K == replaceParamsVal r.params (mkAppRange (.const I Ls) 0 nI args)
      (xs.map .fvar).toArray)
    (hX : (mkAppN (.const I Ls) args).SuppIn ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩)
    (d : Nat) :
    (((mkAppRange (mkAppN (.const aux (lparams.map .param)) (xs.map .fvar).toArray) nI
        args.size args).abstractList xs d).replaceNoCache (restoreFn r env' lparams auxRec)) ==
      (mkAppN (.const I Ls) args).abstractList xs d := by
  have hargs : ∀ a ∈ args.toList, a.SuppIn ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩ := by
    rw [mkAppN_eq_mkAppList] at hX
    intro a ha; exact (Expr.SuppIn.appList.1 hX).2 a ha
  have htd : args.toList = args.toList.take nI ++ args.toList.drop nI ++ [] := by simp
  have hY : mkAppRange (mkAppN (.const aux (lparams.map .param)) (xs.map .fvar).toArray) nI
      args.size args = Expr.mkAppList (.const aux (lparams.map .param))
        (xs.map .fvar ++ args.toList.drop nI) := by
    rw [Expr.mkAppRange_eq (args := args) htd (by simp [Nat.min_eq_left hnI]) (by simp),
      mkAppN_eq_mkAppList, Expr.mkAppList_append]
  have hNas : mkAppRange (.const I Ls) 0 nI args = Expr.mkAppList (.const I Ls) (args.toList.take nI) := by
    rw [Expr.mkAppRange_eq (args := args) (l₁ := []) (l₂ := args.toList.take nI)
      (l₃ := args.toList.drop nI) (i := 0) (by simp) rfl (by simp [Nat.min_eq_left hnI])]
  have hXe : mkAppN (.const I Ls) args = Expr.mkAppList (Expr.mkAppList (.const I Ls)
      (args.toList.take nI)) (args.toList.drop nI) := by
    rw [mkAppN_eq_mkAppList, ← Expr.mkAppList_append, List.take_append_drop]
  -- the occurrence's parameters mention only the constructor's, and no loose variable
  obtain ⟨Nas, hNas_def⟩ : ∃ N, N = Expr.mkAppList (.const I Ls) (args.toList.take nI) := ⟨_, rfl⟩
  have hNlb : Nas.looseBVarRange' = 0 := by
    rw [hNas_def]
    refine Nat.le_zero.1 (looseBVarRange_mkAppList (by simp [Expr.looseBVarRange']) ?_)
    intro a ha
    obtain ⟨i, hi, e⟩ := List.getElem_of_mem ha
    have := hlb i (by simp at hi; omega) a (by
      rw [← e]; simp [List.getElem_take])
    omega
  have hNfv : Nas.SuppIn ⟨fun x => x ∉ ps ∨ x ∈ xs, fun _ => True, fun _ => True⟩ := by
    rw [hNas_def]
    refine Expr.SuppIn.appList.2 ⟨by simp [Expr.SuppIn, Level.LParamsIn.true], fun a ha => ?_⟩
    exact Expr.SuppIn.mono (S := ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩)
      (S' := ⟨fun x => x ∉ ps ∨ x ∈ xs, fun _ => True, fun _ => True⟩)
      ⟨fun _ h => Or.inr h, fun _ => id, fun _ _ => trivial⟩ (hargs a (List.mem_of_mem_take ha))
  -- the auxiliary type's key, abstracted over the block's parameters
  have hKabs : K.abstract r.params == Nas.abstractList xs := by
    rw [hpar]
    show K.abstract ⟨ps.map .fvar⟩ == _
    rw [Expr.abstract_eq']
    refine BEq.trans (abstract'_eqv hK) ?_
    rw [replaceParamsVal, hNas, ← hNas_def, hpar]
    show ((Nas.abstract ⟨xs.map .fvar⟩).instantiateRev ⟨ps.map .fvar⟩).abstract' ps == _
    rw [Expr.abstract_eq', Expr.abstract'_eq_abstractList (by omega) hxs,
      Expr.instantiateRev_eq_instantiateList (by simp [Expr.looseBVarRange'])]
    rw [Expr.abstract'_eq_abstractList (k := 0) ?_ hps]
    · rw [abstractList_instantiateList_fvars _ rfl hps (Expr.SuppIn.abstractList hNfv)]
      exact Expr.eqv_refl _
    · have := Expr.instantiateList_looseBVarRange (n := 0) (k := 0)
        (e := Nas.abstractList xs) (as := (ps.map Expr.fvar).reverse)
        (by have := abstractList_looseBVarRange (xs := xs) (e := Nas); simp; omega)
        (by simp [Expr.looseBVarRange'])
      simpa using this
  have hfind : r.aux2nested.find? aux = some K := hmap ▸ auxMap_find? hnd hmem
  have hauxrec : auxRec.find? aux = none := hrec _ (List.mem_map_of_mem (f := (·.2)) hmem)
  have hrest : ∀ R ∈ (args.toList.drop nI).map (·.abstractList xs d),
      R.SuppIn (ConstOnly (NotAux r env' auxRec)) := by
    intro R hR
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hR
    exact Expr.SuppIn.abstractList (S := ConstOnly (NotAux r env' auxRec))
      (Expr.SuppIn.mono (S := ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩)
        (S' := ⟨fun x => True ∨ x ∈ xs, fun _ => True, NotAux r env' auxRec⟩)
        ⟨fun _ h => Or.inr h, fun _ => id, fun _ => id⟩ (hargs a (List.mem_of_mem_drop ha)))
  rw [hY, abstractList_mkAppList, abstractList_const, List.map_append, abstractList_fvars hxs,
    restore_spine (by simp [hnp, bvs_length]) hfind hauxrec _ _ rfl hrest,
    instantiateLevelParamsRaw_self, hXe, abstractList_mkAppList, ← hNas_def]
  refine mkAppList_eqv (BEq.trans (instantiateRev_eqv hKabs _) ?_)
  rw [hinst _ _ _ (by have := looseBVarRange_abstractList (xs := xs) (m := 0) (by omega : Nas.looseBVarRange' ≤ 0); simpa using this),
    ← abstractList_closed hNlb]
  exact Expr.eqv_refl _

theorem spineHead?_abstractList {xs : List FVarId} {d : Nat} :
    ∀ e : Expr, Result.spineHead? (e.abstractList xs d) = Result.spineHead? e := by
  intro e
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih =>
    show Result.spineHead? ((Expr.abstract1 x e d).abstractList xs d) = _
    rw [ih]
    induction e with
    | app f a ihf => simp [Expr.abstract1, Result.spineHead?, ihf]
    | mdata m b ih' => simp [Expr.abstract1, Result.spineHead?, ih']
    | fvar v => simp only [Expr.abstract1]; split <;> rfl
    | bvar => simp only [Expr.abstract1]; rfl
    | _ => rfl

theorem restoreFn_none_head {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {t : Expr} (hc : ∀ c ls, t ≠ .const c ls)
    (h : ∀ c k, Result.spineHead? t = some (c, k) → NotAux r env' auxRec c ∨ k ≠ r.nparams) :
    restoreFn r env' lparams auxRec t = none := by
  unfold restoreFn
  cases hs : Result.spineHead? t with
  | none => cases t <;> simp_all
  | some p =>
    obtain ⟨c, k⟩ := p
    rcases h c k hs with ⟨h1, h2, h3⟩ | hk
    · cases t <;> simp_all
    · cases t <;> simp_all

/-- Where an auxiliary constant heads a spine of a replaced term, it has at least the parameters'
worth of arguments; any other head is none of the restored names. -/
theorem Replaced.spineHead {r : Result} {env' : Environment} {auxRec : NameMap Name}
    {pairs : List (Expr × Name)} {lvls : List Level} {xs : List FVarId}
    (hnp : r.nparams = xs.length) {X Y : Expr}
    (R : Replaced (NodeRep pairs lvls r.params (xs.map .fvar).toArray) X Y)
    (hX : X.SuppIn ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩) :
    ∀ c k, Result.spineHead? Y = some (c, k) →
      NotAux r env' auxRec c ∨ (c ∈ pairs.map (·.2) ∧ r.nparams ≤ k) := by
  induction R with
  | node h =>
    obtain ⟨I, Ls, args, nI, K, aux, rfl, hnI, -, hmem, -, rfl⟩ := h
    intro c k hs
    have htd : args.toList = args.toList.take nI ++ args.toList.drop nI ++ [] := by simp
    rw [Expr.mkAppRange_eq (args := args) htd (by simp [Nat.min_eq_left hnI]) (by simp),
      mkAppN_eq_mkAppList, ← Expr.mkAppList_append, spineHead?_const_mkAppList] at hs
    cases hs
    exact .inr ⟨List.mem_map_of_mem (f := (·.2)) hmem, by simp [hnp]⟩
  | refl => exact fun c k hs => .inl (spineHead?_suppIn hs hX)
  | app _ _ ih1 _ =>
    intro c k hs
    simp only [Result.spineHead?, Option.map_eq_some_iff] at hs
    obtain ⟨⟨c', k'⟩, hs, e⟩ := hs
    simp only [Prod.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rcases ih1 hX.1 _ k' hs with h | h
    · exact .inl h
    · exact .inr ⟨h.1, by omega⟩
  | lam | forallE | letE | proj | mdata => intro c k hs; simp [Result.spineHead?] at hs

section
variable {xs : List FVarId}
theorem abstractList_app {f a : Expr} : ∀ {d}, (Expr.app f a).abstractList xs d =
    .app (f.abstractList xs d) (a.abstractList xs d) := by
  induction xs generalizing f a <;> simp_all [Expr.abstractList, Expr.abstract1]
theorem abstractList_lam {n t b bi} : ∀ {d}, (Expr.lam n t b bi).abstractList xs d =
    .lam n (t.abstractList xs d) (b.abstractList xs (d + 1)) bi := by
  induction xs generalizing t b <;> simp_all [Expr.abstractList, Expr.abstract1]
theorem abstractList_forallE {n t b bi} : ∀ {d}, (Expr.forallE n t b bi).abstractList xs d =
    .forallE n (t.abstractList xs d) (b.abstractList xs (d + 1)) bi := by
  induction xs generalizing t b <;> simp_all [Expr.abstractList, Expr.abstract1]
theorem abstractList_letE {n t v b nd} : ∀ {d}, (Expr.letE n t v b nd).abstractList xs d =
    .letE n (t.abstractList xs d) (v.abstractList xs d) (b.abstractList xs (d + 1)) nd := by
  induction xs generalizing t v b <;> simp_all [Expr.abstractList, Expr.abstract1]
theorem abstractList_mdata {m e} : ∀ {d}, (Expr.mdata m e).abstractList xs d =
    .mdata m (e.abstractList xs d) := by
  induction xs generalizing e <;> simp_all [Expr.abstractList, Expr.abstract1]
theorem abstractList_proj {s i e} : ∀ {d}, (Expr.proj s i e).abstractList xs d =
    .proj s i (e.abstractList xs d) := by
  induction xs generalizing e <;> simp_all [Expr.abstractList, Expr.abstract1]
end

/-- The round trip: restoring a term whose nested occurrences were replaced, closed over the
constructor's parameters `xs` at any depth `d`, gives the term back, up to `==`. -/
theorem Replaced.restore {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {pairs : List (Expr × Name)} {ps xs : List FVarId}
    (hmap : r.aux2nested = auxMap pairs) (hnd : (pairs.map (·.2)).Nodup)
    (hpar : r.params = (ps.map .fvar).toArray) (hps : ps.Nodup) (hnp : r.nparams = xs.length)
    (hxs : xs.Nodup) (hpl : ps.length = xs.length)
    (hrec : ∀ c ∈ pairs.map (·.2), auxRec.find? c = none)
    (hinst : InstantiateBVars) {X Y : Expr}
    (R : Replaced (NodeRep pairs (lparams.map .param) r.params (xs.map .fvar).toArray) X Y)
    (hX : X.SuppIn ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩) :
    ∀ d, (Y.abstractList xs d).replaceNoCache (restoreFn r env' lparams auxRec) ==
      X.abstractList xs d := by
  have hfree {e : Expr} (he : e.SuppIn ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩) (d : Nat) :
      (e.abstractList xs d).SuppIn (ConstOnly (NotAux r env' auxRec)) :=
    Expr.SuppIn.abstractList (S := ConstOnly (NotAux r env' auxRec))
      (Expr.SuppIn.mono (S := ⟨(· ∈ xs), fun _ => True, NotAux r env' auxRec⟩)
        (S' := ⟨fun x => True ∨ x ∈ xs, fun _ => True, NotAux r env' auxRec⟩)
        ⟨fun _ h => Or.inr h, fun _ => id, fun _ => id⟩ he)
  induction R with
  | node h =>
    obtain ⟨I, Ls, args, nI, K, aux, rfl, hnI, hlb, hmem, hK, rfl⟩ := h
    exact restore_node hmap hnd hpar hps hnp hxs hpl hrec hinst hnI hlb hmem hK hX
  | refl => intro d; rw [restore_id (hfree hX d)]; exact Expr.eqv_refl _
  | @app F a F' a' R1 _ ih1 ih2 =>
    intro d
    simp only [abstractList_app]
    unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) ?_]
    · simp only [Expr.updateApp!, mkApp]; exact eqv_app' (ih1 hX.1 d) (ih2 hX.2 d)
    · intro c k hs
      simp only [Result.spineHead?, Option.map_eq_some_iff, spineHead?_abstractList] at hs
      obtain ⟨⟨c', k'⟩, hs, e⟩ := hs
      simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      rcases R1.spineHead hnp hX.1 _ k' hs with h | h
      · exact .inl h
      · exact .inr (by omega)
  | lam _ _ ih1 ih2 =>
    intro d; simp only [abstractList_lam]; unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only [Expr.updateLambdaE!, Expr.updateLambda!, mkLambda]
    exact eqv_lam' (ih1 hX.1 d) (ih2 hX.2 (d + 1))
  | forallE _ _ ih1 ih2 =>
    intro d; simp only [abstractList_forallE]; unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only [Expr.updateForallE!, Expr.updateForall!, mkForall]
    exact eqv_forallE' (ih1 hX.1 d) (ih2 hX.2 (d + 1))
  | letE _ _ _ ih1 ih2 ih3 =>
    intro d; simp only [abstractList_letE]; unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only
    exact eqv_letE' (ih1 hX.1 d) (ih2 hX.2.1 d) (ih3 hX.2.2 (d + 1))
  | proj _ ih =>
    intro d; simp only [abstractList_proj]; unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only [Expr.updateProj!, mkProj]
    exact eqv_proj' (ih hX d)
  | mdata _ ih =>
    intro d; simp only [abstractList_mdata]; unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only [Expr.updateMData!, mkMData]
    exact eqv_mdata' (ih hX d)

theorem SuppIn.combine {P : FVarId → Prop} {Q : Name → Prop} {e : Expr}
    (h1 : e.SuppIn (FVOnly P)) (h2 : e.SuppIn (ConstOnly Q)) :
    e.SuppIn ⟨P, fun _ => True, Q⟩ := by
  induction e <;> simp_all [Expr.SuppIn, Level.LParamsIn.true]

theorem Opens.consts {lctx ty xs lctx' ty'} (H : Opens lctx ty xs lctx' ty') {Q : Name → Prop}
    (h : ty.SuppIn (ConstOnly Q)) : ty'.SuppIn (ConstOnly Q) := by
  induction H with
  | nil => exact h
  | cons _ ih =>
    refine ih ?_
    rw [Expr.instantiate1_eq]
    exact Expr.SuppIn.instantiate1 (S := ConstOnly Q) (a := .fvar _) trivial h.2

theorem setBody_peel : ∀ {n e b}, peel n e = some b → setBody n e b = e
  | 0, _, _, h => by cases h; rfl
  | n + 1, .forallE .., _, h => by simp only [setBody]; rw [setBody_peel (n := n) h]
  | _ + 1, .bvar .., _, h | _ + 1, .fvar .., _, h | _ + 1, .mvar .., _, h
  | _ + 1, .sort .., _, h | _ + 1, .const .., _, h | _ + 1, .app .., _, h
  | _ + 1, .lam .., _, h | _ + 1, .letE .., _, h | _ + 1, .lit .., _, h
  | _ + 1, .mdata .., _, h | _ + 1, .proj .., _, h => by simp [peel] at h

theorem restore_setBody {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {W W' : Expr}
    (hW : W.replaceNoCache (restoreFn r env' lparams auxRec) == W') :
    ∀ {n e}, (peel n e).isSome → e.SuppIn (ConstOnly (NotAux r env' auxRec)) →
      (setBody n e W).replaceNoCache (restoreFn r env' lparams auxRec) == setBody n e W'
  | 0, _, _, _ => hW
  | n + 1, .forallE nm d b bi, h, he => by
    simp only [setBody]
    unfold Expr.replaceNoCache
    rw [restoreFn_none_head (by simp) (by simp [Result.spineHead?])]
    simp only [Expr.updateForallE!, Expr.updateForall!, mkForall]
    rw [restore_id he.1]
    exact eqv_forallE' (Expr.eqv_refl _) (restore_setBody hW (n := n) h he.2)
  | _ + 1, .bvar .., h, _ | _ + 1, .fvar .., h, _ | _ + 1, .mvar .., h, _
  | _ + 1, .sort .., h, _ | _ + 1, .const .., h, _ | _ + 1, .app .., h, _
  | _ + 1, .lam .., h, _ | _ + 1, .letE .., h, _ | _ + 1, .lit .., h, _
  | _ + 1, .mdata .., h, _ | _ + 1, .proj .., h, _ => by simp [peel] at h

/-- Each processed constructor, restored, is the constructor it was processed from, up to `==`.
The constructor's type mentions none of the restored names. -/
theorem CtorDone.restore {r : Result} {env' : Environment} {lparams : List Name}
    {auxRec : NameMap Name} {pairs : List (Expr × Name)} {ps : List FVarId} {nparams : Nat}
    (hmap : r.aux2nested = auxMap pairs) (hnd : (pairs.map (·.2)).Nodup)
    (hpar : r.params = (ps.map .fvar).toArray) (hps : ps.Nodup) (hnp : r.nparams = nparams)
    (hpl : ps.length = nparams)
    (hrec : ∀ c ∈ pairs.map (·.2), auxRec.find? c = none) (hinst : InstantiateBVars)
    {c₀ c : Constructor} (H : CtorDone pairs (lparams.map .param) r.params nparams c₀ c)
    (hc₀ : c₀.type.SuppIn (ConstOnly (NotAux r env' auxRec)))
    (hcl : c₀.type.looseBVarRange' = 0) :
    r.restoreNested env' lparams c.type auxRec == c₀.type := by
  obtain ⟨-, xs, lctx, body, Y, ho, hlen, hxs, hx, -, hfv, R, hty⟩ := H
  have hpeel := ho.peel hxs hx
  have hY : Y.looseBVarRange' = 0 := Nat.le_zero.1 <| Nat.le_trans R.looseBVarRange_le <|
    Nat.le_of_eq (ho.closed .nil (fun _ _ => LocalContext.find?_empty) hxs hcl).1
  rw [restoreNested_eq, hty, show (xs.map Expr.fvar).toArray = ⟨xs.map .fvar⟩ from rfl,
    ho.mkForall .nil (fun _ _ => LocalContext.find?_empty) hxs hx hcl Y hY]
  conv => lhs; arg 2; rw [← setBody_peel hpeel]
  exact restore_setBody (R.restore hmap hnd hpar hps (hnp.trans hlen.symm) hxs
    (hpl.trans hlen.symm) hrec hinst
    (SuppIn.combine hfv (ho.consts hc₀)) 0) (by rw [hpeel]; rfl) hc₀

/-! ### Where the auxiliary constants sit -/

/-- The application spine of `e` from a constant, not looking through metadata. -/
def spineNM : Expr → Option (Name × List Level × List Expr)
  | .const c ls => some (c, ls, [])
  | .app f a => (spineNM f).map fun (c, ls, as) => (c, ls, as ++ [a])
  | _ => none

/-- Every constant `isAux` picks out in `e` heads a metadata-free spine whose node with exactly `n`
arguments has the parameters `bvs n k` (at depth `k` below them) as its arguments and `lvls` as
its levels. The `Expr` counterpart of `VExpr.AuxAt`. -/
def AuxPlaced (isAux : Name → Bool) (lvls : List Level) (n : Nat) : Nat → Expr → Prop
  | _, .const c ls => isAux c → n = 0 ∧ ls = lvls
  | k, .app f a => match spineNM (.app f a) with
    | some (c, ls, xs) => if isAux c ∧ xs.length = n then xs = bvs n k ∧ ls = lvls
      else AuxPlaced isAux lvls n k f ∧ AuxPlaced isAux lvls n k a
    | none => AuxPlaced isAux lvls n k f ∧ AuxPlaced isAux lvls n k a
  | k, .lam _ t b _ | k, .forallE _ t b _ =>
    AuxPlaced isAux lvls n k t ∧ AuxPlaced isAux lvls n (k + 1) b
  | k, .letE _ t v b _ =>
    AuxPlaced isAux lvls n k t ∧ AuxPlaced isAux lvls n k v ∧ AuxPlaced isAux lvls n (k + 1) b
  | k, .mdata _ e | k, .proj _ _ e => AuxPlaced isAux lvls n k e
  | _, .lit l => l.SuppIn (isAux · = false)
  | _, _ => True

theorem spineNM_suppIn {S : Supp} : ∀ {t : Expr} {c ls xs}, spineNM t = some (c, ls, xs) →
    t.SuppIn S → S.const c
  | .const .., _, _, _, h, ht => by cases h; exact ht.1
  | .app f _, c, ls, xs, h, ht => by
    simp only [spineNM, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', xs'⟩, h, e⟩ := h
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
    exact spineNM_suppIn h ht.1
  | .bvar .., _, _, _, h, _ | .fvar .., _, _, _, h, _ | .mvar .., _, _, _, h, _
  | .sort .., _, _, _, h, _ | .lam .., _, _, _, h, _ | .forallE .., _, _, _, h, _
  | .letE .., _, _, _, h, _ | .lit .., _, _, _, h, _ | .mdata .., _, _, _, h, _
  | .proj .., _, _, _, h, _ => by simp [spineNM] at h

theorem auxPlaced_of_free {isAux : Name → Bool} {lvls n} :
    ∀ {e : Expr} {k}, e.SuppIn (ConstOnly (isAux · = false)) → AuxPlaced isAux lvls n k e := by
  intro e
  induction e with
  | const c ls => intro k h h'; simp_all [Expr.SuppIn]
  | app f a ih1 ih2 =>
    intro k h
    unfold AuxPlaced
    split
    · rename_i c ls xs hs
      rw [if_neg (fun h' => by have := spineNM_suppIn hs h; simp_all)]
      exact ⟨ih1 h.1, ih2 h.2⟩
    · exact ⟨ih1 h.1, ih2 h.2⟩
  | lam _ t b _ ih1 ih2 | forallE _ t b _ ih1 ih2 => intro k h; exact ⟨ih1 h.1, ih2 h.2⟩
  | letE _ t v b _ ih1 ih2 ih3 => intro k h; exact ⟨ih1 h.1, ih2 h.2.1, ih3 h.2.2⟩
  | mdata _ e ih | proj _ _ e ih => intro k h; exact ih h
  | lit l => intro k h; exact h
  | _ => intros; trivial

theorem spineNM_mkAppList {c : Name} {ls : List Level} :
    ∀ {xs : List Expr} {f : Expr} {acc}, spineNM f = some (c, ls, acc) →
      spineNM (Expr.mkAppList f xs) = some (c, ls, acc ++ xs)
  | [], _, _, h => by simpa using h
  | x :: xs, f, acc, h => by
    simp only [Expr.mkAppList]
    rw [spineNM_mkAppList (c := c) (ls := ls) (f := .app f x) (acc := acc ++ [x])
      (by simp [spineNM, h])]
    simp

/-- A replaced occurrence, closed over the parameters: an auxiliary constant at them, applied to
arguments mentioning no auxiliary constant. -/
theorem auxPlaced_node {isAux : Name → Bool} {lvls : List Level} {c : Name} (hc : isAux c)
    {k : Nat} : ∀ (m : Nat) {n : Nat} (rest : List Expr), rest.length = m →
      (∀ R ∈ rest, R.SuppIn (ConstOnly (isAux · = false))) →
      AuxPlaced isAux lvls n k (Expr.mkAppList (.const c lvls) (bvs n k ++ rest))
  | 0, n, rest, hl, _ => by
    obtain rfl := List.eq_nil_of_length_eq_zero hl
    rw [List.append_nil]
    cases n with
    | zero => exact fun _ => ⟨rfl, rfl⟩
    | succ n =>
      obtain ⟨xs, x, hx⟩ : ∃ xs x, bvs (n + 1) k = xs ++ [x] := by
        simpa using (List.eq_nil_or_concat (bvs (n + 1) k)).resolve_left
          (show Expr.bvar (k + n) :: bvs n k ≠ [] from List.cons_ne_nil _ _)
      have hs : spineNM (Expr.mkAppList (.const c lvls) (bvs (n + 1) k)) =
          some (c, lvls, bvs (n + 1) k) := by
        simpa using spineNM_mkAppList (c := c) (ls := lvls) (xs := bvs (n + 1) k)
          (f := .const c lvls) (acc := []) rfl
      rw [hx, Expr.mkAppList_append] at hs ⊢
      simp only [Expr.mkAppList] at hs ⊢
      unfold AuxPlaced; rw [hs]; dsimp only; rw [if_pos ⟨hc, by rw [← hx]; exact bvs_length⟩]
      exact ⟨hx.symm, rfl⟩
  | m + 1, n, rest, hl, hR => by
    obtain ⟨Q, R, rfl⟩ : ∃ Q R, rest = Q ++ [R] :=
      by simpa using (List.eq_nil_or_concat rest).resolve_left (by rintro rfl; simp at hl)
    simp only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] at hl
    have hs : spineNM (Expr.mkAppList (.const c lvls) (bvs n k ++ Q ++ [R])) =
        some (c, lvls, bvs n k ++ Q ++ [R]) := by
      simpa using spineNM_mkAppList (c := c) (ls := lvls) (xs := bvs n k ++ Q ++ [R])
        (f := .const c lvls) (acc := []) rfl
    rw [← List.append_assoc, Expr.mkAppList_append]
    rw [Expr.mkAppList_append] at hs
    simp only [Expr.mkAppList] at hs ⊢
    unfold AuxPlaced; rw [hs]; dsimp only; rw [if_neg (by simp [bvs_length])]
    refine ⟨?_, auxPlaced_of_free (hR R (by simp))⟩
    exact auxPlaced_node hc m Q hl fun R h => hR R (by simp [h])

theorem spineNM_abstractList {xs : List FVarId} {d : Nat} :
    ∀ e : Expr, spineNM (e.abstractList xs d) =
      (spineNM e).map fun (c, ls, as) => (c, ls, as.map (·.abstractList xs d)) := by
  intro e
  induction e with
  | app f a ih =>
    rw [abstractList_app]; simp only [spineNM, ih]
    cases spineNM f <;> simp
  | const => rw [abstractList_const]; rfl
  | lam => rw [abstractList_lam]; rfl
  | forallE => rw [abstractList_forallE]; rfl
  | letE => rw [abstractList_letE]; rfl
  | mdata => rw [abstractList_mdata]; rfl
  | proj => rw [abstractList_proj]; rfl
  | bvar i =>
    induction xs generalizing i with
    | nil => rfl
    | cons x xs ih => simp only [Expr.abstractList, Expr.abstract1]; exact ih _
  | fvar v =>
    induction xs generalizing v with
    | nil => rfl
    | cons x xs ih =>
      simp only [Expr.abstractList, Expr.abstract1]
      split
      · rw [abstractList_bvar (Nat.le_refl _)]; rfl
      · exact ih v
  | mvar | lit | sort =>
    induction xs with
    | nil => rfl
    | cons x xs ih => exact ih

theorem Replaced.spineNM {isAux : Name → Bool} {pairs : List (Expr × Name)} {lvls : List Level}
    {params As : Array Expr} {X Y : Expr}
    (R : Replaced (NodeRep pairs lvls params As) X Y)
    (hX : X.SuppIn (ConstOnly (isAux · = false))) :
    ∀ c ls ys, ElimNestedInductive.spineNM Y = some (c, ls, ys) → isAux c → As.size ≤ ys.length := by
  induction R with
  | node h =>
    obtain ⟨I, Ls, args, nI, K, aux, rfl, hnI, -, hmem, -, rfl⟩ := h
    intro c ls ys hs _
    have htd : args.toList = args.toList.take nI ++ args.toList.drop nI ++ [] := by simp
    rw [Expr.mkAppRange_eq (args := args) htd (by simp [Nat.min_eq_left hnI]) (by simp),
      mkAppN_eq_mkAppList, ← Expr.mkAppList_append] at hs
    have := spineNM_mkAppList (c := aux) (ls := lvls) (xs := As.toList ++ args.toList.drop nI)
      (f := .const aux lvls) (acc := []) rfl
    rw [this] at hs; simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨-, -, rfl⟩ := hs; simp
  | refl => intro c ls ys hs hc; have := spineNM_suppIn hs hX; simp_all
  | app _ _ ih1 _ =>
    intro c ls ys hs hc
    simp only [ElimNestedInductive.spineNM, Option.map_eq_some_iff] at hs
    obtain ⟨⟨c', ls', ys'⟩, hs, e⟩ := hs
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
    have := ih1 hX.1 _ _ _ hs hc; simp; omega
  | _ => intro c ls ys hs; simp [ElimNestedInductive.spineNM] at hs

/-- In a processed constructor's body, closed over its parameters `xs` at depth `d`, every
auxiliary constant sits at the parameters. -/
theorem Replaced.auxPlaced {isAux : Name → Bool} {pairs : List (Expr × Name)}
    {lvls : List Level} {params : Array Expr} {xs : List FVarId} (hxs : xs.Nodup)
    (hpa : ∀ p ∈ pairs, isAux p.2) {X Y : Expr}
    (R : Replaced (NodeRep pairs lvls params (xs.map .fvar).toArray) X Y)
    (hX : X.SuppIn (ConstOnly (isAux · = false))) :
    ∀ d, AuxPlaced isAux lvls xs.length d (Y.abstractList xs d) := by
  have hfree {e : Expr} (he : e.SuppIn (ConstOnly (isAux · = false))) (d : Nat) :
      (e.abstractList xs d).SuppIn (ConstOnly (isAux · = false)) :=
    Expr.SuppIn.abstractList (S := ConstOnly (isAux · = false))
      (Expr.SuppIn.mono (S := ConstOnly (isAux · = false))
        (S' := ⟨fun x => True ∨ x ∈ xs, fun _ => True, (isAux · = false)⟩)
        ⟨fun _ h => Or.inl h, fun _ => id, fun _ => id⟩ he)
  induction R with
  | node h =>
    obtain ⟨I, Ls, args, nI, K, aux, rfl, hnI, -, hmem, -, rfl⟩ := h
    intro d
    have htd : args.toList = args.toList.take nI ++ args.toList.drop nI ++ [] := by simp
    rw [Expr.mkAppRange_eq (args := args) htd (by simp [Nat.min_eq_left hnI]) (by simp),
      mkAppN_eq_mkAppList, ← Expr.mkAppList_append, abstractList_mkAppList, abstractList_const,
      List.map_append, List.toList_toArray, abstractList_fvars hxs]
    have hargs : ∀ a ∈ args.toList, a.SuppIn (ConstOnly (isAux · = false)) := by
      rw [mkAppN_eq_mkAppList] at hX; exact (Expr.SuppIn.appList.1 hX).2
    exact auxPlaced_node (hpa _ hmem) _ _ rfl fun R hR => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hR
      exact hfree (hargs a (List.mem_of_mem_drop ha)) d
  | refl => intro d; exact auxPlaced_of_free (hfree hX d)
  | @app F F' a a' R1 _ ih1 ih2 =>
    intro d
    simp only [abstractList_app]
    unfold AuxPlaced
    split
    · rename_i c ls ys hs
      rw [if_neg]
      · exact ⟨ih1 hX.1 d, ih2 hX.2 d⟩
      · rintro ⟨hc, hl⟩
        simp only [ElimNestedInductive.spineNM, Option.map_eq_some_iff, spineNM_abstractList] at hs
        obtain ⟨⟨c', ls', ys'⟩, hs, e⟩ := hs
        simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
        obtain ⟨⟨c'', ls'', ys''⟩, hs, e⟩ := hs
        simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
        have := R1.spineNM hX.1 _ _ _ hs hc
        simp at hl this; omega
    · exact ⟨ih1 hX.1 d, ih2 hX.2 d⟩
  | lam _ _ ih1 ih2 => intro d; simp only [abstractList_lam]; exact ⟨ih1 hX.1 d, ih2 hX.2 (d + 1)⟩
  | forallE _ _ ih1 ih2 =>
    intro d; simp only [abstractList_forallE]; exact ⟨ih1 hX.1 d, ih2 hX.2 (d + 1)⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    intro d; simp only [abstractList_letE]; exact ⟨ih1 hX.1 d, ih2 hX.2.1 d, ih3 hX.2.2 (d + 1)⟩
  | mdata _ ih => intro d; simp only [abstractList_mdata]; exact ih hX d
  | proj _ ih => intro d; simp only [abstractList_proj]; exact ih hX d

/-! ### Carrying the placement to translations -/

section
variable {R : Name → Option VAuxHead} {ls₀ : List VLevel}

/-- An auxiliary constant heading a spine in a term satisfying `AuxAt` has at least its
parameters' worth of arguments. -/
theorem AuxAt.spine : ∀ {k : Nat} {e : VExpr}, e.AuxAt R ls₀ k →
    ∀ {c ls xs h}, e.constSpine? = some (c, ls, xs) → R c = some h → h.n ≤ xs.length
  | _, .const c ls, H, _, _, _, _, hs, hR => by
    simp only [VExpr.constSpine?, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl, rfl⟩ := hs
    simp only [VExpr.AuxAt, hR] at H; simp [H.1]
  | k, .app f a, H, c, ls, xs, h, hs, hR => by
    simp only [VExpr.AuxAt] at H
    rw [hs] at H; simp only [hR] at H
    split at H
    · omega
    · simp only [VExpr.constSpine?, Option.map_eq_some_iff] at hs
      obtain ⟨⟨c', ls', ys⟩, hs', e⟩ := hs
      simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
      have := AuxAt.spine H.1 hs' hR; simp; omega
  | _, .bvar _, _, _, _, _, _, hs, _ | _, .sort _, _, _, _, _, _, hs, _
  | _, .lam .., _, _, _, _, _, hs, _ | _, .forallE .., _, _, _, _, _, hs, _
  | _, .proj .., _, _, _, _, _, hs, _ => by simp [VExpr.constSpine?] at hs

theorem AuxAt.app {k : Nat} {f a : VExpr} (hf : f.AuxAt R ls₀ k) (ha : a.AuxAt R ls₀ k) :
    (VExpr.app f a).AuxAt R ls₀ k := by
  simp only [VExpr.AuxAt]
  split
  · rename_i c ls xs hs
    split
    · rename_i h hR
      rw [if_neg]
      · exact ⟨hf, ha⟩
      · intro hl
        simp only [VExpr.constSpine?, Option.map_eq_some_iff] at hs
        obtain ⟨⟨c', ls', ys⟩, hs', e⟩ := hs
        simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
        have := AuxAt.spine hf hs' hR; simp at hl; omega
    · exact ⟨hf, ha⟩
  · exact ⟨hf, ha⟩

theorem constSpine?_liftN {δ c : Nat} : ∀ e : VExpr, (e.liftN δ c).constSpine? =
    e.constSpine?.map fun (n, ls, xs) => (n, ls, xs.map (·.liftN δ c))
  | .const _ _ => rfl
  | .app f a => by
    simp only [VExpr.liftN, VExpr.constSpine?, constSpine?_liftN f]
    cases VExpr.constSpine? f <;> simp
  | .bvar _ | .sort _ | .lam .. | .forallE .. | .proj .. => rfl

theorem AuxAt.liftN {δ : Nat} : ∀ {e : VExpr} {k c}, c ≤ k → e.AuxAt R ls₀ k →
    (e.liftN δ c).AuxAt R ls₀ (k + δ)
  | .bvar _, _, _, _, _ | .sort _, _, _, _, _ => trivial
  | .const _ _, _, _, _, H => H
  | .app f a, k, c, hc, H => by
    simp only [VExpr.AuxAt] at H
    split at H
    · rename_i cn ls xs hs
      split at H
      · rename_i h hR
        split at H
        · rename_i hl
          obtain ⟨rfl, rfl⟩ := H
          have hs' := constSpine?_liftN (δ := δ) (c := c) (VExpr.app f a)
          rw [hs] at hs'
          simp only [Option.map_some, VExpr.liftN] at hs'
          have hb := VExpr.bvars_liftN_hi h.n k δ c hc
          simp only [VExpr.liftN, VExpr.AuxAt]
          rw [hs']; simp only [hR, hb, VExpr.length_bvars, ↓reduceIte]
          simp
        · exact AuxAt.app (AuxAt.liftN hc H.1) (AuxAt.liftN hc H.2)
      · exact AuxAt.app (AuxAt.liftN hc H.1) (AuxAt.liftN hc H.2)
    · exact AuxAt.app (AuxAt.liftN hc H.1) (AuxAt.liftN hc H.2)
  | .lam A b, k, c, hc, H | .forallE A b, k, c, hc, H => by
    simp only [VExpr.liftN, VExpr.AuxAt] at H ⊢
    exact ⟨AuxAt.liftN hc H.1, by
      simpa [Nat.add_right_comm] using AuxAt.liftN (Nat.succ_le_succ hc) H.2⟩
  | .proj _ _ e, k, c, hc, H => by simp only [VExpr.liftN, VExpr.AuxAt] at H ⊢; exact AuxAt.liftN hc H

end

/-- The parameters, `n` of them below `k` binders of the term (`k'` of the translation), are
the variables `k'`, …: what `TrExprS` reads a parameter variable as. -/
def ParamsAt (n : Nat) (Δ : VLCtx) (k k' : Nat) : Prop :=
  ∀ j < n, ∃ A, Δ.find? (.inl (k + j)) = some (.bvar (k' + j), A)

/-- What every variable of the context stands for is placed. -/
def CtxAux (R : Name → Option VAuxHead) (ls₀ : List VLevel) (Δ : VLCtx) (k' : Nat) : Prop :=
  ∀ v e A, Δ.find? v = some (e, A) → e.AuxAt R ls₀ k'

theorem ParamsAt.vlam {n Δ k k' T} (H : ParamsAt n Δ k k') :
    ParamsAt n ((none, .vlam T) :: Δ) (k + 1) (k' + 1) := by
  intro j hj
  obtain ⟨A, h⟩ := H j hj
  refine ⟨A.liftN 1, ?_⟩
  rw [show k + 1 + j = (k + j) + 1 by omega]
  simp only [VLCtx.find?, VLCtx.next, h, Option.bind_eq_bind, Option.bind_some]
  simp [VLocalDecl.depth, VExpr.liftN, liftVar]; omega

theorem ParamsAt.vlet {n Δ k k' T V} (H : ParamsAt n Δ k k') :
    ParamsAt n ((none, .vlet T V) :: Δ) (k + 1) k' := by
  intro j hj
  obtain ⟨A, h⟩ := H j hj
  refine ⟨A.liftN 0, ?_⟩
  rw [show k + 1 + j = (k + j) + 1 by omega]
  simp only [VLCtx.find?, VLCtx.next, h, Option.bind_eq_bind, Option.bind_some]
  simp [VLocalDecl.depth]

theorem CtxAux.vlam {R ls₀ Δ k' T} (H : CtxAux R ls₀ Δ k') :
    CtxAux R ls₀ ((none, .vlam T) :: Δ) (k' + 1) := by
  intro v e A h
  simp only [VLCtx.find?] at h
  split at h
  · cases h; trivial
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨e₀, A₀⟩, h1, h2⟩ := h; cases h2
    exact AuxAt.liftN (Nat.zero_le _) (H _ _ _ h1)

theorem CtxAux.vlet {R ls₀ Δ k' T V} (H : CtxAux R ls₀ Δ k') (hV : V.AuxAt R ls₀ k') :
    CtxAux R ls₀ ((none, .vlet T V) :: Δ) k' := by
  intro v e A h
  simp only [VLCtx.find?] at h
  split at h
  · cases h; exact hV
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨e₀, A₀⟩, h1, h2⟩ := h; cases h2
    simpa [VLocalDecl.depth] using H _ _ _ h1

theorem bvs_tr {n : Nat} {Δ : VLCtx} {k k' : Nat} {env : VEnv} {Us : List Name}
    (H : ParamsAt n Δ k k') : ∀ {m} {xs' : List VExpr}, m ≤ n →
      List.Forall₂ (TrExprS env Us Δ) (bvs m k) xs' → xs' = VExpr.bvars m k'
  | 0, _, _, h => by cases h; rfl
  | m + 1, _, hm, .cons h t => by
    rw [bvs_tr H (Nat.le_of_succ_le hm) t, VExpr.bvars_succ]
    cases h with | bvar h =>
    obtain ⟨A, h'⟩ := H m (by omega)
    rw [h'] at h; cases h
    congr 2; omega

/-- A translation's spine from a constant is the term's, translated. -/
theorem TrExprS.spine {env : VEnv} {Us : List Name} {Δ : VLCtx} {e : Expr} {e' : VExpr}
    (H : TrExprS env Us Δ e e') : ∀ {c ls xs}, spineNM e = some (c, ls, xs) →
      ∃ us xs', e'.constSpine? = some (c, us, xs') ∧ ls.mapM (VLevel.ofLevel Us) = some us ∧
        List.Forall₂ (TrExprS env Us Δ) xs xs' := by
  induction H with
  | const _ h2 =>
    intro c ls xs h
    simp only [spineNM, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨_, [], rfl, h2, .nil⟩
  | app _ _ _ ha ih1 _ =>
    intro c ls xs h
    simp only [spineNM, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', ys⟩, h, e⟩ := h
    simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl, rfl⟩ := e
    obtain ⟨us, ys', h1, h2, h3⟩ := ih1 h
    exact ⟨us, ys' ++ [_], by simp [VExpr.constSpine?, h1], h2, forall₂_app h3 (.cons ha .nil)⟩
  | _ => intro c ls xs h; simp [spineNM] at h

/-- Placement carries over to translations: a term whose auxiliary constants (`isAux`) sit at
the parameters translates to one whose constants with an `R` entry (the same ones, with `n`
parameters) do, in a context where the parameters are read as variables and every other variable
stands for something placed. -/
theorem TrExprS.auxAt {env : VEnv} {Us : List Name} {R : Name → Option VAuxHead}
    {ls₀ : List VLevel} {isAux : Name → Bool} {lvls : List Level} {n : Nat}
    (hlv : lvls.mapM (VLevel.ofLevel Us) = some ls₀)
    (hR1 : ∀ c h, R c = some h → isAux c ∧ h.n = n) (hR2 : ∀ c, isAux c → ∃ h, R c = some h)
    {Δ : VLCtx} {e : Expr} {e' : VExpr} (H : TrExprS env Us Δ e e') :
    ∀ {k k'}, ParamsAt n Δ k k' → CtxAux R ls₀ Δ k' → AuxPlaced isAux lvls n k e →
      e'.AuxAt R ls₀ k' := by
  induction H with
  | bvar h => intro k k' _ hC _; exact hC _ _ _ h
  | fvar h => intro k k' _ hC _; exact hC _ _ _ h
  | sort => intros; trivial
  | const _ h2 _ =>
    intro k k' _ _ hA
    simp only [VExpr.AuxAt]
    split
    · rename_i h hR
      obtain ⟨hc, hn⟩ := hR1 _ _ hR
      obtain ⟨hn0, hls⟩ := hA hc
      rw [hls, hlv] at h2; cases h2
      exact ⟨by omega, rfl⟩
    · trivial
  | app h1 h2 tf ta ih1 ih2 =>
    intro k k' hP hC hA
    unfold AuxPlaced at hA
    split at hA
    · rename_i c ls xs hs
      split at hA
      · rename_i hcond
        obtain ⟨rfl, rfl⟩ := hA
        obtain ⟨us, xs', h1', h2', h3⟩ := TrExprS.spine (.app h1 h2 tf ta) hs
        rw [hlv] at h2'; cases h2'
        obtain ⟨h, hR⟩ := hR2 c hcond.1
        have hn := (hR1 _ _ hR).2
        have := bvs_tr hP (Nat.le_refl _) h3
        subst this
        simp only [VExpr.AuxAt]
        rw [h1']; simp only [hR, VExpr.length_bvars, hn, ↓reduceIte]
        simp
      · exact AuxAt.app (ih1 hP hC hA.1) (ih2 hP hC hA.2)
    · exact AuxAt.app (ih1 hP hC hA.1) (ih2 hP hC hA.2)
  | lam _ _ _ ih1 ih2 =>
    intro k k' hP hC hA
    exact ⟨ih1 hP hC hA.1, ih2 hP.vlam hC.vlam hA.2⟩
  | forallE _ _ _ _ ih1 ih2 =>
    intro k k' hP hC hA
    exact ⟨ih1 hP hC hA.1, ih2 hP.vlam hC.vlam hA.2⟩
  | letE _ _ _ _ _ ih2 ih3 =>
    intro k k' hP hC hA
    exact ih3 hP.vlet (hC.vlet (ih2 hP hC hA.2.1)) hA.2.2
  | lit _ _ ih =>
    intro k k' hP hC hA
    exact ih hP hC (auxPlaced_of_free (Expr.SuppIn.toConstructor (S := ConstOnly (isAux · = false)) hA))
  | mdata _ ih => intro k k' hP hC hA; exact ih hP hC hA
  | proj _ _ ih => intro k k' hP hC hA; exact ih hP hC hA

theorem paramsCtx_bvar : ∀ (Ts : List VExpr) {v e A},
    VLCtx.find? (Ts.map fun T => (none, VLocalDecl.vlam T)) v = some (e, A) → ∃ i, e = .bvar i
  | [], v, _, _, h => by cases v <;> simp [VLCtx.find?] at h
  | T :: Ts, v, e, A, h => by
    simp only [List.map_cons, VLCtx.find?] at h
    split at h
    · cases h; exact ⟨0, rfl⟩
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨e₀, A₀⟩, h1, h2⟩ := h; cases h2
      obtain ⟨i, rfl⟩ := paramsCtx_bvar Ts h1
      exact ⟨_, rfl⟩

/-- The context of a telescope of parameters, as `TrExprS` builds it under their binders. -/
theorem paramsCtx (R : Name → Option VAuxHead) (ls₀ : List VLevel) :
    ∀ Ts : List VExpr, ParamsAt Ts.length (Ts.map fun T => (none, VLocalDecl.vlam T)) 0 0 ∧
      CtxAux R ls₀ (Ts.map fun T => (none, VLocalDecl.vlam T)) 0
  | [] => ⟨nofun, fun v e A h => by cases v <;> simp [VLCtx.find?] at h⟩
  | T :: Ts => by
    obtain ⟨hP, -⟩ := paramsCtx R ls₀ Ts
    refine ⟨fun j hj => ?_, fun v e A h => ?_⟩
    · cases j with
      | zero => exact ⟨_, rfl⟩
      | succ j =>
        obtain ⟨A, h⟩ := hP j (by simp at hj; omega)
        refine ⟨A.liftN 1, ?_⟩
        simp only [List.map_cons, VLCtx.find?, VLCtx.next, Nat.zero_add] at h ⊢
        rw [h]; simp [VLocalDecl.depth, VExpr.liftN, liftVar]; omega
    · obtain ⟨i, rfl⟩ := paramsCtx_bvar (T :: Ts) h; trivial

/-- A processed constructor's type: its original's leading binders over a body in which every
auxiliary constant sits at the parameters. -/
theorem CtorDone.placed {isAux : Name → Bool} {pairs : List (Expr × Name)} {lvls : List Level}
    {params : Array Expr} {nparams : Nat} (hpa : ∀ p ∈ pairs, isAux p.2) {c₀ c : Constructor}
    (H : CtorDone pairs lvls params nparams c₀ c)
    (hc₀ : c₀.type.SuppIn (ConstOnly (isAux · = false))) (hcl : c₀.type.looseBVarRange' = 0) :
    ∃ B, c.type = setBody nparams c₀.type B ∧ (peel nparams c₀.type).isSome ∧
      AuxPlaced isAux lvls nparams 0 B := by
  obtain ⟨-, xs, lctx, body, Y, ho, hlen, hxs, hx, -, -, R, hty⟩ := H
  have hpeel := ho.peel hxs hx
  have hY : Y.looseBVarRange' = 0 := Nat.le_zero.1 <| Nat.le_trans R.looseBVarRange_le <|
    Nat.le_of_eq (ho.closed .nil (fun _ _ => LocalContext.find?_empty) hxs hcl).1
  refine ⟨Y.abstractList xs, ?_, by rw [← hlen, hpeel]; rfl, ?_⟩
  · rw [hty, show (xs.map Expr.fvar).toArray = ⟨xs.map .fvar⟩ from rfl,
      ho.mkForall .nil (fun _ _ => LocalContext.find?_empty) hxs hx hcl Y hY, hlen]
  · rw [← hlen]
    exact R.auxPlaced hxs hpa (ho.consts hc₀) 0

/-- The auxiliary types are named as their records are, and those names are fresh for `env`. -/
theorem auxMade_names {env : Environment} {params : Array Expr} {nparams : Nat} :
    ∀ {pairs : List (Expr × Name)} {auxs : List InductiveType},
      List.Forall₂ (fun e T => AuxMade env params nparams (e, T)) pairs auxs →
      pairs.map (·.2) = auxs.map (·.name) ∧ ∀ T ∈ auxs, env.contains T.name = false
  | [], [], .nil => ⟨rfl, nofun⟩
  | _ :: _, T :: _, .cons h t => by
    obtain ⟨h1, h2⟩ := auxMade_names t
    obtain ⟨hn, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hfresh, _⟩ := h
    simp only at hn hfresh
    refine ⟨by simp [← hn, h1], fun T' hT' => ?_⟩
    rcases List.mem_cons.1 hT' with rfl | h
    · exact hfresh
    · exact h2 T' h

end Lean4Lean.ElimNestedInductive

namespace Lean4Lean
open Lean hiding Environment Exception

/-- `checkClosed` passes only on a term with no loose bound variable: the input closedness the
elimination's facts assume (`TypeClosed`). -/
theorem checkClosed.WF (n : Name) (e : Expr) :
    (checkClosed n e).WF fun _ => e.looseBVarRange' = 0 := by
  intro _ h
  unfold checkClosed at h
  split at h
  · cases h
  · rename_i hlb; simpa [Expr.hasLooseBVars] using hlb

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception

theorem Expr.suppIn_of_fvarsIn : ∀ {e : Expr}, e.FVarsIn (fun _ => False) →
    e.SuppIn (ElimNestedInductive.FVOnly fun _ => False)
  | .bvar _, _ | .mvar _, _ => trivial
  | .fvar _, h => h.elim
  | .sort u, _ => Level.LParamsIn.true
  | .const _ us, _ => ⟨trivial, fun u _ => Level.LParamsIn.true⟩
  | .lit (.natVal _), _ => ⟨trivial, trivial, trivial⟩
  | .lit (.strVal _), _ => ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial,
      trivial⟩
  | .app .., h | .lam .., h | .forallE .., h =>
    ⟨Expr.suppIn_of_fvarsIn h.1, Expr.suppIn_of_fvarsIn h.2⟩
  | .letE .., h => ⟨Expr.suppIn_of_fvarsIn h.1, Expr.suppIn_of_fvarsIn h.2.1,
      Expr.suppIn_of_fvarsIn h.2.2⟩
  | .mdata _ e, h | .proj _ _ e, h => Expr.suppIn_of_fvarsIn (e := e) h

end Lean4Lean

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem Except.bind_ok' {ε α β} {x : Except ε α} {f : α → Except ε β} {r : β}
    (h : (x >>= f) = .ok r) : ∃ a, x = .ok a ∧ f a = .ok r := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- A loop over a list that only yields, run to success, ran its body to success on each
element. -/
theorem Except.forIn_ok {ε α} {f : α → PUnit → Except ε (ForInStep PUnit)}
    (hf : ∀ x u s, f x u = .ok s → s = .yield PUnit.unit) :
    ∀ {l : List α} {r : PUnit}, forIn l PUnit.unit f = .ok r → ∀ x ∈ l, ∃ s, f x PUnit.unit = .ok s
  | [], _, _ => nofun
  | x :: l, r, h => by
    rw [List.forIn_cons] at h
    obtain ⟨s, h1, h2⟩ := Except.bind_ok' h
    obtain rfl := hf _ _ _ h1
    intro y hy
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨_, h1⟩
    · exact Except.forIn_ok hf h2 y hy

/-- The checks `addInductive` runs on its input before eliminating nested occurrences give the
closedness the elimination's facts assume. -/
theorem addInductive_inputChecks.WF (env : Environment) (types : List InductiveType) :
    (forIn (m := Except Exception) types PUnit.unit fun indType _ => do
      env.checkNoMVarNoFVar indType.name indType.type
      checkClosed indType.name indType.type
      forIn (m := Except Exception) indType.ctors PUnit.unit fun ctor _ => do
        env.checkNoMVarNoFVar ctor.name ctor.type
        checkClosed ctor.name ctor.type
        checkNoNestedAux ctor.name ctor.type
        pure (ForInStep.yield PUnit.unit)
      pure (ForInStep.yield PUnit.unit)).WF
      fun _ => ∀ T ∈ types, ElimNestedInductive.TypeClosed T := by
  intro _ h T hT
  have yld {α} {m : Except Exception α} {s} (h : (m >>= fun _ =>
      (pure (ForInStep.yield PUnit.unit) : Except Exception _)) = .ok s) :
      s = .yield PUnit.unit := by
    obtain ⟨_, -, h⟩ := Except.bind_ok' h; cases h; rfl
  obtain ⟨s, hs⟩ := Except.forIn_ok (fun _ _ _ h => by
    obtain ⟨_, -, h⟩ := Except.bind_ok' h
    obtain ⟨_, -, h⟩ := Except.bind_ok' h
    exact yld h) h T hT
  obtain ⟨_, h1, hs⟩ := Except.bind_ok' hs
  obtain ⟨_, h2, hs⟩ := Except.bind_ok' hs
  obtain ⟨_, h3, -⟩ := Except.bind_ok' hs
  refine ⟨Expr.suppIn_of_fvarsIn (checkNoMVarNoFVar.WF _ _ _ _ h1), checkClosed.WF _ _ _ h2,
    fun c hc => ?_⟩
  obtain ⟨s', hs'⟩ := Except.forIn_ok (fun _ _ _ h => by
    obtain ⟨_, -, h⟩ := Except.bind_ok' h
    obtain ⟨_, -, h⟩ := Except.bind_ok' h
    exact yld h) h3 c hc
  obtain ⟨_, c1, hs'⟩ := Except.bind_ok' hs'
  obtain ⟨_, c2, -⟩ := Except.bind_ok' hs'
  exact ⟨Expr.suppIn_of_fvarsIn (checkNoMVarNoFVar.WF _ _ _ _ c1), checkClosed.WF _ _ _ c2⟩

end Lean4Lean
