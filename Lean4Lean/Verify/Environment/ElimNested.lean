import Lean4Lean.Inductive.Add
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.Name

/-!
# Eliminating nested occurrences from a block without any

`ElimNestedInductive.run` records each nested occurrence it replaces in `nestedAux`, and only adds
auxiliary types after recording one. So when it ends with nothing recorded, no step recorded
anything (`Quiet`), every replacement left its term alone, and the block's types come back with
their names, and, when there are no parameters to open and close again, unchanged.
-/

namespace Lean4Lean.ElimNestedInductive
open Lean hiding Environment Exception
open Kernel

/-- Run from `s` to `s'` with nothing nested recorded by the end: nothing was recorded at the
start either, the new types are unchanged, and the result satisfies `P`. -/
def Quiet (x : M α) (P : α → Prop) : Prop :=
  ∀ env s a s', x env s = .ok (a, s') → s'.nestedAux = #[] →
    s.nestedAux = #[] ∧ s'.newTypes = s.newTypes ∧ P a

theorem bind_apply {x : M α} {f : α → M β} {env s} :
    (x >>= f) env s = match x env s with
      | .error err => .error err
      | .ok v => f v.1 env v.2 := by
  show StateT.bind (x env) (fun a => f a env) s = _
  simp only [StateT.bind]; show Except.bind _ _ = _
  cases x env s <;> rfl

theorem Quiet.bind {x : M α} {f : α → M β} {P Q} (h1 : Quiet x P)
    (h2 : ∀ a, Quiet (f a) fun b => P a → Q b) : Quiet (x >>= f) Q := by
  intro env s b s' h e
  rw [bind_apply] at h
  split at h
  · cases h
  · rename_i v h₁
    obtain ⟨e₁, hn, hb⟩ := h2 v.1 env v.2 b s' h e
    obtain ⟨e₀, hn₀, hp⟩ := h1 env s v.1 v.2 h₁ e₁
    exact ⟨e₀, hn.trans hn₀, hb hp⟩

theorem Quiet.mono {x : M α} {P Q : α → Prop} (H : Quiet x P) (h : ∀ a, P a → Q a) : Quiet x Q :=
  fun env s a s' h1 e => let ⟨a1, a2, a3⟩ := H env s a s' h1 e; ⟨a1, a2, h a a3⟩

theorem Quiet.pure {a : α} {P : α → Prop} (h : P a) : Quiet (pure a : M α) P := by
  rintro env s _ _ ⟨⟩ e; exact ⟨e, rfl, h⟩

theorem Quiet.get : Quiet (get : M State) fun _ => True := by
  rintro env s _ _ ⟨⟩ e; exact ⟨e, rfl, trivial⟩

theorem Quiet.read : Quiet (read : M Environment) fun _ => True := by
  rintro env s _ _ ⟨⟩ e; exact ⟨e, rfl, trivial⟩

theorem Quiet.liftExcept {x : Except Exception α} {P : α → Prop} (h : ∀ a, x = .ok a → P a) :
    Quiet (liftM x : M α) P := by
  intro env s a s' h1 e
  cases hx : x with
  | error => rw [hx] at h1; cases h1
  | ok a' => rw [hx] at h1; cases h1; exact ⟨e, rfl, h _ hx⟩

theorem Quiet.default {P : α → Prop} [Inhabited α] (h : P default) :
    Quiet (default : M α) P := by
  rintro env s _ _ ⟨⟩ e; exact ⟨e, rfl, h⟩

/-- A computation that leaves the state alone. -/
def Pres (x : M α) : Prop := ∀ env s a s', x env s = .ok (a, s') → s' = s

theorem Pres.quiet {x : M α} (H : Pres x) : Quiet x fun _ => True := by
  intro env s a s' h e; cases H env s a s' h; exact ⟨e, rfl, trivial⟩

theorem Pres.bind {x : M α} {f : α → M β} (h1 : Pres x) (h2 : ∀ a, Pres (f a)) :
    Pres (x >>= f) := by
  intro env s b s' h
  rw [bind_apply] at h
  split at h
  · cases h
  · rename_i v h₁; cases h1 env s _ _ h₁; exact h2 _ env _ _ _ h

theorem Pres.pure {a : α} : Pres (pure a : M α) := by rintro _ _ _ _ ⟨⟩; rfl
theorem Pres.get : Pres (get : M State) := by rintro _ _ _ _ ⟨⟩; rfl
theorem Pres.read : Pres (read : M Environment) := by rintro _ _ _ _ ⟨⟩; rfl
theorem Pres.throw {e : Exception} : Pres (throw e : M α) := by rintro _ _ _ _ ⟨⟩
theorem Pres.liftExcept {x : Except Exception α} : Pres (liftM x : M α) := by
  intro env s a s' h; cases x <;> cases h; rfl
theorem Pres.default [Inhabited α] : Pres (default : M α) := by rintro _ _ _ _ ⟨⟩; rfl

theorem Pres.forIn_list {l : List β} {init : σ} {body : β → σ → M (ForInStep σ)}
    (h : ∀ b r, Pres (body b r)) : Pres (forIn l init body) := by
  induction l generalizing init with
  | nil => exact Pres.pure
  | cons b l ih =>
    rw [List.forIn_cons]
    refine Pres.bind (h b init) fun r => ?_
    cases r
    · exact Pres.pure
    · exact ih

/-- Decompose a computation that never writes the state. -/
macro "pres_tac" : tactic => `(tactic| repeat' (first
  | exact Pres.pure | exact Pres.get | exact Pres.read | exact Pres.throw
  | exact Pres.liftExcept | exact Pres.default
  | (rw [Std.Legacy.Range.forIn_eq_forIn_range']; refine Pres.forIn_list fun _ _ => ?_)
  | refine Pres.bind ?_ fun _ => ?_
  | split
  | (dsimp only; done)
  | intro _))

theorem isNestedInductiveApp?_pres (e : Expr) : Pres (isNestedInductiveApp? e) := by
  unfold isNestedInductiveApp?
  dsimp only
  pres_tac

theorem mkUniqueName.loop_state {n : Name} {env : Environment} {s : State}
    (i : Nat) (fuel : UInt64) {a s'} (h : mkUniqueName.loop n env s i fuel = .ok (a, s')) :
    s'.nestedAux = s.nestedAux ∧ s'.newTypes = s.newTypes := by
  rw [mkUniqueName.loop] at h
  split at h
  · split at h
    · cases h
    · exact mkUniqueName.loop_state (i + 1) (fuel - 1) h
  · cases h; exact ⟨rfl, rfl⟩
termination_by fuel.toNat
decreasing_by
  rename_i h
  have : fuel.toNat ≠ 0 := fun h' => h (UInt64.toNat_inj.1 (by simpa using h'))
  rw [UInt64.toNat_sub_of_le _ _
    (by simpa [UInt64.le_iff_toNat_le] using Nat.one_le_iff_ne_zero.2 this)]
  simp; omega

theorem mkUniqueName_quiet (n : Name) : Quiet (mkUniqueName n) fun _ => True := by
  intro env s a s' h e
  have := mkUniqueName.loop_state _ _ h
  exact ⟨this.1 ▸ e, this.2, trivial⟩

/-- As `Quiet`, but the new types may change. -/
def Mono (x : M α) (P : α → Prop) : Prop :=
  ∀ env s a s', x env s = .ok (a, s') → s'.nestedAux = #[] → s.nestedAux = #[] ∧ P a

theorem Quiet.toMono {x : M α} {P} (H : Quiet x P) : Mono x P :=
  fun env s a s' h e => let ⟨h1, _, h3⟩ := H env s a s' h e; ⟨h1, h3⟩

theorem Mono.bind {x : M α} {f : α → M β} {P Q} (h1 : Mono x P)
    (h2 : ∀ a, Mono (f a) fun b => P a → Q b) : Mono (x >>= f) Q := by
  intro env s b s' h e
  rw [bind_apply] at h
  split at h
  · cases h
  · rename_i v h₁
    obtain ⟨e₁, hb⟩ := h2 v.1 env v.2 b s' h e
    obtain ⟨e₀, hp⟩ := h1 env s v.1 v.2 h₁ e₁
    exact ⟨e₀, hb hp⟩

/-- A computation that cannot end with nothing recorded is `Quiet` vacuously. -/
theorem Quiet.of_mono_false {x : M α} {P} (H : Mono x fun _ => False) : Quiet x P :=
  fun env s a s' h e => (H env s a s' h e).2.elim

theorem Mono.modify {f : State → State} (hf : ∀ s, (f s).nestedAux = #[] → s.nestedAux = #[]) :
    Mono (_root_.modify f : M PUnit) fun _ => True := by
  rintro env s _ _ ⟨⟩ e; exact ⟨hf s e, trivial⟩

theorem Mono.pushAux {p} :
    Mono (_root_.modify fun st => { st with nestedAux := st.nestedAux.push p } : M PUnit)
      fun _ => False := by
  rintro env s _ _ ⟨⟩ e; simp at e

theorem Quiet.withState {f : State → M α} {Q}
    (H : ∀ st, ∀ env a s', f st env st = .ok (a, s') → s'.nestedAux = #[] →
      st.nestedAux = #[] ∧ s'.newTypes = st.newTypes ∧ Q a) :
    Quiet ((MonadState.get : M State) >>= f) Q := by
  intro env s a s' h e
  rw [bind_apply] at h
  exact H s env a s' h e

def stepVal : ForInStep σ → σ
  | .done a | .yield a => a

theorem Quiet.forIn_list {l : List β} {init : σ} {body : β → σ → M (ForInStep σ)}
    {I : σ → Prop} (h : ∀ b r, Quiet (body b r) fun st => I r → I (stepVal st)) :
    Quiet (forIn l init body) fun r => I init → I r := by
  induction l generalizing init with
  | nil => exact Quiet.pure id
  | cons b l ih =>
    rw [List.forIn_cons]
    refine Quiet.bind (h b init) fun r => ?_
    cases r with
    | done a => exact Quiet.pure fun h1 h2 => h1 h2
    | yield a => exact (ih (init := a)).mono fun _ h1 h2 h3 => h1 (h2 h3)

theorem Pres.mapM {l : List β} {f : β → M γ} (h : ∀ b, Pres (f b)) : Pres (l.mapM f) := by
  induction l with
  | nil => exact Pres.pure
  | cons b l ih =>
    rw [List.mapM_cons]
    exact Pres.bind (h b) fun _ => Pres.bind ih fun _ => Pres.pure

theorem replaceParams_pres (params e As) : Pres (replaceParams params e As) := by
  unfold replaceParams; pres_tac

theorem Quiet.withAppAux {k : Expr → Array Expr → M α} {Q}
    (h : ∀ fn args, Quiet (k fn args) Q) : ∀ e args i, Quiet (Expr.withAppAux k e args i) Q
  | .app f a, args, i => by rw [Expr.withAppAux.eq_def]; exact Quiet.withAppAux h f _ _
  | .bvar .., _, _ | .fvar .., _, _ | .mvar .., _, _ | .sort .., _, _ | .const .., _, _
  | .lam .., _, _ | .forallE .., _, _ | .letE .., _, _ | .lit .., _, _ | .mdata .., _, _
  | .proj .., _, _ => by rw [Expr.withAppAux.eq_def]; exact h _ _

theorem Pres.mono {x : M α} (H : Pres x) : Mono x fun _ => True := H.quiet.toMono

theorem Mono.pure {a : α} : Mono (pure a : M α) fun _ => True := Pres.pure.mono

theorem Mono.trivial {x : M α} {P : α → Prop} (H : Mono x fun _ => True) (h : ∀ a, P a) :
    Mono x P := fun env s a s' h1 e => ⟨(H env s a s' h1 e).1, h a⟩

/-- Decompose a computation that only adds to the state's records. -/
macro "mono_tac" : tactic => `(tactic| repeat' (first
  | exact Pres.pure.mono | exact Pres.get.mono | exact Pres.read.mono
  | exact Pres.liftExcept.mono | exact Pres.default.mono
  | exact (Pres.mapM fun _ => by pres_tac).mono
  | exact Mono.modify fun _ h => h
  | (refine Mono.bind (P := fun _ => True) ?_ fun _ => Mono.trivial ?_ fun _ _ => True.intro)
  | split
  | (dsimp only; done)
  | intro _))

theorem replaceIfNested_quiet (lctx : LocalContext) (params As : Array Expr) (e : Expr) :
    Quiet (replaceIfNested lctx params As e) (· = none) := by
  unfold replaceIfNested
  refine Quiet.bind (isNestedInductiveApp?_pres e).quiet fun r => ?_
  cases r with
  | none => exact Quiet.pure fun _ => rfl
  | some I_val =>
    refine (Quiet.withAppAux (fun fn args => ?_) _ _ _).mono fun _ h _ => h
    split
    · dsimp only
      split
      · refine Quiet.bind (replaceParams_pres _ _ _).quiet fun Iparams => ?_
        refine (Quiet.withState fun st => ?_).mono fun _ h _ => h
        rcases hfs : Array.findSome? (fun x : Expr × Name =>
          if (x.fst == Iparams) = true then some x.snd else none) st.nestedAux with _ | aux
        · simp only [hfs]
          refine fun env a s' h e => (?_ : Quiet _ (· = none)) env st a s' h e
          refine Quiet.bind Quiet.read fun env => ?_
          refine Quiet.bind (Quiet.forIn_list (I := (· = none)) fun J r => ?_) fun r => ?_
          · refine Quiet.bind Pres.liftExcept.quiet fun x => ?_
            split
            · refine Quiet.bind (mkUniqueName_quiet _) fun _ => ?_
              refine Quiet.bind Pres.liftExcept.quiet fun _ => ?_
              refine Quiet.bind (replaceParams_pres _ _ _).quiet fun _ => ?_
              refine Quiet.of_mono_false (Mono.bind Mono.pushAux fun _ => Mono.trivial ?_ fun _ h => h)
              mono_tac
            · intro env s a s' h e
              cases h; exact ⟨e, rfl, fun _ h => h⟩
          · split
            · exact Quiet.pure fun h _ => h rfl
            · exact Quiet.default fun _ _ => rfl
        · simp only [hfs]
          intro env a s' h e
          cases h; rw [e] at hfs; simp at hfs
      · exact Quiet.default rfl
    · exact Quiet.default rfl

theorem replaceNoCacheT_quiet {f : Expr → M (Option Expr)} (hf : ∀ e, Quiet (f e) (· = none)) :
    ∀ e : Expr, Quiet (e.replaceNoCacheT f) (· = e) := by
  intro e
  induction e with
  | bvar | fvar | mvar | sort | const | lit =>
    unfold Expr.replaceNoCacheT
    refine Quiet.bind (hf _) fun r => ?_
    cases r
    · exact Quiet.pure fun _ => rfl
    · exact Quiet.pure fun h => nomatch h
  | app f' a ih1 ih2 =>
    unfold Expr.replaceNoCacheT
    refine Quiet.bind (hf _) fun r => ?_
    cases r
    · refine Quiet.bind ih1 fun _ => Quiet.bind ih2 fun _ => Quiet.pure ?_
      rintro rfl rfl _; rfl
    · exact Quiet.pure fun h => nomatch h
  | lam _ d b _ ih1 ih2 | forallE _ d b _ ih1 ih2 =>
    unfold Expr.replaceNoCacheT
    refine Quiet.bind (hf _) fun r => ?_
    cases r
    · refine Quiet.bind ih1 fun _ => Quiet.bind ih2 fun _ => Quiet.pure ?_
      rintro rfl rfl _; rfl
    · exact Quiet.pure fun h => nomatch h
  | letE _ t v b _ ih1 ih2 ih3 =>
    unfold Expr.replaceNoCacheT
    refine Quiet.bind (hf _) fun r => ?_
    cases r
    · refine Quiet.bind ih1 fun _ => Quiet.bind ih2 fun _ => Quiet.bind ih3 fun _ => Quiet.pure ?_
      rintro rfl rfl rfl _; rfl
    · exact Quiet.pure fun h => nomatch h
  | mdata _ b ih | proj _ _ b ih =>
    unfold Expr.replaceNoCacheT
    refine Quiet.bind (hf _) fun r => ?_
    cases r
    · refine Quiet.bind ih fun _ => Quiet.pure ?_
      rintro rfl _; rfl
    · exact Quiet.pure fun h => nomatch h

theorem Quiet.throw {e : Exception} {P : α → Prop} : Quiet (throw e : M α) P := by
  rintro _ _ _ _ ⟨⟩

theorem mkFreshId_quiet : Quiet (mkFreshId : M Name) fun _ => True := by
  rintro env s a s' ⟨⟩ e; exact ⟨e, rfl, trivial⟩

theorem withParams.loop_quiet {k : LocalContext → Expr → Array Expr → M α} {Q} {N : Nat}
    (hk : ∀ lctx ty ps, ps.size = N → Quiet (k lctx ty ps) Q) :
    ∀ n lctx type params, params.size + n = N → Quiet (withParams.loop k lctx type params n) Q
  | 0, _, _, _, hN => by rw [withParams.loop]; exact hk _ _ _ hN
  | n + 1, lctx, type, params, hN => by
    unfold withParams.loop
    split
    · exact Quiet.bind mkFreshId_quiet fun _ =>
        (withParams.loop_quiet hk n _ _ _ (by simp; omega)).mono fun _ h _ => h
    · exact Quiet.throw

theorem Quiet.mapM {l : List β} {f : β → M γ} {R : β → γ → Prop}
    (h : ∀ a ∈ l, Quiet (f a) (R a)) : Quiet (l.mapM f) (List.Forall₂ R l) := by
  induction l with
  | nil => exact Quiet.pure .nil
  | cons a l ih =>
    rw [List.mapM_cons]
    exact Quiet.bind (h a (.head _)) fun b =>
      Quiet.bind (ih fun a ha => h a (.tail _ ha)) fun bs => Quiet.pure fun h1 h2 => .cons h2 h1

theorem mkForall_empty (lctx : LocalContext) (e : Expr) : lctx.mkForall #[] e = e := by
  have := LocalContext.mkBinding_eq (isLambda := false) (lctx := lctx) (xs := []) (b := e)
  simp only [List.map_nil] at this
  rw [LocalContext.mkForall, this]
  simp [LocalContext.mkBindingList, LocalContext.mkBindingList.core,
    LocalContext.mkBindingList.go, Expr.abstractList_eq_foldl]

theorem bind_ok {x : M α} {f : α → M β} {env s b s'} (h : (x >>= f) env s = .ok (b, s')) :
    ∃ a s₁, x env s = .ok (a, s₁) ∧ f a env s₁ = .ok (b, s') := by
  rw [bind_apply] at h
  split at h
  · cases h
  · rename_i v hv; exact ⟨v.1, v.2, hv, h⟩

/-- The step of `run`'s loop on one constructor, with its assertion's failure as `default`. -/
def ctorStep (nparams : Nat) (params : Array Expr) (ctor : Constructor) : M Constructor :=
  withParams ctor.type nparams fun lctx ctorType As =>
    if (As.size == nparams) = true then do
      let e ← replaceAllNested lctx params As ctorType
      pure { name := ctor.name, type := lctx.mkForall As e }
    else default

theorem ctorStep_quiet (nparams : Nat) (params : Array Expr) (ctor : Constructor) :
    Quiet (ctorStep nparams params ctor) fun ct =>
      ct.name = ctor.name ∧ (nparams = 0 → ct = ctor) := by
  have hrep (lctx As ty) : Quiet (replaceAllNested lctx params As ty) (· = ty) :=
    replaceNoCacheT_quiet (replaceIfNested_quiet lctx params As) ty
  by_cases h0 : nparams = 0
  · subst h0
    unfold ctorStep withParams
    rw [withParams.loop]
    simp only [Array.size_empty, beq_self_eq_true, if_true]
    refine Quiet.bind (hrep _ _ _) fun e => Quiet.pure ?_
    rintro rfl; rw [mkForall_empty]; exact ⟨rfl, fun _ => rfl⟩
  · unfold ctorStep withParams
    refine withParams.loop_quiet (N := nparams) (fun lctx ty As hN => ?_) _ _ _ _ (by simp)
    rw [if_pos (by simp [hN])]
    exact Quiet.bind (hrep _ _ _) fun _ => Quiet.pure fun _ => ⟨rfl, fun h => (h0 h).elim⟩

theorem forall₂_ctors {P : Prop} : ∀ {l l' : List Constructor},
    List.Forall₂ (fun ct ct' => ct'.name = ct.name ∧ (P → ct' = ct)) l l' →
    l.map (·.name) = l'.map (·.name) ∧ (P → l' = l)
  | [], [], .nil => ⟨rfl, fun _ => rfl⟩
  | _ :: _, _ :: _, .cons h1 t =>
    let ih := forall₂_ctors t
    ⟨by simp [h1.1, ih.1], fun h0 => by rw [h1.2 h0, ih.2 h0]⟩

theorem size_foldl_insert : ∀ (l : List (Expr × Name)) (m : Std.TreeMap Name Expr Name.quickCmp),
    (l.foldl (fun m x => m.insert x.2 x.1) m).size = 0 → l = []
  | [], _, _ => rfl
  | x :: l, m, h => by
    have h1 : ∀ (l : List (Expr × Name)) (m : Std.TreeMap Name Expr Name.quickCmp),
        m.size ≤ (l.foldl (fun m x => m.insert x.2 x.1) m).size := by
      intro l; induction l with
      | nil => intro _; exact Nat.le_refl _
      | cons y l ih => intro m; exact Nat.le_trans Std.TreeMap.size_le_size_insert (ih _)
    have h2 : (m.insert x.2 x.1).size ≠ 0 := by
      have := Std.TreeMap.isEmpty_insert (t := m) (k := x.2) (v := x.1)
      rw [Std.TreeMap.isEmpty_eq_size_eq_zero] at this
      simpa using this
    have := h1 l (m.insert x.2 x.1)
    simp only [List.foldl_cons] at h
    omega

/-- What the loop of `run` keeps of the types it was given. -/
def KeepsTypes (nparams : Nat) (types : List InductiveType) (ts : List InductiveType) : Prop :=
  ts.map (·.name) = types.map (·.name) ∧ (nparams = 0 → ts = types)

theorem run.loop_spec {nparams : Nat} {lctx : LocalContext} {params : Array Expr}
    {types : List InductiveType} {env : Environment} :
    ∀ (fuel i : Nat) (s : State) (res : Result) (s' : State),
      run.loop nparams lctx params i fuel env s = .ok (res, s') → res.aux2nested.size = 0 →
      s.nestedAux = #[] ∧ (KeepsTypes nparams types s.newTypes.toList →
        KeepsTypes nparams types res.types)
  | 0, i, s, res, s', h, _ => by rw [run.loop] at h; cases h
  | fuel + 1, i, s, res, s', h, hz => by
    rw [run.loop, bind_apply] at h
    rw [show (MonadState.get : M State) env s = .ok (s, s) from rfl] at h
    dsimp only at h
    split at h
    · rename_i hi
      obtain ⟨ctors, s₁, hv, h⟩ := bind_ok h
      obtain ⟨_, s₂, hm, h⟩ := bind_ok h
      cases hm
      have ih := run.loop_spec (types := types) fuel (i + 1) _ res s' h hz
      obtain ⟨e₀, hnt, hR⟩ := Quiet.mapM (fun ct _ => ctorStep_quiet nparams params ct)
        env s ctors s₁ hv ih.1
      refine ⟨e₀, fun hK => ih.2 ?_⟩
      have hR' := forall₂_ctors hR
      simp only [hnt]
      refine ⟨?_, fun h0 => ?_⟩
      · rw [← hK.1]
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.getElem_map,
          List.getElem_set]
        split <;> simp_all
      · rw [← hK.2 h0, hR'.2 h0]
        apply List.ext_getElem (by simp)
        intro j h1 h2
        simp only [Array.set!_eq_setIfInBounds, Array.toList_setIfInBounds, List.getElem_set]
        split <;> simp_all
    · cases h
      refine ⟨?_, id⟩
      have := size_foldl_insert s.nestedAux.toList ∅ (by
        rw [Array.foldl_toList]; exact hz)
      simpa using this

theorem withParams.loop_ok {k : LocalContext → Expr → Array Expr → M α} {env : Environment}
    {a : α} {s' : State} :
    ∀ n lctx type params s, withParams.loop k lctx type params n env s = .ok (a, s') →
      ∃ lctx' ty ps s₁, s₁.newTypes = s.newTypes ∧ k lctx' ty ps env s₁ = .ok (a, s')
  | 0, lctx, type, params, s, h => by rw [withParams.loop] at h; exact ⟨_, _, _, s, rfl, h⟩
  | n + 1, lctx, type, params, s, h => by
    unfold withParams.loop at h
    split at h
    · obtain ⟨_, s₁, hf, h⟩ := bind_ok h
      cases hf
      obtain ⟨l, t, p, s₂, e, h⟩ := withParams.loop_ok n _ _ _ _ h
      exact ⟨l, t, p, s₂, e, h⟩
    · cases h

/-- Eliminating nested occurrences from a block that has none keeps its types' names, and, without
parameters to open and close again, its types. -/
theorem run_flat {fuel nparams : Nat} {types : List InductiveType} {env : Environment}
    {s : State} {res : Result} (h : (run fuel nparams types env).run' s = .ok res)
    (hs : s.newTypes = types.toArray) (hflat : res.aux2nested.size = 0) :
    KeepsTypes nparams types res.types := by
  obtain ⟨⟨res', s'⟩, h1, h2⟩ : ∃ p, run fuel nparams types env s = .ok p ∧ p.1 = res := by
    revert h; unfold StateT.run'
    cases run fuel nparams types env s <;> simp [Functor.map, Except.map]
  subst h2
  unfold run at h1
  split at h1
  · obtain ⟨lctx, ty, ps, s₁, e, h⟩ := withParams.loop_ok _ _ _ _ _ h1
    refine (run.loop_spec fuel 0 s₁ _ _ h hflat).2 ?_
    rw [e, hs]; exact ⟨rfl, fun _ => rfl⟩
  · cases h1

end Lean4Lean.ElimNestedInductive