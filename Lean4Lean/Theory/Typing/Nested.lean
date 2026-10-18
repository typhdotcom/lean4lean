import Lean4Lean.Theory.Typing.Iota
import Lean4Lean.Theory.Typing.IotaInv
import Lean4Lean.Theory.Typing.ConstsSat

/-!
# Restoring a nested block's translation

The kernel checks a nested block by translating it into a flat one, whose auxiliary types and
constructors are constants, and then restores the recursors it built: each auxiliary constant
applied to the block's parameters becomes the occurrence it stands for
(`ElimNestedInductive.Result.restoreNested`). `VExpr.restore` is that replacement on the
translation.

Typing judgments of the flat block carry over to an environment without the auxiliary constants by
replacing each with a closed term of its type (`VEnv.IsDefEq.replaceConst`): the occurrence, as a
function of the parameters. On a term whose auxiliary constants are all applied to the
parameters, that replacement and `restore` differ by beta reduction (`replaceConst_restore`).
-/

namespace Lean4Lean
open VExpr

/-- What an auxiliary constant stands for, once applied to `n` arguments: the constant `name` at
levels `lvls`, applied to `args`, both stated over the auxiliary constant's levels and its `n`
arguments as variables. -/
structure VAuxHead where
  n : Nat
  name : Name
  lvls : List VLevel
  args : List VExpr

/-- The occurrence an auxiliary constant at levels `ls` applied to `xs` stands for. -/
def VAuxHead.inst (h : VAuxHead) (ls : List VLevel) (xs : List VExpr) : VExpr :=
  .appN (.const h.name (h.lvls.map (·.inst ls)))
    (h.args.map fun a => (a.instL ls).subst (VExpr.Subst.dflt.consList xs))

/-- The occurrence as a function of the arguments, with binder types `Ps`. -/
def VAuxHead.lam (h : VAuxHead) (Ps : List VExpr) : VExpr :=
  .lams Ps (.appN (.const h.name h.lvls) h.args)

theorem VInductiveType.typeHead_eq_inst {T : VInductiveType} {n : VNested}
    (hn : T.nested = some n) (k : Nat) (ls : List VLevel) (ps : List VExpr) :
    T.typeHead ls ps = VAuxHead.inst ⟨k, n.ind, n.lvls, n.args⟩ ls ps := by
  simp [VInductiveType.typeHead, hn, VAuxHead.inst]

theorem VInductiveType.ctorHead_eq_inst {T : VInductiveType} {n : VNested}
    (hn : T.nested = some n) (c : VConstructor) (k : Nat) (ls : List VLevel) (ps : List VExpr) :
    T.ctorHead c ls ps = VAuxHead.inst ⟨k, c.name, n.lvls, n.args⟩ ls ps := by
  simp [VInductiveType.ctorHead, hn, VAuxHead.inst]

namespace VExpr

/-! ### Restoring auxiliary applications -/

/-- The head constant of `e`'s application spine, and its arguments. -/
def constSpine? : VExpr → Option (Name × List VLevel × List VExpr)
  | .const c ls => some (c, ls, [])
  | .app f a => (constSpine? f).map fun (c, ls, as) => (c, ls, as ++ [a])
  | _ => none

theorem constSpine?_appN' : ∀ {f : VExpr} {c ls ys} (xs : List VExpr),
    f.constSpine? = some (c, ls, ys) → (f.appN xs).constSpine? = some (c, ls, ys ++ xs)
  | _, _, _, _, [], h => by simpa using h
  | f, c, ls, ys, x :: xs, h => by
    have := constSpine?_appN' (f := .app f x) (c := c) (ls := ls) (ys := ys ++ [x]) xs
      (by simp [constSpine?, h])
    simpa [VExpr.appN] using this

theorem constSpine?_appN (c : Name) (ls : List VLevel) (xs : List VExpr) :
    (VExpr.appN (.const c ls) xs).constSpine? = some (c, ls, xs) :=
  constSpine?_appN' (ys := []) xs rfl

theorem eq_of_constSpine? : ∀ {e : VExpr} {c ls xs}, e.constSpine? = some (c, ls, xs) →
    e = .appN (.const c ls) xs
  | .const _ _, _, _, _, h => by cases h; rfl
  | .app f a, c, ls, xs, h => by
    simp only [constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', xs'⟩, h1, h2⟩ := h
    cases h2
    rw [eq_of_constSpine? h1, VExpr.appN_append]; rfl

/-- The replacement `restore` makes at a node: an auxiliary constant applied to exactly as many
arguments as it stands for a function of. -/
def restoreAux (R : Name → Option VAuxHead) (e : VExpr) : Option VExpr :=
  e.constSpine?.bind fun (c, ls, xs) =>
    (R c).bind fun h => if xs.length = h.n then some (h.inst ls xs) else none

/-- `ElimNestedInductive.Result.restoreNested` on the translation: top down, a constant `ren`
renames is renamed, and an auxiliary constant `R` describes, applied to exactly its arguments, is
replaced by the occurrence it stands for, without descending into it. -/
def restore (R : Name → Option VAuxHead) (ren : Name → Option Name) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => match ren c with
    | some c' => .const c' ls
    | none => (restoreAux R (.const c ls)).getD (.const c ls)
  | .app f a => (restoreAux R (.app f a)).getD (.app (restore R ren f) (restore R ren a))
  | .lam A b => .lam (restore R ren A) (restore R ren b)
  | .forallE A b => .forallE (restore R ren A) (restore R ren b)
  | .proj s i e => .proj s i (restore R ren e)

section
variable {R : Name → Option VAuxHead} {ren : Name → Option Name}

theorem VAuxHead.inst_subst (h : VAuxHead) (ls : List VLevel) (xs : List VExpr) (σ : Subst) :
    (h.inst ls xs).subst σ = h.inst ls (xs.map (·.subst σ)) := by
  simp [VAuxHead.inst, VExpr.subst_appN, VExpr.subst, Function.comp_def, VExpr.subst_subst,
    VExpr.Subst.consList_comp, VExpr.Subst.dflt_comp]

theorem VAuxHead.inst_instL (h : VAuxHead) (ls ls' : List VLevel) (xs : List VExpr) :
    (h.inst ls xs).instL ls' = h.inst (ls.map (·.inst ls')) (xs.map (·.instL ls')) := by
  simp [VAuxHead.inst, VExpr.instL_appN, VExpr.instL, VExpr.instL_subst,
    VExpr.Subst.consList_instL, VExpr.instL_instL, VLevel.inst_inst, Function.comp_def]
  rfl

theorem restoreAux_eq_none {e : VExpr} (H : e.ConstsSat (R · = none)) : restoreAux R e = none := by
  unfold restoreAux
  cases h : e.constSpine? with
  | none => rfl
  | some p =>
    obtain ⟨c, ls, xs⟩ := p
    rw [eq_of_constSpine? h, ConstsSat.appN] at H
    simp [show R c = none from H.1]

theorem restore_of_constsSat :
    ∀ {e : VExpr}, e.ConstsSat (fun c => R c = none ∧ ren c = none) → e.restore R ren = e
  | .bvar _, _ | .sort _, _ => rfl
  | .const c ls, H => by
    simp [restore, H.2, restoreAux_eq_none (e := .const c ls) (H.1 : R c = none)]
  | .app f a, H => by
    simp only [restore, restoreAux_eq_none (e := .app f a) (H.mono fun _ h => h.1),
      Option.getD_none, restore_of_constsSat H.1, restore_of_constsSat H.2]
  | .lam .., H | .forallE .., H => by
    simp [restore, restore_of_constsSat H.1, restore_of_constsSat H.2]
  | .proj _ _ e, H => by simp [restore, restore_of_constsSat (e := e) H]

theorem constSpine?_subst_some {σ : Subst} : ∀ {e : VExpr} {c ls xs},
    e.constSpine? = some (c, ls, xs) → (e.subst σ).constSpine? = some (c, ls, xs.map (·.subst σ))
  | e, c, ls, xs, h => by
    rw [eq_of_constSpine? h, VExpr.subst_appN, VExpr.subst_const, constSpine?_appN]

theorem constSpine?_subst_none {σ : Subst} {p : Name → Prop} (hσ : ∀ i, (σ i).ConstsSat p) :
    ∀ {e : VExpr} {c ls xs}, e.constSpine? = none →
      (e.subst σ).constSpine? = some (c, ls, xs) → p c
  | .bvar i, c, ls, xs, _, h => by
    have := hσ i
    rw [VExpr.subst_bvar, eq_of_constSpine? h, ConstsSat.appN] at *
    exact this.1
  | .app f a, c, ls, xs, h0, h => by
    simp only [constSpine?, Option.map_eq_none_iff] at h0
    simp only [VExpr.subst_app, constSpine?, Option.map_eq_some_iff] at h
    obtain ⟨⟨c', ls', xs'⟩, h1, h2⟩ := h
    cases h2
    exact constSpine?_subst_none hσ h0 h1
  | .sort _, _, _, _, _, h | .lam .., _, _, _, _, h | .forallE .., _, _, _, _, h
  | .proj .., _, _, _, _, h => by cases h
  | .const .., _, _, _, h0, _ => by cases h0

theorem restoreAux_subst {σ : Subst} (hσ : ∀ i, (σ i).ConstsSat (R · = none)) (e : VExpr) :
    restoreAux R (e.subst σ) = (restoreAux R e).map (·.subst σ) := by
  unfold restoreAux
  cases h : e.constSpine? with
  | some p =>
    obtain ⟨c, ls, xs⟩ := p
    rw [constSpine?_subst_some h]
    simp only [Option.bind_some]
    cases R c with
    | none => rfl
    | some hd =>
      simp only [Option.bind_some, List.length_map]
      split <;> simp [VAuxHead.inst_subst]
  | none =>
    simp only [Option.bind_none, Option.map_none]
    cases h' : (e.subst σ).constSpine? with
    | none => rfl
    | some p =>
      obtain ⟨c, ls, xs⟩ := p
      simp [constSpine?_subst_none hσ h h']

theorem restore_subst :
    ∀ {e : VExpr} {σ : Subst}, (∀ i, (σ i).ConstsSat (fun c => R c = none ∧ ren c = none)) →
      (e.subst σ).restore R ren = (e.restore R ren).subst σ
  | .bvar i, σ, hσ => by simp [restore, restore_of_constsSat (hσ i)]
  | .sort _, _, _ => rfl
  | .const c ls, σ, hσ => by
    simp only [VExpr.subst_const, restore]
    split
    · rfl
    · have := restoreAux_subst (R := R) (fun i => (hσ i).mono fun _ h => h.1) (.const c ls)
      simp only [VExpr.subst_const] at this
      cases hr : restoreAux R (.const c ls) with
      | none => rfl
      | some r =>
        rw [hr] at this
        simp only [Option.map_some, Option.some.injEq] at this
        simp [← this]
  | .app f a, σ, hσ => by
    have := restoreAux_subst (R := R) (fun i => (hσ i).mono fun _ h => h.1) (.app f a)
    simp only [VExpr.subst_app] at this
    simp only [VExpr.subst_app, restore, this]
    cases restoreAux R (.app f a) with
    | some r => rfl
    | none => simp [restore_subst (e := f) hσ, restore_subst (e := a) hσ]
  | .lam A b, σ, hσ | .forallE A b, σ, hσ => by
    have hσ' : ∀ i, (σ.lift i).ConstsSat (fun c => R c = none ∧ ren c = none) := by
      intro i; cases i with
      | zero => trivial
      | succ i => exact (hσ i).liftN
    simp [VExpr.subst, restore, restore_subst (e := A) hσ, restore_subst (e := b) hσ']
  | .proj _ _ e, σ, hσ => by simp [VExpr.subst, restore, restore_subst (e := e) hσ]

theorem restore_liftN {e : VExpr} {n k : Nat} :
    (e.liftN n k).restore R ren = (e.restore R ren).liftN n k := by
  rw [liftN_eq_subst, liftN_eq_subst, restore_subst (R := R) (ren := ren)
    (σ := Subst.ofLift _) fun _ => trivial]

theorem restore_inst {e a : VExpr} {k : Nat}
    (ha : a.ConstsSat (fun c => R c = none ∧ ren c = none)) :
    (e.inst a k).restore R ren = (e.restore R ren).inst a k := by
  rw [instN_eq, instN_eq, restore_subst]
  intro i
  induction k generalizing i with
  | zero => cases i <;> simp [Subst.liftN, Subst.cons, Subst.id, ConstsSat, ha]
  | succ k ih =>
    cases i with
    | zero => trivial
    | succ i => exact (ih i).liftN

theorem constSpine?_instL {ls' : List VLevel} : ∀ {e : VExpr},
    (e.instL ls').constSpine? =
      (e.constSpine?).map fun (c, ls, xs) => (c, ls.map (·.inst ls'), xs.map (·.instL ls'))
  | .const _ _ => rfl
  | .app f a => by
    simp only [instL, constSpine?, constSpine?_instL (e := f), Option.map_map]
    congr 1; funext ⟨c, ls, xs⟩; simp
  | .bvar _ | .sort _ | .lam .. | .forallE .. | .proj .. => rfl

theorem restoreAux_instL (ls' : List VLevel) (e : VExpr) :
    restoreAux R (e.instL ls') = (restoreAux R e).map (·.instL ls') := by
  unfold restoreAux
  rw [constSpine?_instL]
  cases e.constSpine? with
  | none => rfl
  | some p =>
    obtain ⟨c, ls, xs⟩ := p
    simp only [Option.map_some, Option.bind_some]
    cases R c with
    | none => rfl
    | some hd =>
      simp only [Option.bind_some, List.length_map]
      split <;> simp [VAuxHead.inst_instL]

theorem restore_instL {ls' : List VLevel} : ∀ {e : VExpr},
    (e.instL ls').restore R ren = (e.restore R ren).instL ls'
  | .bvar _ | .sort _ => rfl
  | .const c ls => by
    simp only [instL, restore]
    split
    · rfl
    · have := restoreAux_instL (R := R) ls' (.const c ls)
      simp only [instL] at this
      rw [this]; cases restoreAux R (.const c ls) <;> rfl
  | .app f a => by
    have := restoreAux_instL (R := R) ls' (.app f a)
    simp only [instL] at this
    simp only [instL, restore, this]
    cases restoreAux R (.app f a) with
    | some r => rfl
    | none =>
      simp only [Option.map_none, Option.getD_none, restore_instL (e := f), restore_instL (e := a)]
      rfl
  | .lam A b | .forallE A b => by simp [instL, restore, restore_instL (e := A), restore_instL (e := b)]
  | .proj _ _ e => by simp [instL, restore, restore_instL (e := e)]

/-- An auxiliary constant applied to exactly its arguments, then to more, is the occurrence it
stands for applied to the rest, restored. -/
theorem restore_appN {c : Name} {h : VAuxHead} (hc : R c = some h) (hr : ren c = none)
    (ls : List VLevel) {xs : List VExpr} (hxs : xs.length = h.n) :
    ∀ ys : List VExpr, (VExpr.appN (.const c ls) (xs ++ ys)).restore R ren =
      VExpr.appN (h.inst ls xs) (ys.map (·.restore R ren)) := by
  have base : (VExpr.appN (.const c ls) xs).restore R ren = h.inst ls xs := by
    have hA : restoreAux R (VExpr.appN (.const c ls) xs) = some (h.inst ls xs) := by
      simp [restoreAux, constSpine?_appN, hc, hxs]
    rcases List.eq_nil_or_concat xs with rfl | ⟨xs', x, rfl⟩
    · simp only [VExpr.appN] at hA ⊢; simp [restore, hr, hA]
    · rw [List.concat_eq_append, VExpr.appN_append] at hA ⊢
      simp only [VExpr.appN] at hA ⊢
      simp [restore, hA]
  intro ys
  induction h' : ys.length generalizing ys with
  | zero => rw [List.eq_nil_of_length_eq_zero h']; simpa using base
  | succ m ih =>
    obtain ⟨ys, y, rfl⟩ : ∃ ys' y, ys = ys' ++ [y] := by
      rcases List.eq_nil_or_concat ys with rfl | ⟨ys', y, rfl⟩
      · simp at h'
      · exact ⟨ys', y, List.concat_eq_append ..⟩
    have ih := ih ys (by simpa using h')
    have hA : restoreAux R (VExpr.appN (.const c ls) (xs ++ ys ++ [y])) = none := by
      simp [restoreAux, constSpine?_appN, hc, hxs]
    rw [VExpr.appN_append] at hA
    simp only [VExpr.appN] at hA
    rw [← List.append_assoc, VExpr.appN_append]
    simp only [VExpr.appN]
    rw [restore, hA, Option.getD_none, ih, List.map_append, VExpr.appN_append]; rfl

end

/-! ### Replacing constants by closed terms -/

/-- Replaces each constant `c` with `F c = some r` by `r` at the constant's levels. -/
def replaceConst (F : Name → Option VExpr) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u
  | .const c ls => match F c with
    | some r => r.instL ls
    | none => .const c ls
  | .app f a => .app (f.replaceConst F) (a.replaceConst F)
  | .lam A b => .lam (A.replaceConst F) (b.replaceConst F)
  | .forallE A b => .forallE (A.replaceConst F) (b.replaceConst F)
  | .proj s i e => .proj s i (e.replaceConst F)

section
variable {F : Name → Option VExpr}

theorem replaceConst_of_constsSat :
    ∀ {e : VExpr}, e.ConstsSat (F · = none) → e.replaceConst F = e
  | .bvar _, _ | .sort _, _ => rfl
  | .const _ _, H => by simp [replaceConst, show F _ = none from H]
  | .app .., H | .lam .., H | .forallE .., H => by
    simp [replaceConst, replaceConst_of_constsSat H.1, replaceConst_of_constsSat H.2]
  | .proj _ _ e, H => by simp [replaceConst, replaceConst_of_constsSat (e := e) H]

theorem replaceConst_appN (f : VExpr) :
    ∀ as : List VExpr, (f.appN as).replaceConst F = (f.replaceConst F).appN (as.map (·.replaceConst F))
  | [] => rfl
  | a :: as => by simp [VExpr.appN, replaceConst_appN _ as, replaceConst]

/-- The replacements are closed. -/
def ClosedConsts (F : Name → Option VExpr) : Prop := ∀ c r, F c = some r → r.ClosedN

variable (hF : ClosedConsts F)
include hF

theorem replaceConst_liftN : ∀ {e : VExpr} {n k : Nat},
    (e.liftN n k).replaceConst F = (e.replaceConst F).liftN n k
  | .bvar _, _, _ | .sort _, _, _ => rfl
  | .const c ls, n, k => by
    simp only [liftN, replaceConst]
    split
    · next r h => exact ((hF c r h).instL.liftN_eq (Nat.zero_le _)).symm
    · rfl
  | .app f a, _, _ => by simp [liftN, replaceConst, replaceConst_liftN (e := f),
      replaceConst_liftN (e := a)]
  | .lam A b, _, _ | .forallE A b, _, _ => by
    simp [liftN, replaceConst, replaceConst_liftN (e := A), replaceConst_liftN (e := b)]
  | .proj _ _ e, _, _ => by simp [liftN, replaceConst, replaceConst_liftN (e := e)]

theorem replaceConst_lift {e : VExpr} : e.lift.replaceConst F = (e.replaceConst F).lift :=
  replaceConst_liftN hF

theorem replaceConst_inst : ∀ {e a : VExpr} {k : Nat},
    (e.inst a k).replaceConst F = (e.replaceConst F).inst (a.replaceConst F) k
  | .bvar i, a, k => by
    simp only [inst, replaceConst, instVar]
    split
    · rfl
    · split
      · exact replaceConst_liftN hF
      · rfl
  | .sort _, _, _ => rfl
  | .const c ls, a, k => by
    simp only [inst, replaceConst]
    split
    · next r h => exact ((hF c r h).instL.instN_eq (Nat.zero_le _)).symm
    · rfl
  | .app f b, _, _ => by simp [inst, replaceConst, replaceConst_inst (e := f),
      replaceConst_inst (e := b)]
  | .lam A b, _, _ | .forallE A b, _, _ => by
    simp [inst, replaceConst, replaceConst_inst (e := A), replaceConst_inst (e := b)]
  | .proj _ _ e, _, _ => by simp [inst, replaceConst, replaceConst_inst (e := e)]

theorem replaceConst_subst : ∀ {e : VExpr} {σ : Subst},
    (e.subst σ).replaceConst F = (e.replaceConst F).subst fun i => (σ i).replaceConst F
  | .bvar _, _ | .sort _, _ => rfl
  | .const c ls, σ => by
    simp only [subst, replaceConst]
    split
    · next r h => exact ((hF c r h).instL.subst_eq (fun _ h => absurd h (Nat.not_lt_zero _))).symm
    · rfl
  | .app f a, _ => by simp [subst, replaceConst, replaceConst_subst (e := f),
      replaceConst_subst (e := a)]
  | .lam A b, σ | .forallE A b, σ => by
    have : (fun i => (σ.lift i).replaceConst F) = Subst.lift fun i => (σ i).replaceConst F := by
      funext i; cases i <;> simp [Subst.lift, replaceConst, replaceConst_lift hF]
    simp [subst, replaceConst, replaceConst_subst (e := A), replaceConst_subst (e := b), this]
  | .proj _ _ e, _ => by simp [subst, replaceConst, replaceConst_subst (e := e)]

omit hF in
theorem replaceConst_instL : ∀ {e : VExpr} {ls : List VLevel},
    (e.instL ls).replaceConst F = (e.replaceConst F).instL ls
  | .bvar _, _ | .sort _, _ => rfl
  | .const c ls', ls => by
    simp only [instL, replaceConst]
    split
    · rw [instL_instL]
    · rfl
  | .app f a, _ => by simp [instL, replaceConst, replaceConst_instL (e := f),
      replaceConst_instL (e := a)]
  | .lam A b, _ | .forallE A b, _ => by
    simp [instL, replaceConst, replaceConst_instL (e := A), replaceConst_instL (e := b)]
  | .proj _ _ e, _ => by simp [instL, replaceConst, replaceConst_instL (e := e)]

omit hF in
theorem replaceConst_consList (σ : Subst) : ∀ L : List VExpr,
    (fun i => (σ.consList L i).replaceConst F) =
      Subst.consList (fun i => (σ i).replaceConst F) (L.map (·.replaceConst F))
  | [] => rfl
  | a :: L => by
    show (fun i => ((σ.cons a).consList L i).replaceConst F) = _
    rw [replaceConst_consList _ L]
    have : (fun i => (σ.cons a i).replaceConst F) =
        Subst.cons (fun i => (σ i).replaceConst F) (a.replaceConst F) := by
      funext i; cases i <;> rfl
    rw [this]; rfl

omit hF in
theorem replaceConst_projs {s : Name} {k : Nat} {e : VExpr} :
    (VExpr.projs s k e).map (·.replaceConst F) = VExpr.projs s k (e.replaceConst F) :=
  VExpr.projs_map _ fun _ _ => rfl

theorem replaceConst_projType {c : VConstructor}
    (hc : ∀ f ∈ c.fields, f.type.ConstsSat (F · = none))
    (ls : List VLevel) (s : Name) (k : Nat) (As : List VExpr) (e : VExpr) :
    (c.projType ls s k As e).replaceConst F =
      c.projType ls s k (As.map (·.replaceConst F)) (e.replaceConst F) := by
  have hX : (((c.fields[k]?.map VField.type).getD default).instL ls).replaceConst F =
      ((c.fields[k]?.map VField.type).getD default).instL ls := by
    rw [replaceConst_instL]; congr 1
    cases h : c.fields[k]? with
    | none => rfl
    | some f => exact replaceConst_of_constsSat (hc f (List.mem_of_getElem? h))
  simp only [VConstructor.projType, replaceConst_subst hF, hX, replaceConst_consList,
    List.map_append, replaceConst_projs]
  rfl

end

end VExpr

namespace VEnv
open VExpr

/-- `E₁` is `E₀` with the constants `F` replaces added, each replaced by a closed term of its type:
the rest of `E₁`, its rules and its recorded blocks are `E₀`'s and mention none of them. -/
structure ConstSubst (F : Name → Option VExpr) (E₁ E₀ : VEnv) : Prop where
  closed : ClosedConsts F
  const : ∀ c ci, E₁.constants c = some ci →
    (F c = none ∧ E₀.constants c = some ci ∧ ci.type.ConstsSat (F · = none)) ∨
    ∃ r, F c = some r ∧ E₀.HasType ci.uvars [] r (ci.type.replaceConst F)
  defeqs : ∀ df, E₁.defeqs df → E₀.defeqs df ∧ df.lhs.ConstsSat (F · = none) ∧
    df.rhs.ConstsSat (F · = none) ∧ df.type.ConstsSat (F · = none)
  inducts : ∀ s b, E₁.inducts s = some b → E₀.inducts s = some b
  block : ∀ s d t T, E₁.inducts s = some (d, t) → d.types[t]? = some T → F s = none ∧
    ∀ c, T.ctors = [c] → F c.name = none ∧ ∀ f ∈ c.fields, f.type.ConstsSat (F · = none)

theorem _root_.Lean4Lean.Lookup.replaceConst {F : Name → Option VExpr} (hF : ClosedConsts F) {Γ i A}
    (H : Lookup Γ i A) : Lookup (Γ.map (·.replaceConst F)) i (A.replaceConst F) := by
  induction H with
  | zero => rw [replaceConst_lift hF]; exact .zero
  | succ _ ih => rw [replaceConst_lift hF]; exact .succ ih

/-- Typing judgments carry over a constant substitution. -/
theorem IsDefEq.replaceConst {F : Name → Option VExpr} {E₁ E₀ : VEnv} (H₀ : E₀.Ordered)
    (hS : ConstSubst F E₁ E₀) {U Γ e e' A} (H : E₁.IsDefEq U Γ e e' A) :
    E₀.IsDefEq U (Γ.map (·.replaceConst F)) (e.replaceConst F) (e'.replaceConst F)
      (A.replaceConst F) := by
  have hF := hS.closed
  induction H with
  | bvar h => exact .bvar (h.replaceConst hF)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | constDF h1 h2 h3 h4 h5 =>
    rw [replaceConst_instL]
    rcases hS.const _ _ h1 with ⟨hc, h1', hty⟩ | ⟨r, hc, hr⟩
    · simp only [VExpr.replaceConst, hc, replaceConst_of_constsSat hty]
      exact .constDF h1' h2 h3 h4 h5
    · simp only [VExpr.replaceConst, hc]
      have := IsDefEq.instL_r H₀ (Γ := []) trivial h2 h3 h5 hr
      exact this.weak0 H₀
  | appDF _ _ ih1 ih2 =>
    rw [replaceConst_inst hF]; exact .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    simp only [VExpr.replaceConst, replaceConst_inst hF]; exact .beta ih1 ih2
  | eta _ ih =>
    simp only [VExpr.replaceConst, replaceConst_lift hF] at ih ⊢; exact .eta ih
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    obtain ⟨h1', hl, hr, ht⟩ := hS.defeqs _ h1
    simp only [replaceConst_instL, replaceConst_of_constsSat hl, replaceConst_of_constsSat hr,
      replaceConst_of_constsSat ht]
    exact .extra h1' h2 h3
  | projDF h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ _ h13 _ ih1 ih2 ih3 =>
    obtain ⟨hs, hcs⟩ := hS.block _ _ _ _ h1 h2
    have hc := (hcs _ h3).2
    simp only [replaceConst_appN, VExpr.replaceConst, hs, replaceConst_projType hF hc,
      List.map_append] at ih1 ih2 ih3 ⊢
    exact .projDF (hS.inducts _ _ h1) h2 h3 h4 h5 h6 (by simpa using h7) (by simpa using h8)
      (by simpa using h9) (by simpa using h10) ih1 ih2 h13 ih3
  | projIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 _ h12 _ _ ih1 ih2 ih3 =>
    obtain ⟨hs, hcs⟩ := hS.block _ _ _ _ h1 h2
    obtain ⟨hcn, hc⟩ := hcs _ h3
    simp only [replaceConst_appN, VExpr.replaceConst, hs, hcn, replaceConst_projType hF hc,
      List.map_append] at ih1 ih2 ih3 ⊢
    refine .projIota (hS.inducts _ _ h1) h2 h3 h4 (by simp [h5]) h6 h7 (by simpa using h8)
      (by simpa using h9) (by simpa using h10) ih1 h12 ih2 ih3
  | projEta h1 h2 h3 h4 h5 h6 h7 h8 hPA _ _ ih1 ih2 =>
    obtain ⟨hs, hcs⟩ := hS.block _ _ _ _ h1 h2
    have hcn := (hcs _ h3).1
    simp only [replaceConst_appN, VExpr.replaceConst, hs, hcn, List.map_append,
      replaceConst_projs] at ih1 ih2 ⊢
    exact .projEta (hS.inducts _ _ h1) h2 h3 h4 h5 h6 h7 (by simpa using h8) hPA ih1 ih2

section
variable {F : Name → Option VExpr} {E₁ E₀ : VEnv} (H₀ : E₀.Ordered) (hS : ConstSubst F E₁ E₀)
include H₀ hS

theorem HasType.replaceConst {U Γ e A} (H : E₁.HasType U Γ e A) :
    E₀.HasType U (Γ.map (·.replaceConst F)) (e.replaceConst F) (A.replaceConst F) :=
  IsDefEq.replaceConst H₀ hS H

theorem IsType.replaceConst {U Γ A} (H : E₁.IsType U Γ A) :
    E₀.IsType U (Γ.map (·.replaceConst F)) (A.replaceConst F) :=
  let ⟨u, h⟩ := H; ⟨u, h.replaceConst H₀ hS⟩

theorem IsDefEqU.replaceConst {U Γ e e'} (H : E₁.IsDefEqU U Γ e e') :
    E₀.IsDefEqU U (Γ.map (·.replaceConst F)) (e.replaceConst F) (e'.replaceConst F) :=
  let ⟨_, h⟩ := H; ⟨_, IsDefEq.replaceConst H₀ hS h⟩

theorem IsTele.replaceConst {U Γ As} (H : E₁.IsTele U Γ As) :
    E₀.IsTele U (Γ.map (·.replaceConst F)) (As.map (·.replaceConst F)) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.replaceConst H₀ hS) ih

theorem TeleDefEq.replaceConst {U Γ As Bs} (H : E₁.TeleDefEq U Γ As Bs) :
    E₀.TeleDefEq U (Γ.map (·.replaceConst F)) (As.map (·.replaceConst F))
      (Bs.map (·.replaceConst F)) := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons (h.replaceConst H₀ hS) ih

end

/-! ### Beta back to the restored term -/

/-- Each auxiliary constant of `R` in `e` is applied to the parameters, at levels `ls₀`: at depth
`k` below them, exactly the variables `bvars h.n k`, and nothing else is applied to it. -/
def _root_.Lean4Lean.VExpr.AuxAt (R : Name → Option VAuxHead) (ls₀ : List VLevel) :
    Nat → VExpr → Prop
  | _, .bvar _ | _, .sort _ => True
  | _, .const c ls => match R c with
    | some h => h.n = 0 ∧ ls = ls₀
    | none => True
  | k, .app f a => match (VExpr.app f a).constSpine? with
    | some (c, ls, xs) => match R c with
      | some h => if xs.length = h.n then xs = bvars h.n k ∧ ls = ls₀
        else f.AuxAt R ls₀ k ∧ a.AuxAt R ls₀ k
      | none => f.AuxAt R ls₀ k ∧ a.AuxAt R ls₀ k
    | none => f.AuxAt R ls₀ k ∧ a.AuxAt R ls₀ k
  | k, .lam A b | k, .forallE A b => A.AuxAt R ls₀ k ∧ b.AuxAt R ls₀ (k + 1)
  | k, .proj _ _ e => e.AuxAt R ls₀ k

theorem _root_.Lean4Lean.VExpr.Subst.ofLift_consList_bvars (n k : Nat) :
    (Subst.ofLift (.skipN .refl (n + k))).consList (bvars n k) = .ofLift (.skipN .refl k) := by
  rw [Subst.consList_bvars]; funext i
  simp only [Subst.ofLift, Lift.liftVar_skipN, Lift.liftVar]
  split <;> first | rfl | (congr 1; omega)

theorem Ctx.SubstEq.defeqCtx {E : VEnv} {U : Nat} (henv : E.Ordered) {Γ₀ Γ₁ Γ₂ : List VExpr}
    (h : IsDefEqCtx E U Γ₀ Γ₁ Γ₂) {σ σ' Δ} (W : Ctx.SubstEq E U Γ₁ σ σ' Δ) :
    Ctx.SubstEq E U Γ₂ σ σ' Δ := by
  induction W with
  | nil => exact .nil
  | cons _ hA hh ih => exact .cons ih hA (hh.defeqDFC henv h)

/-- The identity instantiates a telescope over parameters agreeing with it: the form
`replaceConst_restore` takes the auxiliary constants' binders in. -/
theorem Ctx.SubstEq.id_teleDefEq {E : VEnv} {U : Nat} (henv : E.WF) {Qs Ps : List VExpr}
    (hT : E.TeleDefEq U [] Qs Ps) (hP : E.IsTele U [] Ps) :
    Ctx.SubstEq E U Qs.reverse .id .id Ps.reverse := by
  have hc := hT.defeqCtx henv (Γ' := []) .zero trivial hP
  simp only [List.append_nil] at hc
  exact (Ctx.SubstEq.id henv.ordered (by simpa using hP.onCtx trivial)).defeqCtx henv.ordered
    (hc.symm henv.ordered)

/-- Replacing each auxiliary constant by the occurrence as a function of the parameters, and
restoring it, agree on a term whose auxiliary constants are applied to the parameters: they
differ by beta reduction. `Γ₀` ends the context with the parameters, which the identity
instantiates each auxiliary constant's binders with. -/
theorem replaceConst_restore {E₀ : VEnv} (henv : E₀.WF) {U : Nat} {R : Name → Option VAuxHead}
    {F : Name → Option VExpr} {ls₀ : List VLevel} {Γ₀ : List VExpr}
    (hFR : ∀ c, R c = none → F c = none)
    (hR : ∀ c h, R c = some h → ∃ Ps, F c = some (h.lam Ps) ∧ Ps.length = h.n ∧
      (∀ a ∈ h.args, a.ClosedN h.n) ∧ VExpr.WF E₀ U [] ((h.lam Ps).instL ls₀) ∧
      Ctx.SubstEq E₀ U Γ₀ .id .id (Ps.map (·.instL ls₀)).reverse) {e : VExpr} :
    ∀ {Δ : List VExpr}, OnCtx (Δ ++ Γ₀) (E₀.IsType U) → e.AuxAt R ls₀ Δ.length →
      VExpr.WF E₀ U (Δ ++ Γ₀) (e.replaceConst F) →
      E₀.IsDefEqU U (Δ ++ Γ₀) (e.replaceConst F) (e.restore R fun _ => none) := by
  induction e with
  | bvar _ | sort _ => exact fun _ _ hW => hW
  | const c ls =>
    intro Δ _ hA hW
    cases hc : R c with
    | none =>
      have : restoreAux R (.const c ls) = none := by simp [restoreAux, constSpine?, hc]
      simp only [VExpr.replaceConst, hFR c hc, restore, this, Option.getD_none] at hW ⊢
      exact hW
    | some h =>
      simp only [VExpr.AuxAt, hc] at hA
      obtain ⟨hn, hls⟩ := hA
      subst ls
      obtain ⟨Ps, hF, hPs, hcl, -⟩ := hR c h hc
      have hPs : Ps = [] := List.eq_nil_of_length_eq_zero (hPs.trans hn)
      subst hPs
      have hres : restoreAux R (.const c ls₀) = some (h.inst ls₀ []) := by
        simp [restoreAux, constSpine?, hc, hn]
      have heq : VExpr.replaceConst F (.const c ls₀) =
          (VExpr.const c ls₀).restore R fun _ => none := by
        simp only [VExpr.replaceConst, hF, restore, hres, Option.getD_some, VAuxHead.lam,
          VExpr.lams_nil, VAuxHead.inst, instL_appN, instL]
        congr 1
        refine List.map_congr_left fun a ha => ?_
        exact ((hcl a ha).instL.subst_eq (fun _ h => absurd h (hn ▸ Nat.not_lt_zero _))).symm
      exact heq ▸ hW
  | app f a ihf iha =>
    intro Δ hΓ hA hW
    have app_case (hf : f.AuxAt R ls₀ Δ.length) (ha : a.AuxAt R ls₀ Δ.length)
        (hres : restoreAux R (.app f a) = none) :
        E₀.IsDefEqU U (Δ ++ Γ₀) ((VExpr.app f a).replaceConst F)
          ((VExpr.app f a).restore R fun _ => none) := by
      simp only [VExpr.replaceConst, restore, hres, Option.getD_none] at hW ⊢
      obtain ⟨X, Y, h1, h2⟩ := hW.app_inv henv.ordered hΓ
      have ih1 := ihf hΓ hf ⟨_, h1⟩
      have ih2 := iha hΓ ha ⟨_, h2⟩
      exact ⟨_, .appDF (ih1.of_l henv hΓ h1) (ih2.of_l henv hΓ h2)⟩
    cases hsp : (VExpr.app f a).constSpine? with
    | none =>
      have hA' : f.AuxAt R ls₀ Δ.length ∧ a.AuxAt R ls₀ Δ.length := by
        simpa [VExpr.AuxAt, hsp] using hA
      exact app_case hA'.1 hA'.2 (by simp [restoreAux, hsp])
    | some p =>
      obtain ⟨c, ls, xs⟩ := p
      cases hc : R c with
      | none =>
        have hA' : f.AuxAt R ls₀ Δ.length ∧ a.AuxAt R ls₀ Δ.length := by
          simpa [VExpr.AuxAt, hsp, hc] using hA
        exact app_case hA'.1 hA'.2 (by simp [restoreAux, hsp, hc])
      | some h =>
        by_cases hlen : xs.length = h.n
        · have hA' : xs = bvars h.n Δ.length ∧ ls = ls₀ := by
            simpa [VExpr.AuxAt, hsp, hc, hlen] using hA
          obtain ⟨hxs, hls⟩ := hA'
          subst xs ls
          have hres : restoreAux R (.app f a) = some (h.inst ls₀ (bvars h.n Δ.length)) := by
            simp [restoreAux, hsp, hc, hlen]
          obtain ⟨Ps, hF, hPs, hcl, hwf, hS⟩ := hR c h hc
          rw [restore, hres, Option.getD_some]
          rw [eq_of_constSpine? hsp] at hW ⊢
          simp only [replaceConst_appN, VExpr.replaceConst, hF] at hW ⊢
          have hbv : (bvars h.n Δ.length).map (·.replaceConst F) = bvars h.n Δ.length := by
            simp [VExpr.bvars, VExpr.replaceConst]
          rw [hbv]
          simp only [VAuxHead.lam, instL_lams] at hwf ⊢
          obtain ⟨hTele, T, hL⟩ := hwf.lams_inv henv.ordered (Γ := []) trivial
          have hclosed := IsDefEq.closedN henv.ordered hwf.choose_spec (Γ := []) trivial
          have hτ : (Subst.ofLift (.skipN .refl (h.n + Δ.length))).consList (bvars h.n Δ.length) =
              .ofLift (.skipN .refl Δ.length) := Subst.ofLift_consList_bvars _ _
          have hW' : Ctx.SubstEq E₀ U (Δ ++ Γ₀)
              ((Subst.ofLift (.skipN .refl (h.n + Δ.length))).consList (bvars h.n Δ.length))
              ((Subst.ofLift (.skipN .refl (h.n + Δ.length))).consList (bvars h.n Δ.length))
              ((Ps.map (·.instL ls₀)).reverse ++ []) := by
            rw [hτ, List.append_nil]
            have := hS.weak' henv.ordered (Ctx.Lift'.skipN_append (Ctx.Lift'.refl (Γ := Γ₀)) Δ)
            exact this
          have hb := IsDefEq.lams_beta henv.ordered hΓ (Δ := []) .nil hTele hL
            (by simp [hPs]) hW'
          rw [hclosed.subst_eq (fun _ h => absurd h (Nat.not_lt_zero _)), hτ] at hb
          have heq : (((VExpr.const h.name h.lvls).appN h.args).instL ls₀).subst
              (.ofLift (.skipN .refl Δ.length)) = h.inst ls₀ (bvars h.n Δ.length) := by
            simp only [instL_appN, instL, subst_appN, subst_const, VAuxHead.inst, List.map_map]
            congr 1
            refine List.map_congr_left fun a ha => ?_
            refine (hcl a ha).instL.subst_congr fun i hi => ?_
            rw [Subst.consList_bvars]
            simp [hi, Subst.ofLift, Lift.liftVar_skipN, Lift.liftVar]
          exact ⟨_, heq ▸ hb⟩
        · have hA' : f.AuxAt R ls₀ Δ.length ∧ a.AuxAt R ls₀ Δ.length := by
            simpa [VExpr.AuxAt, hsp, hc, hlen] using hA
          exact app_case hA'.1 hA'.2 (by simp [restoreAux, hsp, hc, hlen])
  | lam A b ihA ihb =>
    intro Δ hΓ hA hW
    obtain ⟨hAA, hAb⟩ := hA
    simp only [VExpr.replaceConst, restore] at hW ⊢
    obtain ⟨⟨u, hAT⟩, B, hbT⟩ := VExpr.WF.lam_inv henv.ordered hΓ hW
    have ih1 := ihA hΓ hAA ⟨_, hAT⟩
    have ih2 := ihb (Δ := _ :: Δ) ⟨hΓ, _, hAT⟩ hAb ⟨_, hbT⟩
    exact ⟨_, .lamDF (ih1.of_l henv hΓ hAT) (ih2.of_l henv ⟨hΓ, _, hAT⟩ hbT)⟩
  | forallE A b ihA ihb =>
    intro Δ hΓ hA hW
    obtain ⟨hAA, hAb⟩ := hA
    simp only [VExpr.replaceConst, restore] at hW ⊢
    obtain ⟨_, hfT⟩ := hW
    obtain ⟨⟨u, hAT⟩, v, hbT⟩ := HasType.forallE_inv henv.ordered hfT
    have ih1 := ihA hΓ hAA ⟨_, hAT⟩
    have ih2 := ihb (Δ := _ :: Δ) ⟨hΓ, _, hAT⟩ hAb ⟨_, hbT⟩
    exact ⟨_, .forallEDF (ih1.of_l henv hΓ hAT) (ih2.of_l henv ⟨hΓ, _, hAT⟩ hbT)⟩
  | proj s i e ihe =>
    intro Δ hΓ hA hW
    simp only [VExpr.replaceConst, restore] at hW ⊢
    obtain ⟨_, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, hx, -⟩ :=
      hW.proj_inv henv.ordered hΓ
    exact VExpr.WF.proj_congr henv hΓ hW (ihe hΓ hA ⟨_, hx⟩)

end VEnv
end Lean4Lean
