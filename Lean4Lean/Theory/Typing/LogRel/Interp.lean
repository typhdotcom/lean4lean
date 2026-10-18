import Lean4Lean.Theory.Typing.LogRel.Shape
import Lean4Lean.Theory.Typing.LogRel.WHRed
import Lean4Lean.Theory.Typing.LogRel.KIota
import Lean4Lean.Theory.Typing.LogRel.StepUniq

/-!
# The shape model

`LE_Interp env ρ m M`: the shape `m` approximates the value of the term `M` under the valuation
`ρ` of its free variables. Constants are interpreted by the reduction steps of `LogRel.Step`,
read off the environment, without their checks: a definition by its unfolding, an inductive
type by an `indTy` shape at its arguments, a constructor by a `ctor` shape of its fields (or
`bot` where its type is a proposition), a recursor by its iota or K-like reduct, `Quot.lift` by
its computation rule, and a projection by the field of a constructor shape. A constant's shape
is typed at an interpretation of its type, which keeps the interpretation of a reduct whose check
fails typed.

Ported from `Experimental/ShapeLogRel.lean`, with the pattern rules there replaced by the steps.
-/

namespace Lean4Lean
open Lean4Lean VExpr
namespace LogRel

/-- A constructor whose structure has eta (`VEnv.IsDefEq.projEta`): the only constructor of a type
without indices that is not recursive. Its constructor shape carries no information when all its
fields' shapes are `bot`. -/
def _root_.Lean4Lean.VEnv.IsEtaCtor (env : VEnv) (c : Name) : Prop :=
  ∃ s d t T c', env.inducts s = some (d, t) ∧ d.types[t]? = some T ∧ T.ctors = [c'] ∧
    T.indices = [] ∧ d.isRec = false ∧ c'.name = c

open Classical in
/-- The shapes' view of an environment's structures with eta. -/
noncomputable def _root_.Lean4Lean.VEnv.shapeEnv (env : VEnv) : ShapeEnv :=
  ⟨fun c => decide (env.IsEtaCtor c)⟩

open Classical in
theorem _root_.Lean4Lean.VEnv.shapeEnv_isStruct (env : VEnv) :
    @IsStruct env.shapeEnv c = true ↔ env.IsEtaCtor c := by
  show decide (env.IsEtaCtor c) = true ↔ _; exact decide_eq_true_iff

variable [ShapeEnv]

/-- Constants the model interprets by given shapes instead of by their steps: `I c ls` are the
shapes of the constant `c ∈ dom` at levels `ls`. A recursive definition's body is related by the
logical relation in the model that interprets the definitions of its block by the shapes where
they are already related. By default no constant is. -/
class AxInterp where
  dom : Name → Prop
  I : Name → List VLevel → TShape → Prop

/-- The model with no constant interpreted by given shapes. -/
instance (priority := low) AxInterp.none : AxInterp := ⟨fun _ => False, fun _ _ _ => False⟩


open Classical in
/-- Whether the block's types are relevant (not propositions) at the levels `ls`: the flag of
their `indTy` shapes. -/
noncomputable def _root_.Lean4Lean.VInductDecl.rel (d : VInductDecl) (ls : List VLevel) : Bool :=
  !decide (d.PropAt ls)

open Classical in
/-- Whether a sort is relevant (not `Prop`). -/
noncomputable def levelRel (l : VLevel) : Bool := !decide (l ≈ .zero)

theorem levelRel_imax {u v : VLevel} : levelRel (.imax u v) = levelRel v := by
  unfold levelRel; congr 2; exact propext VLevel.imax_eq_zero

/-- `AppS h as m`: `m` approximates the shape `h` applied to the shapes `as` in turn. -/
inductive AppS : TShape → List TShape → TShape → Prop
  | nil : m ≤ h → AppS h [] m
  | cons {f : WShape (n+1)} {x : WShape n} :
    f.T ≤ h → x.T ≤ a → AppS (f.app x).T as m → AppS h (a :: as) m

/-- The codomain of a pi type shape, as a function shape. -/
def WShape.piCod : WShape (n+1) → WShape (n+1)
  | ⟨.forallE _ f, w⟩ => WShape.lam' ⟨f, w.2⟩
  | _ => .bot

/-- The codomain of a pi type shape at an argument shape. -/
def WShape.piApp (s : WShape (n+1)) (x : WShape n) : WShape n := s.piCod.app x

@[simp] theorem WShape.piCod_bot : (WShape.bot : WShape (n+1)).piCod = .bot := rfl
@[simp] theorem WShape.piCod_forallE {a : WShape n} {f : WShapeFun n} :
    (WShape.forallE a f).piCod = .lam' f := rfl

theorem WShape.piCod_mono {s s' : WShape (n+1)} (h : s ≤ s') : s.piCod ≤ s'.piCod := by
  cases s using WShape.casesOn' with
  | bot => exact WShape.bot_le
  | forallE a f =>
    obtain ⟨a', f', -, hf, rfl⟩ := WShape.forallE_le.1 h
    exact WShape.lam'_le_lam'.2 hf
  | _ => exact WShape.bot_le

theorem WShape.lift_piCod {s : WShape (n+1)} (le : n ≤ m) :
    s.piCod.lift (m+1) = (s.lift (m+1)).piCod := by
  cases s using WShape.casesOn' with
  | bot => simp
  | forallE a f => rw [piCod_forallE, lift_forallE le, piCod_forallE, lift_lam' le]
  | sort r => rw [lift_sort]; exact lift_bot
  | lam f h => rw [lift_lam le]; exact lift_bot
  | ctor c l h => rw [lift_ctor le]; exact lift_bot
  | indTy r c l => rw [lift_indTy le]; exact lift_bot

theorem WShape.lift_piApp {s : WShape (n+1)} {x : WShape n} (le : n ≤ m) :
    (s.piApp x).lift m = (s.lift (m+1)).piApp (x.lift m) := by
  rw [piApp, piApp, lift_app le, lift_piCod le]

theorem TShape.piApp_mono {f : WShape (n + 1)} {f' : WShape (m + 1)} {a : WShape n}
    {a' : WShape m} (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.piApp a).T ≤ (f'.piApp a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', WShape.lift_piApp lm₁, WShape.lift_piApp lm₂]
  refine (WShape.app_mono_l (WShape.piCod_mono ?_) _).trans (WShape.app_mono_r ?_)
  · exact (TShape.LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁
  · exact (TShape.LE.def lm₁ lm₂).1 le₂

theorem WShape.Compat.piApp {f f' : WShape (n+1)} {a a' : WShape n}
    (cf : f.Compat f') (ca : a.Compat a') : (f.piApp a).Compat (f'.piApp a') := by
  obtain ⟨zf, h1, h2⟩ := WShape.Compat.iff.1 cf
  exact WShape.Compat.app (WShape.Compat.iff.2 ⟨zf.piCod, piCod_mono h1, piCod_mono h2⟩) ca

theorem TShape.Compat.piApp {f : WShape (n + 1)} {f' : WShape (m + 1)}
    {a : WShape n} {a' : WShape m}
    (cf : f.T.Compat f'.T) (ca : a.T.Compat a'.T) :
    (f.piApp a).T.Compat (f'.piApp a').T := by
  have le₁ := Nat.le_max_left n m; have le₂ := Nat.le_max_right n m
  rw [TShape.Compat.def le₁ le₂, WShape.lift_piApp le₁, WShape.lift_piApp le₂]
  exact WShape.Compat.piApp
    ((TShape.Compat.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 cf)
    ((TShape.Compat.def le₁ le₂).1 ca)

/-- `PiAppS h as m`: `m` approximates the codomain of the pi type shape `h` at the argument shapes
`as` in turn. -/
inductive PiAppS : TShape → List TShape → TShape → Prop
  | nil : m ≤ h → PiAppS h [] m
  | cons {f : WShape (n+1)} {x : WShape n} :
    f.T ≤ h → x.T ≤ a → PiAppS (f.piApp x).T as m → PiAppS h (a :: as) m

/-- The shapes of the fields of a K-like reduct, from the shapes `is` of the indices: a field that
is an index has that index's shape; any other field is a proof, of shape `bot`. These are the
shapes of every choice of fields `Step.kIota` allows. -/
def kFieldShapes (c : VConstructor) (is : List TShape) : List TShape :=
  (List.range c.fields.length).map fun k => match VInductDecl.fieldIdx c k with
    | some i => is.getD i TShape.bot
    | none => TShape.bot

theorem kFieldShapes_mono {c : VConstructor} {is is' : List TShape}
    (h : is.Forall₂ (· ≤ ·) is') : (kFieldShapes c is).Forall₂ (· ≤ ·) (kFieldShapes c is') := by
  simp only [kFieldShapes]
  refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
  generalize List.range c.fields.length = ks
  induction ks with
  | nil => exact .nil
  | cons k ks ih =>
  refine .cons ?_ ih
  split
  · next i _ =>
    clear ih
    show is.getD i TShape.bot ≤ is'.getD i TShape.bot
    clear ‹VInductDecl.fieldIdx c k = some i›
    induction h generalizing i with
    | nil => exact .rfl
    | cons h1 _ ih2 => cases i with
      | zero => exact h1
      | succ i => exact ih2 i
  · exact .rfl

variable [AxInterp]

variable (env : VEnv) (c : Name) (ls : List VLevel) (R : TShape → VExpr → Prop) in
/-- The shapes `m` of the constant `c` at levels `ls` applied to arguments whose shapes are
`rargs` (last argument first). `R` interprets the closed terms the constant reduces to. -/
inductive LE_Interp.Const : ∀ {n}, List (WShape n) → TShape → Prop
  | bot : Const (n := n) rargs (WShape.T (n := n') .bot)
  | lam {f : WShapeFun n} : (∀ x y, (x, y) ∈ f → Const (x :: rargs) y.T) →
    m ≤ WShape.T (n := n + 1) (.lam' f) → Const rargs m
  /-- A constant interpreted by given shapes. -/
  | ext : AxInterp.dom c →
    AxInterp.I c ls₀ m' → List.Forall₂ (· ≈ ·) ls₀ ls → m ≤ m' → Const (n := n) [] m
  /-- A definition unfolds. -/
  | delta {df : VDefEq} : ¬AxInterp.dom c → env.defeqs df → df.lhs = .const c (VLevel.params df.uvars) → ls.length = df.uvars →
    R h (df.rhs.instL ls) → m ≤ h → Const (n := n) [] m
  /-- An inductive type applied to its parameters and indices, with its constructors' field
  telescopes at the parameters. -/
  | indTy {d : VInductDecl} {t : Nat} {T : VInductiveType} {rargs ctys : List (WShape n)} :
    env.inducts c = some (d, t) → d.types[t]? = some T →
    rargs.length = d.params.length + T.indices.length → ctys.length = T.ctors.length →
    (∀ (i : Nat) (c' : VConstructor) (cty : WShape n), T.ctors[i]? = some c' → ctys[i]? = some cty →
      ∃ h, R h (c'.type.instL ls) ∧
      PiAppS h ((rargs.reverse.take d.params.length).map (·.T)) cty.T) →
    m ≤ (WShape.indTy (n := n) (d.rel ls) ⟨c, rargs.length, T.ctors.map (·.name), T.ctors.map (·.fields.length)⟩
      (rargs.reverse ++ ctys)).T → (hnd : ¬AxInterp.dom c := by assumption) → Const rargs m
  /-- A constructor applied to its parameters and fields, of a type that is not a proposition: the
  shape of its fields. -/
  | ctor {d : VInductDecl} {t t' : Nat} {T : VInductiveType} {c' : VConstructor}
    {rargs : List (WShape n)} : env.inducts s = some (d, t) → d.types[t']? = some T → c' ∈ T.ctors → c'.name = c →
    ¬d.PropAt ls → rargs.length = d.params.length + c'.fields.length →
    m ≤ (WShape.ctor' (n := n) c (rargs.reverse.drop d.params.length)).T → (hnd : ¬AxInterp.dom c := by assumption) → Const rargs m
  /-- A recursor on a constructor shape, at levels where its type is not a proposition. -/
  | iota {fs : List (WShape n)} {x : WShape (n+1)} {rest : List (WShape (n+1))}
    {T : VInductiveType}
    {c' : VConstructor} {d : VInductDecl} {t j q : Nat} :
    env.inducts s = some (d, t) → c = d.recName j → d.allCtors[q]? = some (j, c') →
    d.allTypes[j]? = some T → ¬d.PropAt (d.blockLevels ls) →
    rest.length = d.majorIdx T → fs.length = c'.fields.length →
    R h (d.iotaRhs ls q j c') →
    AppS h ((rest.reverse.take (d.params.length + d.allTypes.length + d.allCtors.length)).map
      (·.T) ++ fs.map (·.T)) m → (WShape.ctor' c'.name fs).T ≤ x.T →
    (hnd : ¬AxInterp.dom c := by assumption) → Const (x :: rest) m
  /-- A recursor at levels where its type is a proposition with large elimination, on any major
  premise: the iota rule's right-hand side at the fields `kFieldShapes` reads off the indices. -/
  | kIota {d : VInductDecl} {t j q : Nat} {T : VInductiveType} {c' : VConstructor}
    {rargs : List (WShape n)} {e : WShape n} : env.inducts s = some (d, t) → c = d.recName j →
    d.allCtors[q]? = some (j, c') → d.allTypes[j]? = some T → T.ctors = [c'] →
    d.PropAt (d.blockLevels ls) → d.largeElim = true → rargs.length = d.majorIdx T →
    R h (d.iotaRhs ls q j c') →
    AppS h ((rargs.reverse.take (d.params.length + (d.allTypes.length + d.allCtors.length))).map
      (·.T) ++ kFieldShapes c' ((rargs.reverse.drop
        (d.params.length + (d.allTypes.length + d.allCtors.length))).map (·.T))) m →
    (hnd : ¬AxInterp.dom c := by assumption) → Const (e :: rargs) m
  /-- The quotient type, with `Quot.mk`'s field telescope at its arguments. -/
  | quotTy {rargs : List (WShape n)} {cty : WShape n} {ci : VConstant} :
    env.defeqs quotDefEq → c = ``Quot → ls = [u] → rargs.length = 2 →
    env.constants ``Quot.mk = some ci → R h (ci.type.instL ls) →
    PiAppS h (rargs.reverse.map (·.T)) cty.T →
    m ≤ (WShape.indTy (n := n) (levelRel u) ⟨c, 2, [``Quot.mk], [1]⟩ (rargs.reverse ++ [cty])).T →
    (hnd : ¬AxInterp.dom c := by assumption) → Const rargs m
  /-- `Quot.mk`, where the quotient is not a proposition. -/
  | quotMk {a r α : WShape n} : env.defeqs quotDefEq → c = ``Quot.mk → ls = [u] →
    ¬u ≈ .zero → m ≤ (WShape.ctor' (n := n) c [a]).T → (hnd : ¬AxInterp.dom c := by assumption) → Const [a, r, α] m
  /-- `Quot.lift` on `Quot.mk`. -/
  | quot {a : WShape n} {x h f β r α : WShape (n+1)} : env.defeqs quotDefEq →
    c = ``Quot.lift →
    ls = [u, v] → ¬u ≈ .zero → AppS f.T [a.T] m → (WShape.ctor' ``Quot.mk [a]).T ≤ x.T →
    (hnd : ¬AxInterp.dom c := by assumption) → Const (x :: [h, f, β, r, α]) m
  /-- `Quot.lift` on any proof of a quotient that is a proposition. -/
  | quotK {q h f β r α : WShape n} : env.defeqs quotDefEq → c = ``Quot.lift →
    ls = [u, v] → u ≈ .zero → AppS f.T [TShape.bot] m → (hnd : ¬AxInterp.dom c := by assumption) → Const [q, h, f, β, r, α] m

inductive LE_Interp (env : VEnv) : Valuation → TShape → VExpr → Prop
  | bot : LE_Interp env ρ (WShape.T (n := n) .bot) M
  | bvar : m ≤ ρ i → LE_Interp env ρ m (.bvar i)
  | sort : m ≤ .sort (levelRel l) → LE_Interp env ρ m (.sort l)
  | app : LE_Interp env ρ (WShape.T f) F → LE_Interp env ρ a.T A →
    m ≤ (f.app a).T → LE_Interp env ρ m (.app F A)
  | lam : LE_Interp env ρ (WShape.T (n := n) a) A →
    WShape.HasDom f a → (∀ x, x.HasType a → LE_Interp env (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := _+1) (.lam' f) → LE_Interp env ρ m (.lam A F)
  | forallE : LE_Interp env ρ (WShape.T (n := n) b) B → LE_Interp env ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp env (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.forallE b f) → LE_Interp env ρ m (.forallE B F)
  | const :
    env.constants c = some ci → ls.length = ci.uvars →
    m ≤ m' → m'.HasType a →
    LE_Interp env ρ a (ci.type.instL ls) →
    LE_Interp.Const env c ls R [] m' → (∀ m e, R m e → LE_Interp env ρ m e) →
    LE_Interp env ρ m (.const c ls)
  /-- A projection of a structure: the field of a constructor shape. A constructor shape's fields
  are typed at its type's field telescope (`Shape.ctorOK`), so the field is typed at the
  projection's type. -/
  | proj {fs : List (WShape n)} {d : VInductDecl} {t : Nat} {T : VInductiveType}
    {c : VConstructor} :
    env.inducts s = some (d, t) → d.types[t]? = some T → T.ctors = [c] →
    LE_Interp env ρ (WShape.ctor' c.name fs).T e → fs[k]? = some x → m ≤ x.T →
    LE_Interp env ρ m (.proj s k e)

namespace LE_Interp
variable {env : VEnv}

theorem bvar' : LE_Interp env ρ (ρ i) (.bvar i) := .bvar .rfl
theorem bvar0 : LE_Interp env (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem sort' : LE_Interp env ρ (.sort (levelRel l)) (.sort l) := .sort .rfl
theorem app' (h1 : LE_Interp env ρ (WShape.T f) F) (h2 : LE_Interp env ρ a.T A) :
    LE_Interp env ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem lam' {f : WShapeFun n} {a : WShape n}
    (h1 : LE_Interp env ρ (WShape.T a) A) (h2 : WShape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp env (ρ.push x.T) (f.app x).T F) :
    LE_Interp env ρ (WShape.T (n := n+1) (WShape.lam' f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem forallE' {f : WShapeFun n} {b b' : WShape n}
    (h1 : LE_Interp env ρ b.T B) (h2 : LE_Interp env ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → LE_Interp env (ρ.push x.T) (f.app x).T F) :
    LE_Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F) :=
  .forallE h1 h2 h3 h4 .rfl

theorem bvar_iff : LE_Interp env ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem le_sort (H : LE_Interp env ρ m (.sort u)) : m ≤ .sort (levelRel u) := by
  generalize eq : VExpr.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.AppS.mono (h : m ≤ m') (h' : h₀ ≤ h₁)
    (H : AppS h₀ as m') : AppS h₁ as m := by
  induction H generalizing m h₁ with
  | nil h1 => exact .nil (h.trans (h1.trans h'))
  | cons h1 h2 _ ih => exact .cons (h1.trans h') h2 (ih h .rfl)

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.AppS.args_mono (H : AppS h as m) :
    ∀ {as'}, as.Forall₂ (· ≤ ·) as' → AppS h as' m := by
  induction H with
  | nil h1 => intro _ e; cases e; exact .nil h1
  | cons h1 h2 _ ih => intro _ e; cases e with | cons a1 a2 => exact .cons h1 (h2.trans a1) (ih a2)

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.PiAppS.mono (h : m ≤ m') (h' : h₀ ≤ h₁)
    (H : PiAppS h₀ as m') : PiAppS h₁ as m := by
  induction H generalizing m h₁ with
  | nil h1 => exact .nil (h.trans (h1.trans h'))
  | cons h1 h2 _ ih => exact .cons (h1.trans h') h2 (ih h .rfl)

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.PiAppS.args_mono (H : PiAppS h as m) :
    ∀ {as'}, as.Forall₂ (· ≤ ·) as' → PiAppS h as' m := by
  induction H with
  | nil h1 => intro _ e; cases e; exact .nil h1
  | cons h1 h2 _ ih => intro _ e; cases e with | cons a1 a2 => exact .cons h1 (h2.trans a1) (ih a2)

omit [AxInterp] in
/-- Lifting a list of shapes keeps each above itself. -/
theorem lift_T_ge {l : List (WShape n₁)} (hn : n₁ ≤ n₂) :
    (l.map (·.T)).Forall₂ (· ≤ ·) ((l.map (WShape.lift n₂)).map (·.T)) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact .cons (TShape.lift_eqv (a := x.T) hn).2 ih

theorem Const.mono (h : m ≤ m') (H : Const env c ls R rargs m') : Const env c ls R rargs m := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | lam _ h2 ih => exact .lam (ih · · · .rfl) (h.trans h2)
  | ext h1 h4 h5 h6 => exact .ext h1 h4 h5 (h.trans h6)
  | delta h0 h1 h2 h3 h4 h5 => exact .delta h0 h1 h2 h3 h4 (h.trans h5)
  | indTy h1 h2 h3 h4 h5 h6 => exact .indTy h1 h2 h3 h4 h5 (h.trans h6)
  | ctor h1 h2 h3 h4 h5 h6 h7 => exact .ctor h1 h2 h3 h4 h5 h6 (h.trans h7)
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .iota h1 h2 h3 h4 h5 h6 h7 h8 (h9.mono h .rfl) h10
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 (h10.mono h .rfl)
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 => exact .quotTy h1 h2 h3 h4 h5 h6 h7 (h.trans h8)
  | quotMk h1 h2 h3 h4 h5 => exact .quotMk h1 h2 h3 h4 (h.trans h5)
  | quot h1 h2 h3 h4 h5 h6 => exact .quot h1 h2 h3 h4 (h5.mono h .rfl) h6
  | quotK h1 h2 h3 h4 h5 => exact .quotK h1 h2 h3 h4 (h5.mono h .rfl)

omit [ShapeEnv] in
theorem _root_.List.forall₂_append' {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {l₁' l₂' : List β}, l₁.Forall₂ R l₁' → l₂.Forall₂ R l₂' →
      (l₁ ++ l₂).Forall₂ R (l₁' ++ l₂')
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons a h, h' => .cons a (List.forall₂_append' h h')

omit [ShapeEnv] in
theorem _root_.List.forall₂_take' {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {k : Nat}, l.Forall₂ R l' → (l.take k).Forall₂ R (l'.take k)
  | _, _, 0, _ => .nil
  | _, _, _+1, .nil => .nil
  | _, _, k+1, .cons a h => .cons a (List.forall₂_take' (k := k) h)

omit [ShapeEnv] in
theorem _root_.List.forall₂_refl' {r : α → α → Prop} (hr : ∀ a, r a a) :
    ∀ {l : List α}, l.Forall₂ r l
  | [] => .nil
  | _ :: _ => .cons (hr _) (List.forall₂_refl' hr)

/-- A constant's interpretation at larger argument shapes. -/
theorem Const.mono_l (h : rargs.Forall₂ (· ≤ ·) rargs') (H : Const env c ls R rargs m) :
    Const env c ls R rargs' m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam (fun x y h' => ih _ _ h' (.cons .rfl h)) h2
  | ext h1 h4 h5 h6 => cases h; exact .ext h1 h4 h5 h6
  | delta h0 h1 h2 h3 h4 h5 => cases h; exact .delta h0 h1 h2 h3 h4 h5
  | indTy h1 h2 h3 h4 h5 h6 =>
    have hr := List.Forall₂.reverse.2 h
    refine .indTy h1 h2 (h.length_eq ▸ h3) h4 (fun i c' cty a1 a2 => ?_) (h6.trans ?_)
    · obtain ⟨hh, b1, b2⟩ := h5 i c' cty a1 a2
      exact ⟨hh, b1, b2.args_mono (List.forall₂_map_left_iff.2
        (List.forall₂_map_right_iff.2 (List.forall₂_take' hr |>.imp fun _ _ e => e.T)))⟩
    · rw [h.length_eq]
      exact (WShape.indTy_le_indTy.2 ⟨rfl, rfl,
        List.forall₂_append' hr (List.forall₂_refl' fun _ => .rfl)⟩).T
  | ctor h1 h2 h3 h4 h5 h6 h7 =>
    exact .ctor h1 h2 h3 h4 h5 (h.length_eq ▸ h6) (h7.trans
      (WShape.ctor'_le_ctor' (List.forall₂_drop' (List.Forall₂.reverse.2 h))).T)
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases h with | cons hx h =>
    refine .iota h1 h2 h3 h4 h5 (h.length_eq ▸ h6) h7 h8 (h9.args_mono ?_)
      (h10.trans (WShape.LE.T hx))
    refine List.forall₂_append' ?_ (List.forall₂_refl' fun _ => .rfl)
    exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
      (List.forall₂_take' (List.Forall₂.reverse.2 h) |>.imp fun _ _ e => e.T))
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    cases h with | cons hx h =>
    have hr := List.Forall₂.reverse.2 h
    refine .kIota h1 h2 h3 h4 h5 h6 h7 (h.length_eq ▸ h8) h9 (h10.args_mono ?_)
    refine List.forall₂_append' ?_ (kFieldShapes_mono ?_)
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        (List.forall₂_take' hr |>.imp fun _ _ e => e.T))
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        (List.forall₂_drop' hr |>.imp fun _ _ e => e.T))
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 =>
    have hr := List.Forall₂.reverse.2 h
    refine .quotTy h1 h2 h3 (h.length_eq ▸ h4) h5 h6 (h7.args_mono ?_) (h8.trans ?_)
    · exact List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2
        (hr.imp fun _ _ e => e.T))
    · exact (WShape.indTy_le_indTy.2 ⟨rfl, rfl,
        List.forall₂_append' hr (.cons .rfl .nil)⟩).T
  | quotMk h1 h2 h3 h4 h5 =>
    cases h with | cons ha h =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h
    exact .quotMk h1 h2 h3 h4 (h5.trans (WShape.ctor'_le_ctor' (.cons ha .nil)).T)
  | quot h1 h2 h3 h4 h5 h6 =>
    cases h with | cons hx h =>
    cases h with | cons _ h =>
    cases h with | cons hf h =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h
    exact .quot h1 h2 h3 h4 (h5.mono .rfl (WShape.LE.T hf)) (h6.trans (WShape.LE.T hx))
  | quotK h1 h2 h3 h4 h5 =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h with | cons hf h =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h with | cons _ h =>
    cases h
    exact .quotK h1 h2 h3 h4 (h5.mono .rfl (WShape.LE.T hf))

omit [AxInterp] in
/-- A function shape and an argument shape joined with others at a common level, and the
application of the joins above the join of the applications. -/
theorem _root_.Lean4Lean.LogRel.TShape.app_join {f : WShape (n+1)} {f' : WShape (n'+1)}
    {x : WShape n} {x' : WShape n'} (cf : f.T.Compat f'.T) (cx : x.T.Compat x'.T) :
    ∃ (N : Nat) (F : WShape (N+1)) (X : WShape N), TShape.Join f.T f'.T F.T ∧
      TShape.Join x.T x'.T X.T ∧ (f.app x).T.Compat (f'.app x').T ∧
      (f.app x).T.join (f'.app x').T ≤ (F.app X).T := by
  have hn : n ≤ max n n' := Nat.le_max_left ..
  have hn' : n' ≤ max n n' := Nat.le_max_right ..
  have cfw := (TShape.Compat.def (x := f.T) (y := f'.T) (Nat.succ_le_succ hn)
    (Nat.succ_le_succ hn')).1 cf
  have cxw := (TShape.Compat.def (x := x.T) (y := x'.T) hn hn').1 cx
  have jF : TShape.Join f.T f'.T ((f.lift (max n n' + 1)).join (f'.lift (max n n' + 1))).T :=
    (TShape.Join.def (Nat.succ_le_succ hn) (Nat.succ_le_succ hn') (Nat.le_refl _)).2
      (by rw [WShape.lift_self]; exact WShape.Join.mk cfw)
  have jX : TShape.Join x.T x'.T ((x.lift (max n n')).join (x'.lift (max n n'))).T :=
    (TShape.Join.def hn hn' (Nat.le_refl _)).2 (by rw [WShape.lift_self]; exact WShape.Join.mk cxw)
  have cap := TShape.Compat.app cf cx
  exact ⟨_, _, _, jF, jX, cap, (TShape.Join.mk cap _).2
    ⟨TShape.app_mono jF.le.1 jX.le.1, TShape.app_mono jF.le.2 jX.le.2⟩⟩

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.AppS.compat_join (hh : h.Compat h') (H1 : AppS h as m)
    (H2 : AppS h' as' m') (has : as.Forall₂ TShape.Compat as') :
    m.Compat m' ∧ AppS (h.join h') (as.zipWith TShape.join as') (m.join m') := by
  induction H1 generalizing h' as' m' with
  | nil h1 =>
    cases has; cases H2 with | nil h2
    have c := TShape.Compat.mono h1 h2 hh
    have jh := (TShape.Join.mk hh).le
    exact ⟨c, .nil ((TShape.Join.mk c _).2 ⟨h1.trans jh.1, h2.trans jh.2⟩)⟩
  | cons hf1 hx1 _ ih =>
    cases has with | cons ha has
    cases H2 with | cons hf2 hx2 H2
    have cf := TShape.Compat.mono hf1 hf2 hh
    have cx := TShape.Compat.mono hx1 hx2 ha
    obtain ⟨N, F, X, jF, jX, cap, hle⟩ := TShape.app_join cf cx
    have ⟨c, j⟩ := ih cap H2 has
    have jh := (TShape.Join.mk hh).le
    have ja := (TShape.Join.mk ha).le
    exact ⟨c, .cons ((jF _).2 ⟨hf1.trans jh.1, hf2.trans jh.2⟩)
      ((jX _).2 ⟨hx1.trans ja.1, hx2.trans ja.2⟩) (j.mono .rfl hle)⟩

omit [AxInterp] in
/-- A pi type shape and an argument shape joined with others at a common level, and the codomain
of the joins above the join of the codomains. -/
theorem _root_.Lean4Lean.LogRel.TShape.piApp_join {f : WShape (n+1)} {f' : WShape (n'+1)}
    {x : WShape n} {x' : WShape n'} (cf : f.T.Compat f'.T) (cx : x.T.Compat x'.T) :
    ∃ (N : Nat) (F : WShape (N+1)) (X : WShape N), TShape.Join f.T f'.T F.T ∧
      TShape.Join x.T x'.T X.T ∧ (f.piApp x).T.Compat (f'.piApp x').T ∧
      (f.piApp x).T.join (f'.piApp x').T ≤ (F.piApp X).T := by
  have hn : n ≤ max n n' := Nat.le_max_left ..
  have hn' : n' ≤ max n n' := Nat.le_max_right ..
  have cfw := (TShape.Compat.def (x := f.T) (y := f'.T) (Nat.succ_le_succ hn)
    (Nat.succ_le_succ hn')).1 cf
  have cxw := (TShape.Compat.def (x := x.T) (y := x'.T) hn hn').1 cx
  have jF : TShape.Join f.T f'.T ((f.lift (max n n' + 1)).join (f'.lift (max n n' + 1))).T :=
    (TShape.Join.def (Nat.succ_le_succ hn) (Nat.succ_le_succ hn') (Nat.le_refl _)).2
      (by rw [WShape.lift_self]; exact WShape.Join.mk cfw)
  have jX : TShape.Join x.T x'.T ((x.lift (max n n')).join (x'.lift (max n n'))).T :=
    (TShape.Join.def hn hn' (Nat.le_refl _)).2 (by rw [WShape.lift_self]; exact WShape.Join.mk cxw)
  have cap := TShape.Compat.piApp cf cx
  exact ⟨_, _, _, jF, jX, cap, (TShape.Join.mk cap _).2
    ⟨TShape.piApp_mono jF.le.1 jX.le.1, TShape.piApp_mono jF.le.2 jX.le.2⟩⟩

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.PiAppS.compat_join (hh : h.Compat h') (H1 : PiAppS h as m)
    (H2 : PiAppS h' as' m') (has : as.Forall₂ TShape.Compat as') :
    m.Compat m' ∧ PiAppS (h.join h') (as.zipWith TShape.join as') (m.join m') := by
  induction H1 generalizing h' as' m' with
  | nil h1 =>
    cases has; cases H2 with | nil h2
    have c := TShape.Compat.mono h1 h2 hh
    have jh := (TShape.Join.mk hh).le
    exact ⟨c, .nil ((TShape.Join.mk c _).2 ⟨h1.trans jh.1, h2.trans jh.2⟩)⟩
  | cons hf1 hx1 _ ih =>
    cases has with | cons ha has
    cases H2 with | cons hf2 hx2 H2
    have cf := TShape.Compat.mono hf1 hf2 hh
    have cx := TShape.Compat.mono hx1 hx2 ha
    obtain ⟨N, F, X, jF, jX, cap, hle⟩ := TShape.piApp_join cf cx
    have ⟨c, j⟩ := ih cap H2 has
    have jh := (TShape.Join.mk hh).le
    have ja := (TShape.Join.mk ha).le
    exact ⟨c, .cons ((jF _).2 ⟨hf1.trans jh.1, hf2.trans jh.2⟩)
      ((jX _).2 ⟨hx1.trans ja.1, hx2.trans ja.2⟩) (j.mono .rfl hle)⟩

/-- What a constant is to the model: a definition, an inductive type, a constructor, a recursor, or
one of the quotient's constants. -/
inductive Role where
  | delta (df : VDefEq)
  | indTy (d : VInductDecl) (t : Nat)
  | ctor (d : VInductDecl) (t : Nat) (c : VConstructor)
  | recursor (d : VInductDecl) (j : Nat)
  | quotTy | quotMk | quotLift

/-- `c` has the role `r`, in which the model's interpretation of it computes at `n` arguments: what
`Const`'s cases other than `bot` and `lam` require. -/
inductive ConstArity (env : VEnv) (c : Name) : Role → Nat → Prop
  | delta {df : VDefEq} : env.defeqs df → df.lhs = .const c (VLevel.params df.uvars) → ConstArity env c (.delta df) 0
  | indTy {d : VInductDecl} {t : Nat} {T : VInductiveType} :
    env.inducts c = some (d, t) → d.types[t]? = some T →
    ConstArity env c (.indTy d t) (d.params.length + T.indices.length)
  | ctor {s : Name} {d : VInductDecl} {t t' : Nat} {T : VInductiveType} {c' : VConstructor} :
    env.inducts s = some (d, t) → d.types[t']? = some T → c' ∈ T.ctors → c'.name = c →
    ConstArity env c (.ctor d t' c') (d.params.length + c'.fields.length)
  | recursor {s : Name} {d : VInductDecl} {t j : Nat} {T : VInductiveType} :
    env.inducts s = some (d, t) → c = d.recName j → d.allTypes[j]? = some T →
    ConstArity env c (.recursor d j) (d.majorIdx T + 1)
  | quotTy : env.defeqs quotDefEq → c = ``Quot → ConstArity env c .quotTy 2
  | quotMk : env.defeqs quotDefEq → c = ``Quot.mk → ConstArity env c .quotMk 3
  | quotLift : env.defeqs quotDefEq → c = ``Quot.lift → ConstArity env c .quotLift 6

/-- A constant has at most one role. A well-formed environment's constants do: each role is a
constant the environment declares once. -/
def ConstRoles (env : VEnv) : Prop :=
  ∀ {c : Name} {r r' : Role} {n n' : Nat}, ConstArity env c r n → ConstArity env c r' n' → r = r'

/-- The role a name has in the proof that rule names are unique. -/
def Role.toStepUniq : Role → StepUniqProof.Role
  | .delta df => .defn df
  | .indTy d t => .indTy d t
  | .ctor d t c => .ctor d t c
  | .recursor d j => .recr d j
  | .quotTy => .quotTy
  | .quotMk => .quotMk
  | .quotLift => .quotLift

theorem Role.toStepUniq_inj : ∀ {r r' : Role}, r.toStepUniq = r'.toStepUniq → r = r'
  | .delta _, .delta _, h | .indTy .., .indTy .., h | .ctor .., .ctor .., h
  | .recursor .., .recursor .., h => by cases h; rfl
  | .quotTy, .quotTy, _ | .quotMk, .quotMk, _ | .quotLift, .quotLift, _ => rfl
  | .delta _, .indTy .., h | .delta _, .ctor .., h | .delta _, .recursor .., h
  | .delta _, .quotTy, h | .delta _, .quotMk, h | .delta _, .quotLift, h
  | .indTy .., .delta _, h | .indTy .., .ctor .., h | .indTy .., .recursor .., h
  | .indTy .., .quotTy, h | .indTy .., .quotMk, h | .indTy .., .quotLift, h
  | .ctor .., .delta _, h | .ctor .., .indTy .., h | .ctor .., .recursor .., h
  | .ctor .., .quotTy, h | .ctor .., .quotMk, h | .ctor .., .quotLift, h
  | .recursor .., .delta _, h | .recursor .., .indTy .., h | .recursor .., .ctor .., h
  | .recursor .., .quotTy, h | .recursor .., .quotMk, h | .recursor .., .quotLift, h
  | .quotTy, .delta _, h | .quotTy, .indTy .., h | .quotTy, .ctor .., h
  | .quotTy, .recursor .., h | .quotTy, .quotMk, h | .quotTy, .quotLift, h
  | .quotMk, .delta _, h | .quotMk, .indTy .., h | .quotMk, .ctor .., h
  | .quotMk, .recursor .., h | .quotMk, .quotTy, h | .quotMk, .quotLift, h
  | .quotLift, .delta _, h | .quotLift, .indTy .., h | .quotLift, .ctor .., h
  | .quotLift, .recursor .., h | .quotLift, .quotTy, h | .quotLift, .quotMk, h => by cases h

/-- A well-formed environment gives each constant at most one role. -/
theorem _root_.Lean4Lean.VEnv.WF.constRoles {env : VEnv} (henv : env.WF) : ConstRoles env := by
  obtain ⟨ρ, hρ⟩ := (StepUniqProof.names_of_WF henv).roles
  have key {c r n} (h : ConstArity env c r n) : ρ c = r.toStepUniq := by
    cases h with
    | delta h1 h2 => exact hρ.defn h1 h2
    | indTy h1 h2 => exact hρ.indTy h1
    | ctor h1 h2 h3 h4 => exact h4 ▸ hρ.ownCtor h1 h2 h3
    | recursor h1 h2 h3 => exact h2 ▸ hρ.recr h1 (List.getElem?_eq_some_iff.1 h3).1
    | quotTy h1 h2 => exact h2 ▸ (hρ.quot h1).2.2
    | quotMk h1 h2 => exact h2 ▸ (hρ.quot h1).2.1
    | quotLift h1 h2 => exact h2 ▸ (hρ.quot h1).1
  intro c r r' n n' H1 H2
  exact Role.toStepUniq_inj ((key H1).symm.trans (key H2))

theorem ConstArity.determ (H1 : ConstArity env c r n) (H2 : ConstArity env c r n') : n = n' := by
  cases H1 with
  | indTy _ h2 => cases H2 with | indTy _ h4 => cases h2.symm.trans h4; rfl
  | recursor _ _ h3 => cases H2 with | recursor _ _ h6 => cases h3.symm.trans h6; rfl
  | _ => cases H2 <;> rfl

/-- A constant's interpretation computes only at its arity: at more arguments than that it is
`bot` (the lambda cases' bodies at the extra arguments are). -/
theorem Const.arity (H : Const env c ls R rargs m) :
    m ≤ (WShape.bot (n := 0)).T ∨ (∃ f, m ≤ WShape.T (n := _ + 1) (WShape.lam' f) ∧
      ∀ x y, (x, y) ∈ f → Const env c ls R (x :: rargs) y.T) ∨
    (∃ r, ConstArity env c r rargs.length) ∨ (AxInterp.dom c ∧ rargs = []) := by
  cases H with
  | bot => exact .inl (TShape.bot_eqv.1.trans TShape.bot_eqv.2)
  | lam h1 h2 => exact .inr (.inl ⟨_, h2, h1⟩)
  | ext h0 => exact .inr (.inr (.inr ⟨h0, rfl⟩))
  | delta _ h1 h2 => exact .inr (.inr (.inl ⟨_, ConstArity.delta h1 h2⟩))
  | indTy h1 h2 h3 => exact .inr (.inr (.inl ⟨_, by rw [h3]; exact ConstArity.indTy h1 h2⟩))
  | ctor h1 h2 h3 h4 h5 h6 =>
    exact .inr (.inr (.inl ⟨_, by rw [h6]; exact ConstArity.ctor h1 h2 h3 h4⟩))
  | iota h1 h2 h3 h4 h5 h6 =>
    exact .inr (.inr (.inl ⟨_, by rw [List.length_cons, h6]; exact ConstArity.recursor h1 h2 h4⟩))
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .inr (.inr (.inl ⟨_, by rw [List.length_cons, h8]; exact ConstArity.recursor h1 h2 h4⟩))
  | quotTy h1 h2 h3 h4 =>
    exact .inr (.inr (.inl ⟨_, by rw [h4]; exact ConstArity.quotTy h1 h2⟩))
  | quotMk h1 h2 => exact .inr (.inr (.inl ⟨_, ConstArity.quotMk h1 h2⟩))
  | quot h1 h2 => exact .inr (.inr (.inl ⟨_, ConstArity.quotLift h1 h2⟩))
  | quotK h1 h2 => exact .inr (.inr (.inl ⟨_, ConstArity.quotLift h1 h2⟩))

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.WShape.lam'_le_bot {f : WShapeFun n}
    (H : ∀ x y, (x, y) ∈ f → y ≤ .bot) : WShape.lam' f ≤ .bot := by
  by_cases hf : f.NonZero
  · obtain ⟨⟨x, y⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
    exact (hn (H x y hxy)).elim
  · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
    exact WShape.lam'_bot ▸ this

/-- At more arguments than its arity, a constant's interpretation is `bot`. -/
theorem Const.compat_mismatch (hR : ConstRoles env) {rargs1 : List (WShape n)} {r : Role}
    (h_len : n₂ < rargs1.length) (H1 : Const env c ls R rargs1 m) (H2 : ConstArity env c r n₂) :
    m ≤ TShape.bot := by
  have key {r' L} (h : ConstArity env c r' L) (hl : n₂ < L) : False := by
    cases hR h H2; have := h.determ H2; omega
  induction H1 with
  | bot => exact TShape.bot_eqv.1
  | lam _ m_le ih =>
    refine m_le.trans ((WShape.lam'_le_bot fun x y h => WShape.LE.T_iff.1
      ((ih x y h (by simp; omega)).trans TShape.bot_eqv.2)).T.trans TShape.bot_eqv.1)
  | ext | delta => simp at h_len
  | indTy h1 h2 h3 => exact (key (.indTy h1 h2) (by rw [← h3]; exact h_len)).elim
  | ctor h1 h2 h3 h4 _ h6 => exact (key (.ctor h1 h2 h3 h4) (by rw [← h6]; exact h_len)).elim
  | iota h1 h2 h3 h4 _ h6 =>
    exact (key (.recursor h1 h2 h4) (by simp only [List.length_cons] at h_len; omega)).elim
  | kIota h1 h2 h3 h4 _ _ _ h8 =>
    exact (key (.recursor h1 h2 h4) (by simp only [List.length_cons] at h_len; omega)).elim
  | quotTy h1 h2 _ h4 => exact (key (.quotTy h1 h2) (by rw [← h4]; exact h_len)).elim
  | quotMk h1 h2 => exact (key (.quotMk h1 h2) (by simpa using h_len)).elim
  | quot h1 h2 => exact (key (.quotLift h1 h2) (by simpa using h_len)).elim
  | quotK h1 h2 => exact (key (.quotLift h1 h2) (by simpa using h_len)).elim

/-- The closed terms a constant's interpretation reads, reinterpreted. -/
theorem Const.mapR (hR : ∀ {h e}, R h e → R' h e) (H : Const env c ls R rargs m) :
    Const env c ls R' rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ext h0 h3 hl h4 => exact .ext h0 h3 hl h4
  | delta h0 h1 h2 h3 h4 h5 => exact .delta h0 h1 h2 h3 (hR h4) h5
  | indTy h1 h2 h3 h4 h5 h6 =>
    refine .indTy h1 h2 h3 h4 (fun i c' cty a1 a2 => ?_) h6
    obtain ⟨h, b1, b2⟩ := h5 i c' cty a1 a2
    exact ⟨h, hR b1, b2⟩
  | ctor h1 h2 h3 h4 h5 h6 h7 => exact .ctor h1 h2 h3 h4 h5 h6 h7
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .iota h1 h2 h3 h4 h5 h6 h7 (hR h8) h9 h10
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 => exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 (hR h9) h10
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 => exact .quotTy h1 h2 h3 h4 h5 (hR h6) h7 h8
  | quotMk h1 h2 h3 h4 h5 => exact .quotMk h1 h2 h3 h4 h5
  | quot h1 h2 h3 h4 h5 h6 => exact .quot h1 h2 h3 h4 h5 h6
  | quotK h1 h2 h3 h4 h5 => exact .quotK h1 h2 h3 h4 h5

/-- A constant's interpretation built as a function, against its computing at the same arguments,
is `bot`. -/
theorem Const.lam_le_bot (hR : ConstRoles env) {f : WShapeFun n} {rargs : List (WShape n)}
    (he : ∀ x y, (x, y) ∈ f → Const env c ls R (x :: rargs) y.T)
    (m_le : m ≤ WShape.T (n := n + 1) (.lam' f)) (A : ConstArity env c r rargs.length) :
    m ≤ TShape.bot := by
  by_cases hf : f.NonZero
  · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
    have := compat_mismatch hR (by simp) (he s t (WShapeFun.mem_val hxy)) A
    exact (hn (WShape.LE.T_iff.1 (this.trans TShape.bot_eqv.2))).elim
  · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
    exact m_le.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_eqv.1

/-- A constant the model interprets by given shapes is `bot` at any argument: only its bare
interpretation is given. -/
theorem Const.le_bot_of_dom (hd : AxInterp.dom c) (H : Const env c ls R rargs m)
    (hr : rargs ≠ []) : m ≤ TShape.bot := by
  induction H with
  | bot => exact TShape.bot_eqv.1
  | lam _ m_le ih =>
    exact m_le.trans ((WShape.lam'_le_bot fun x y h => WShape.LE.T_iff.1
      ((ih x y h (by simp)).trans TShape.bot_eqv.2)).T.trans TShape.bot_eqv.1)
  | ext => exact (hr rfl).elim
  | delta h0 => exact (h0 hd).elim
  | indTy _ _ _ _ _ _ hnd | ctor _ _ _ _ _ _ _ hnd | iota _ _ _ _ _ _ _ _ _ _ hnd
  | kIota _ _ _ _ _ _ _ _ _ _ hnd | quotTy _ _ _ _ _ _ _ _ hnd | quotMk _ _ _ _ _ hnd
  | quot _ _ _ _ _ _ hnd | quotK _ _ _ _ _ hnd => exact (hnd hd).elim

/-- A function shape of a constant the model interprets by given shapes is `bot`. -/
theorem Const.lam_le_bot_dom (hd : AxInterp.dom c) {f : WShapeFun n} {rargs : List (WShape n)}
    (he : ∀ x y, (x, y) ∈ f → Const env c ls R (x :: rargs) y.T)
    (m_le : m ≤ WShape.T (n := n + 1) (.lam' f)) : m ≤ TShape.bot :=
  m_le.trans ((WShape.lam'_le_bot fun x y h => WShape.LE.T_iff.1
    ((Const.le_bot_of_dom hd (he x y h) (by simp)).trans TShape.bot_eqv.2)).T.trans
    TShape.bot_eqv.1)

/-- A structure's constructor is the only constructor of every type of a block it is a constructor
of (the auxiliary types of a nested block included). -/
def EtaCtorUniq (env : VEnv) : Prop :=
  ∀ {s : Name} {d : VInductDecl} {t q q' j : Nat} {c c' : VConstructor},
    env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    d.allCtors[q']? = some (j, c') → env.IsEtaCtor c.name → q = q'

/-- A well-formed environment's structures' constructors are the only constructors of the types
they are constructors of. -/
theorem _root_.Lean4Lean.VEnv.WF.etaCtorUniq {env : VEnv} (henv : env.WF) : EtaCtorUniq env := by
  have H := StepUniqProof.names_of_WF henv
  obtain ⟨ρ, hρ⟩ := H.roles
  rintro s d t q q' j c c' hs hq hq' ⟨s'', d'', t'', T'', c'', i1, i2, i3, -, -, i6⟩
  have e1 := hρ.ownCtor i1 i2 (i3 ▸ List.mem_singleton_self c'')
  obtain ⟨d', t', T', c₁, e2, r1, r2, T0, r3, r4⟩ := hρ.ctor hs (List.mem_of_getElem? hq)
  rw [← i6] at e2
  cases e1.symm.trans e2
  cases r1.symm.trans i2
  rw [i3] at r4
  have mem {q : Nat} {c : VConstructor} (h : d.allCtors[q]? = some (j, c)) :
      c.name = c''.name := by
    obtain ⟨T1, h1, h2⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? h)
    cases r3.symm.trans h1
    have := List.mem_map_of_mem (f := (·.name)) h2
    rw [r4] at this; simpa using this
  exact henv.stepUniq.ctor hs hq hq' ((mem hq).trans (mem hq').symm)

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.WShape.map_T_zipWith_join :
    ∀ {l1 l2 : List (WShape n)},
    (l1.zipWith WShape.join l2).map (·.T) = (l1.map (·.T)).zipWith TShape.join (l2.map (·.T))
  | [], _ => rfl
  | _ :: _, [] => rfl
  | _ :: _, _ :: _ => by
    simp only [List.zipWith_cons_cons, List.map_cons, WShape.T_join]
    rw [WShape.map_T_zipWith_join]

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.WShape.Compat.map_T {l1 l2 : List (WShape n)}
    (h : l1.Forall₂ WShape.Compat l2) : (l1.map (·.T)).Forall₂ TShape.Compat (l2.map (·.T)) :=
  List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 (h.imp fun _ _ e => e.T))

omit [ShapeEnv] in
theorem _root_.List.forall₂_of_length {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length → (∀ x ∈ l, ∀ y ∈ l', R x y) →
      l.Forall₂ R l'
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, h, H =>
    .cons (H _ (.head _) _ (.head _)) (List.forall₂_of_length (by simpa using h)
      fun x hx y hy => H x (.tail _ hx) y (.tail _ hy))

omit [AxInterp] in
/-- The fields of compatible constructor shapes of the same constructor are compatible: a shape that
collapses has fields `bot`. -/
theorem _root_.Lean4Lean.LogRel.WShape.Compat.ctor'_inv {l l' : List (WShape n)}
    (h : (WShape.ctor' c l).Compat (.ctor' c l')) (hl : l.length = l'.length) :
    l.Forall₂ WShape.Compat l' := by
  have allbot {l : List (WShape n)} (h : ¬(IsStruct c → WShape.ListNonZero l)) :
      ∀ x ∈ l, x ≤ .bot := fun x hx => Decidable.by_contra fun hn => h fun _ => ⟨x, hx, hn⟩
  unfold WShape.ctor' at h
  split at h <;> rename_i h1 <;> split at h <;> rename_i h2
  · exact (WShape.Compat.ctor_ctor.1 h).2
  · exact List.forall₂_of_length hl fun x _ y hy =>
      WShape.Compat.mono .rfl (allbot h2 y hy) .bot_r
  · exact List.forall₂_of_length hl fun x hx y _ =>
      WShape.Compat.mono (allbot h1 x hx) .rfl .bot_l
  · exact List.forall₂_of_length hl fun x hx y _ =>
      WShape.Compat.mono (allbot h1 x hx) .rfl .bot_l

omit [ShapeEnv] in
theorem _root_.List.forall₂_of_getElem? {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, l.length = l'.length →
      (∀ (i : Nat) (a : α) (b : β), l[i]? = some a → l'[i]? = some b → R a b) → l.Forall₂ R l'
  | [], [], _, _ => .nil
  | _ :: _, _ :: _, h, H =>
    .cons (H 0 _ _ rfl rfl) (List.forall₂_of_getElem? (by simpa using h)
      fun i a b h1 h2 => H (i + 1) a b h1 h2)

omit [ShapeEnv] in
theorem _root_.List.forall₂_getD {R : α → β → Prop} {d : α} {d' : β} :
    ∀ {l : List α} {l' : List β}, l.Forall₂ R l' → R d d' → ∀ i, R (l.getD i d) (l'.getD i d')
  | _, _, .nil, h, _ => by simpa using h
  | _, _, .cons a _, _, 0 => by simpa using a
  | _, _, .cons _ l, h, i+1 => by simpa using List.forall₂_getD l h i

omit [AxInterp] in
theorem getD_join_le : ∀ {l l' : List TShape} (i : Nat), l.length = l'.length →
    (l.getD i TShape.bot).join (l'.getD i TShape.bot) ≤ (l.zipWith TShape.join l').getD i TShape.bot
  | [], [], _, _ => by simpa using (TShape.Join.mk TShape.Compat.bot_l _).2 ⟨.rfl, .rfl⟩
  | _ :: _, _ :: _, 0, _ => by simpa using TShape.LE.rfl
  | _ :: _, _ :: _, i+1, h => by simpa using getD_join_le i (by simpa using h)

omit [AxInterp] in
theorem kFieldShapes_compat {c : VConstructor} {is is' : List TShape}
    (h : is.Forall₂ TShape.Compat is') :
    (kFieldShapes c is).Forall₂ TShape.Compat (kFieldShapes c is') := by
  simp only [kFieldShapes]
  refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
  generalize List.range c.fields.length = ks
  induction ks with
  | nil => exact .nil
  | cons k ks ih =>
    refine .cons ?_ ih
    cases VInductDecl.fieldIdx c k with
    | some i => exact List.forall₂_getD h TShape.Compat.bot_l i
    | none => exact TShape.Compat.bot_l

omit [AxInterp] in
theorem kFieldShapes_join_le {c : VConstructor} {is is' : List TShape}
    (hl : is.length = is'.length) :
    ((kFieldShapes c is).zipWith TShape.join (kFieldShapes c is')).Forall₂ (· ≤ ·)
      (kFieldShapes c (is.zipWith TShape.join is')) := by
  simp only [kFieldShapes, List.zipWith_map, List.zipWith_self]
  refine List.forall₂_map_left_iff.2 (List.forall₂_map_right_iff.2 ?_)
  generalize List.range c.fields.length = ks
  induction ks with
  | nil => exact .nil
  | cons k ks ih =>
    refine .cons ?_ ih
    cases VInductDecl.fieldIdx c k with
    | some i => exact getD_join_le i hl
    | none => exact (TShape.Join.mk TShape.Compat.bot_l _).2 ⟨.rfl, .rfl⟩

omit [AxInterp] in
theorem _root_.Lean4Lean.LogRel.WShape.Compat.ctor'_cases {l l' : List (WShape n)}
    (h : (WShape.ctor' c l).Compat (.ctor' c' l')) :
    c = c' ∨ IsStruct c = true ∨ IsStruct c' = true := by
  unfold WShape.ctor' at h
  split at h <;> rename_i h1 <;> split at h <;> rename_i h2
  · exact .inl (WShape.Compat.ctor_ctor.1 h).1
  · exact .inr (.inr (Decidable.by_contra fun hn => h2 fun e => absurd e hn))
  · exact .inr (.inl (Decidable.by_contra fun hn => h1 fun e => absurd e hn))
  · exact .inr (.inl (Decidable.by_contra fun hn => h1 fun e => absurd e hn))

omit [ShapeEnv] in
theorem _root_.List.Forall₂.getElem?' {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β} {k : Nat} {a : α} {b : β}, l.Forall₂ R l' →
      l[k]? = some a → l'[k]? = some b → R a b
  | _, _, 0, _, _, .cons h _, rfl, rfl => h
  | _, _, _+1, _, _, .cons _ h, e1, e2 => List.Forall₂.getElem?' h e1 e2

omit [AxInterp] in
/-- Compatible constructor shapes of a constructor: one has fields `bot`, or their fields are
compatible. -/
theorem _root_.Lean4Lean.LogRel.WShape.Compat.ctor'_fields {l l' : List (WShape n)}
    (h : (WShape.ctor' c l).Compat (.ctor' c l')) :
    (∀ x ∈ l, x ≤ .bot) ∨ (∀ y ∈ l', y ≤ .bot) ∨ l.Forall₂ WShape.Compat l' := by
  have allbot {l : List (WShape n)} (h : ¬(IsStruct c → WShape.ListNonZero l)) :
      ∀ x ∈ l, x ≤ .bot := fun x hx => Decidable.by_contra fun hn => h fun _ => ⟨x, hx, hn⟩
  unfold WShape.ctor' at h
  split at h <;> rename_i h1 <;> split at h <;> rename_i h2
  · exact .inr (.inr (WShape.Compat.ctor_ctor.1 h).2)
  · exact .inr (.inl (allbot h2))
  · exact .inl (allbot h1)
  · exact .inl (allbot h1)

section
local macro "arity" : tactic => `(tactic| first
  | exact ConstArity.delta ‹_› ‹_›
  | exact ConstArity.indTy ‹_› ‹_›
  | exact ConstArity.ctor ‹_› ‹_› ‹_› ‹_›
  | exact ConstArity.recursor ‹_› ‹_› ‹_›
  | exact ConstArity.quotTy ‹_› ‹_›
  | exact ConstArity.quotMk ‹_› ‹_›
  | exact ConstArity.quotLift ‹_› ‹_›)

set_option hygiene false in
local macro "mismatch " h:term : tactic =>
  `(tactic| first
    | exact absurd ‹AxInterp.dom c› ‹¬AxInterp.dom c›
    | exact absurd (hRo $h (by arity)) (by intro h; cases h))

omit [ShapeEnv] [AxInterp] in
theorem levels_equiv_trans : ∀ {l₁ l₂ l₃ : List VLevel}, List.Forall₂ (· ≈ ·) l₁ l₂ →
    List.Forall₂ (· ≈ ·) l₂ l₃ → List.Forall₂ (· ≈ ·) l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons a h, .cons b h' => .cons (Eq.trans a b) (levels_equiv_trans h h')

omit [ShapeEnv] [AxInterp] in
theorem levels_equiv_symm : ∀ {l₁ l₂ : List VLevel}, List.Forall₂ (· ≈ ·) l₁ l₂ →
    List.Forall₂ (· ≈ ·) l₂ l₁
  | _, _, .nil => .nil
  | _, _, .cons a h => .cons (Eq.symm a) (levels_equiv_symm h)

/-- What the model needs of the shapes it gives constants: compatible ones join within them. -/
structure AxOK : Prop where
  join : ∀ {c ls₁ ls₂ m₁ m₂}, AxInterp.I c ls₁ m₁ → AxInterp.I c ls₂ m₂ →
    List.Forall₂ (· ≈ ·) ls₁ ls₂ → m₁.Compat m₂ ∧ AxInterp.I c ls₁ (m₁.join m₂)

omit [AxInterp] in
theorem AxOK.none : @AxOK _ (@AxInterp.none _) := ⟨nofun⟩

theorem Const.compat_join (hRo : ConstRoles env) (hU : StepUniq env) (hA : AxOK)
    (hS : ∀ c, IsStruct c = true → env.IsEtaCtor c) (hE : EtaCtorUniq env)
    {rargs1 rargs2 : List (WShape n)} (hc : List.Forall₂ WShape.Compat rargs1 rargs2)
    (H1 : Const env c ls R rargs1 m) (H2 : Const env c ls R' rargs2 m')
    (hR_bot : ∀ {n} {e}, R (WShape.T (n := n) .bot) e)
    (hR'_bot : ∀ {n} {e}, R' (WShape.T (n := n) .bot) e)
    (hR₃_mono : ∀ {a a' A}, a ≤ a' → R₃ a' A → R₃ a A)
    (hRR : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A) :
    m.Compat m' ∧ Const env c ls R₃ (rargs1.zipWith WShape.join rargs2) (m.join m') := by
  have toR₃ {h e} (hr : R h e) : R₃ h e :=
    have ⟨a1, a2⟩ := hRR hr (hR'_bot (n := 0))
    hR₃_mono (TShape.Join.mk a1).le.1 a2
  have toR₃' {h e} (hr : R' h e) : R₃ h e :=
    have ⟨a1, a2⟩ := hRR (hR_bot (n := 0)) hr
    hR₃_mono (TShape.Join.mk a1).le.2 a2
  -- one side below `bot`
  have bot_l {n m m' rargs1 rargs2} (hm : m ≤ TShape.bot) (H : Const (n := n) env c ls R' rargs2 m')
      (hc : List.Forall₂ WShape.Compat rargs1 rargs2) :
      m.Compat m' ∧ Const env c ls R₃ (rargs1.zipWith WShape.join rargs2) (m.join m') := by
    have hbc : m.Compat m' := TShape.Compat.mono hm .rfl .bot_l
    refine ⟨hbc, ((H.mapR toR₃').mono_l (WShape.le_zipWith_join hc).2).mono ?_⟩
    exact (TShape.Join.mk hbc _).2 ⟨hm.trans TShape.bot_le', .rfl⟩
  have bot_r {n m m' rargs1 rargs2} (hm : m' ≤ TShape.bot) (H : Const (n := n) env c ls R rargs1 m)
      (hc : List.Forall₂ WShape.Compat rargs1 rargs2) :
      m.Compat m' ∧ Const env c ls R₃ (rargs1.zipWith WShape.join rargs2) (m.join m') := by
    have hbc : m.Compat m' := TShape.Compat.mono .rfl hm .bot_r
    refine ⟨hbc, ((H.mapR toR₃).mono_l (WShape.le_zipWith_join hc).1).mono ?_⟩
    exact (TShape.Join.mk hbc _).2 ⟨.rfl, hm.trans TShape.bot_le'⟩
  induction H1 generalizing m' with
  | bot => exact bot_l TShape.bot_eqv.1 H2 hc
  | @lam n rargs m f he m_le ih =>
    rcases Const.arity H2 with hb | ⟨f', m_le', he'⟩ | ⟨r, A⟩ | ⟨hd, -⟩
    · exact bot_r hb (.lam he m_le) hc
    · have hfc : WShapeFun.Compat f f' := by
        simp only [WShapeFun.Compat.def, Prod.forall]
        intro x y h1 x' y' h2 hc'
        exact WShape.Compat.T_iff.2 (ih _ _ h1 (hc.cons hc') (he' _ _ h2)).1
      refine have hmc := .mono m_le m_le' (WShape.Compat.lam'_lam' hfc).T; ⟨hmc, ?_⟩
      have hJ_lam : WShape.Join (.lam' f) (.lam' f') (.lam' (f.join f')) :=
        WShape.Join.lam'.2 (.mk hfc)
      refine .lam (f := f.join f') ?_ <|
        (TShape.Join.mk hmc _).2 ⟨m_le.trans hJ_lam.le.1.T, m_le'.trans hJ_lam.le.2.T⟩
      simp only [WShapeFun.mem_join hfc]
      rintro _ _ ⟨⟨x, y⟩, h1, ⟨x', y'⟩, h2, hc', rfl, rfl⟩; dsimp only at *
      have ⟨x₁, le, a1⟩ := f.app_eq (x.join x')
      have ⟨x₂, le', a2⟩ := f'.app_eq (x.join x')
      have hxc' := WShape.Compat.iff.2 ⟨_, le, le'⟩
      have ⟨hyc, ih⟩ := ih _ _ a1 (hc.cons hxc') (he' _ _ a2)
      rw [WShape.T_join] at ih
      exact ih.mono_l <| .cons ((WShape.Join.mk hxc' _).2 ⟨le, le'⟩) <|
        List.forall₂_refl' fun _ => .rfl
    · exact bot_l (Const.lam_le_bot hRo he m_le (hc.length_eq ▸ A)) H2 hc
    · exact bot_l (Const.lam_le_bot_dom hd he m_le) H2 hc
  | @ext _ _ _ n' h0 h3 hl h4 =>
    cases hc
    have H1 := Const.ext (env := env) (R := R) (n := n') h0 h3 hl h4
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 .nil
    | lam he' m_le' => exact bot_r (Const.lam_le_bot_dom h0 he' m_le') H1 .nil
    | ext _ a3 al a4 =>
      have ⟨c₁, j₁⟩ := hA.join h3 a3 (levels_equiv_trans hl (levels_equiv_symm al))
      have jl := (TShape.Join.mk c₁).le
      have cm := TShape.Compat.mono h4 a4 c₁
      exact ⟨cm, .ext h0 j₁ hl ((TShape.Join.mk cm _).2 ⟨h4.trans jl.1, a4.trans jl.2⟩)⟩
    | delta a0 => exact (a0 h0).elim
    | _ => exact absurd h0 ‹¬AxInterp.dom c›
  | @delta _ _ n' _ h0 h1 h2 h3 h4 h5 =>
    have A1 := ConstArity.delta h1 h2
    have H1 := Const.delta (R := R) (n := n') h0 h1 h2 h3 h4 h5
    cases hc
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 .nil
    | lam he' m_le' => exact bot_r (Const.lam_le_bot hRo he' m_le' A1) H1 .nil
    | ext a0 => exact (h0 a0).elim
    | delta _ a1 a2 a3 a4 a5 =>
      cases hU.delta h1 a1 h2 a2
      have ⟨c₁, j₁⟩ := hRR h4 a4
      have jl := (TShape.Join.mk c₁).le
      have cm := TShape.Compat.mono h5 a5 c₁
      exact ⟨cm, .delta h0 h1 h2 h3 j₁ ((TShape.Join.mk cm _).2 ⟨h5.trans jl.1, a5.trans jl.2⟩)⟩
    | _ => clear H1 h0 h1 h2 h3 h4 h5; mismatch A1
  | @ctor _ _ _ d _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 =>
    have A1 := ConstArity.ctor h1 h2 h3 h4
    have H1 : Const env c ls R _ _ := .ctor h1 h2 h3 h4 h5 h6 h7
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' =>
      exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq, h6]; exact A1)) H1 hc
    | ctor a1 a2 a3 a4 a5 a6 a7 =>
      cases hRo A1 (ConstArity.ctor a1 a2 a3 a4)
      have hcL := List.forall₂_drop' (k := d.params.length) (List.Forall₂.reverse.2 hc)
      have cm := TShape.Compat.mono h7 a7 (WShape.Compat.ctor'_ctor' hcL).T
      refine ⟨cm, .ctor h1 h2 h3 h4 h5 (by rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, h6]) ?_⟩
      rw [List.reverse_zipWith hc.length_eq, List.drop_zipWith]
      exact (TShape.Join.mk cm _).2 ⟨h7.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hcL).1).T,
        a7.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hcL).2).T⟩
    | _ => clear H1 h1 h2 h3 h4 h5 h6 h7; mismatch A1
  | @quotMk _ _ _ a r α h1 h2 h3 h4 h5 =>
    have A1 := ConstArity.quotMk h1 h2
    have H1 : Const env c ls R [a, r, α] _ := .quotMk h1 h2 h3 h4 h5
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' => exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq]; exact A1)) H1 hc
    | quotMk a1 a2 a3 a4 a5 =>
      obtain ⟨ha, -⟩ := List.forall₂_cons.1 hc
      have hcL : [_].Forall₂ WShape.Compat [_] := .cons ha .nil
      have cm := TShape.Compat.mono h5 a5 (WShape.Compat.ctor'_ctor' hcL).T
      refine ⟨cm, .quotMk h1 h2 h3 h4 ?_⟩
      exact (TShape.Join.mk cm _).2 ⟨h5.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hcL).1).T,
        a5.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hcL).2).T⟩
    | _ => clear H1 h1 h2 h3 h4 h5; mismatch A1
  | @quotK _ _ _ _ q hh f β r α h1 h2 h3 h4 h5 =>
    have A1 := ConstArity.quotLift h1 h2
    have H1 : Const env c ls R [q, hh, f, β, r, α] _ := .quotK h1 h2 h3 h4 h5
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' => exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq]; exact A1)) H1 hc
    | quotK a1 a2 a3 a4 a5 =>
      obtain ⟨-, hc⟩ := List.forall₂_cons.1 hc
      obtain ⟨-, hc⟩ := List.forall₂_cons.1 hc
      obtain ⟨hf, -⟩ := List.forall₂_cons.1 hc
      have hb : TShape.bot.Compat TShape.bot := .bot_l
      have ⟨cm, j⟩ := AppS.compat_join hf.T h5 a5 (.cons hb .nil)
      refine ⟨cm, .quotK h1 h2 h3 h4 ?_⟩
      rw [WShape.T_join] at j
      exact j.args_mono (.cons ((TShape.Join.mk hb _).2 ⟨.rfl, .rfl⟩) .nil)
    | quot a1 a2 a3 a4 =>
      cases h3.symm.trans a3; exact absurd h4 a4
    | _ => clear H1 h1 h2 h3 h4 h5; mismatch A1
  | @quot _ _ _ _ a x hh f β r α h1 h2 h3 h4 h5 h6 =>
    have A1 := ConstArity.quotLift h1 h2
    have H1 : Const env c ls R [x, hh, f, β, r, α] _ := .quot h1 h2 h3 h4 h5 h6
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' => exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq]; exact A1)) H1 hc
    | quotK a1 a2 a3 a4 =>
      cases h3.symm.trans a3; exact absurd a4 h4
    | @quot _ _ _ _ a' x' _ f' _ _ _ a1 a2 a3 a4 a5 a6 =>
      obtain ⟨hx, hc⟩ := List.forall₂_cons.1 hc
      obtain ⟨-, hc⟩ := List.forall₂_cons.1 hc
      obtain ⟨hf, -⟩ := List.forall₂_cons.1 hc
      have hcx := TShape.Compat.mono h6 a6 hx.T
      have cc := WShape.Compat.T_iff.2 hcx
      obtain ⟨ha, -⟩ := List.forall₂_cons.1 (WShape.Compat.ctor'_inv cc rfl)
      have ⟨cm, j⟩ := AppS.compat_join hf.T h5 a5 (.cons ha.T .nil)
      refine ⟨cm, .quot (a := a.join a') h1 h2 h3 h4 ?_ ?_⟩
      · rw [WShape.T_join] at j
        simpa only [List.zipWith_cons_cons, List.zipWith_nil_left, WShape.T_join] using j
      · have hx' := (WShape.Join.mk hx).le
        rw [show [a.join a'] = [a].zipWith WShape.join [a'] from rfl,
          ← WShape.ctor'_join (.cons ha .nil)]
        exact WShape.LE.T ((WShape.Join.mk cc _).2
          ⟨(WShape.LE.T_iff.1 h6).trans hx'.1, (WShape.LE.T_iff.1 a6).trans hx'.2⟩)
    | _ => clear H1 h1 h2 h3 h4 h5 h6; mismatch A1
  | @indTy _ _ d t T rargs ctys h1 h2 h3 h4 h5 h6 =>
    have A1 := ConstArity.indTy h1 h2
    have H1 : Const env c ls R rargs _ := .indTy h1 h2 h3 h4 h5 h6
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' =>
      exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq, h3]; exact A1)) H1 hc
    | @indTy _ _ d' t' T' rargs2 ctys' a1 a2 a3 a4 a5 a6 =>
      cases h1.symm.trans a1; cases h2.symm.trans a2
      have hargs := WShape.Compat.map_T
        (List.forall₂_take' (k := d.params.length) (List.Forall₂.reverse.2 hc))
      have key : ∀ (i : Nat) (c' : VConstructor) (cty cty' : WShape _), T.ctors[i]? = some c' →
          ctys[i]? = some cty →
          ctys'[i]? = some cty' → cty.Compat cty' ∧ ∃ h, R₃ h (c'.type.instL ls) ∧
            PiAppS h (((rargs.zipWith WShape.join rargs2).reverse.take d.params.length).map (·.T))
              (cty.join cty').T := by
        intro i c' cty cty' e1 e2 e3
        obtain ⟨h, b1, b2⟩ := h5 i c' cty e1 e2
        obtain ⟨h', b1', b2'⟩ := a5 i c' cty' e1 e3
        have ⟨ch, jh⟩ := hRR b1 b1'
        have ⟨cc, jc⟩ := PiAppS.compat_join ch b2 b2' hargs
        refine ⟨WShape.Compat.T_iff.2 cc, _, jh, ?_⟩
        rw [← WShape.T_join, List.reverse_zipWith hc.length_eq, List.take_zipWith,
          WShape.map_T_zipWith_join]
        exact jc
      have hctys : ctys.Forall₂ WShape.Compat ctys' :=
        List.forall₂_of_getElem? (h4.trans a4.symm) fun i a b e2 e3 => by
          obtain ⟨c', e1⟩ : ∃ c', T.ctors[i]? = some c' :=
            ⟨_, List.getElem?_eq_getElem (h4 ▸ (List.getElem?_eq_some_iff.1 e2).1)⟩
          exact (key i c' a b e1 e2 e3).1
      have hl := List.forall₂_append' (List.Forall₂.reverse.2 hc) hctys
      rw [← hc.length_eq] at a6
      have cm := TShape.Compat.mono h6 a6 (WShape.Compat.indTy_indTy.2 ⟨rfl, rfl, hl⟩).T
      have hzl : (rargs.zipWith WShape.join rargs2).length = rargs.length := by
        rw [List.length_zipWith, ← hc.length_eq, Nat.min_self]
      refine ⟨cm, .indTy (ctys := ctys.zipWith WShape.join ctys') h1 h2 (hzl.trans h3)
        (by rw [List.length_zipWith, h4, a4, Nat.min_self]) (fun i c' cty e1 e2 => ?_) ?_⟩
      · obtain ⟨a, b, e2', e3', rfl⟩ := List.getElem?_zipWith_eq_some.1 e2
        obtain ⟨-, h, j1, j2⟩ := key i c' a b e1 e2' e3'
        exact ⟨h, j1, j2⟩
      · rw [hzl, List.reverse_zipWith hc.length_eq,
          ← List.zipWith_append (by simp [hc.length_eq])]
        exact (TShape.Join.mk cm _).2
          ⟨h6.trans (WShape.indTy_le_indTy.2 ⟨rfl, rfl, (WShape.le_zipWith_join hl).1⟩).T,
            a6.trans (WShape.indTy_le_indTy.2 ⟨rfl, rfl, (WShape.le_zipWith_join hl).2⟩).T⟩
    | _ => clear H1 h1 h2 h3 h4 h5 h6; mismatch A1
  | @quotTy _ u h m rargs cty ci h1 h2 h3 h4 h5 h6 h7 h8 =>
    have A1 := ConstArity.quotTy h1 h2
    have H1 : Const env c ls R rargs _ := .quotTy h1 h2 h3 h4 h5 h6 h7 h8
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' =>
      exact bot_r (Const.lam_le_bot hRo he' m_le' (by rw [← hc.length_eq, h4]; exact A1)) H1 hc
    | @quotTy _ u' h' _ rargs2 cty' ci' a1 a2 a3 a4 a5 a6 a7 a8 =>
      cases h3.symm.trans a3; cases h5.symm.trans a5
      have ⟨ch, jh⟩ := hRR h6 a6
      have ⟨cc, jc⟩ := PiAppS.compat_join ch h7 a7 (WShape.Compat.map_T (List.Forall₂.reverse.2 hc))
      have hl := List.forall₂_append' (List.Forall₂.reverse.2 hc)
        (.cons (WShape.Compat.T_iff.2 cc) .nil)
      have cm := TShape.Compat.mono h8 a8 (WShape.Compat.indTy_indTy.2 ⟨rfl, rfl, hl⟩).T
      refine ⟨cm, .quotTy (cty := cty.join cty') h1 h2 h3
        (by rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, h4]) h5 jh ?_ ?_⟩
      · rw [← WShape.T_join, List.reverse_zipWith hc.length_eq, WShape.map_T_zipWith_join]
        exact jc
      · rw [List.reverse_zipWith hc.length_eq,
          show [cty.join cty'] = [cty].zipWith WShape.join [cty'] from rfl,
          ← List.zipWith_append (by simp [hc.length_eq])]
        exact (TShape.Join.mk cm _).2
          ⟨h8.trans (WShape.indTy_le_indTy.2 ⟨rfl, rfl, (WShape.le_zipWith_join hl).1⟩).T,
            a8.trans (WShape.indTy_le_indTy.2 ⟨rfl, rfl, (WShape.le_zipWith_join hl).2⟩).T⟩
    | _ => clear H1 h1 h2 h3 h4 h5 h6 h7 h8; mismatch A1
  | @iota _ s h m fs x rest T c' d t j q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    have A1 := ConstArity.recursor h1 h2 h4
    have H1 : Const env c ls R (x :: rest) _ := .iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' =>
      exact bot_r (Const.lam_le_bot hRo he' m_le'
        (by rw [← hc.length_eq, List.length_cons, h6]; exact A1)) H1 hc
    | @iota _ s' h' _ fs' x' rest' T' c'' d' t' j' q' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      cases hRo A1 (ConstArity.recursor a1 a2 a4)
      cases h4.symm.trans a4
      obtain ⟨hx, hc⟩ := List.forall₂_cons.1 hc
      have cc := WShape.Compat.T_iff.2 (TShape.Compat.mono h10 a10 hx.T)
      have hq : q = q' := by
        rcases WShape.Compat.ctor'_cases cc with e | e | e
        · exact hU.ctor h1 h3 a3 e
        · exact hE h1 h3 a3 (hS _ e)
        · exact (hE h1 a3 h3 (hS _ e)).symm
      cases hq; cases h3.symm.trans a3
      have hfs := WShape.Compat.ctor'_inv cc (h7.trans a7.symm)
      have hrest := List.forall₂_take'
        (k := d.params.length + d.allTypes.length + d.allCtors.length)
        (List.Forall₂.reverse.2 hc)
      have ⟨ch, jh⟩ := hRR h8 a8
      have ⟨cm, j⟩ := AppS.compat_join ch h9 a9
        (List.forall₂_append' (WShape.Compat.map_T hrest) (WShape.Compat.map_T hfs))
      refine ⟨cm, .iota (fs := fs.zipWith WShape.join fs') (x := x.join x') h1 h2 h3 h4 h5
        (by rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, h6])
        (by rw [List.length_zipWith, h7, a7, Nat.min_self]) jh ?_ ?_⟩
      · rw [List.reverse_zipWith hc.length_eq, List.take_zipWith, WShape.map_T_zipWith_join,
          WShape.map_T_zipWith_join, ← List.zipWith_append (by simp [hc.length_eq])]
        exact j
      · have hx' := (WShape.Join.mk hx).le
        rw [← WShape.ctor'_join hfs]
        exact WShape.LE.T ((WShape.Join.mk cc _).2
          ⟨(WShape.LE.T_iff.1 h10).trans hx'.1, (WShape.LE.T_iff.1 a10).trans hx'.2⟩)
    | kIota a1 a2 a3 a4 a5 a6 =>
      cases hRo A1 (ConstArity.recursor a1 a2 a4); exact absurd a6 h5
    | _ => clear H1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10; mismatch A1
  | @kIota _ s h m d t j q T c' rargs e h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    have A1 := ConstArity.recursor h1 h2 h4
    have H1 : Const env c ls R (e :: rargs) _ := .kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    cases H2 with
    | bot => exact bot_r TShape.bot_eqv.1 H1 hc
    | lam he' m_le' =>
      exact bot_r (Const.lam_le_bot hRo he' m_le'
        (by rw [← hc.length_eq, List.length_cons, h8]; exact A1)) H1 hc
    | iota a1 a2 a3 a4 a5 =>
      cases hRo A1 (ConstArity.recursor a1 a2 a4); exact absurd h6 a5
    | @kIota _ s' h' _ d' t' j' q' T' c'' rargs' e' a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 =>
      cases hRo A1 (ConstArity.recursor a1 a2 a4)
      cases h4.symm.trans a4
      cases h5.symm.trans a5
      cases hU.ctor h1 h3 a3 rfl
      obtain ⟨-, hc⟩ := List.forall₂_cons.1 hc
      have hr := List.Forall₂.reverse.2 hc
      have ⟨ch, jh⟩ := hRR h9 a9
      have ⟨cm, j⟩ := AppS.compat_join ch h10 a10
        (List.forall₂_append' (WShape.Compat.map_T (List.forall₂_take' hr))
          (kFieldShapes_compat (WShape.Compat.map_T (List.forall₂_drop' hr))))
      refine ⟨cm, .kIota (e := e.join e') h1 h2 h3 h4 h5 h6 h7
        (by rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, h8]) jh ?_⟩
      rw [List.zipWith_append (by simp [hc.length_eq])] at j
      refine j.args_mono (List.forall₂_append' ?_ ?_)
      · rw [List.reverse_zipWith hc.length_eq, List.take_zipWith, WShape.map_T_zipWith_join]
        exact List.forall₂_refl' fun _ => .rfl
      · rw [List.reverse_zipWith hc.length_eq, List.drop_zipWith, WShape.map_T_zipWith_join]
        exact kFieldShapes_join_le (by simp [hc.length_eq])
    | _ => clear H1 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10; mismatch A1

end

theorem Const.lift (hn : n₁ ≤ n₂) (H : Const (n := n₁) env c ls R rargs m) :
    Const env c ls R (rargs.map (WShape.lift n₂)) m := by
  induction H generalizing n₂ with
  | bot => exact .bot
  | @lam _ rargs m f _ h2 ih =>
    refine .lam (f := f.lift n₂) (fun _ _ h => ?_) ?_
    · obtain ⟨x, y, h', rfl, rfl⟩ := (WShapeFun.mem_lift hn).1 h
      exact (ih _ _ h' hn).mono (TShape.lift_eqv hn).1
    · exact WShape.lift_lam' hn ▸ h2.trans (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | ext h0 h3 hl h4 => exact .ext h0 h3 hl h4
  | delta h0 h1 h2 h3 h4 h5 => exact .delta h0 h1 h2 h3 h4 h5
  | @indTy _ _ d _ _ rargs ctys h1 h2 h3 h4 h5 h6 =>
    refine .indTy (ctys := ctys.map (WShape.lift n₂)) h1 h2 (by simpa using h3) (by simpa using h4)
      (fun i c' cty' a1 a2 => ?_) ?_
    · obtain ⟨cty, e, rfl⟩ : ∃ cty, ctys[i]? = some cty ∧ cty.lift n₂ = cty' := by
        simpa using a2
      obtain ⟨h, b1, b2⟩ := h5 i c' cty a1 e
      refine ⟨h, b1, (b2.mono (TShape.lift_eqv hn).1 .rfl).args_mono ?_⟩
      rw [← List.map_reverse, ← List.map_take]
      exact lift_T_ge hn
    · rw [List.length_map]; refine h6.trans ?_
      rw [← List.map_reverse, ← List.map_append, ← WShape.lift_indTy hn]
      exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | ctor h1 h2 h3 h4 h5 h6 h7 =>
    refine .ctor h1 h2 h3 h4 h5 (by simpa using h6) (h7.trans ?_)
    rw [← List.map_reverse, ← List.map_drop, ← WShape.lift_ctor' hn]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | @iota _ _ _ _ fs x rest _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    obtain ⟨k, rfl⟩ : ∃ k, n₂ = k + 1 := ⟨n₂ - 1, by omega⟩
    have hk : _ ≤ k := Nat.le_of_succ_le_succ hn
    simp only [List.map_cons]
    refine .iota (fs := fs.map (WShape.lift k)) h1 h2 h3 h4 h5 (by simpa using h6)
      (by simpa using h7) h8 (h9.args_mono ?_) ?_
    · rw [← List.map_reverse, ← List.map_take]
      exact List.forall₂_append' (lift_T_ge hn) (lift_T_ge hk)
    · rw [← WShape.lift_ctor' hk]
      exact (TShape.lift_eqv hn).1.trans (h10.trans (TShape.lift_eqv hn).2)
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    refine .kIota h1 h2 h3 h4 h5 h6 h7 (by simpa using h8) h9 (h10.args_mono ?_)
    rw [← List.map_reverse, ← List.map_take, ← List.map_drop]
    exact List.forall₂_append' (lift_T_ge hn) (kFieldShapes_mono (lift_T_ge hn))
  | @quotTy _ _ _ _ rargs cty _ h1 h2 h3 h4 h5 h6 h7 h8 =>
    refine .quotTy (cty := cty.lift n₂) h1 h2 h3 (by simpa using h4) h5 h6
      ((h7.mono (TShape.lift_eqv hn).1 .rfl).args_mono ?_) (h8.trans ?_)
    · rw [← List.map_reverse]; exact lift_T_ge hn
    · rw [← List.map_reverse, show [cty.lift n₂] = [cty].map (WShape.lift n₂) from rfl,
        ← List.map_append, ← WShape.lift_indTy hn]
      exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | @quotMk _ _ _ a r α h1 h2 h3 h4 h5 =>
    refine .quotMk h1 h2 h3 h4 (h5.trans ?_)
    rw [show [a.lift n₂] = [a].map (WShape.lift n₂) from rfl, ← WShape.lift_ctor' hn]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | quot h1 h2 h3 h4 h5 h6 =>
    obtain ⟨k, rfl⟩ : ∃ k, n₂ = k + 1 := ⟨n₂ - 1, by omega⟩
    have hk : _ ≤ k := Nat.le_of_succ_le_succ hn
    simp only [List.map_cons, List.map_nil]
    refine .quot h1 h2 h3 h4 ((h5.mono .rfl (TShape.lift_eqv hn).2).args_mono
      (.cons (TShape.lift_eqv hk).2 .nil)) ?_
    rw [← List.map_singleton (f := WShape.lift k), ← WShape.lift_ctor' hk]
    exact (TShape.lift_eqv hn).1.trans (h6.trans (TShape.lift_eqv hn).2)
  | quotK h1 h2 h3 h4 h5 =>
    exact .quotK h1 h2 h3 h4 (h5.mono .rfl (TShape.lift_eqv hn).2)

theorem mono (h : m ≤ m') (H : LE_Interp env ρ m' M) : LE_Interp env ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 (h.trans h3) h4 h5 h6 h7
  | proj h1 h2 h3 h4 h5 h6 => exact .proj h1 h2 h3 h4 h5 (h.trans h6)

theorem mono_l (hρ : ρ.LE ρ') (H : LE_Interp env ρ m M) : LE_Interp env ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | const h1 h2 h3 h4 _ h6 _ ihA ihR => exact .const h1 h2 h3 h4 (ihA hρ) h6 (ihR · · · hρ)
  | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih hρ) h5 h6

theorem lift (le : m.1 ≤ n) (H : LE_Interp env ρ m M) : LE_Interp env ρ (m.2.lift n).T M :=
  H.mono (TShape.lift_eqv le).1

/-- The closed terms the interpretation of constants reads: the right-hand sides of the
environment's definitions and its recursors' reducts, and the constants' types. -/
structure ClosedRules (env : VEnv) : Prop where
  defeq : env.defeqs df → df.rhs.ClosedN
  constType : env.constants c = some ci → ci.type.ClosedN
  ctor : env.inducts s = some (d, t) → d.types[t]? = some T → c ∈ T.ctors → c.type.ClosedN
  iotaRhs : env.inducts s = some (d, t) → d.allCtors[q]? = some (j, c) →
    (d.iotaRhs ls q j c).ClosedN

omit [ShapeEnv] in
theorem ClosedRules.of_ordered (henv : env.Ordered) (hU : StepUniq env)
    (hctor : ∀ {s d t T c}, env.inducts s = some (d, t) → d.types[t]? = some T → c ∈ T.ctors →
      VExpr.ClosedN c.type) :
    ClosedRules env where
  defeq h := (henv.closed.2 h).2.1
  constType h := henv.closedC h
  ctor := hctor
  iotaRhs h1 h2 := Step.iotaRhs_closed henv hU h1 h2

theorem Const.closed (hcl : ClosedRules env) (H : Const env c ls R rargs m) :
    Const env c ls (fun h e => e.ClosedN ∧ R h e) rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ext h0 h3 hl h4 => exact .ext h0 h3 hl h4
  | delta h0 h1 h2 h3 h4 h5 => exact .delta h0 h1 h2 h3 ⟨(hcl.defeq h1).instL, h4⟩ h5
  | indTy h1 h2 h3 h4 h5 h6 =>
    refine .indTy h1 h2 h3 h4 (fun i c' cty a1 a2 => ?_) h6
    obtain ⟨h, b1, b2⟩ := h5 i c' cty a1 a2
    exact ⟨h, ⟨(hcl.ctor h1 h2 (List.mem_of_getElem? a1)).instL, b1⟩, b2⟩
  | ctor h1 h2 h3 h4 h5 h6 h7 => exact .ctor h1 h2 h3 h4 h5 h6 h7
  | iota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .iota h1 h2 h3 h4 h5 h6 h7 ⟨hcl.iotaRhs h1 h3, h8⟩ h9 h10
  | kIota h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .kIota h1 h2 h3 h4 h5 h6 h7 h8 ⟨hcl.iotaRhs h1 h3, h9⟩ h10
  | quotTy h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .quotTy h1 h2 h3 h4 h5 ⟨(hcl.constType h5).instL, h6⟩ h7 h8
  | quotMk h1 h2 h3 h4 h5 => exact .quotMk h1 h2 h3 h4 h5
  | quot h1 h2 h3 h4 h5 h6 => exact .quot h1 h2 h3 h4 h5 h6
  | quotK h1 h2 h3 h4 h5 => exact .quotK h1 h2 h3 h4 h5

theorem closed (hcl : ClosedRules env) (cl : VExpr.ClosedN M k) (h : ∀ i < k, ρ i = ρ' i)
    (H : LE_Interp env ρ m M) : LE_Interp env ρ' m M := by
  induction H generalizing k ρ' with
  | bot => exact .bot
  | sort h1 => exact .sort h1
  | bvar h1 => exact .bvar ((h _ cl).symm ▸ h1)
  | app hf ha h1 ih_f ih_a => exact .app (ih_f cl.1 h) (ih_a cl.2 h) h1
  | lam ha hdom hbody h1 ih_a ih_body =>
    refine .lam (ih_a cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | j+1, hi => exact h j (Nat.lt_of_succ_lt_succ hi)
  | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b cl.1 h) (ih_b' cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | i+1, hi => exact h i (Nat.lt_of_succ_lt_succ hi)
  | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
    refine .const h1 h2 h3 h4 (ih1 ?_ h) (h6.closed hcl) fun m e ⟨a1, a2⟩ => ?_
    · exact (hcl.constType h1).instL.mono (Nat.zero_le _)
    · exact ih2 m e a2 (a1.mono (Nat.zero_le _)) h
  | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih cl h) h5 h6

theorem closed_iff (hcl : ClosedRules env) {M : VExpr} (cl : VExpr.ClosedN M)
    {ρ ρ' : Valuation} {m : TShape} : LE_Interp env ρ m M ↔ LE_Interp env ρ' m M :=
  ⟨closed hcl cl nofun, closed hcl cl nofun⟩

theorem weak'_iff (hcl : ClosedRules env) (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp env ρ' m (M.lift' l) ↔ LE_Interp env ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ (h6.closed hcl) ?_
      · exact ih1 _ h <| (hcl.constType h1).instL.lift'_eq (by trivial)
      · rintro m A ⟨a1, a2⟩; exact ih2 _ _ a2 _ h <| a1.lift'_eq (by trivial)
    | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih _ h rfl) h5 h6
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ (h6.closed hcl) ?_
      · exact (hcl.constType h1).instL.lift'_eq (by trivial) ▸ ih1 _ h
      · rintro m A ⟨a1, a2⟩; exact a1.lift'_eq (by trivial) ▸ ih2 _ _ a2 _ h
    | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih l h) h5 h6

theorem weak_iff (hcl : ClosedRules env) :
    LE_Interp env (ρ.push x) m M.lift ↔ LE_Interp env ρ m M := by
  have e : M.lift = M.lift' (.skip .refl) := by
    simpa using (VExpr.lift'_consN_skipN (e := M) (n := 1) (k := 0)).symm
  rw [e]; exact weak'_iff hcl _ fun _ => rfl

theorem weak (hcl : ClosedRules env) (H : LE_Interp env ρ m M) :
    LE_Interp env (ρ.push x) m M.lift := (weak_iff hcl).2 H

/-- A projection's interpretation, at a deeper level. -/
theorem proj_lift {fs : List (WShape n)} {x : WShape n} {k : Nat} (hN : n ≤ N)
    (H : LE_Interp env ρ (WShape.ctor' c fs).T e) (h5 : fs[k]? = some x) (h6 : m ≤ x.T) :
    LE_Interp env ρ (WShape.ctor' c (fs.map (·.lift N))).T e ∧
      (fs.map (·.lift N))[k]? = some (x.lift N) ∧ m ≤ (x.lift N).T :=
  ⟨by rw [← WShape.lift_ctor' hN]; exact H.mono (TShape.lift_eqv (Nat.succ_le_succ hN)).1,
    by simp [h5], h6.trans (TShape.lift_eqv hN).2⟩

/-- Two interpretations of a term are compatible, and their join is one. -/
theorem compat_join (hRo : ConstRoles env) (hU : StepUniq env) (hA : AxOK)
    (hS : ∀ c, IsStruct c = true → env.IsEtaCtor c) (hE : EtaCtorUniq env) {m₁ m₂ : TShape}
    (hρ : ρ'.LE ρ) (H1 : LE_Interp env ρ' m₁ M) (H2 : LE_Interp env ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp env ρ (m₁.join m₂) M := by
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp env ρ m M) :
      m₁.Compat m₂ ∧ LE_Interp env ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : LE_Interp env ρ' m₁ M) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧ LE_Interp env ρ (m₁.join (WShape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 (h2.trans TShape.sort_eqv.2) (.sort .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | lam ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | lam ha' hdom' he' h1'
    rename_i ρ' n₁ a₁ A f₁ F m₁ n₂ a₂ f₂
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp env (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom' x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he' x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      refine mk ?_ ?_ hle'
      · exact (WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1
      · exact (WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : WShapeFun.Compat (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom' := (WShape.HasDom.lift le₂).2 hdom'
    have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h1'.trans ?_) <| .lam' ia (hdom.join cf ca_w hdom') fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
        WShape.lift_lam' le₁ ▸ WShape.lam'_le_lam'.2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
        WShape.lift_lam' le₂ ▸ WShape.lam'_le_lam'.2 jf.le.2
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
    exact (ja _).2 (WShape.Join.mk oy_c).le |>.T
  | forallE hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | forallE hb2 ha2 hdom2 he2 h12
    rename_i ρ' n₁ b₁ B b₁' f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp env (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_forallE le₁ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_forallE le₂ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | @const _ _ _ _ _ _ _ _ R₁ h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
    cases H2 with | @const _ _ _ _ _ _ _ _ R₂ a1 a2 a3 a4 a5 a6 a7 => ?_ | bot =>
      exact bot_r hρ (.const h1 h2 h3 h4 h5 h6 h7)
    cases h1.symm.trans a1
    let Rd (R : TShape → VExpr → Prop) m e := m ≤ .bot ∨ ∃ m', m ≤ m' ∧ R m' e
    have h6' := h6.mapR (R' := Rd R₁) (fun hr => Or.inr ⟨_, .rfl, hr⟩)
    have a6' := a6.mapR (R' := Rd R₂) (fun hr => Or.inr ⟨_, .rfl, hr⟩)
    have mono {R a a' A} (le : a ≤ a') : Rd R a' A → Rd R a A :=
      .imp (by exact le.trans) fun ⟨_, le', hr⟩ => by exact ⟨_, le.trans le', hr⟩
    have ⟨hc1, hj1⟩ := Const.compat_join (R₃ := LE_Interp env ρ) hRo hU hA hS hE .nil
        (h6'.lift (Nat.le_max_left ..)) (a6'.lift (Nat.le_max_right ..))
        (.inl TShape.bot_le') (.inl TShape.bot_le') .mono <| by
      rintro m₁ m₂ A (hb1 | ⟨m₁', le1, hr1⟩) (hb2 | ⟨m₂', le2, hr2⟩)
      · exact mk hb1 hb2 .bot
      · exact mk (hb1.trans TShape.bot_le') le2 (a7 m₂' A hr2)
      · exact mk le1 (hb2.trans TShape.bot_le') ((h7 m₁' A hr1).mono_l hρ)
      · have ⟨c, lej⟩ := ih2 m₁' A hr1 hρ (a7 m₂' A hr2)
        exact mk (le1.trans (TShape.Join.mk c).le.1) (le2.trans (TShape.Join.mk c).le.2) lej
    have ⟨ac, alej⟩ := ih1 hρ a5
    have ⟨b1, b2⟩ := (TShape.Join.mk hc1).le
    have ⟨b3, b4⟩ := (TShape.Join.mk ac).le
    refine have hc := .mono h3 a3 hc1; ⟨hc, ?_⟩
    refine .const h1 h2 ?_ ?_ alej hj1 fun _ _ => id
    · exact (TShape.Join.mk hc _).2 ⟨h3.trans b1, a3.trans b2⟩
    · have aty := h4.isType.join ac a4.isType
      exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)
  | @proj n1 _ _ _ _ x1 _ fs1 d t T c h1 h2 h3 h4 h5 h6 ih =>
    cases H2 with
    | bot => exact bot_r hρ (.proj h1 h2 h3 h4 h5 h6)
    | @proj n2 _ _ _ _ x2 _ fs2 _ _ _ _ a1 a2 a3 a4 a5 a6 =>
      cases h1.symm.trans a1; cases h2.symm.trans a2; cases h3.symm.trans a3
      have hN1 := Nat.le_max_left n1 n2; have hN2 := Nat.le_max_right n1 n2
      obtain ⟨b4, b5, b6⟩ := proj_lift hN2 a4 a5 a6
      obtain ⟨-, g5, g6⟩ := proj_lift hN1 h4 h5 h6
      have ⟨cc, j⟩ := ih hρ b4
      have le1 : (WShape.ctor' c.name (fs1.map (·.lift (max n1 n2)))).T ≤
          (WShape.ctor' c.name fs1).T := by
        rw [← WShape.lift_ctor' hN1]; exact (TShape.lift_eqv (Nat.succ_le_succ hN1)).1
      have cc' := WShape.Compat.T_iff.2 (TShape.Compat.mono le1 .rfl cc)
      rcases WShape.Compat.ctor'_fields cc' with hb | hb | hfs
      · have hm := g6.trans (WShape.LE.T (hb _ (List.mem_of_getElem? g5)))
        exact mk (hm.trans TShape.bot_eqv.1 |>.trans TShape.bot_le') .rfl (.proj a1 a2 a3 a4 a5 a6)
      · have hm := b6.trans (WShape.LE.T (hb _ (List.mem_of_getElem? b5)))
        exact mk .rfl (hm.trans TShape.bot_eqv.1 |>.trans TShape.bot_le')
          ((LE_Interp.proj h1 h2 h3 h4 h5 h6).mono_l hρ)
      · have hx := hfs.getElem?' g5 b5
        have jx := (WShape.Join.mk hx).le
        have jc := (TShape.Join.mk cc).le
        have J := j.mono (m := (WShape.ctor' c.name ((fs1.map (·.lift (max n1 n2))).zipWith
          WShape.join (fs2.map (·.lift (max n1 n2))))).T) (by
          rw [← WShape.ctor'_join hfs]
          exact ((WShape.Join.mk cc').T _).2 ⟨le1.trans jc.1, jc.2⟩)
        refine mk (g6.trans (WShape.LE.T jx.1)) (b6.trans (WShape.LE.T jx.2))
          (.proj h1 h2 h3 J ?_ .rfl)
        rw [List.getElem?_zipWith, g5, b5]


/-- The roles a constant the model interprets by given shapes may have: a definition, an inductive
type or a recursor, whose interpretations are what a proof by `GoodOver` gives. -/
def Role.DomOK : Role → Prop
  | .delta _ | .indTy .. | .recursor .. => True
  | _ => False

variable (env) in
/-- The model interprets by given shapes only definitions, inductive types and recursors. -/
def DomRole : Prop := ∀ {c r k}, AxInterp.dom c → ConstArity env c r k → r.DomOK

/-- What the model needs of its environment: unique roles of constants and rule names, structures
as the shapes see them, and closed rules. A well-formed environment has them
(`VEnv.WF.modelEnv`). -/
structure ModelEnv (env : VEnv) : Prop where
  roles : ConstRoles env
  domRole : DomRole env
  stepUniq : StepUniq env
  struct : ∀ c, IsStruct c = true → env.IsEtaCtor c
  structOf : ∀ c, env.IsEtaCtor c → IsStruct c = true
  etaCtor : EtaCtorUniq env
  closed : ClosedRules env
  ax : AxOK

theorem compat (hM : ModelEnv env) (H1 : LE_Interp env ρ m₁ M) (H2 : LE_Interp env ρ m₂ M) :
    m₁.Compat m₂ :=
  (compat_join hM.roles hM.stepUniq hM.ax hM.struct hM.etaCtor .rfl H1 H2).1

theorem join' (hM : ModelEnv env) (H1 : LE_Interp env ρ m₁ M) (H2 : LE_Interp env ρ m₂ M) :
    LE_Interp env ρ (m₁.join m₂) M :=
  (compat_join hM.roles hM.stepUniq hM.ax hM.struct hM.etaCtor .rfl H1 H2).2

theorem join (hM : ModelEnv env) (J : m₁.Join m₂ m) (H1 : LE_Interp env ρ m₁ M)
    (H2 : LE_Interp env ρ m₂ M) : LE_Interp env ρ m M :=
  (H1.join' hM H2).mono ((J _).2 (TShape.Join.mk (H1.compat hM H2)).le)

theorem subst (hM : ModelEnv env) : LE_Interp env ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp env ρ' m M ∧ ∀ i, LE_Interp env ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · suffices ∀ {ρ m N}, LE_Interp env ρ m N → ∀ (M : VExpr) (σ : Subst), M.subst σ = N →
        ∃ ρ', LE_Interp env ρ' m M ∧ ∀ i, LE_Interp env ρ (ρ' i) (σ i) from this H M σ rfl
    intro ρ m N H M σ eq
    have bvar {ρ : Valuation} {m N} {σ : Subst} {j} (hσj : σ j = N) (hN : LE_Interp env ρ m N) :
        ∃ ρ', LE_Interp env ρ' m (.bvar j) ∧ ∀ i, LE_Interp env ρ (ρ' i) (σ i) := by
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, .bvar (if_pos rfl ▸ .rfl), fun k => ?_⟩
      dsimp; split <;> rename_i ek
      · subst ek; exact hσj ▸ hN
      · exact .bot
    induction H generalizing M σ with
    | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | sort h1 =>
      cases M with | bvar => exact bvar eq (.sort h1) | sort => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .sort h1, fun _ => .bot⟩
    | bvar h1 => cases M with | bvar => exact bvar eq (.bvar h1) | _ => cases eq
    | app hf ha h1 ih_f ih_a =>
      cases M with | bvar => exact bvar eq (.app hf ha h1) | app F' A' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hF, h₁⟩ := ih_f F' σ rfl
      have ⟨ρ₂, hA, h₂⟩ := ih_a A' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat hM (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' hM (h₂ i)
    | @lam ρ n₁ a A f F m_orig ha hdom hbody h1 ih_a ih_body =>
      cases M with | bvar => exact bvar eq (.lam ha hdom hbody h1) | lam A' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp env ρ' a.T A' ∧ (∀ i, LE_Interp env ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp env (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', ha', hρ, H⟩ := this
        refine ⟨ρ', .lam ha' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1.T⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp env ρ' x.2.T F' ∧ ∀ i, LE_Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρA, ha', hρA⟩ := ih_a A' σ rfl
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp env ρ' x.2.T F' ∧ ∀ i, LE_Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp env ρ' a.T A' ∧ (∀ i, LE_Interp env ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp env (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with | nil => exact ⟨ρA, ha', hρA, nofun⟩ | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, ha₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp env ρ (ρ₁' i) (σ i) := (weak_iff hM.closed).1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat hM (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha₂.mono_l hj2, fun i => (hρ₁' i).join' hM (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @forallE ρ n₁ b B b' f F m_orig hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.forallE hb hb' hdom hbody h1) | forallE B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp env ρ' b.T B' ∧ LE_Interp env ρ' b'.T B' ∧
          (∀ i, LE_Interp env ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, LE_Interp env (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp env ρ' x.2.T F' ∧ ∀ i, LE_Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat hM (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp env ρ' x.2.T F' ∧ ∀ i, LE_Interp env (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp env ρ' b.T B' ∧ LE_Interp env ρ' b'.T B' ∧ (∀ i, LE_Interp env ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp env (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' hM (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp env ρ (ρ₁' i) (σ i) := (weak_iff hM.closed).1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat hM (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' hM (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        refine hy.mono_l ?_
        rw [← show ρ₁'.push (ρ₁ 0) = ρ₁ from by funext i; cases i <;> rfl]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | proj h1 h2 h3 h4 h5 h6 ih =>
      cases M with
      | bvar => exact bvar eq (.proj h1 h2 h3 h4 h5 h6) | proj s' k' E => ?_ | _ => cases eq
      cases eq
      have ⟨ρ', hE, hρ⟩ := ih E σ rfl
      exact ⟨ρ', .proj h1 h2 h3 hE h5 h6, hρ⟩
    | const h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
      cases M with
      | bvar => exact bvar eq (.const h1 h2 h3 h4 h5 h6 h7) | const => ?_ | _ => cases eq
      cases eq
      refine ⟨.nil, .const h1 h2 h3 h4 ?_ (h6.closed hM.closed) fun m e ⟨a1, a2⟩ => ?_, fun _ => .bot⟩
      · exact (closed_iff hM.closed (hM.closed.constType h1).instL).1 h5
      · exact (closed_iff hM.closed a1).1 (h7 m e a2)
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak hM.closed
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak hM.closed
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ (h6.closed hM.closed) fun _ _ ⟨a1, a2⟩ => ?_
      · exact (hM.closed.constType h1).instL.subst_eq (fun _ h => (Nat.not_lt_zero _ h).elim) ▸ ih1 h
      · exact a1.subst_eq (fun _ h => (Nat.not_lt_zero _ h).elim) ▸ ih2 _ _ a2 h
    | proj h1 h2 h3 _ h5 h6 ih => exact .proj h1 h2 h3 (ih h) h5 h6

theorem inst (hM : ModelEnv env) : LE_Interp env ρ f (F.inst A) ↔
    ∃ a, LE_Interp env (ρ.push a) f F ∧ LE_Interp env ρ a A := by
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · rw [VExpr.inst_eq] at H
    have ⟨ρ', hF, hσ⟩ := (LE_Interp.subst hM).1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · rw [VExpr.inst_eq]
    exact (LE_Interp.subst hM (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem forallE_inv (hM : ModelEnv env) {b} {f : WShapeFun n} {B F}
    (H : LE_Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp env ρ b.T B ∧ ∀ {{X x}}, LE_Interp env ρ x.T X → LE_Interp env ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine (inst hM).2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem forallE_inv' (hM : ModelEnv env) {b} {f : WShapeFun n} {B F}
    (H : LE_Interp env ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp env ρ b.T B ∧ ∀ x, LE_Interp env (ρ.push x.T) (f.app x).T F := by
  refine ⟨(H.forallE_inv hM).1, fun x => ?_⟩
  have := ((LE_Interp.weak (x := x.T) hM.closed H).forallE_inv hM).2 .bvar0
  rwa [VExpr.inst_liftN_bvar] at this

theorem lam_inv (hM : ModelEnv env) {f : WShapeFun n} {B F}
    (H : LE_Interp env ρ (WShape.T (n := n+1) (.lam' f)) (.lam B F))
    {{X x}} (hx : LE_Interp env ρ x.T X) : LE_Interp env ρ (f.app x).T (F.inst X) := by
  unfold WShape.lam' at H; split at H <;> rename_i hn; rotate_left
  · by_cases hl : f.app x ≤ .bot; · exact .mono hl.T .bot
    have ⟨_, _, h⟩ := f.app_eq x; exact absurd ⟨_, h, hl⟩ hn
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') := by
    rw [WShape.lam_eq_lam' (hl := hn)] at le; exact le.lam'_decomp
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    rw [WShape.LE.def, WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  refine (inst hM).2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiF x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans ((TShape.LE.def le₂ le₁).2 le2_w)⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono (?_ : (f.app x).T ≤ (f₁.app x₁w).T)
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    show ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem lam_inv' (hM : ModelEnv env) {f : WShapeFun n} {hl : f.NonZero} {B F}
    (H : LE_Interp env ρ (WShape.T (n := n+1) (WShape.lam f hl)) (.lam B F)) (x : WShape n) :
    LE_Interp env (ρ.push x.T) (f.app x).T F := by
  have := (WShape.lam_eq_lam' ▸ LE_Interp.weak (x := x.T) hM.closed H).lam_inv hM .bvar0
  rwa [VExpr.inst_liftN_bvar] at this


variable (env) in
inductive Valuation.Fits : (Γ Δ : List VExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {a}, LE_Interp env ρ a A → ∃ a', a ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType .type) →
    LE_Interp env ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

variable (env) in
def InterpTyped (ρ : Valuation) (m : TShape) (M A : VExpr) :=
  ∃ m' a, m ≤ m' ∧ LE_Interp env ρ m' M ∧ LE_Interp env ρ a A ∧ m'.HasType a

theorem InterpTyped.bot : InterpTyped env ρ (WShape.T (n := n) .bot) M A := by
  refine ⟨WShape.T (n := n) .bot, WShape.T (n := n) .bot, TShape.bot_le', .bot, .bot, ?_⟩
  exact WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort

theorem InterpTyped.mk (le : m ≤ m') (h_m : LE_Interp env ρ m' M) (h_a : LE_Interp env ρ a A)
    (h_type : m'.HasType a) : InterpTyped env ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.out (H : InterpTyped env ρ m M A) :
    ∃ n', ∃ m' : WShape n', ∃ a : WShape n', m.1 ≤ n' ∧ m ≤ m'.T ∧
      LE_Interp env ρ m'.T M ∧ LE_Interp env ρ a.T A ∧ m'.HasType a := by
  obtain ⟨m', a, hle, hm, ha, hty⟩ := H
  let k := max m.1 (max m'.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  refine ⟨k, m'.2.lift k, a.2.lift k, hk.1, ?_, hm.lift hk.2.1, ha.lift hk.2.2, ?_⟩
  · exact hle.trans (TShape.lift_eqv hk.2.1).2
  · exact (TShape.HasType.def hk.2.1 hk.2.2).1 hty

theorem InterpTyped.hsort' {ρ A U}
    (H : ∀ {a}, LE_Interp env ρ a A → InterpTyped env ρ a A (.sort U))
    {a} (h : LE_Interp env ρ a A) :
    ∃ a', a ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType (.sort (levelRel U)) :=
  have ⟨_, _, h1, h2, h3, h4⟩ := H h; ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩

theorem InterpTyped.hsort {ρ A U}
    (H : ∀ {a}, LE_Interp env ρ a A → InterpTyped env ρ a A (.sort U))
    {a} (h : LE_Interp env ρ a A) : ∃ a', a ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType .type :=
  have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, h3.toType⟩

theorem sound_bot :
    (LE_Interp env ρ (WShape.T (n := n) .bot) M ↔ LE_Interp env ρ (WShape.T (n := n) .bot) N) ∧
    (LE_Interp env ρ (WShape.T (n := n) .bot) M → InterpTyped env ρ (WShape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

theorem sound_app (hM : ModelEnv env)
    (H1 : ∀ {m}, LE_Interp env ρ m F → InterpTyped env ρ m F (.forallE A B))
    (H2 : ∀ {b}, LE_Interp env ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ LE_Interp env ρ b' (B.inst X) ∧ b'.HasType .type)
    (h1 : LE_Interp env ρ m (F.app X)) : InterpTyped env ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    rw [show f_shape = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := LE_Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  rw [WShape.lift_forallE hk.2.1] at a3'
  have h_Binst := a3'.forallE_inv hM |>.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  have c1_f := (WShape.HasTypeLam.iff.1 c1).2.2
  have ⟨_, e1, e2, e3⟩ := c1_d (a_sh.lift k)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans <| TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    rw [WShape.lift_lam' hk.1.1, WShape.lam'_app]
    refine g2.mono_r ((WShapeFun.app_mono_l b6 _).trans (WShapeFun.app_mono_r e1) |>.T.trans le') ?_
    exact (WShape.HasTypeLam.iff.1 c1).2.2 _ e2 |>.mono_l (WShapeFun.app_mono_r e1) e3 |>.T

theorem sound_lam (hM : ModelEnv env)
    (H1 : ∀ {m}, LE_Interp env ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {a x}, LE_Interp env ρ a A → x.HasType a →
      ∀ {e}, LE_Interp env (ρ.push x) e F → InterpTyped env (ρ.push x) e F B)
    (h1 : LE_Interp env ρ m (A.lam F)) : InterpTyped env ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam _ n a _ f _ _ h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp env (ρ.push p.1.T) p.2.T F) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (a.lift k) ∧ WShape.HasDom b (a.lift k) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp env (ρ.push x.T) (f'.app x).T F) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp env (ρ.push x.T) (b.app x).T B) ∧
        (∀ x, x.HasType (a.lift k) → (f'.app x).HasType (b.app x)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h2 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h3 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ := H _ (Nat.le_refl _)
    have h1' := h1.lift le
    refine ⟨_, _, ?_, .lam' h1' hd1 hi1, .forallE' h1' h1' hd2 hi2, ?_⟩
    · refine h4.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le)).2 (WShape.lift_lam' le ▸ ?_)
      refine WShape.lam'_le_lam'.2 <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 (hsingle _ (WShapeFun.mem_elems.2 h₀))
    · exact WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
        ⟨WShape.HasTypePi.iff.2 ⟨hd2, fun x h => (hi3 x h).isType⟩, hd1, hi3⟩
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    have ha : (a.lift k).HasType .type :=
      WShape.lift_type.symm ▸ (WShape.HasType.lift hk).2 h2.isType
    refine ⟨.bot, .bot, nofun, .bot ha, .bot ha, fun x h => ?_, fun x h => ?_, fun x h => ?_⟩
    · exact WShapeFun.bot_app ▸ .bot
    · exact WShapeFun.bot_app ▸ .bot
    · simp [WShapeFun.bot_app]; exact .bot' (.bot' .sort)
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h2 p.1
    have ⟨e', b', le_e, he', hb', heb'⟩ := H2 h1 (WShape.HasType.T hx') (h3 x' hx')
    let m' := max e'.1 b'.1; have ⟨lf, lb⟩ := Nat.max_le.1 (Nat.le_refl m')
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk : n ≤ k := Nat.le_trans le1 le₁
    have le_ek := Nat.le_trans lf le₂; have le_bk := Nat.le_trans lb le₂
    have ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁, hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (e'.2.lift k)
    let sb := WShapeFun.single (x'.lift k) (b'.2.lift k)
    have hi1_any z : LE_Interp env (ρ.push z.T) (f₁.app z).T F :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have hi2_any z : LE_Interp env (ρ.push z.T) (b₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd2₁ z
      (hi2₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have he'_at_x' : LE_Interp env (ρ.push (x'.lift k).T) (e'.2.lift k).T F :=
      (he'.lift le_ek).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hb'_at_x' : LE_Interp env (ρ.push (x'.lift k).T) (b'.2.lift k).T B :=
      (hb'.lift le_bk).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = e'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat hM (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have hcb : b₁.Compat sb := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sb_app : sb.app z = b'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sb_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi2_any z).compat hM (sb_app ▸ hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    have jb := WShapeFun.Join.mk hcb
    refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join hM (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine LE_Interp.join hM (jb.app_l x).T (hi2_any x) (WShapeFun.single_app ▸ ?_); split
      · exact hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · have hT1 := hi3₁ x hx
      have hT2 : (sf.app x).HasType (sb.app x) := by
        rw [WShapeFun.single_app, WShapeFun.single_app]; split
        · exact (TShape.HasType.def le_ek le_bk).1 heb'
        · exact .bot' (.bot' .sort)
      have jb_x := jb.app_l x
      have := hT1.isType.join' jb_x hT2.isType
      exact (this.mono_r jb_x.le.1 hT1).join' (jf.app_l x) (this.mono_r jb_x.le.2 hT2)

theorem sound_forallE (hM : ModelEnv env)
    (H1 : ∀ {m}, LE_Interp env ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp env ρ a' A ∧ a'.HasType (.sort (levelRel u)))
    (H2 : ∀ {a x}, LE_Interp env ρ a A → x.HasType a →
      ∀ {e}, LE_Interp env (ρ.push x) e B → InterpTyped env (ρ.push x) e B (.sort v))
    (h1 : LE_Interp env ρ m (A.forallE B)) :
    InterpTyped env ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp env (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → LE_Interp env (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort (levelRel v))) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat hM h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hM hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).forallE (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_forallE (Nat.le_trans le le₂)]
      refine WShape.forallE_le_forallE.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .forallE' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort, levelRel_imax]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .forallE <| WShape.HasTypePi.iff.2 ⟨b2'.mono_r ?_ this, fun x hx => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      have ⟨x', _, dmem⟩ := (f'.lift k).app_eq x
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      refine eq ▸ WShape.lift_sort.symm ▸ (WShape.HasType.lift le₂).2 (.mono_l e2 e3 ?_)
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      exact (hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 h3.isType
    · simp [WShapeFun.bot_app]; exact .bot' .sort
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort (levelRel v)) := .mono_r hb'.le_sort .sort heb'
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : LE_Interp env (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : LE_Interp env (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat hM (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join hM (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort


omit [ShapeEnv] [AxInterp] in
/-- A well-formed environment is one the model can interpret, with its own structures. -/
theorem _root_.Lean4Lean.VEnv.WF.modelEnv {env : VEnv} (henv : env.WF)
    {ax : @AxInterp env.shapeEnv} (hA : @AxOK env.shapeEnv ax)
    (hD : @DomRole env.shapeEnv ax env) :
    @ModelEnv env.shapeEnv ax env :=
  letI := env.shapeEnv
  { ax := hA
    domRole := hD
    roles := henv.constRoles
    stepUniq := henv.stepUniq
    struct := fun _ h => (env.shapeEnv_isStruct).1 h
    structOf := fun _ h => (env.shapeEnv_isStruct).2 h
    etaCtor := henv.etaCtorUniq
    closed := ClosedRules.of_ordered henv.ordered henv.stepUniq fun {s d t T c} hs hT hc => by
      obtain ⟨_, envT, hwf₀, hd, hT₁, -⟩ := henv.inducts hs
      have hwfT : envT.WF := VEnv.WF.addConstList hwf₀ (fun p hp => by
        simp only [VInductDecl.typeConsts, List.mem_map] at hp
        obtain ⟨T, hT, rfl⟩ := hp
        exact (hd.types T hT).1) hT₁
      obtain ⟨_, h⟩ := ((hd.ctors envT hT₁ T (List.mem_append_left _ (List.mem_of_getElem? hT))).2
        c hc).type
      exact h.closedN hwfT.ordered trivial }

end LE_Interp
