import Lean4Lean.Theory.Typing.LogRel.IndVal

/-!
# The logical relation at a successor depth

Upstream's `LRS` (`Experimental/ShapeLogRel.lean`), over `VExpr` and this theory's reduction:

* equalities of types are chains (`TyEq`), and the arguments of related inductive type
  applications are related by chains of equalities (`TmEq`), since composing two equalities at
  different sorts needs uniqueness of typing;
* a type that reduces to a pi type, or to an application of an inductive type former, is related
  only to one that does too; two types that reduce to neutral normal forms are related to each
  other (`NeRed`), as a stuck term can have a pi or inductive type shape in the model;
* a function at a type that reduces to a neutral normal form carries no information.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem forallE_whnf : WHNF env U Γ (.forallE A B) := fun _ h => nomatch h

/-- A family of types at equal arguments is equal, by beta through its lambda. -/
theorem instDF_ty (hA₁ : env.HasType U Γ A₁ (.sort u)) (hA₂ : env.HasType U (A₁::Γ) A₂ (.sort v))
    (ha : env.IsDefEq U Γ a b A₁) : env.IsDefEq U Γ (A₂.inst a) (A₂.inst b) (.sort v) :=
  (VEnv.IsDefEq.beta hA₂ ha.hasType.1).symm.trans <|
    .trans (.appDF (.lamDF hA₁ hA₂) ha) (.beta hA₂ ha.hasType.2)

namespace NeRed
variable (hU : StepUniq env)
include hU

theorem not_forallE (H : NeRed env U Γ M) (h : StepS env U Γ M (.forallE A B)) : False := by
  obtain ⟨M', h1, h2, h3⟩ := H
  cases StepS.determ hU h1 h2 h forallE_whnf
  nomatch h3

theorem not_inert (hn : Inert env n) (H : NeRed env U Γ M)
    (h : StepS env U Γ M ((VExpr.const n ls).appN As)) : False := by
  obtain ⟨M', h1, h2, h3⟩ := H
  cases StepS.determ hU h1 h2 h hn.whnf
  exact hn.not_neutral h3

end NeRed

namespace IndRel

theorem not_neRed (hU : StepUniq env) (H : IndRel env U Γ h M N) : ¬NeRed env U Γ M :=
  fun h' => let ⟨hn, _, _, _, _, h1, _⟩ := H; NeRed.not_inert hU hn h' h1

end IndRel

variable [ShapeEnv]

section
variable (IH : LogRel env U Γ n)

/-- Pi edge validity: related arguments give related codomains. -/
def LRS.PiDefEq (B F₁ F₂ : VExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → env.IsDefEq U Γ a b' B → IH.DefEq a b' B p b →
    IH.TyDefEq (F₁.inst a) (F₁.inst b') (f.app p) ∧
    IH.TyDefEq (F₂.inst a) (F₂.inst b') (f.app p)) ∧
  ∀ {{a p}}, p.HasType b → env.HasType U Γ a B → IH.DefEq a a B p b →
    IH.TyDefEq (F₁.inst a) (F₂.inst a) (f.app p)

/-- Two types that reduce to related pi types. -/
def LRS.ValTyPi2 (M₁ M₂ : VExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂,
    StepS env U Γ M₁ (.forallE B₁ F₁) ∧ StepS env U Γ M₂ (.forallE B₂ F₂) ∧
    TyEq env U Γ B₁ B₂ ∧ TyEq env U (B₁::Γ) F₁ F₂ ∧ IH.TyDefEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

/-- Two functions whose applications to related arguments are related. -/
def LRS.LamDefEq (M N A₁ A₂ : VExpr) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) :
    Prop :=
  (∀ {{a b p}}, WShape.HasType p a₁ → env.IsDefEq U Γ a b A₁ → IH.DefEq a b A₁ p a₁ →
    IH.DefEq (M.app a) (M.app b) (A₂.inst a) (m.app p) (a₂.app p) ∧
    IH.DefEq (N.app a) (N.app b) (A₂.inst a) (m.app p) (a₂.app p)) ∧
  (∀ {{a p}}, WShape.HasType p a₁ → env.HasType U Γ a A₁ → IH.DefEq a a A₁ p a₁ →
    IH.DefEq (M.app a) (N.app a) (A₂.inst a) (m.app p) (a₂.app p))

/-- Functions at a type that reduces to a pi type. -/
def LRS.LamClause (M N A : VExpr) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) :
    Prop :=
  ∃ A₁ A₂ u v, StepS env U Γ A (.forallE A₁ A₂) ∧ TyEq env U Γ A (.forallE A₁ A₂) ∧
    env.HasType U Γ A₁ (.sort u) ∧ IH.TyDefEq A₁ A₁ a₁ ∧ env.HasType U (A₁::Γ) A₂ (.sort v) ∧
    LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧ LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂

end


section
variable (IH : LogRel env U Γ n)

theorem _root_.Lean4Lean.LogRel.Shape.WF.indTy_mem {l : List (Shape n)}
    (h : Shape.WF (n := n+1) (.indTy r c l)) : ∀ x ∈ l, x.WF := h

/-- Type validity at shape `m`: sorts at equivalent levels, related pi types, applications of
the same type former, or two stuck types. -/
def LRS.TyDefEq (M N : VExpr) : WShape (n+1) → Prop
  | ⟨.bot, _⟩ | ⟨.lam _, _⟩ | ⟨.ctor _ _, _⟩ => True
  | ⟨.sort _, _⟩ => SortRel env U Γ M N
  | ⟨.forallE b f, wf⟩ =>
    LRS.ValTyPi2 IH M N ⟨b, wf.1⟩ ⟨f, wf.2⟩ ∨ (NeRed env U Γ M ∧ NeRed env U Γ N)
  | ⟨.indTy _ h l, wf⟩ =>
    (IndRel env U Γ h M N ∧ IndTele IH h (l.pmap Subtype.mk wf.indTy_mem) M N) ∨
    (NeRed env U Γ M ∧ NeRed env U Γ N)

section
variable (env : VEnv) (U : Nat) (Γ : List VExpr)

/-- Terms `ms` and `ns` typed equal along the telescope `T`, instantiated with `ms`. -/
def ProjsTyped : VExpr → List VExpr → List VExpr → Prop
  | _, [], [] => True
  | T, m :: ms, n :: ns => ∃ D B, StepS env U Γ T (.forallE D B) ∧ env.IsDefEq U Γ m n D ∧
    ProjsTyped (B.inst m) ms ns
  | _, _, _ => False

/-- The projections of a structure's stuck values are typed along its constructor's telescope. -/
def StructTy (h : IndHead) (M : VExpr) : Prop :=
  ∀ c i k, IsStruct c = true → h.ctors.idxOf? c = some i → h.arities[i]? = some k →
    ∃ ci, env.constants c = some ci ∧ ∀ lsA AsA,
    StepS env U Γ M ((VExpr.const h.name lsA).appN AsA) →
    WHNF env U Γ ((VExpr.const h.name lsA).appN AsA) →
    ∀ M' N', WHNF env U Γ M' → Neutral env M' → WHNF env U Γ N' → Neutral env N' →
      env.IsDefEq U Γ M' N' M →
      ProjsTyped env U Γ (ctorTeleAt ci k lsA AsA) (VExpr.projs h.name k M')
        (VExpr.projs h.name k N')

end

/-- What the relation knows of the typing of a type `M` at shape `m`, given that `M`'s own type is
a sort: a pi type reduces, typed, to a pi type whose domain and codomains at related arguments
satisfy the same one depth down; a structure's stuck values have typed projections. -/
def LRS.TyTyped (M : VExpr) : WShape (n+1) → Prop
  | ⟨.forallE b f, wf⟩ => NeRed env U Γ M ∨ ∃ A₁ A₂ u v,
    StepS env U Γ M (.forallE A₁ A₂) ∧ TyEq env U Γ M (.forallE A₁ A₂) ∧
    env.HasType U Γ A₁ (.sort u) ∧ env.HasType U (A₁::Γ) A₂ (.sort v) ∧ IH.TyTy A₁ ⟨b, wf.1⟩ ∧
    ∀ x p, p.HasType ⟨b, wf.1⟩ → env.HasType U Γ x A₁ → IH.DefEq x x A₁ p ⟨b, wf.1⟩ →
      IH.TyTy (A₂.inst x) (WShapeFun.app ⟨f, wf.2⟩ p)
  | ⟨.indTy _ h _, _⟩ => NeRed env U Γ M ∨ StructTy env U Γ h M
  | _ => True

/-- Values of an inductive type at a constructor shape: for a structure, their projections are
related (structure eta); otherwise both reduce to the constructor with related fields, or both
are stuck. Anything is related at a stuck type. -/
def LRS.IndVal (A M N : VExpr) (h : IndHead) (l : List (WShape n)) (c : Name)
    (fs : List (WShape n)) : Prop :=
  (if IsStruct c then StructVal IH h l A M N c fs else CtorVal IH h l A M N c fs) ∨
    NeRed env U Γ A ∨ (IsStruct c = false ∧ TNeRed env U Γ M A ∧ TNeRed env U Γ N A)

/-- Term validity at value shape `m` and type shape `a`. -/
def LRS.DefEq (M N A : VExpr) (m a : WShape (n+1)) : Prop :=
  match ha : a.1 with
  | .bot => True
  | .sort _ => LRS.TyDefEq IH M N m ∧
    ∀ u, TyEq env U Γ A (.sort u) → LRS.TyTyped IH M m ∧ LRS.TyTyped IH N m
  | .forallE a₁ a₂ =>
    have wfa1 := (ha ▸ a.2).1; have wfa2 := (ha ▸ a.2).2
    match hm : m.1 with
    | .bot => True
    | .lam mg =>
      LRS.LamClause IH M N A ⟨mg, (hm ▸ m.2).1⟩ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩ ∨ NeRed env U Γ A
    | _ => False
  | .indTy _ h l =>
    match hm : m.1 with
    | .ctor c fs => LRS.IndVal IH A M N h
        (l.pmap Subtype.mk fun x hx => by have := a.2; rw [ha] at this; exact this x hx)
        c (fs.pmap Subtype.mk fun x hx => by have := m.2; rw [hm] at this; exact this.1 x hx)
    | _ => True
  | _ => False

end

variable {IH : LogRel env U Γ n}

@[simp] theorem LRS.TyDefEq.bot : LRS.TyDefEq IH M N .bot := trivial
@[simp] theorem LRS.TyDefEq.sort_iff : LRS.TyDefEq IH M N (.sort r) ↔ SortRel env U Γ M N := .rfl
@[simp] theorem LRS.TyDefEq.forallE_iff : LRS.TyDefEq IH M N (.forallE b f) ↔
    LRS.ValTyPi2 IH M N b f ∨ (NeRed env U Γ M ∧ NeRed env U Γ N) := .rfl
theorem WShape.pmap_map_val :
    ∀ (l : List (WShape n)) (h : ∀ x ∈ l.map (·.1), Shape.WF x), (l.map (·.1)).pmap Subtype.mk h = l
  | [], _ => rfl
  | _ :: l, h => by simp only [List.map_cons, List.pmap_cons]; rw [WShape.pmap_map_val l]; rfl

@[simp] theorem LRS.TyDefEq.indTy_iff : LRS.TyDefEq IH M N (.indTy r h l) ↔
    (IndRel env U Γ h M N ∧ IndTele IH h l M N) ∨ (NeRed env U Γ M ∧ NeRed env U Γ N) := by
  show (IndRel env U Γ h M N ∧ IndTele IH h ((l.map (·.1)).pmap Subtype.mk _) M N) ∨ _ ↔ _
  rw [WShape.pmap_map_val]
@[simp] theorem LRS.TyDefEq.lam_m : LRS.TyDefEq IH M N (.lam f hf) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.ctor_m {c l h} : LRS.TyDefEq (n := n) IH M N (.ctor c l h) ↔ True :=
  .rfl
@[simp] theorem LRS.TyDefEq.lam' : LRS.TyDefEq IH M N (.lam' f) := by
  unfold WShape.lam'; split <;> trivial
@[simp] theorem LRS.TyDefEq.ctor' : LRS.TyDefEq IH M N (.ctor' c l) := by
  unfold WShape.ctor'; split <;> trivial

@[simp] theorem LRS.TyTyped.bot : LRS.TyTyped IH M .bot := trivial
@[simp] theorem LRS.TyTyped.sort : LRS.TyTyped IH M (.sort r) := trivial
@[simp] theorem LRS.TyTyped.lam_m : LRS.TyTyped IH M (.lam f hf) := trivial
@[simp] theorem LRS.TyTyped.ctor_m {c l h} : LRS.TyTyped (n := n) IH M (.ctor c l h) := trivial
theorem LRS.TyTyped.forallE_iff : LRS.TyTyped IH M (.forallE b f) ↔ NeRed env U Γ M ∨
    ∃ A₁ A₂ u v, StepS env U Γ M (.forallE A₁ A₂) ∧ TyEq env U Γ M (.forallE A₁ A₂) ∧
    env.HasType U Γ A₁ (.sort u) ∧ env.HasType U (A₁::Γ) A₂ (.sort v) ∧ IH.TyTy A₁ b ∧
    ∀ x p, p.HasType b → env.HasType U Γ x A₁ → IH.DefEq x x A₁ p b →
      IH.TyTy (A₂.inst x) (f.app p) := .rfl
theorem LRS.TyTyped.indTy_iff : LRS.TyTyped IH M (.indTy r h l) ↔
    NeRed env U Γ M ∨ StructTy env U Γ h M := .rfl

theorem LRS.PiDefEq.left :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f := fun ⟨h1, _⟩ =>
  ⟨fun _ _ _ hp ha a1 => ⟨(h1 hp ha a1).1, (h1 hp ha a1).1⟩, fun _ _ hp ha a1 => (h1 hp ha a1).1⟩

theorem IndTele.left' (hU : StepUniq env) (hR : IndRel env U Γ h M N)
    (H : IndTele IH h l M N) : IndTele IH h l M M :=
  let ⟨_, _, _, _, _, _, r2, _⟩ := hR; H.trans hU ⟨_, _, r2⟩ H.symm

theorem LRS.TyDefEq.left (hU : StepUniq env) :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH M M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · exact SortRel.left
  · rintro (⟨B₁, F₁, _, _, rM, _, hB, hF, hValB, hE⟩ | ⟨h, -⟩)
    · obtain ⟨_, hB₁⟩ := hB.isType_l; obtain ⟨_, hF₁⟩ := hF.isType_l
      exact .inl ⟨B₁, F₁, B₁, F₁, rM, rM, .refl hB₁, .refl hF₁, IH.left_ty hValB, hE.left⟩
    · exact .inr ⟨h, h⟩
  · rintro (⟨h, hT⟩ | ⟨h, -⟩)
    · exact .inl ⟨h.left, hT.left' hU h⟩
    · exact .inr ⟨h, h⟩

theorem LRS.TyDefEq.symm (henv : env.Ordered) : LRS.TyDefEq IH M N m → LRS.TyDefEq IH N M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · exact SortRel.symm
  · rintro (⟨_, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩ | ⟨h1, h2⟩)
    · have hValB' := IH.symm_ty hValB
      refine .inl ⟨_, _, _, _, rN, rM, hB.symm, (TyEq.ctx henv hB hF).symm, hValB',
        fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
      · exact (hE1 hp (hB.symm.defeqDF ha) (IH.conv hB.symm hValB' a1)).symm
      · exact IH.symm_ty (hE2 hp (hB.symm.defeqDF ha) (IH.conv hB.symm hValB' a1))
    · exact .inr ⟨h2, h1⟩
  · rintro (⟨h, hT⟩ | ⟨h1, h2⟩)
    · exact .inl ⟨h.symm, hT.symm⟩
    · exact .inr ⟨h2, h1⟩

theorem LRS.TyDefEq.trans (henv : env.Ordered) (hU : StepUniq env) :
    LRS.TyDefEq IH M₁ M₂ m → LRS.TyDefEq IH M₂ M₃ m → LRS.TyDefEq IH M₁ M₃ m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · exact SortRel.trans hU
  · rintro (⟨B₁, F₁, B₂, F₂, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩ | ⟨h1, h2⟩)
      (⟨_, _, B₃, F₃, rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩ | ⟨h2', h3⟩)
    · cases StepS.determ hU rM₂ forallE_whnf rM₂' forallE_whnf
      refine .inl ⟨_, _, _, _, rM₁, rM₃, hB₁₂.trans hB₂₃, hF₁₂.trans (TyEq.ctx henv hB₁₂.symm hF₂₃),
        IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
      · exact ⟨(hE1.1 hp ha a1).1, (hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hB₁₂ hValB₁₂ a1)).2⟩
      · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hB₁₂ hValB₁₂ a1))
    · exact (h2'.not_forallE hU rM₂).elim
    · exact (h2.not_forallE hU rM₂').elim
    · exact .inr ⟨h1, h3⟩
  · rintro (⟨h, hT⟩ | ⟨h1, h2⟩) (⟨h', hT'⟩ | ⟨h2', h3⟩)
    · have ⟨_, _, _, _, _, _, r2, _⟩ := h
      exact .inl ⟨h.trans hU h', hT.trans hU ⟨_, _, r2⟩ hT'⟩
    · exact (h.symm.not_neRed hU h2').elim
    · exact (h'.not_neRed hU h2).elim
    · exact .inr ⟨h1, h3⟩

theorem LRS.TyDefEq.whr (hU : StepUniq env) (hA : StepS env U Γ A A') (hB : StepS env U Γ B B') :
    LRS.TyDefEq IH A B m ↔ LRS.TyDefEq IH A' B' m := by
  dsimp [LRS.TyDefEq]; split <;> try exact .rfl
  · exact SortRel.whr hU hA hB
  · refine or_congr ⟨?_, ?_⟩ (and_congr (NeRed.whr hU hA) (NeRed.whr hU hB))
    · rintro ⟨B₁, F₁, B₂, F₂, rM, rN, rest⟩
      exact ⟨B₁, F₁, B₂, F₂, StepS.determ_l hU hA rM forallE_whnf,
        StepS.determ_l hU hB rN forallE_whnf, rest⟩
    · rintro ⟨B₁, F₁, B₂, F₂, rM, rN, rest⟩
      exact ⟨B₁, F₁, B₂, F₂, hA.trans rM, hB.trans rN, rest⟩
  · refine or_congr ⟨fun ⟨h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ?_⟩
      (and_congr (NeRed.whr hU hA) (NeRed.whr hU hB))
    · exact ⟨(IndRel.whr hU hA hB).1 h1, (IndTele.whr hU h1.1 hA hB).1 h2⟩
    · exact ⟨(IndRel.whr hU hA hB).2 h1, (IndTele.whr hU h1.1 hA hB).2 h2⟩

/-! ### Functions and pi edges -/

theorem LRS.LamDefEq.left :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LRS.LamDefEq.whr (hA₁ : env.HasType U Γ A₁ (.sort u))
    (hA₂ : env.HasType U (A₁::Γ) A₂ (.sort v))
    (hM : TRed env U Γ M M' (.forallE A₁ A₂)) (hN : TRed env U Γ N N' (.forallE A₁ A₂)) :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  have r2 {M M' a b} (hM : TRed env U Γ M M' (.forallE A₁ A₂)) (ha : env.IsDefEq U Γ a b A₁) :
      TRed env U Γ (M.app b) (M'.app b) (A₂.inst a) :=
    (hM.app ha.hasType.2).defeqDF (instDF_ty hA₁ hA₂ ha).symm
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (hM.app ha.hasType.1) (r2 hM ha)).1 d1,
      (IH.whr (hN.app ha.hasType.1) (r2 hN ha)).1 d2⟩
  · exact (IH.whr (hM.app ha) (hN.app ha)).1 (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (hM.app ha.hasType.1) (r2 hM ha)).2 d1,
      (IH.whr (hN.app ha.hasType.1) (r2 hN ha)).2 d2⟩
  · exact (IH.whr (hM.app ha) (hN.app ha)).2 (pae hp ha a1)

theorem LRS.LamDefEq.mono_r_1
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  have hm_d := WShape.HasDom.iff.1 hm.2.1
  have hm_f := WShape.HasTypeLam.iff.1 hm |>.2.2
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm_d x
    have hax' := hx.isType.mono_r le₁ hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm_f x' hax
    have hg_p := hg_x.mono_l (WShapeFun.app_mono_r le') h1
    have le_cod := (WShapeFun.app_mono_r le').trans (WShapeFun.app_mono_l le₂ _)
    have ht_cod := (WShape.HasTypePi.iff.1 hm'.1).2 x hx
    have hm_target := ht_cod.mono_r le_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).1
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

theorem LRS.PiDefEq.mono_r_2
    (le₁ : b ≤ b') (le₂ : f ≤ f')
    (htpi : WShape.HasTypePi f b r) (htpi' : WShape.HasTypePi f' b' r')
    (hValA₁ : IH.TyDefEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    have htpi_w := WShape.HasTypePi.iff.1 htpi
    have htpi'_w := WShape.HasTypePi.iff.1 htpi'
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi_w.2 _ hp).toType; have hm_src := (htpi'_w.2 _ hp').toType
    · let ⟨t1, t2⟩ := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t1,
             IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src t2⟩
    · exact IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyDefEq A₁ A₁ a₁') (htpi' : WShape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have htpi'_w := WShape.HasTypePi.iff.1 htpi'
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm_w.2.2 _ hp
    have ht_src := (htpi'_w.2 _ hp').toType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (WShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

theorem LRS.LamDefEq.mono_l
    (le : m ≤ m') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have hm'_w := WShape.HasTypeLam.iff.1 hm'
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm_w.2.2 _ hp
    have hm_src := hm'_w.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src q

theorem LRS.PiDefEq.join
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type)
    (hC_b : b₁.Compat b₂)
    (ht₁ : WShape.HasTypePi f₁ b₁ r₁) (ht₂ : WShape.HasTypePi f₂ b₂ r₂)
    (hC_f : WShapeFun.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (f₁.join f₂) := by
  have hJ_b := WShape.Join.mk hC_b
  have htB_join := htB₁.join hC_b htB₂
  have hJ_f := WShapeFun.Join.mk hC_f
  have ht₁_w := WShape.HasTypePi.iff.1 ht₁
  have ht₂_w := WShape.HasTypePi.iff.1 ht₂
  have hd₁ := WShape.HasDom.iff.1 ht₁.1
  have hd₂ := WShape.HasDom.iff.1 ht₂.1
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨d_x, d_le, d_ht, d_app⟩ := hd₁ p
    have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
      (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp a1)
    obtain ⟨e_x, e_le, e_ht, e_app⟩ := hd₂ p
    have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
      (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp a1)
    have ht_f1 : (f₁.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₁.app_eq p; (ht₁.2 _ _ hm).toType
    have ht_f2 : (f₂.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₂.app_eq p; (ht₂.2 _ _ hm).toType
    have hJ_fp := hJ_f.app_l p
    have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join' hJ_fp ht_f2
    have ht_fJ' := ht_f1.join hC_fp ht_f2
    have cvt_d {A B} (h : IH.TyDefEq A B (f₁.app d_x)) : IH.TyDefEq A B (f₁.app p) :=
      IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toType h
    have cvt_e {A B} (h : IH.TyDefEq A B (f₂.app e_x)) : IH.TyDefEq A B (f₂.app p) :=
      IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toType h
  · constructor
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).1) (cvt_e (hE₂.1 e_ht ha c3).1)
    · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d (hE₁.1 d_ht ha c2).2) (cvt_e (hE₂.1 e_ht ha c3).2)
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (cvt_d (hE₁.2 d_ht ha c2)) (cvt_e (hE₂.2 e_ht ha c3))

/-! ### Term validity -/

@[simp] theorem LRS.DefEq.bot_a : LRS.DefEq IH M N A m .bot = True := rfl
@[simp] theorem LRS.DefEq.sort_a : LRS.DefEq IH M N A m (.sort r) = (LRS.TyDefEq IH M N m ∧
    ∀ u, TyEq env U Γ A (.sort u) → LRS.TyTyped IH M m ∧ LRS.TyTyped IH N m) := rfl
@[simp] theorem LRS.DefEq.bot_m : LRS.DefEq IH M N A .bot (.forallE a₁ a₂) = True := rfl
@[simp] theorem LRS.DefEq.lam_forallE (IH : LogRel env U Γ n) :
    LRS.DefEq IH M N A (.lam f hf) (.forallE a₁ a₂) ↔
    LRS.LamClause IH M N A f a₁ a₂ ∨ NeRed env U Γ A := .rfl
@[simp] theorem LRS.DefEq.sort_forallE :
    LRS.DefEq IH M N A (.sort r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.forallE_forallE :
    LRS.DefEq IH M N A (.forallE b g) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_forallE :
    LRS.DefEq IH M N A (.ctor c l h) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.indTy_forallE :
    LRS.DefEq IH M N A (.indTy r c l) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.lam_a : LRS.DefEq IH M N A m (.lam f hf) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_a {c l h} :
    LRS.DefEq (n := n) IH M N A m (.ctor c l h) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_indTy {hf} :
    LRS.DefEq (n := n) IH M N A (.ctor c fs hf) (.indTy r h l) ↔ LRS.IndVal IH A M N h l c fs := by
  show LRS.IndVal IH A M N h ((l.map (·.1)).pmap Subtype.mk _) c ((fs.map (·.1)).pmap Subtype.mk _) ↔ _
  rw [WShape.pmap_map_val, WShape.pmap_map_val]
@[simp] theorem LRS.DefEq.bot_indTy : LRS.DefEq (n := n) IH M N A .bot (.indTy r c l) ↔ True :=
  .rfl

theorem LRS.LamClause.left : LRS.LamClause IH M N A f a₁ a₂ → LRS.LamClause IH M M A f a₁ a₂
  | ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP⟩ =>
    ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP.left⟩

theorem LRS.LamClause.symm : LRS.LamClause IH M N A f a₁ a₂ → LRS.LamClause IH N M A f a₁ a₂
  | ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP⟩ =>
    ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP.symm⟩

theorem LRS.LamClause.trans (hU : StepUniq env) :
    LRS.LamClause IH M₁ M₂ A f a₁ a₂ → LRS.LamClause IH M₂ M₃ A f a₁ a₂ →
    LRS.LamClause IH M₁ M₃ A f a₁ a₂
  | ⟨_, _, _, _, rA, eA, hA1, hA2, hA₂, hE, hP⟩, ⟨_, _, _, _, rA', _, _, _, _, _, hP'⟩ => by
    cases StepS.determ hU rA forallE_whnf rA' forallE_whnf
    exact ⟨_, _, _, _, rA, eA, hA1, hA2, hA₂, hE, hP.trans hP'⟩

theorem LRS.LamClause.whr (hM : TRed env U Γ M M' A) (hN : TRed env U Γ N N' A) :
    LRS.LamClause IH M N A f a₁ a₂ ↔ LRS.LamClause IH M' N' A f a₁ a₂ := by
  constructor <;> intro ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP⟩
  · exact ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE,
      (LRS.LamDefEq.whr hA1 hA₂ (hM.tyEq eA) (hN.tyEq eA)).1 hP⟩
  · exact ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE,
      (LRS.LamDefEq.whr hA1 hA₂ (hM.tyEq eA) (hN.tyEq eA)).2 hP⟩

theorem LRS.LamClause.not_neRed (hU : StepUniq env) :
    LRS.LamClause IH M N A f a₁ a₂ → ¬NeRed env U Γ A
  | ⟨_, _, _, _, rA, _⟩, h => h.not_forallE hU rA

theorem NeRed.not_sort' (hU : StepUniq env) : ¬NeRed env U Γ (.sort u) :=
  fun h => h.not_sort hU .rfl

theorem not_sort_forallE : ¬StepS env U Γ (.sort u) (.forallE A B) := fun h => by
  cases StepS.of_whnf sort_whnf h

namespace LRS.IndVal

theorem left : LRS.IndVal IH A M N h l c fs → LRS.IndVal IH A M M h l c fs := by
  unfold LRS.IndVal; split <;> rename_i hs
  · rintro (H | H | ⟨h, -⟩)
    · exact .inl H.left
    · exact .inr (.inl H)
    · simp [hs] at h
  · rintro (H | H | ⟨h, H, -⟩)
    · exact .inl H.left
    · exact .inr (.inl H)
    · exact .inr (.inr ⟨h, H, H⟩)

theorem symm (hU : StepUniq env) :
    LRS.IndVal IH A M N h l c fs → LRS.IndVal IH A N M h l c fs := by
  unfold LRS.IndVal; split
  · rintro (H | H | ⟨h, H1, H2⟩)
    · exact .inl (H.symm hU)
    · exact .inr (.inl H)
    · exact .inr (.inr ⟨h, H2, H1⟩)
  · rintro (H | H | ⟨h, H1, H2⟩)
    · exact .inl (H.symm hU)
    · exact .inr (.inl H)
    · exact .inr (.inr ⟨h, H2, H1⟩)

theorem trans (hU : StepUniq env) :
    LRS.IndVal IH A M₁ M₂ h l c fs → LRS.IndVal IH A M₂ M₃ h l c fs →
    LRS.IndVal IH A M₁ M₃ h l c fs := by
  unfold LRS.IndVal; split <;> rename_i hs
  · rintro (H1 | H1 | ⟨hf, -⟩) H2
    · rcases H2 with H2 | H2 | ⟨hf', -⟩
      · exact .inl (H1.trans hU H2)
      · exact .inr (.inl H2)
      · rw [hs] at hf'; cases hf'
    · exact .inr (.inl H1)
    · rw [hs] at hf; cases hf
  · rintro (H1 | H1 | ⟨h1, N1, N2⟩) H2
    · rcases H2 with H2 | H2 | ⟨h2, N2', N3⟩
      · exact .inl (H1.trans hU H2)
      · exact .inr (.inl H2)
      · let ⟨_, _, r⟩ := H1.red_r; exact (NeRed.not_inert hU H1.inert N2'.neRed r).elim
    · exact .inr (.inl H1)
    rcases H2 with H2 | H2 | ⟨h2, N2', N3⟩
    · let ⟨_, _, r⟩ := H2.red_l; exact (NeRed.not_inert hU H2.inert N2.neRed r).elim
    · exact .inr (.inl H2)
    · exact .inr (.inr ⟨h1, N1, N3⟩)

theorem conv (hU : StepUniq env) (hE : TyEq env U Γ A B)
    (hAB : (IndRel env U Γ h A B ∧ IndTele IH h l A B) ∨ (NeRed env U Γ A ∧ NeRed env U Γ B)) :
    LRS.IndVal IH A M N h l c fs → LRS.IndVal IH B M N h l c fs := by
  unfold LRS.IndVal
  rintro (H | hA | H)
  · rcases hAB with ⟨hR, hT⟩ | ⟨-, hB⟩
    · have hBB := hT.symm.left' hU hR.symm
      refine .inl ?_
      by_cases hs : IsStruct c = true
      · rw [if_pos hs] at H ⊢; exact H.conv hU hE hR hT hBB
      · rw [if_neg hs] at H ⊢; exact H.conv hU hE hR hT hBB
    · exact .inr (.inl hB)
  · rcases hAB with ⟨hR, -⟩ | ⟨-, hB⟩
    · exact (hR.not_neRed hU hA).elim
    · exact .inr (.inl hB)
  · exact .inr (.inr ⟨H.1, H.2.1.tyEq hE, H.2.2.tyEq hE⟩)

theorem whr (hU : StepUniq env) (hM : TRed env U Γ M M' A) (hN : TRed env U Γ N N' A) :
    LRS.IndVal IH A M N h l c fs ↔ LRS.IndVal IH A M' N' h l c fs := by
  unfold LRS.IndVal
  refine or_congr ?_
    (or_congr .rfl (and_congr .rfl (and_congr (TNeRed.whr hU hM) (TNeRed.whr hU hN))))
  split
  · exact StructVal.whr hU hM hN
  · exact ⟨fun H => (CtorVal.whr hU H.inert hM hN).1 H, fun H => (CtorVal.whr hU H.inert hM hN).2 H⟩

theorem fits_of {m : WShape (n+1)} (hm : m.HasType (.indTy r h l)) (e : m = .ctor c fs hf) :
    ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs := by
  subst e
  obtain ⟨i, hi, hfit⟩ := hm.ctor_fits
  intro i' hi'; rw [hi] at hi'; cases hi'; exact hfit

theorem mono_r (hU : StepUniq env) (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs) :
    LRS.IndVal IH A M N h l' c fs → LRS.IndVal IH A M N h l c fs := by
  unfold LRS.IndVal
  rintro (H | H)
  · refine .inl ?_
    by_cases hs : IsStruct c = true
    · rw [if_pos hs] at H ⊢; exact H.mono_r hU hl htel htel' hfit
    · rw [if_neg hs] at H ⊢; exact H.mono_r hU hl htel htel' hfit
  · exact .inr H

theorem mono_up (hU : StepUniq env) (hl : l.Forall₂ (· ≤ ·) l')
    (htel : ∀ i, (ctorTel h l i).HasType .type) (htel' : ∀ i, (ctorTel h l' i).HasType .type)
    (hfit' : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l' i) fs)
    (hA : (IndRel env U Γ h A A ∧ IndTele IH h l' A A) ∨ (NeRed env U Γ A ∧ NeRed env U Γ A)) :
    LRS.IndVal IH A M N h l c fs → LRS.IndVal IH A M N h l' c fs := by
  unfold LRS.IndVal
  rintro (H | H)
  · rcases hA with ⟨-, hT⟩ | ⟨hA, -⟩
    · refine .inl ?_
      by_cases hs : IsStruct c = true
      · rw [if_pos hs] at H ⊢; exact H.mono_up hU hl htel htel' hfit' hT
      · rw [if_neg hs] at H ⊢; exact H.mono_up hU hl htel htel' hfit' hT
    · exact .inr (.inl hA)
  · exact .inr H

theorem mono_l (hfs : fs.Forall₂ (· ≤ ·) fs')
    (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs) :
    LRS.IndVal IH A M N h l c fs' → LRS.IndVal IH A M N h l c fs := by
  unfold LRS.IndVal
  rintro (H | H)
  · refine .inl ?_
    by_cases hs : IsStruct c = true
    · rw [if_pos hs] at H ⊢; exact H.mono_l hfs htel hfit
    · rw [if_neg hs] at H ⊢; exact H.mono_l hfs htel hfit
  · exact .inr H

end LRS.IndVal

theorem LRS.TyTyped.whr (hU : StepUniq env) (hM : StepS env U Γ M M') (e : TyEq env U Γ M M') :
    LRS.TyTyped IH M m ↔ LRS.TyTyped IH M' m := by
  cases m using WShape.casesOn' with
  | forallE b f =>
    rw [LRS.TyTyped.forallE_iff, LRS.TyTyped.forallE_iff]
    refine or_congr (NeRed.whr hU hM) ⟨?_, ?_⟩
    · rintro ⟨A₁, A₂, u, v, r, eA, rest⟩
      exact ⟨A₁, A₂, u, v, StepS.determ_l hU hM r forallE_whnf, e.symm.trans eA, rest⟩
    · rintro ⟨A₁, A₂, u, v, r, eA, rest⟩
      exact ⟨A₁, A₂, u, v, hM.trans r, e.trans eA, rest⟩
  | indTy r h l =>
    rw [LRS.TyTyped.indTy_iff, LRS.TyTyped.indTy_iff]
    refine or_congr (NeRed.whr hU hM) ⟨fun H c i k hs hi hk => ?_, fun H c i k hs hi hk => ?_⟩
    · obtain ⟨ci, hc, H⟩ := H c i k hs hi hk
      exact ⟨ci, hc, fun lsA AsA rA W M₁ N₁ w1 n1 w2 n2 hMN =>
        H lsA AsA (hM.trans rA) W M₁ N₁ w1 n1 w2 n2 (e.symm.defeqDF hMN)⟩
    · obtain ⟨ci, hc, H⟩ := H c i k hs hi hk
      exact ⟨ci, hc, fun lsA AsA rA W M₁ N₁ w1 n1 w2 n2 hMN =>
        H lsA AsA (StepS.determ_l hU hM rA W) W M₁ N₁ w1 n1 w2 n2 (e.defeqDF hMN)⟩
  | _ => exact .rfl

theorem LRS.TyTyped.mono (hU : StepUniq env) {m m' : WShape (n+1)} (le : m ≤ m')
    (hm : m.HasType .type) (hm' : m'.HasType .type) (hT : LRS.TyDefEq IH M M m')
    (H : LRS.TyTyped IH M m') : LRS.TyTyped IH M m := by
  cases m using WShape.casesOn' with
  | forallE s f =>
    obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
    rw [LRS.TyTyped.forallE_iff] at H ⊢
    rw [LRS.TyDefEq.forallE_iff] at hT
    refine H.imp id fun ⟨A₁, A₂, u, v, rA, eA, hA₁, hA₂, y1, hY⟩ => ?_
    rcases hT with ⟨B₁, F₁, B₂, F₂, rM, rM', -, -, hValB, hE⟩ | ⟨hn, -⟩
    · cases StepS.determ hU rA forallE_whnf rM forallE_whnf
      cases StepS.determ hU rA forallE_whnf rM' forallE_whnf
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 hm'
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨A₁, A₂, u, v, rA, eA, hA₁, hA₂, IH.tyTy_mono h1 ht ht' (IH.left_ty hValB) y1,
        fun x p hp0 hx hr => ?_⟩
      have hp1 := WShape.HasType.mono_r h1 ht' hp0
      have hr1 := IH.mono_r_1 h1 hp0 hp1 (IH.left_ty hValB) hr
      exact IH.tyTy_mono (WShapeFun.app_mono_l h2 p) ((WShape.HasTypePi.iff.1 hp).2 p hp0).toType
        ((WShape.HasTypePi.iff.1 hp').2 p hp1).toType (IH.left_ty (hE.2 hp1 hx hr1))
        (hY x p hp1 hx hr1)
    · exact (hn.not_forallE hU rA).elim
  | indTy r h l =>
    obtain ⟨l', rfl, -⟩ := WShape.indTy_le.1 le
    rw [LRS.TyTyped.indTy_iff] at H ⊢; exact H
  | _ => trivial

theorem LRS.TyTyped.join (hU : StepUniq env) {m₁ m₂ : WShape (n+1)} (hC : m₁.Compat m₂)
    (hm₁ : m₁.HasType .type) (hm₂ : m₂.HasType .type)
    (hT₁ : LRS.TyDefEq IH M M m₁) (hT₂ : LRS.TyDefEq IH M M m₂)
    (H1 : LRS.TyTyped IH M m₁) (H2 : LRS.TyTyped IH M m₂) : LRS.TyTyped IH M (m₁.join m₂) := by
  cases hm₁.unfold with
  | bot => rwa [WShape.bot_join]
  | sort =>
    cases hm₂.unfold with
    | bot => rwa [WShape.join_bot]
    | sort => simp only [WShape.sort_join_sort]; split <;> trivial
    | _ => cases hC
  | forallE hp₁ =>
    cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
    simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
    rw [WShape.forallE_join_forallE hC.1 hC.2]
    rw [LRS.TyTyped.forallE_iff] at H1 H2 ⊢
    rw [LRS.TyDefEq.forallE_iff] at hT₁ hT₂
    rcases H1 with hn | ⟨A₁, A₂, u, v, rA, eA, hA₁, hA₂, y1, hY1⟩
    · exact .inl hn
    rcases H2 with hn | ⟨_, _, _, _, rA', _, _, _, y2, hY2⟩
    · exact .inl hn
    cases StepS.determ hU rA forallE_whnf rA' forallE_whnf
    rcases hT₁ with ⟨_, _, _, _, r1, r1', -, -, hV1, hE1⟩ | ⟨hn, -⟩
    · rcases hT₂ with ⟨_, _, _, _, r2, r2', -, -, hV2, hE2⟩ | ⟨hn, -⟩
      · cases StepS.determ hU rA forallE_whnf r1 forallE_whnf
        cases StepS.determ hU rA forallE_whnf r1' forallE_whnf
        cases StepS.determ hU rA forallE_whnf r2 forallE_whnf
        cases StepS.determ hU rA forallE_whnf r2' forallE_whnf
        have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
        have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
        refine .inr ⟨A₁, A₂, u, v, rA, eA, hA₁, hA₂,
          IH.tyTy_join hC.1 ht₁ ht₂ (IH.left_ty hV1) (IH.left_ty hV2) y1 y2,
          fun x p hp hx hr => ?_⟩
        have hJ_b := WShape.Join.mk hC.1
        have htB_join := ht₁.join hC.1 ht₂
        have hJ_f := WShapeFun.Join.mk hC.2
        have ht₁_w := WShape.HasTypePi.iff.1 hp₁
        have ht₂_w := WShape.HasTypePi.iff.1 hp₂
        obtain ⟨d_x, d_le, d_ht, d_app⟩ := WShape.HasDom.iff.1 hp₁.1 p
        have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
          (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp hr)
        obtain ⟨e_x, e_le, e_ht, e_app⟩ := WShape.HasDom.iff.1 hp₂.1 p
        have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
          (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp hr)
        have ht_f1 := hp₁.app_isType p
        have ht_f2 := hp₂.app_isType p
        have hJ_fp := hJ_f.app_l p
        have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
        have ht_fJ := ht_f1.join' hJ_fp ht_f2
        have ht_fJ' := ht_f1.join hC_fp ht_f2
        have T1 := hE1.2 d_ht hx c2
        have T2 := hE2.2 e_ht hx c3
        have T1' := IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toType (IH.left_ty T1)
        have T2' := IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toType (IH.left_ty T2)
        have t1' := IH.tyTy_mono d_app ht_f1 (ht₁_w.2 d_x d_ht).toType (IH.left_ty T1)
          (hY1 x d_x d_ht hx c2)
        have t2' := IH.tyTy_mono e_app ht_f2 (ht₂_w.2 e_x e_ht).toType (IH.left_ty T2)
          (hY2 x e_x e_ht hx c3)
        exact IH.tyTy_mono hC_fJ ht_fJ ht_fJ' (IH.join_ty hC_fp ht_f1 ht_f2 T1' T2')
          (IH.tyTy_join hC_fp ht_f1 ht_f2 T1' T2' t1' t2')
      · exact (hn.not_forallE hU rA).elim
    · exact (hn.not_forallE hU rA).elim
  | @indTy _ _ _ r c l =>
    cases hm₂.unfold with
    | bot => rwa [WShape.join_bot]
    | @indTy _ _ _ r' c' l' =>
      obtain ⟨rfl, rfl, hl⟩ := WShape.Compat.indTy_indTy.1 hC
      rw [WShape.indTy_join hl]
      rw [LRS.TyTyped.indTy_iff] at H1 ⊢; exact H1
    | _ => cases hC
  | _ => cases hm₂.unfold <;> first | rwa [WShape.join_bot] | cases hC | trivial

theorem LRS.TyDefEq.mono_l (hU : StepUniq env) {m m' : WShape (n+1)} (le : m ≤ m')
    (hm : m.HasType .type) (hm' : m'.HasType .type)
    (h : LRS.TyDefEq IH M N m') : LRS.TyDefEq IH M N m := by
    cases m using WShape.casesOn' with
    | bot => simp only [LRS.TyDefEq.bot]
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE s f =>
      obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
      simp only [LRS.TyDefEq.forallE_iff] at h ⊢
      refine h.imp (fun h => ?_) id
      have ⟨_, hm_pi, _⟩ := WShape.HasType.forallE_l.1 hm
      have ⟨_, hm'_pi, _⟩ := WShape.HasType.forallE_l.1 hm'
      let ⟨B₁, F₁, B₂, F₂, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hm_pi).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hm'_pi).1.isType
      exact ⟨B₁, F₁, B₂, F₂, rM, rN, hBB', hFF', IH.mono_r_2_ty h1 ht ht' hValB,
        hEdge.mono_r_2 h1 h2 hm_pi hm'_pi (IH.left_ty hValB)⟩
    | lam => simp only [LRS.TyDefEq.lam_m]
    | ctor => simp only [LRS.TyDefEq.ctor_m]
    | indTy r c l =>
      obtain ⟨l', rfl, hl⟩ := WShape.indTy_le.1 le
      rw [LRS.TyDefEq.indTy_iff] at h ⊢
      exact h.imp (fun ⟨hR, hT⟩ => ⟨hR, hT.mono hU hl hm.indTy_tels' hm'.indTy_tels'⟩) id

theorem LRS.DefEq.mono_l (henv : env.Ordered) (hU : StepUniq env) {m m' : WShape (n+1)}
    (le : m ≤ m') (hm : m.HasType a) (hm' : m'.HasType a)
    (h : LRS.DefEq IH M N A m' a) : LRS.DefEq IH M N A m a := by
  cases a using WShape.casesOn' with
  | bot => simp only [LRS.DefEq.bot_a]
  | sort r =>
    simp only [LRS.DefEq.sort_a] at h ⊢
    obtain ⟨h, hT⟩ := h
    refine ⟨LRS.TyDefEq.mono_l hU le hm.toType hm'.toType h, fun u e => ⟨?_, ?_⟩⟩
    · exact LRS.TyTyped.mono hU le hm.toType hm'.toType (LRS.TyDefEq.left hU h) (hT u e).1
    · exact LRS.TyTyped.mono hU le hm.toType hm'.toType
        (LRS.TyDefEq.left hU (LRS.TyDefEq.symm henv h)) (hT u e).2
  | forallE a₁ a₂ =>
    cases m using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_m]
    | lam f hf =>
      obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv hm
      have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
      simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
      · injection hgf' with hgf'; have := WShapeFun.ext hgf'.symm; subst this
        obtain ⟨g'', hg'', hm'_lam⟩ := WShape.HasType.forallE_inv hm'
        rw [hg''] at h
        by_cases hg''nz : g''.NonZero
        · rw [show WShape.lam' g'' = WShape.lam g'' hg''nz from
            (WShape.lam_eq_lam' (hl := hg''nz)).symm] at h
          simp only [LRS.DefEq.lam_forallE] at h ⊢
          rw [WShape.lam_eq_lam' (hl := hf), hg''] at le
          have le_g := WShape.lam'_le_lam'.1 le
          refine h.imp (fun h => ?_) id
          let ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP⟩ := h
          exact ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hE, hP.mono_l le_g hm_lam hm'_lam⟩
        · simp only [WShape.lam', dif_neg hg''nz] at hg''
          cases WShape.le_bot.1 (hg'' ▸ le)
      · cases hgf'
    | _ => cases hm
  | indTy r h l =>
    cases m using WShape.casesOn' with
    | ctor c fs hf =>
      obtain ⟨fs', hf', rfl, hfs⟩ := WShape.ctor_le.1 le
      rw [LRS.DefEq.ctor_indTy] at h ⊢
      exact LRS.IndVal.mono_l hfs hm.indTy_tels (LRS.IndVal.fits_of hm rfl) h
    | _ => trivial
  | _ => cases hm.isType

theorem LRS.TyDefEq.join (hU : StepUniq env) {m₁ m₂ : WShape (n+1)} (hC : m₁.Compat m₂)
    (hm₁ : m₁.HasType .type) (hm₂ : m₂.HasType .type)
    (h1 : LRS.TyDefEq IH A B m₁) (h2 : LRS.TyDefEq IH A B m₂) : LRS.TyDefEq IH A B (m₁.join m₂) := by
  cases hm₁.unfold with
  | bot h₁ => rwa [WShape.bot_join]
  | sort =>
    cases hm₂.unfold with
    | bot => rwa [WShape.join_bot]
    | sort =>
      simp only [WShape.sort_join_sort] at h1 h2 ⊢
      split <;> simp_all only [LRS.TyDefEq.sort_iff, WShape.Compat.sort_sort]
    | _ => cases hC
  | forallE hp₁ =>
    cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
    simp only [LRS.TyDefEq.forallE_iff] at h1 h2
    simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
    simp only [LRS.TyDefEq.forallE_iff, WShape.forallE_join_forallE hC.1 hC.2]
    rcases h1 with ⟨B₁, F₁, B₂, F₂, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ | ⟨hn1, hn2⟩ <;>
      rcases h2 with ⟨_, _, _, _, rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ | ⟨hn1', hn2'⟩
    · cases StepS.determ hU rA forallE_whnf rA' forallE_whnf
      cases StepS.determ hU rB forallE_whnf rB' forallE_whnf
      have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
      have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
      refine .inl ⟨B₁, F₁, B₂, F₂, rA, rB, hBB, hFF, IH.join_ty hC.1 ht₁ ht₂ hValB₁ hValB₂, ?_⟩
      exact .join ht₁ ht₂ hC.1 hp₁ hp₂ hC.2 hEdge₁ hEdge₂
    · exact (hn1'.not_forallE hU rA).elim
    · exact (hn1.not_forallE hU rA').elim
    · exact .inr ⟨hn1, hn2⟩
  | @indTy _ _ _ r c l =>
    cases hm₂.unfold with
    | bot => rwa [WShape.join_bot]
    | @indTy _ _ _ r' c' l' =>
      obtain ⟨rfl, rfl, hl⟩ := WShape.Compat.indTy_indTy.1 hC
      rw [WShape.indTy_join hl]
      rw [LRS.TyDefEq.indTy_iff] at h1 h2 ⊢
      rcases h1 with ⟨hR, hT1⟩ | ⟨hn1, hn2⟩ <;> rcases h2 with ⟨hR', hT2⟩ | ⟨hn1', hn2'⟩
      · exact .inl ⟨hR, hT1.join hU hl hm₁.indTy_tels' hm₂.indTy_tels' hT2⟩
      · exact (hR.not_neRed hU hn1').elim
      · exact (hR'.not_neRed hU hn1).elim
      · exact .inr ⟨hn1, hn2⟩
    | _ => cases hC
  | _ => cases hm₂.unfold <;> first | rwa [WShape.join_bot] | cases hC | trivial

theorem LRS.LamDefEq.join {g₁ g₂ : WShapeFun n} (hC : WShapeFun.Compat g₁ g₂)
    (hm₁ : WShape.HasTypeLam g₁ a₁ a₂) (hm₂ : WShape.HasTypeLam g₂ a₁ a₂)
    (H1 : LRS.LamDefEq IH M N A₁ A₂ g₁ a₁ a₂) (H2 : LRS.LamDefEq IH M N A₁ A₂ g₂ a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ (g₁.join g₂) a₁ a₂ := by
  have hJ := WShapeFun.Join.mk hC
  have w₁ := (WShape.HasTypeLam.iff.1 hm₁).2.2
  have w₂ := (WShape.HasTypeLam.iff.1 hm₂).2.2
  have wJ := (WShape.HasTypeLam.iff.1 (WShape.HasTypeLam.join hC hm₁ hm₂)).2.2
  have key {p X Y B} (hp : p.HasType a₁) (d1 : IH.DefEq X Y B (g₁.app p) (a₂.app p))
      (d2 : IH.DefEq X Y B (g₂.app p) (a₂.app p)) :
      IH.DefEq X Y B ((g₁.join g₂).app p) (a₂.app p) := by
    obtain ⟨hCp, -, hle⟩ := WShape.Join.iff.1 (hJ.app_l p)
    exact IH.mono_l hle (wJ _ hp) ((w₁ _ hp).join hCp (w₂ _ hp))
      (IH.join hCp (w₁ _ hp) (w₂ _ hp) d1 d2)
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => key hp (H1.2 hp ha a1) (H2.2 hp ha a1)⟩
  exact ⟨key hp (H1.1 hp ha a1).1 (H2.1 hp ha a1).1, key hp (H1.1 hp ha a1).2 (H2.1 hp ha a1).2⟩

theorem LRS.LamClause.join (hU : StepUniq env) {g₁ g₂ : WShapeFun n}
    (hC : WShapeFun.Compat g₁ g₂)
    (hm₁ : WShape.HasTypeLam g₁ a₁ a₂) (hm₂ : WShape.HasTypeLam g₂ a₁ a₂) :
    LRS.LamClause IH M N A g₁ a₁ a₂ → LRS.LamClause IH M N A g₂ a₁ a₂ →
    LRS.LamClause IH M N A (g₁.join g₂) a₁ a₂
  | ⟨_, _, _, _, rA, eA, hA1, hA2, hA₂, hE, hP⟩, ⟨_, _, _, _, rA', _, _, _, _, _, hP'⟩ => by
    cases StepS.determ hU rA forallE_whnf rA' forallE_whnf
    exact ⟨_, _, _, _, rA, eA, hA1, hA2, hA₂, hE, hP.join hC hm₁ hm₂ hP'⟩

theorem LRS.IndVal.join (hU : StepUniq env) {fs₁ fs₂ : List (WShape n)}
    (hC : fs₁.Forall₂ WShape.Compat fs₂) (htel : ∀ i, (ctorTel h l i).HasType .type)
    (hfit₁ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₁)
    (hfit₂ : ∀ i, h.ctors.idxOf? c = some i → TelFits (ctorTel h l i) fs₂) :
    LRS.IndVal IH A M N h l c fs₁ → LRS.IndVal IH A M N h l c fs₂ →
    LRS.IndVal IH A M N h l c (fs₁.zipWith WShape.join fs₂) := by
  unfold LRS.IndVal; split <;> rename_i hs
  · rintro (H1 | H1 | ⟨hf, -⟩) H2
    · rcases H2 with H2 | H2 | ⟨hf', -⟩
      · exact .inl (H1.join hU hC htel hfit₁ hfit₂ H2)
      · exact .inr (.inl H2)
      · rw [hs] at hf'; cases hf'
    · exact .inr (.inl H1)
    · rw [hs] at hf; cases hf
  · rintro (H1 | H1 | ⟨h1, N1, N2⟩) H2
    · rcases H2 with H2 | H2 | ⟨h2, N1', N2'⟩
      · exact .inl (H1.join hU hC htel hfit₁ hfit₂ H2)
      · exact .inr (.inl H2)
      · let ⟨_, _, r⟩ := H1.red_l; exact (NeRed.not_inert hU H1.inert N1'.neRed r).elim
    · exact .inr (.inl H1)
    rcases H2 with H2 | H2 | ⟨h2, N1', N2'⟩
    · let ⟨_, _, r⟩ := H2.red_l; exact (NeRed.not_inert hU H2.inert N1.neRed r).elim
    · exact .inr (.inl H2)
    · exact .inr (.inr ⟨h1, N1, N2⟩)

theorem LRS.DefEq.join (henv : env.Ordered) (hU : StepUniq env) {m₁ m₂ a : WShape (n+1)}
    (hC : m₁.Compat m₂)
    (hm₁ : m₁.HasType a) (hm₂ : m₂.HasType a)
    (h1 : LRS.DefEq IH M N A m₁ a) (h2 : LRS.DefEq IH M N A m₂ a) :
    LRS.DefEq IH M N A (m₁.join m₂) a := by
  cases a using WShape.casesOn' with
  | bot => trivial
  | sort r =>
    obtain ⟨h1, y1⟩ := h1; obtain ⟨h2, y2⟩ := h2
    refine ⟨LRS.TyDefEq.join hU hC hm₁.toType hm₂.toType h1 h2, fun u e => ⟨?_, ?_⟩⟩
    · exact LRS.TyTyped.join hU hC hm₁.toType hm₂.toType (LRS.TyDefEq.left hU h1)
        (LRS.TyDefEq.left hU h2) (y1 u e).1 (y2 u e).1
    · exact LRS.TyTyped.join hU hC hm₁.toType hm₂.toType
        (LRS.TyDefEq.left hU (LRS.TyDefEq.symm henv h1))
        (LRS.TyDefEq.left hU (LRS.TyDefEq.symm henv h2)) (y1 u e).2 (y2 u e).2
  | forallE a₁ a₂ =>
    obtain ⟨g₁, rfl, hg₁⟩ := WShape.HasType.forallE_inv hm₁
    obtain ⟨g₂, rfl, hg₂⟩ := WShape.HasType.forallE_inv hm₂
    by_cases hz₂ : g₂.NonZero
    case neg =>
      rw [show WShape.lam' g₂ = .bot by simp [WShape.lam', hz₂], WShape.join_bot]; exact h1
    by_cases hz₁ : g₁.NonZero
    case neg =>
      rw [show WShape.lam' g₁ = .bot by simp [WShape.lam', hz₁], WShape.bot_join]; exact h2
    have hCg : g₁.Compat g₂ := WShape.Compat.lam'.1 hC
    have hJ : WShape.Join (.lam' g₁) (.lam' g₂) (.lam' (g₁.join g₂)) :=
      WShape.Join.lam'.2 (WShapeFun.Join.mk hCg)
    have hz : (g₁.join g₂).NonZero := (WShapeFun.NonZero.join hCg).2 (.inl hz₁)
    refine LRS.DefEq.mono_l henv hU (WShape.Join.iff.1 hJ).2.1 (hm₁.join hC hm₂)
      (WShape.HasType.join' hJ hm₁ hm₂) ?_
    rw [← WShape.lam_eq_lam' (hl := hz), LRS.DefEq.lam_forallE]
    rw [← WShape.lam_eq_lam' (hl := hz₁), LRS.DefEq.lam_forallE] at h1
    rw [← WShape.lam_eq_lam' (hl := hz₂), LRS.DefEq.lam_forallE] at h2
    rcases h1 with h1 | h1 <;> [skip; exact .inr h1]
    rcases h2 with h2 | h2 <;> [skip; exact .inr h2]
    exact .inl (h1.join hU hCg hg₁ hg₂ h2)
  | indTy r h l =>
    rcases hm₁.indTy_cases with rfl | ⟨c₁, fs₁, hf₁, rfl⟩
    · rw [WShape.bot_join]; exact h2
    rcases hm₂.indTy_cases with rfl | ⟨c₂, fs₂, hf₂, rfl⟩
    · rw [WShape.join_bot]; exact h1
    obtain ⟨rfl, hl⟩ := WShape.Compat.ctor_ctor.1 hC
    rw [LRS.DefEq.ctor_indTy] at h1 h2
    have hJ := LRS.IndVal.join hU hl hm₁.indTy_tels (LRS.IndVal.fits_of hm₁ rfl)
      (LRS.IndVal.fits_of hm₂ rfl) h1 h2
    rw [WShape.ctor_eq_ctor', WShape.ctor_eq_ctor', WShape.ctor'_join hl]
    unfold WShape.ctor'; split
    · rw [LRS.DefEq.ctor_indTy]; exact hJ
    · trivial
  | lam => exact absurd hm₁.isType WShape.HasType.lam_isType
  | ctor => exact absurd hm₁.isType WShape.HasType.ctor_isType

def LRS (henv : env.Ordered) (hU : StepUniq env) (IH : LogRel env U Γ n) :
    LogRel env U Γ (n+1) where
  DefEq := LRS.DefEq IH
  TyDefEq := LRS.TyDefEq IH
  TyTy := LRS.TyTyped IH
  sort_iff := ⟨And.left, fun h => ⟨h, fun _ _ => ⟨trivial, trivial⟩⟩⟩
  sort_a_iff := .rfl
  sort_iff_ty := .rfl
  bot ha := by
    cases ha.unfold <;> first | trivial | exact ⟨trivial, fun _ _ => ⟨trivial, trivial⟩⟩
  left_ty := .left hU
  left {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact fun ⟨h, y⟩ => ⟨.left hU h, fun u e => ⟨(y u e).1, (y u e).1⟩⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      exact Or.imp .left id
    · split
      · exact LRS.IndVal.left
      · exact id
  symm_ty := .symm henv
  symm {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact fun ⟨h, y⟩ => ⟨.symm henv h, fun u e => ⟨(y u e).2, (y u e).1⟩⟩
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      exact Or.imp .symm id
    · split
      · exact LRS.IndVal.symm hU
      · exact id
  trans_ty := .trans henv hU
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact fun ⟨h1, y1⟩ ⟨h2, y2⟩ => ⟨.trans henv hU h1 h2, fun u e => ⟨(y1 u e).1, (y2 u e).2⟩⟩
    · split <;> try trivial
      rintro (h1 | h1) (h2 | h2)
      · exact .inl (h1.trans hU h2)
      · exact (h1.not_neRed hU h2).elim
      · exact .inr h1
      · exact .inr h1
    · split
      · exact LRS.IndVal.trans hU
      · exact fun _ => id
  conv {A A' a M N m} hE := by
    cases a using WShape.casesOn' with
    | indTy r h l =>
      rw [LRS.TyDefEq.indTy_iff]
      intro hAA
      cases m using WShape.casesOn' with
      | ctor c fs hf =>
        rw [LRS.DefEq.ctor_indTy, LRS.DefEq.ctor_indTy]; exact LRS.IndVal.conv hU hE hAA
      | _ => exact id
    | bot => intros; trivial
    | sort => exact fun _ ⟨h, y⟩ => ⟨h, fun u e => y u (hE.trans e)⟩
    | lam => intro _ h; simp at h
    | ctor => intro _ h; simp at h
    | forallE a₁ a₂ =>
    rw [LRS.TyDefEq.forallE_iff]
    rintro (⟨B, F, B', F', rA, rA', hBB', hFF', hValB, hEdge⟩ | ⟨-, hA'⟩)
    · cases m using WShape.casesOn' with
      | lam => ?_
      | bot => intros; trivial
      | _ => intro h; simp at h
      rw [LRS.DefEq.lam_forallE, LRS.DefEq.lam_forallE]
      rintro (⟨_, _, _, v', rA₁, eA, hA1, hValA, hA₂, hEdge₁, hP⟩ | hA)
      · cases StepS.determ hU rA forallE_whnf rA₁ forallE_whnf
        obtain ⟨_, hB'⟩ := hBB'.isType_r
        obtain ⟨_, hF'⟩ := hFF'.isType_r
        refine .inl ⟨_, _, _, _, rA', hE.symm.trans (eA.trans (TyEq.forallE henv hBB' hFF')),
          hB', IH.left_ty (IH.symm_ty hValB), hBB'.defeqDF_l henv hF', ?_, ?_⟩
        · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
            have ha' := hBB'.symm.defeqDF ha
          · exact and_self_iff.2 (hEdge.1 hp ha' (IH.conv hBB'.symm (IH.symm_ty hValB) a1)).2
          · exact (hEdge.1 hp ha' (IH.conv hBB'.symm (IH.symm_ty hValB) a1)).2
        refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
          have a2 := IH.conv hBB'.symm (IH.symm_ty hValB) a1
          have ha' := hBB'.symm.defeqDF ha
          have c := hEdge.2 hp ha'.hasType.1 (IH.left a2)
          have e := TyEq.inst henv ha'.hasType.1 hFF')
        · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv e c v1, IH.conv e c v2⟩
        · exact IH.conv e c (hP.2 hp ha' a2)
      · exact (hA.not_forallE hU rA).elim
    · cases m using WShape.casesOn' with
      | lam => rw [LRS.DefEq.lam_forallE, LRS.DefEq.lam_forallE]; exact fun _ => .inr hA'
      | bot => intros; trivial
      | _ => intro h; simp at h
  toType := And.left
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      cases m using WShape.casesOn' with
      | bot => simp [LRS.DefEq.bot_m]
      | lam f hf =>
        simp only [LRS.DefEq.lam_forallE] at h ⊢
        refine h.imp (fun h => ?_) id
        have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm.isType
        have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht
        obtain ⟨g, hg, hm'⟩ := WShape.HasType.forallE_inv hm
        have hgf : g = f := by
          have := congrArg (·.1) hg; simp only [WShape.lam, WShape.lam'] at this
          split at this
          · injection this with this; exact WShapeFun.ext this.symm
          · cases this
        subst hgf
        let ⟨A₁, A₂, u, v, rA, eA, hA1, hA2, hA₂, hEdge, hP⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hp).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
        refine ⟨A₁, A₂, u, v, rA, eA, hA1, IH.mono_r_2_ty le1 ht ht' hA2, hA₂, ?_⟩
        exact ⟨hEdge.mono_r_2 le1 le2 hp hp' hA2, hP.mono_r_2 le1 le2 hm' hA2 hp'⟩
      | sort => simp [LRS.DefEq.sort_forallE] at h
      | forallE => simp [LRS.DefEq.forallE_forallE] at h
      | ctor => simp [LRS.DefEq.ctor_forallE] at h
      | indTy => simp [LRS.DefEq.indTy_forallE] at h
    | lam f hf => exact absurd hm.isType WShape.HasType.lam_isType
    | ctor => exact absurd hm.isType WShape.HasType.ctor_isType
    | indTy r h l =>
      obtain ⟨l', rfl, hl⟩ := WShape.indTy_le.1 le
      cases m using WShape.casesOn' with
      | ctor c fs hf =>
        rw [LRS.DefEq.ctor_indTy] at h ⊢
        exact LRS.IndVal.mono_r hU hl hm.indTy_tels ht.indTy_tels' (LRS.IndVal.fits_of hm rfl) h
      | _ => trivial
  mono_r_2_ty {a a' A B} le ha ha' h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      simp only [LRS.TyDefEq.forallE_iff] at h ⊢
      refine h.imp (fun h => ?_) id
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 ha
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ha'
      let ⟨B₁, F₁, B₂, F₂, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨B₁, F₁, B₂, F₂, rA, rB, hBB', hFF', IH.mono_r_2_ty le1 ht ht' hValB, ?_⟩
      exact hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)
    | lam f hf => simp [LRS.TyDefEq.lam_m]
    | ctor => simp [LRS.TyDefEq.ctor_m]
    | indTy r c l =>
      obtain ⟨l', rfl, hl⟩ := WShape.indTy_le.1 le
      rw [LRS.TyDefEq.indTy_iff] at h ⊢
      exact h.imp (fun ⟨hR, hT⟩ => ⟨hR, hT.mono hU hl ha.indTy_tels' ha'.indTy_tels'⟩) id
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases a' using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      obtain rfl | rfl := WShape.le_sort.1 le
      · have := ha.bot_r; subst this
        exact ⟨trivial, fun _ _ => ⟨trivial, trivial⟩⟩
      · exact h
    | forallE a₁' a₂' =>
      obtain rfl | ⟨a₁, a₂, rfl, le1, le2⟩ := WShape.le_forallE_iff.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_m]
      · cases m using WShape.casesOn' with
        | bot => simp only [LRS.DefEq.bot_m]
        | lam f hf =>
          simp only [LRS.DefEq.lam_forallE] at h ⊢
          refine h.elim (fun h => ?_) .inr
          obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv ha
          have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
          simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
          · injection hgf' with hgf'
            have := WShapeFun.ext hgf'.symm; subst this
            obtain ⟨g', hg', hm'_lam⟩ := WShape.HasType.forallE_inv ha'
            have hgf2 : (WShape.lam g hf).1 = (WShape.lam' g').1 := congrArg (·.1) hg'
            simp only [WShape.lam, WShape.lam'] at hgf2; split at hgf2
            · injection hgf2 with hgf2; have := WShapeFun.ext hgf2.symm; subst this
              let ⟨A₁, A₂, u, v, rA, eA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
              simp only [LRS.TyDefEq.forallE_iff] at hA
              rcases hA with ⟨B₁, F₁, B₂, F₂, rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ |
                ⟨hn, -⟩
              · cases StepS.determ hU rA forallE_whnf rA' forallE_whnf
                cases StepS.determ hU rA forallE_whnf rA'' forallE_whnf
                refine .inl ⟨_, _, _, _, rA, eA, hA1, hValB_tgt, hA₂, hEdge_tgt, ?_⟩
                exact hP.mono_r_1 le1 le2 hm_lam hm'_lam hEdge_tgt
              · exact .inr hn
            · cases hgf2
          · cases hgf'
        | sort => exact (LRS.DefEq.sort_forallE.1 h).elim
        | forallE => exact (LRS.DefEq.forallE_forallE.1 h).elim
        | ctor => exact (LRS.DefEq.ctor_forallE.1 h).elim
        | indTy => exact (LRS.DefEq.indTy_forallE.1 h).elim
    | lam f hf => exact absurd ha'.isType WShape.HasType.lam_isType
    | ctor => exact absurd ha'.isType WShape.HasType.ctor_isType
    | indTy r h l' =>
      rcases WShape.le_indTy.1 le with rfl | ⟨l, rfl, hl⟩
      · have := ha.bot_r; subst this; trivial
      · cases m using WShape.casesOn' with
        | ctor c fs hf =>
          rw [LRS.DefEq.ctor_indTy] at h ⊢; rw [LRS.TyDefEq.indTy_iff] at hA
          exact LRS.IndVal.mono_up hU hl ha.indTy_tels ha'.indTy_tels
            (LRS.IndVal.fits_of ha' rfl) hA h
        | _ => trivial
  mono_l le hm hm' h := LRS.DefEq.mono_l henv hU le hm hm' h
  join_ty hC hm₁ hm₂ h1 h2 := LRS.TyDefEq.join hU hC hm₁ hm₂ h1 h2
  join hC hm₁ hm₂ h1 h2 := LRS.DefEq.join henv hU hC hm₁ hm₂ h1 h2
  whr {M M' N N' A m a} hM hN := by
    cases a using WShape.casesOn' with
    | sort =>
      refine and_congr (LRS.TyDefEq.whr hU hM.1 hN.1) (forall_congr' fun u => forall_congr' fun e =>
        and_congr ?_ ?_)
      · exact LRS.TyTyped.whr hU hM.1 (.base (e.defeqDF hM.2))
      · exact LRS.TyTyped.whr hU hN.1 (.base (e.defeqDF hN.2))
    | forallE =>
      cases m using WShape.casesOn' with | lam => ?_ | _ => rfl
      exact or_congr (LRS.LamClause.whr hM hN) .rfl
    | indTy =>
      cases m using WShape.casesOn' with
      | ctor => rw [LRS.DefEq.ctor_indTy, LRS.DefEq.ctor_indTy]; exact LRS.IndVal.whr hU hM hN
      | _ => exact .rfl
    | _ => rfl
  whr_ty hA hB := LRS.TyDefEq.whr hU hA hB
  tyTy_bot := trivial
  tyTy_mono le hm hm' hT h := LRS.TyTyped.mono hU le hm hm' hT h
  tyTy_join hC hm₁ hm₂ hT₁ hT₂ h1 h2 := LRS.TyTyped.join hU hC hm₁ hm₂ hT₁ hT₂ h1 h2
  tyTy_whr hA e := LRS.TyTyped.whr hU hA e

/-- The logical relation at every depth. -/
def LR (henv : env.Ordered) (hU : StepUniq env) : (n : Nat) → LogRel env U Γ n
  | 0 => LR0 hU
  | n+1 => LRS henv hU (LR henv hU n)

end LogRel
end Lean4Lean
