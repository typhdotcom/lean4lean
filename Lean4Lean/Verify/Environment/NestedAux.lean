import Lean4Lean.Verify.Environment.Restore
import Lean4Lean.Verify.Environment.ElimNestedRun
import Lean4Lean.Theory.Typing.NestedAux

/-!
# An auxiliary type's `AuxWF`, from the elimination

The elimination creates an auxiliary type for a nested occurrence `J Ls Ds` by instantiating `J`'s
declared type, and its constructors', at the occurrence's levels and parameters
(`ElimNestedInductive.Created`). Its translation is then the earlier type's, instantiated as
`AuxWF` states it, up to the universe levels the kernel simplifies when it instantiates them.
-/

namespace Lean4Lean
open Lean

/-- Abstracting a variable from a term without free variables instantiated by arguments for its
loose variables abstracts it from the arguments. -/
theorem abstract1_instantiate' {x : FVarId} : ∀ {b : Expr} {as : List Expr} {d : Nat},
    b.SuppIn (ElimNestedInductive.FVOnly fun _ => False) → b.looseBVarRange' ≤ d + as.length →
    (b.instantiate' as d).abstract1 x d = b.instantiate' (as.map (·.abstract1 x 0)) d
  | .bvar i, as, d, _, hr => by
    simp only [Expr.looseBVarRange'] at hr
    simp only [Expr.instantiate']
    by_cases h1 : i < d
    · simp [h1, Expr.abstract1]
    · have h2 : i - d < as.length := by omega
      simp only [h1, if_false, dif_pos h2, List.length_map, List.getElem_map]
      have := ElimNestedInductive.abstract1_liftLooseBVars (x := x) (δ := d) (e := as[i - d])
        (s := 0) (k := 0) (Nat.le_refl _)
      simpa using this
  | .fvar _, _, _, hs, _ => hs.elim
  | .mvar _, _, _, _, _ | .sort _, _, _, _, _ | .const .., _, _, _, _ | .lit _, _, _, _, _ => rfl
  | .mdata _ e, as, d, hs, hr => by
    simp only [Expr.instantiate', Expr.abstract1]
    rw [abstract1_instantiate' (b := e) hs hr]
  | .proj _ _ e, as, d, hs, hr => by
    simp only [Expr.instantiate', Expr.abstract1]
    rw [abstract1_instantiate' (b := e) hs hr]
  | .app f a, as, d, hs, hr => by
    simp only [Expr.looseBVarRange', Nat.max_le] at hr
    simp only [Expr.instantiate', Expr.abstract1]
    rw [abstract1_instantiate' hs.1 hr.1, abstract1_instantiate' hs.2 hr.2]
  | .lam _ t b _, as, d, hs, hr | .forallE _ t b _, as, d, hs, hr => by
    simp only [Expr.looseBVarRange', Nat.max_le] at hr
    simp only [Expr.instantiate', Expr.abstract1]
    rw [abstract1_instantiate' hs.1 hr.1, abstract1_instantiate' (d := d + 1) hs.2 (by omega)]
  | .letE _ t v b _, as, d, hs, hr => by
    simp only [Expr.looseBVarRange', Nat.max_le] at hr
    simp only [Expr.instantiate', Expr.abstract1]
    rw [abstract1_instantiate' hs.1 hr.1.1, abstract1_instantiate' hs.2.1 hr.1.2,
      abstract1_instantiate' (d := d + 1) hs.2.2 (by omega)]

theorem abstractList_instantiate' : ∀ {xs : List FVarId} {b : Expr} {as : List Expr},
    b.SuppIn (ElimNestedInductive.FVOnly fun _ => False) → b.looseBVarRange' ≤ as.length →
    (b.instantiate' as 0).abstractList xs 0 = b.instantiate' (as.map (·.abstractList xs 0)) 0
  | [], _, as, _, _ => by simp
  | x :: xs, b, as, hs, hr => by
    simp only [Expr.abstractList]
    rw [abstract1_instantiate' hs (by simpa using hr), abstractList_instantiate' hs (by simpa using hr)]
    simp [List.map_map, Function.comp_def]

/-- Contexts whose entries have related values, as far as the translation reads them. -/
def ValRel (R : VExpr → VExpr → Prop) (Δ₁ Δ₂ : VLCtx) : Prop :=
  ∀ v e₁ A₁, Δ₁.find? v = some (e₁, A₁) → ∃ e₂ A₂, Δ₂.find? v = some (e₂, A₂) ∧ R e₁ e₂

theorem ValRel.cons {R : VExpr → VExpr → Prop}
    (hR : ∀ (e e' : VExpr) (n : Nat), R e e' → R (e.liftN n) (e'.liftN n))
    {Δ₁ Δ₂ : VLCtx} (H : ValRel R Δ₁ Δ₂) {d₁ d₂ : VLocalDecl}
    (hd : d₁.depth = d₂.depth) (hv : R d₁.value d₂.value) :
    ValRel R ((none, d₁) :: Δ₁) ((none, d₂) :: Δ₂) := by
  intro v e₁ A₁ h
  obtain (_ | i) | fv := v
  · simp only [VLCtx.find?, VLCtx.next, Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h; exact ⟨_, _, ⟨rfl, rfl⟩, hv⟩
  all_goals
    simp only [VLCtx.find?, VLCtx.next, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq, Prod.mk.injEq] at h ⊢
    obtain ⟨⟨_, _⟩, h, rfl, rfl⟩ := h
    obtain ⟨_, _, h2, hr⟩ := H _ _ _ h
    exact ⟨_, _, ⟨_, h2, rfl, rfl⟩, hd ▸ hR _ _ _ hr⟩

theorem ValRel.append_paramCtx {R : VExpr → VExpr → Prop}
    (hR : ∀ (e e' : VExpr) (n : Nat), R e e' → R (e.liftN n) (e'.liftN n))
    (hb : R (.bvar 0) (.bvar 0)) {Δ₁ Δ₂ : VLCtx}
    (H : ValRel R Δ₁ Δ₂) : ∀ {As Bs : List VExpr}, As.length = Bs.length →
      ValRel R (paramCtx As ++ Δ₁) (paramCtx Bs ++ Δ₂)
  | [], [], _ => H
  | _ :: _, _ :: _, h => (ValRel.append_paramCtx hR hb H (Nat.succ.inj h)).cons hR rfl hb

theorem ValRel.eq_self {Δ : VLCtx} : ValRel Eq Δ Δ := fun _ _ _ h => ⟨_, _, h, rfl⟩

/-- The translation reads a context only for its entries' values. -/
theorem PTr.ctxRel {CL : Literal → Prop} {Us : List Name} {Δ₁ Δ₂ : VLCtx} {e : Expr} {e' : VExpr}
    (H : PTr Us CL Δ₁ e e') (hΔ : ValRel Eq Δ₁ Δ₂) : PTr Us CL Δ₂ e e' := by
  have hR : ∀ (e e' : VExpr) (n : Nat), e = e' → e.liftN n = e'.liftN n := fun _ _ _ h => h ▸ rfl
  induction H generalizing Δ₂ with
  | bvar h => obtain ⟨_, _, h2, rfl⟩ := hΔ _ _ _ h; exact .bvar h2
  | fvar h => obtain ⟨_, _, h2, rfl⟩ := hΔ _ _ _ h; exact .fvar h2
  | sort h => exact .sort h
  | const h => exact .const h
  | app _ _ ih1 ih2 => exact .app (ih1 hΔ) (ih2 hΔ)
  | lam _ _ ih1 ih2 => exact .lam (ih1 hΔ) (ih2 (hΔ.cons hR rfl rfl))
  | forallE _ _ ih1 ih2 => exact .forallE (ih1 hΔ) (ih2 (hΔ.cons hR rfl rfl))
  | letE _ _ _ ih1 ih2 ih3 => exact .letE (ih1 hΔ) (ih2 hΔ) (ih3 (hΔ.cons hR rfl rfl))
  | lit h _ ih => exact .lit h (ih hΔ)
  | mdata _ ih => exact .mdata (ih hΔ)
  | proj _ ih => exact .proj (ih hΔ)

/-- A literal telescope translates to one, its body in the context of its binders. -/
theorem PTr.peel {CL : Literal → Prop} {Us : List Name} :
    ∀ {n : Nat} {Δ : VLCtx} {e b : Expr} {e' : VExpr}, PTr Us CL Δ e e' →
      ElimNestedInductive.peel n e = some b →
      ∃ ps B, e' = .foralls ps B ∧ ps.length = n ∧ PTr Us CL (paramCtx ps.reverse ++ Δ) b B
  | 0, _, _, _, _, H, h => by
    cases h; exact ⟨[], _, rfl, rfl, by simpa [paramCtx] using H⟩
  | n + 1, Δ, .forallE .., b, _, H, h => by
    cases H with | forallE _ H2 =>
    obtain ⟨ps, B, rfl, hl, H3⟩ := PTr.peel (n := n) H2 h
    refine ⟨_ :: ps, B, rfl, by simp [hl], ?_⟩
    simpa [paramCtx] using H3
  | _ + 1, _, .bvar .., _, _, _, h | _ + 1, _, .fvar .., _, _, _, h
  | _ + 1, _, .mvar .., _, _, _, h | _ + 1, _, .sort .., _, _, _, h
  | _ + 1, _, .const .., _, _, _, h | _ + 1, _, .app .., _, _, _, h
  | _ + 1, _, .lam .., _, _, _, h | _ + 1, _, .letE .., _, _, _, h
  | _ + 1, _, .lit .., _, _, _, h | _ + 1, _, .mdata .., _, _, _, h
  | _ + 1, _, .proj .., _, _, _, h => by simp [ElimNestedInductive.peel] at h

/-- A telescope with its body replaced translates to the telescope's translation over the body's. -/
theorem PTr.setBody {CL : Literal → Prop} {Us : List Name} {X : Expr} :
    ∀ {n : Nat} {Δ : VLCtx} {e : Expr} {T : VExpr}, (ElimNestedInductive.peel n e).isSome →
      PTr Us CL Δ (ElimNestedInductive.setBody n e X) T →
      ∃ ps Y, T = .foralls ps Y ∧ ps.length = n ∧ PTr Us CL (paramCtx ps.reverse ++ Δ) X Y
  | 0, _, _, _, _, H => ⟨[], _, rfl, rfl, by simpa [paramCtx, ElimNestedInductive.setBody] using H⟩
  | n + 1, Δ, .forallE .., _, h, H => by
    cases H with | forallE _ H2 =>
    obtain ⟨ps, Y, rfl, hl, H3⟩ := PTr.setBody (n := n) h H2
    refine ⟨_ :: ps, Y, rfl, by simp [hl], ?_⟩
    simpa [paramCtx] using H3
  | _ + 1, _, .bvar .., _, h, _ | _ + 1, _, .fvar .., _, h, _
  | _ + 1, _, .mvar .., _, h, _ | _ + 1, _, .sort .., _, h, _
  | _ + 1, _, .const .., _, h, _ | _ + 1, _, .app .., _, h, _
  | _ + 1, _, .lam .., _, h, _ | _ + 1, _, .letE .., _, h, _
  | _ + 1, _, .lit .., _, h, _ | _ + 1, _, .mdata .., _, h, _
  | _ + 1, _, .proj .., _, h, _ => by simp [ElimNestedInductive.peel] at h

theorem peel_instantiateLevelParamsCore' {red : Bool} {F : Name → Level} :
    ∀ {n : Nat} {e : Expr}, ElimNestedInductive.peel n (Expr.instantiateLevelParamsCore' red F e) =
      (ElimNestedInductive.peel n e).map (Expr.instantiateLevelParamsCore' red F)
  | 0, _ => rfl
  | n + 1, .forallE .. => peel_instantiateLevelParamsCore' (n := n)
  | _ + 1, .bvar .. | _ + 1, .fvar .. | _ + 1, .mvar .. | _ + 1, .sort ..
  | _ + 1, .const .. | _ + 1, .app .. | _ + 1, .lam .. | _ + 1, .letE ..
  | _ + 1, .lit .. | _ + 1, .mdata .. | _ + 1, .proj .. => rfl

section
variable {CL : Literal → Prop} {Us ps : List Name} {ls : List Level} {ls' : List VLevel}
  (Hls : ls.mapM (VLevel.ofLevel Us) = some ls') (eq : ps.length = ls.length)
  {F : Name → Level}
  (eqF : (fun x => ((List.idxOf? x ps).bind fun x => ls[x]?).getD (Level.param x)) = F)
include Hls eq eqF

/-- Instantiating level parameters, simplifying the levels as the kernel does, translates to the
instantiated translation up to universe levels. -/
theorem PTr.instL_eqUpTo (red : Bool) {Δ₁ Δ₂ : VLCtx} {e : Expr} {e' : VExpr}
    (H1 : PTr ps CL Δ₁ e e') (hΔ : ValRel (VEnv.EqUpToLevels Us.length) (Δ₁.instL ls') Δ₂) :
    ∃ X, PTr Us CL Δ₂ (Expr.instantiateLevelParamsCore' red F e) X ∧
      VEnv.EqUpToLevels Us.length (e'.instL ls') X := by
  have Hls' := VLevel.WF.of_mapM_ofLevel Hls
  have hR : ∀ (e e' : VExpr) (n : Nat), VEnv.EqUpToLevels Us.length e e' →
      VEnv.EqUpToLevels Us.length (e.liftN n) (e'.liftN n) := fun _ _ _ h => h.weakN
  induction H1 generalizing Δ₂ with
  | bvar h1 =>
    obtain ⟨_, _, h2, hr⟩ := hΔ _ _ _ (VLCtx.find?_instL (ls := ls') h1)
    exact ⟨_, .bvar h2, hr⟩
  | fvar h1 =>
    obtain ⟨_, _, h2, hr⟩ := hΔ _ _ _ (VLCtx.find?_instL (ls := ls') h1)
    exact ⟨_, .fvar h2, hr⟩
  | sort h1 =>
    have ⟨_, a1, a2⟩ := substParams_wf Hls eq eqF red h1
    exact ⟨_, .sort a1, .sort (.inst Hls') (.of_ofLevel a1) a2.symm⟩
  | const h1 =>
    have ⟨_, a1, a2⟩ := substParams_wf_list Hls eq eqF red h1
    refine ⟨_, .const a1, .const ?_ (.of_mapM_ofLevel a1) (List.Forall₂.flip
      (Lean4Lean.List.Forall₂.imp (fun _ _ h => h.symm) a2))⟩
    simp only [List.mem_map]; rintro _ ⟨_, _, rfl⟩; exact .inst Hls'
  | app _ _ ih1 ih2 =>
    obtain ⟨_, a1, b1⟩ := ih1 hΔ
    obtain ⟨_, a2, b2⟩ := ih2 hΔ
    exact ⟨_, .app a1 a2, .app b1 b2⟩
  | lam _ _ ih1 ih2 =>
    obtain ⟨X1, a1, b1⟩ := ih1 hΔ
    obtain ⟨_, a2, b2⟩ := ih2 (hΔ.cons hR (d₂ := .vlam X1) rfl .bvar)
    exact ⟨_, .lam a1 a2, .lam b1 b2⟩
  | forallE _ _ ih1 ih2 =>
    obtain ⟨X1, a1, b1⟩ := ih1 hΔ
    obtain ⟨_, a2, b2⟩ := ih2 (hΔ.cons hR (d₂ := .vlam X1) rfl .bvar)
    exact ⟨_, .forallE a1 a2, .forallE b1 b2⟩
  | letE _ _ _ ih1 ih2 ih3 =>
    obtain ⟨X1, a1, b1⟩ := ih1 hΔ
    obtain ⟨X2, a2, b2⟩ := ih2 hΔ
    obtain ⟨_, a3, b3⟩ := ih3 (hΔ.cons hR (d₂ := .vlet X1 X2) rfl b2)
    exact ⟨_, .letE a1 a2 a3, b3⟩
  | lit h1 _ ih =>
    obtain ⟨_, a1, b1⟩ := ih hΔ
    refine ⟨_, .lit h1 ?_, b1⟩
    rwa [Expr.instantiateLevelParamsCore_eq_self Literal.toConstructor_hasLevelParam] at a1
  | mdata _ ih =>
    obtain ⟨_, a1, b1⟩ := ih hΔ
    exact ⟨_, .mdata a1, b1⟩
  | proj _ ih =>
    obtain ⟨_, a1, b1⟩ := ih hΔ
    exact ⟨_, .proj a1, .proj b1⟩

end

/-- A translation's universe levels are well formed, as far as its context's values' are. -/
theorem PTr.eqUpTo_refl {CL : Literal → Prop} {Us : List Name} {Δ : VLCtx} {e : Expr}
    {e' : VExpr} (H : PTr Us CL Δ e e')
    (hΔ : ValRel (fun a b => a = b ∧ VEnv.EqUpToLevels Us.length a a) Δ Δ) :
    VEnv.EqUpToLevels Us.length e' e' := by
  have hR : ∀ (e e' : VExpr) (n : Nat), (e = e' ∧ VEnv.EqUpToLevels Us.length e e) →
      (e.liftN n = e'.liftN n ∧ VEnv.EqUpToLevels Us.length (e.liftN n) (e.liftN n)) :=
    fun _ _ _ ⟨h1, h2⟩ => ⟨h1 ▸ rfl, h2.weakN⟩
  induction H with
  | bvar h | fvar h =>
    obtain ⟨_, _, h2, rfl, hr⟩ := hΔ _ _ _ h
    cases h.symm.trans h2; exact hr
  | sort h => exact .sort (.of_ofLevel h) (.of_ofLevel h) (by rfl)
  | const h =>
    exact .const (.of_mapM_ofLevel h) (.of_mapM_ofLevel h) (Lean4Lean.List.Forall₂.rfl fun _ _ => by rfl)
  | app _ _ ih1 ih2 => exact .app (ih1 hΔ) (ih2 hΔ)
  | lam _ _ ih1 ih2 =>
    exact .lam (ih1 hΔ) (ih2 (hΔ.cons hR (d₁ := .vlam _) (d₂ := .vlam _) rfl ⟨rfl, .bvar⟩))
  | forallE _ _ ih1 ih2 =>
    exact .forallE (ih1 hΔ) (ih2 (hΔ.cons hR (d₁ := .vlam _) (d₂ := .vlam _) rfl ⟨rfl, .bvar⟩))
  | letE _ _ _ ih1 ih2 ih3 =>
    exact ih3 (hΔ.cons hR (d₁ := .vlet _ _) (d₂ := .vlet _ _) rfl ⟨rfl, ih2 hΔ⟩)
  | lit _ _ ih => exact ih hΔ
  | mdata _ ih => exact ih hΔ
  | proj _ ih => exact .proj (ih hΔ)

theorem ValRel.refl_paramCtx {Us : List Name} : ∀ (As : List VExpr),
    ValRel (fun a b => a = b ∧ VEnv.EqUpToLevels Us.length a a) (paramCtx As) (paramCtx As)
  | [] => fun _ _ _ h => by simp [paramCtx, VLCtx.find?] at h
  | _ :: As => (ValRel.refl_paramCtx As).cons
      (fun _ _ _ ⟨h1, h2⟩ => ⟨h1 ▸ rfl, h2.weakN⟩) (d₁ := .vlam _) (d₂ := .vlam _) rfl ⟨rfl, .bvar⟩

/-- What the elimination makes of an earlier constant's declared type `ty`, instantiated at an
occurrence's levels `Ls` and first `nI` arguments, under the parameters `xs` of the constructor
it was found in: a telescope over the parameters whose body is, up to universe levels, the
body of `ty`'s translation under its first `nI` binders, at the levels and the arguments. -/
theorem instShape {CL : Literal → Prop} {Us : List Name} {cty : Expr} {xs : List FVarId}
    {lctx : LocalContext} {body : Expr} (ho : ElimNestedInductive.Opens {} cty xs lctx body)
    (hnd : xs.Nodup) (hx : ∀ x ∈ xs, cty.SuppIn (ElimNestedInductive.FVOnly (· ≠ x)))
    (hcl : cty.looseBVarRange' = 0) {ty : Expr}
    (hty : ty.SuppIn (ElimNestedInductive.FVOnly fun _ => False)) (htl : ty.looseBVarRange' = 0)
    {lps : List Name} {Ls : List Level} {nI : Nat} {args : Array Expr} {v : Expr}
    (hlb : ∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0) (hle : nI ≤ args.size)
    (hv : ElimNestedInductive.instantiateForallParams (ty.instantiateLevelParams lps Ls) nI args =
      .ok v)
    {CL' : Literal → Prop} (hCL : ∀ l, CL' l → CL l)
    {TJ : VExpr} (hJ : PTr lps CL' [] ty TJ) {lvls : List VLevel}
    (hls : Ls.mapM (VLevel.ofLevel Us) = some lvls) (hlen : lps.length = Ls.length)
    {T : VExpr} (hT : PTr Us CL [] (lctx.mkForall (xs.map .fvar).toArray v) T)
    {Ps ys : List VExpr} (hPs : Ps.length = xs.length)
    (hys : List.Forall₂ (PTr Us CL (paramCtx Ps))
      ((args.extract 0 nI).toList.map (·.abstractList xs)) ys) :
    ∃ psJ BJ ps Y, TJ = .foralls psJ BJ ∧ psJ.length = nI ∧ T = .foralls ps Y ∧
      ps.length = xs.length ∧
      VEnv.EqUpToLevels Us.length Y ((BJ.instL lvls).subst (VExpr.Subst.dflt.consList ys)) := by
  obtain ⟨b, hb, rfl⟩ := ElimNestedInductive.instantiateForallParams_ok hv
  rw [Expr.instantiateLevelParams_eq, peel_instantiateLevelParamsCore'] at hb
  obtain ⟨bJ, hbJ, rfl⟩ := Option.map_eq_some_iff.1 hb
  generalize hred : (!lps.isEmpty && !Ls.isEmpty) = red at hT
  generalize hF : (fun x => ((List.idxOf? x lps).bind fun x => Ls[x]?).getD (Level.param x)) = F
    at hT
  have hargs : ((args.extract 0 nI).toList).length = nI := by simp; omega
  have hex : ∀ a ∈ (args.extract 0 nI).toList, a.looseBVarRange' = 0 := by
    intro a ha
    rw [Array.toList_extract] at ha
    simp [List.extract] at ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact hlb i (by simp at hi; omega) _ (by simp [List.getElem_take])
  -- the body under the earlier constant's parameters, and its levels instantiated
  have hbS : bJ.SuppIn (ElimNestedInductive.FVOnly fun _ => False) :=
    ElimNestedInductive.SuppIn.peel hbJ hty
  have hbL : bJ.looseBVarRange' ≤ nI := by
    have := ElimNestedInductive.peel_looseBVarRange (k := 0) hbJ (Nat.le_of_eq htl); omega
  obtain ⟨psJ, BJ, rfl, hpsJ, hBJ⟩ := hJ.peel hbJ
  simp only [List.append_nil] at hBJ
  obtain ⟨BLP, hBLP, hBe⟩ := hBJ.instL_eqUpTo hls hlen hF red
    (Δ₂ := paramCtx (psJ.reverse.map (·.instL lvls))) (by
      rw [paramCtx_instL]
      have h0 : ValRel (VEnv.EqUpToLevels Us.length) [] [] := fun _ _ _ h => by
        simp [VLCtx.find?] at h
      simpa using ValRel.append_paramCtx (fun _ _ _ h => h.weakN) .bvar h0
        (As := psJ.reverse.map (·.instL lvls)) (Bs := psJ.reverse.map (·.instL lvls)) rfl)
  -- the body, instantiated and abstracted
  generalize hbLPdef : Expr.instantiateLevelParamsCore' red F bJ = bLP at hBLP hT
  have hbLS : bLP.SuppIn (ElimNestedInductive.FVOnly fun _ => False) := by
    subst hred hF hbLPdef; rw [← Expr.instantiateLevelParams_eq]
    exact ElimNestedInductive.SuppIn.instantiateLevelParams hbS
  have hbLL : bLP.looseBVarRange' ≤ nI := by
    subst hred hF hbLPdef; rw [← Expr.instantiateLevelParams_eq,
      ElimNestedInductive.instantiateLevelParams_looseBVarRange]; exact hbL
  have hv' : bLP.instantiateRevRange 0 nI args =
      bLP.instantiate' ((args.extract 0 nI).toList.reverse) 0 := by
    rw [Expr.instantiateRevRange_eq, Expr.instantiateRev_eq_instantiate']
  have hvc : (bLP.instantiateRevRange 0 nI args).looseBVarRange' = 0 := by
    rw [hv', Expr.instantiate'_eq_instantiateList (by simpa using hex)]
    have := Expr.instantiateList_looseBVarRange (n := 0) (k := 0) (e := bLP)
      (as := (args.extract 0 nI).toList.reverse) (by simp; omega)
      (fun a ha => Nat.le_of_eq (hex a (List.mem_reverse.1 ha)))
    omega
  -- the auxiliary type, as a telescope over the constructor's parameters
  have hmk : lctx.mkForall (xs.map .fvar).toArray (bLP.instantiateRevRange 0 nI args) =
      ElimNestedInductive.setBody xs.length cty
        ((bLP.instantiateRevRange 0 nI args).abstractList xs) :=
    ho.mkForall .nil (fun _ _ => LocalContext.find?_empty) hnd hx hcl _ hvc
  rw [hmk] at hT
  obtain ⟨ps, Y, rfl, hpsl, hY⟩ := PTr.setBody (by simp [ho.peel hnd hx]) hT
  simp only [List.append_nil] at hY
  rw [hv', abstractList_instantiate' hbLS (by rw [List.length_reverse, hargs]; exact hbLL),
    List.map_reverse] at hY
  have hys' : List.Forall₂ (PTr Us CL (paramCtx ps.reverse))
      ((args.extract 0 nI).toList.map (·.abstractList xs)) ys :=
    Lean4Lean.List.Forall₂.imp (fun _ _ h => h.ctxRel (by
      simpa using ValRel.append_paramCtx (fun _ _ _ h => h ▸ rfl) rfl (ValRel.eq_self (Δ := []))
        (As := Ps) (Bs := ps.reverse) (by simp [hPs, hpsl]))) hys
  have hlenys : ys.length = nI := by
    rw [← Lean4Lean.List.Forall₂.length_eq hys]; simp; omega
  have hX := PTr.inst' hys' (As := psJ.reverse.map (·.instL lvls)) (by simp [hpsJ, hlenys]) .base
    (hBLP.mono_lit hCL)
  have := hY.unique hX
  subst this
  refine ⟨psJ, BJ, ps, _, rfl, hpsJ, rfl, hpsl, ?_⟩
  show VEnv.EqUpToLevels _ (BLP.subst (VExpr.Subst.dflt.consList ys)) _
  refine VEnv.EqUpToLevels.subst hBe.symm fun i => ?_
  refine VEnv.EqUpToLevels.consList (fun _ => .sort (by trivial) (by trivial) (by rfl)) ?_ i
  refine List.Forall₂.rfl fun y hy => ?_
  obtain ⟨_, -, h⟩ := Lean4Lean.List.Forall₂.forall_exists_r hys' y hy
  exact h.eqUpTo_refl (ValRel.refl_paramCtx _)

theorem le_leadingForalls_of_peel : ∀ {n : Nat} {e b : Expr},
    ElimNestedInductive.peel n e = some b → n ≤ e.leadingForalls
  | 0, _, _, _ => Nat.zero_le _
  | n + 1, .forallE _ _ body _, b, h => by
    simp only [ElimNestedInductive.peel] at h
    simp only [Expr.leadingForalls]; exact Nat.succ_le_succ (le_leadingForalls_of_peel h)
  | _ + 1, .bvar .., _, h | _ + 1, .fvar .., _, h | _ + 1, .mvar .., _, h
  | _ + 1, .sort .., _, h | _ + 1, .const .., _, h | _ + 1, .app .., _, h
  | _ + 1, .lam .., _, h | _ + 1, .letE .., _, h | _ + 1, .lit .., _, h
  | _ + 1, .mdata .., _, h | _ + 1, .proj .., _, h => by simp [ElimNestedInductive.peel] at h

theorem forall₂_imp_mem {R S : α → β → Prop} (h : ∀ a b, a ∈ l₁ → R a b → S a b) :
    List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂ := by
  intro H
  induction H with
  | nil => exact .nil
  | cons hab _ ih =>
    exact .cons (h _ _ (.head _) hab) (ih fun a b ha hr => h a b (.tail _ ha) hr)

/-- An auxiliary type is `AuxWF`, from what the elimination made it of. It was created, while the
constructor `cty` was opened at its parameters `xs`, for an occurrence of the earlier type `J`, of
the block of `I` and so with `I`'s parameter count `nI`, at the levels `Ls` and the first `nI`
arguments `args`. `ys` translates those arguments over the parameters, and they are typed at `J`'s
literal binders (`hargTy`, from the kernel's check of the occurrence). The auxiliary type `T` is the
translation of what the elimination made, and its declared parameters agree with the block's
(`hTag`, from the check of the translated block). -/
theorem VInductiveType.AuxWF.of_created {safety : DefinitionSafety} {C : ConstMap} {Q : Bool}
    {venv : VEnv} (hTr : TrEnv' safety C Q venv) {E : VEnv} (hE : E.WF) (hle : venv ≤ E)
    {d : VInductDecl} (hP : E.IsTele d.uvars [] d.params)
    {CL : Literal → Prop} (hCL : ∀ l, venv.ContainsLits l → CL l) {Us : List Name}
    (hUs : Us.length = d.uvars)
    (hCcl : ∀ n ci, C.find? n = some ci →
      ci.type.SuppIn (ElimNestedInductive.FVOnly fun _ => False) ∧ ci.type.looseBVarRange' = 0)
    {cty : Expr} {xs : List FVarId} {lctx : LocalContext} {body : Expr}
    (ho : ElimNestedInductive.Opens {} cty xs lctx body) (hnd : xs.Nodup)
    (hx : ∀ x ∈ xs, cty.SuppIn (ElimNestedInductive.FVOnly (· ≠ x)))
    (hcl : cty.looseBVarRange' = 0) (hxs : xs.length = d.params.length)
    {J : Name} {Jv : InductiveVal} (hJ : C.find? J = some (.inductInfo Jv))
    (hJs : safety ≤ (ConstantInfo.inductInfo Jv).safety)
    {I : Name} {Iv : InductiveVal} (hI : C.find? I = some (.inductInfo Iv))
    (hIs : safety ≤ (ConstantInfo.inductInfo Iv).safety) (hJI : J ∈ Iv.all)
    {Ls : List Level} {args : Array Expr} {nI : Nat} {v : Expr} (hnI : nI = Iv.numParams)
    (hle' : nI ≤ args.size) (hlb : ∀ i < nI, ∀ a, args[i]? = some a → a.looseBVarRange' = 0)
    (hv : ElimNestedInductive.instantiateForallParams
      (Jv.type.instantiateLevelParams Jv.levelParams Ls) nI args = .ok v)
    {lvls : List VLevel} (hls : Ls.mapM (VLevel.ofLevel Us) = some lvls)
    (hLs : Jv.levelParams.length = Ls.length)
    {Ps ys : List VExpr} (hPs : Ps.length = xs.length)
    (hys : List.Forall₂ (PTr Us CL (paramCtx Ps))
      ((args.extract 0 nI).toList.map (·.abstractList xs)) ys)
    {Qs : List VExpr} (hQ : E.TeleDefEq d.uvars [] Qs d.params)
    (hargTy : ∀ L R, PTr Jv.levelParams CL [] Jv.type (.foralls L R) → L.length = nI →
      ∀ i (a A : VExpr), ys[i]? = some a → L[i]? = some A →
        E.HasType d.uvars Qs.reverse a
          ((A.instL lvls).subst (VExpr.Subst.dflt.consList (ys.take i))))
    {T : VInductiveType} (hT : PTr Us CL [] (lctx.mkForall (xs.map .fvar).toArray v) T.type)
    (hTag : ∀ ps B, T.type = .foralls ps B → ps.length = d.params.length →
      E.TeleDefEq d.uvars [] ps d.params)
    (hctors : List.Forall₂ (fun Jc (c : VConstructor) => c.name = Jc ∧ ∃ ci v',
        C.find? Jc = some ci ∧ ElimNestedInductive.instantiateForallParams
          (ci.type.instantiateLevelParams ci.levelParams Ls) nI args = .ok v' ∧
        PTr Us CL [] (lctx.mkForall (xs.map .fvar).toArray v') c.type) Jv.ctors T.ctors) :
    T.AuxWF E d ⟨J, lvls, ys⟩ := by
  have henv := hTr.wf
  have hJn : Jv.name = J := hTr.aligned.find?_name hJ
  obtain ⟨dI, tI, TI, venv₀, hind, hTI, hiv, hlpU, hle₀, htr, hag⟩ := hTr.inductInfo_type hJ hJs
  rw [hJn] at hind
  -- the earlier type's block is the occurrence's type's, so its parameters number `nI`
  obtain ⟨dIv, tIv, TIv, hindI, -, hivI, -⟩ := hTr.inductInfo hI hIs
  have hJmem : J ∈ dIv.names := by rw [← hivI.2.2.2.2.1]; exact hJI
  obtain ⟨T', hT'm, hT'n⟩ := List.mem_map.1 hJmem
  obtain ⟨t', ht'⟩ := List.mem_iff_getElem?.1 hT'm
  have hindJ := henv.inducts_getElem hindI ht'
  rw [hT'n, hind] at hindJ
  cases hindJ
  have hnI' : nI = dI.params.length := hnI.trans hivI.2.2.1
  -- the occurrence's arguments and the auxiliary type's body
  have hCL₀ : ∀ l, venv₀.ContainsLits l → CL l := fun l h => hCL l (h.mono hle₀)
  obtain ⟨psJ, BJ, ps, Y, hTIty, hpsJl, hTty, hpsl, hYeq⟩ := instShape ho hnd hx hcl
    (hCcl J _ hJ).1 (hCcl J _ hJ).2 hlb hle' hv hCL₀ htr.toPTr hls hLs hT hPs hys
  have hlvlen : lvls.length = dI.uvars := by
    rw [← Lean4Lean.List.Forall₂.length_eq (List.mapM_eq_some.1 hls), ← hLs, hlpU]
  have hlvwf : ∀ l ∈ lvls, l.WF d.uvars := hUs ▸ VLevel.WF.of_mapM_ofLevel hls
  have hyslen : ys.length = nI := by
    rw [← Lean4Lean.List.Forall₂.length_eq hys]; simp; omega
  have hpeel : nI ≤ Jv.type.leadingForalls := by
    obtain ⟨b, hb, -⟩ := ElimNestedInductive.instantiateForallParams_ok hv
    rw [Expr.instantiateLevelParams_eq, peel_instantiateLevelParamsCore'] at hb
    obtain ⟨bJ, hbJ, -⟩ := Option.map_eq_some_iff.1 hb
    exact le_leadingForalls_of_peel hbJ
  have hle₀E := hle₀.trans hle
  refine AuxWF.of_lit hE (hle.inducts hind) hTI hlvlen hlvwf (hyslen.trans hnI') hTIty
    ((hag (hnI' ▸ hpeel) psJ BJ hTIty (hpsJl.trans hnI')).mono hle₀E) hQ hP
    (hargTy psJ BJ (hTIty ▸ htr.toPTr.mono_lit hCL₀) hpsJl)
    ⟨ps, Y, hTag ps Y hTty (hpsl.trans hxs), hTty, hUs ▸ hYeq⟩ ?_
  -- the constructors: the earlier type's, instantiated
  have hctorsN : Jv.ctors = TI.ctors.map (·.name) := hiv.2.2.2.2.2.1
  rw [hctorsN, List.forall₂_map_left_iff] at hctors
  have hB := hTr.blockConsts hind
  obtain ⟨lp, -, -, hBc⟩ := hB
  refine forall₂_imp_mem (fun cI c hcI ⟨hcn, ci, v', hci, hv', hc⟩ => ?_) hctors
  obtain ⟨w, hw, hwc⟩ := hBc tI cI (VInductDecl.mem_ctors_iff.2 ⟨TI, hTI, hcI⟩)
  cases hci.symm.trans hw
  obtain ⟨T₁, hT₁, hc₁, -, -, hwi, -, -, hwU, -⟩ := hwc
  have hws : safety ≤ (ConstantInfo.ctorInfo w).safety := by
    have h1 : w.isUnsafe = dI.isUnsafe := hwU
    have h2 : Jv.isUnsafe = dI.isUnsafe := hiv.2.2.2.2.2.2.2.2
    have : (ConstantInfo.ctorInfo w).safety = (ConstantInfo.inductInfo Jv).safety := by
      simp [ConstantInfo.safety, ConstantInfo.isUnsafe, ConstantInfo.isPartial, h1, h2]
    exact this ▸ hJs
  obtain ⟨d', t', c', venv₁, hind', hcv', -, hlp', hle₁, htrc⟩ := hTr.ctorInfo_type hw hws
  cases hT₁.symm.trans hTI
  have hTIn : TI.name = J := hiv.1.symm.trans hJn
  rw [hwi, hTIn, hind] at hind'
  cases hind'
  obtain ⟨T₂, hT₂, hc₂, -⟩ := hcv'
  cases hT₂.symm.trans hTI
  cases hc₂.symm.trans hc₁
  have hlen : w.levelParams.length = Ls.length := hlp'.trans (hlpU.symm.trans hLs)
  obtain ⟨psI, BcI, ps', Y', hcIty, hpsIl, hcty, hps'l, hY'⟩ := instShape ho hnd hx hcl
    (hCcl _ _ hw).1 (hCcl _ _ hw).2 hlb hle' hv' (fun l h => hCL l (h.mono hle₁)) htrc.toPTr
    hls hlen hc hPs hys
  exact ⟨hcn, psI, BcI, hcIty, hpsIl.trans hnI', ps', Y', hps'l.trans hxs, hcty, hUs ▸ hY'⟩

end Lean4Lean

