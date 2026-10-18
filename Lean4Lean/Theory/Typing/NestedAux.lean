import Lean4Lean.Theory.Typing.NestedEnv

/-!
# An auxiliary type's `AuxWF` from its literal forms

The kernel checks a nested occurrence's arguments against the binders the earlier type is
declared with, not against its block's parameters; `AuxWF.of_lit` moves them across, by the
agreement of those binders with the parameters.
-/

namespace Lean4Lean
open VExpr

namespace VEnv

theorem TeleDefEq.instL {env : VEnv} {U U' : Nat} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) :
    ∀ {Γ As Bs}, env.TeleDefEq U' Γ As Bs →
      env.TeleDefEq U (Γ.map (·.instL ls)) (As.map (·.instL ls)) (Bs.map (·.instL ls))
  | _, [], [], .nil => .nil
  | _, _ :: _, _ :: _, .cons h t => .cons (h.instL hls) (by simpa using TeleDefEq.instL hls t)

/-- A substitution for a telescope is one for a telescope that agrees with it. -/
theorem Ctx.SubstEq.defeqTele {env : VEnv} {U : Nat} (henv : env.Ordered) {Γ₀ : List VExpr}
    (hΓ₀ : OnCtx Γ₀ (env.IsType U)) {Δ₀ Δ₁ Δ₂ : List VExpr} (h : env.IsDefEqCtx U Δ₀ Δ₁ Δ₂) :
    ∀ {σ σ'}, Ctx.SubstEq env U Γ₀ σ σ' Δ₁ → Ctx.SubstEq env U Γ₀ σ σ' Δ₂ := by
  induction h with
  | zero => exact fun W => W
  | succ h hA ih =>
    intro σ σ' W
    cases W with | cons W' _ hh =>
    exact .cons (ih W') (hA.hasType.2.defeqDFC henv h) (.defeqDF (hA.subst henv W'.left hΓ₀) hh)

end VEnv

namespace VInductiveType

/-- `AuxWF` from what the kernel establishes: the occurrence's arguments typed against the binders
`psJ` the earlier type is declared with, over parameters `Qs` agreeing with the block's, and the
auxiliary type's declared type and constructors as the earlier type's instantiated. -/
theorem AuxWF.of_lit {env : VEnv} (henv : env.WF) {d : VInductDecl} {T : VInductiveType}
    {o : VNested} {dI : VInductDecl} {tI : Nat} {TI : VInductiveType}
    (hind : env.inducts o.ind = some (dI, tI)) (hTI : dI.types[tI]? = some TI)
    (hlen : o.lvls.length = dI.uvars) (hlwf : ∀ l ∈ o.lvls, l.WF d.uvars)
    (hargslen : o.args.length = dI.params.length) {psJ : List VExpr} {BJ : VExpr}
    (hTIty : TI.type = .foralls psJ BJ) (hpsJ : env.TeleDefEq dI.uvars [] psJ dI.params)
    {Qs : List VExpr} (hQ : env.TeleDefEq d.uvars [] Qs d.params)
    (hP : env.IsTele d.uvars [] d.params)
    (hargs : ∀ i (a P : VExpr), o.args[i]? = some a → psJ[i]? = some P →
      env.HasType d.uvars Qs.reverse a
        ((P.instL o.lvls).subst (VExpr.Subst.dflt.consList (o.args.take i))))
    (hty : ∃ ps' Y, env.TeleDefEq d.uvars [] ps' d.params ∧ T.type = .foralls ps' Y ∧
      VEnv.EqUpToLevels d.uvars Y ((BJ.instL o.lvls).subst (VExpr.Subst.dflt.consList o.args)))
    (hctors : List.Forall₂ (fun cI c => c.name = cI.name ∧ ∃ ps B, cI.type = .foralls ps B ∧
        ps.length = dI.params.length ∧ ∃ ps' Y, ps'.length = d.params.length ∧
          c.type = .foralls ps' Y ∧
          VEnv.EqUpToLevels d.uvars Y ((B.instL o.lvls).subst (VExpr.Subst.dflt.consList o.args)))
      TI.ctors T.ctors) :
    T.AuxWF env d o := by
  have hPP : OnCtx d.params.reverse (env.IsType d.uvars) := by simpa using hP.onCtx trivial
  obtain ⟨env₀, envTI, -, hdI, hTI', hleI, TI', hTI'', -⟩ := henv.inducts hind
  cases hTI.symm.trans hTI''
  have hdIP0 : env.IsTele dI.uvars [] dI.params :=
    (hdI.params.mono (VEnv.addConstList_le hTI')).mono hleI
  have hdIP : env.IsTele d.uvars [] (dI.params.map (·.instL o.lvls)) := by
    simpa using hdIP0.instL hlwf
  have hTIT : env.IsType dI.uvars [] TI.type :=
    ((hdI.types TI (List.mem_of_getElem? hTI)).1.mono (VEnv.addConstList_le hTI')).mono hleI
  rw [hTIty] at hTIT
  have hpsJT : env.IsTele d.uvars [] (psJ.map (·.instL o.lvls)) := by
    simpa using (VEnv.IsType.foralls_inv henv.ordered hTIT).1.instL hlwf
  have hlenJ : psJ.length = dI.params.length := hpsJ.length_eq
  -- the arguments, against the declared binders, over `Qs`
  have hQP : env.IsDefEqCtx d.uvars [] Qs.reverse d.params.reverse := by
    simpa using hQ.defeqCtx henv (Γ' := []) .zero trivial hP
  have W₁ : VEnv.Ctx.SubstEq env d.uvars Qs.reverse (Subst.dflt.consList o.args)
      (Subst.dflt.consList o.args) ((psJ.map (·.instL o.lvls)).reverse ++ []) :=
    VEnv.Ctx.SubstEq.ofGetElem .nil o.args.length rfl hpsJT (by simp [hargslen, hlenJ])
      fun r h h' => by
        have h'' : r < psJ.length := by simpa using h'
        simpa using hargs r _ _ (List.getElem?_eq_getElem h) (List.getElem?_eq_getElem h'')
  -- moved to the block's parameters, both the arguments' context and the telescope
  have hJP : env.IsDefEqCtx d.uvars [] (psJ.map (·.instL o.lvls)).reverse
      (dI.params.map (·.instL o.lvls)).reverse := by
    simpa using (hpsJ.instL hlwf).defeqCtx henv (Γ' := []) .zero trivial (by simpa using hdIP)
  have W₂ := (W₁.defeqCtx henv.ordered hQP)
  rw [List.append_nil] at W₂
  have W₃ : VEnv.Ctx.SubstEq env d.uvars d.params.reverse (Subst.dflt.consList o.args)
      (Subst.dflt.consList o.args) ((dI.params.map (·.instL o.lvls)).reverse ++ []) := by
    rw [List.append_nil]; exact VEnv.Ctx.SubstEq.defeqTele henv.ordered hPP hJP W₂
  refine ⟨⟨dI, tI, TI, hind, hTI, hlen, hlwf, hargslen, fun i a P ha hP' => ?_,
    ⟨psJ, BJ, hTIty, hpsJ, hty⟩, hctors⟩⟩
  have hi := (List.getElem?_eq_some_iff.1 ha).1
  have hi' : i < dI.params.length := (List.getElem?_eq_some_iff.1 hP').1
  have := VEnv.Ctx.SubstEq.getElem _ rfl W₃ (by simp [hargslen]) i hi (by simpa using hi')
  simp only [List.getElem_map] at this
  rwa [(List.getElem?_eq_some_iff.1 ha).2, (List.getElem?_eq_some_iff.1 hP').2] at this

end VInductiveType

end Lean4Lean
