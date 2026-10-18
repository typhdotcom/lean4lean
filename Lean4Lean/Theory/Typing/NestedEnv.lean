import Lean4Lean.Theory.Typing.NestedDecl
import Lean4Lean.Theory.Typing.InductiveRules

/-!
# The constant substitution of a restored nested block

The translation of a nested block is checked with its auxiliary types as constants (`E₁`); the
restored block has only its own types (`E₀`). `RestoreSpec.restoreEnv` builds the `RestoreEnv`
that carries the translation's judgments over: each auxiliary type and constructor becomes the
occurrence it stands for as a function of the parameters (`nestedF`), typed in `E₀` from the
restored block's `AuxWF`.
-/

namespace Lean4Lean
open VExpr

theorem VEnv.addConstList_defeqs : ∀ {env env' : VEnv} {cs : List (Name × VConstant)},
    env.addConstList cs = some env' → env'.defeqs = env.defeqs
  | _, _, [], h => by cases h; rfl
  | _, _, _ :: _, h => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    rw [VEnv.addConstList_defeqs h2]
    unfold VEnv.addConst at h1; split at h1 <;> cases h1; rfl

/-- A constant of an environment extended by a list is the old environment's or the list's. -/
theorem VEnv.addConstList_constants_cases :
    ∀ {env env' : VEnv} {cs : List (Name × VConstant)} {c : Name} {ci : VConstant},
    env.addConstList cs = some env' → env'.constants c = some ci →
    env.constants c = some ci ∨ (c, ci) ∈ cs
  | _, _, [], _, _, h, hc => by cases h; exact .inl hc
  | _, _, (m, ci') :: cs, c, ci, h, hc => by
    simp only [VEnv.addConstList, List.foldlM_cons, Option.bind_eq_bind,
      Option.bind_eq_some_iff] at h
    obtain ⟨env₁, h1, h2⟩ := h
    rcases VEnv.addConstList_constants_cases h2 hc with h | h
    · rw [VEnv.addConst_constants_eq h1] at h
      dsimp only at h
      split at h
      · cases h; subst_vars; exact .inr (.head _)
      · exact .inl h
    · exact .inr (.tail _ h)

theorem VExpr.ConstsSat.of_instL {p : Name → Prop} {ls : List VLevel} :
    ∀ {e : VExpr}, (e.instL ls).ConstsSat p → e.ConstsSat p
  | .bvar _, _ | .sort _, _ => trivial
  | .const _ _, H => H
  | .app .., H | .lam .., H | .forallE .., H => ⟨of_instL H.1, of_instL H.2⟩
  | .proj _ _ e, H => of_instL (e := e) H

namespace VEnv
variable {env : VEnv} {U : Nat}

/-- A telescope of an ordered environment mentions only its constants. -/
theorem IsTele.constsSat (henv : env.Ordered) : ∀ {Γ As : List VExpr}, env.IsTele U Γ As →
    OnCtx Γ (env.IsType U) → ∀ A ∈ As, A.ConstsSat (env.constants · |>.isSome)
  | _, [], _, _ => nofun
  | Γ, A :: As, .cons ⟨u, hA⟩ t, hΓ => by
    intro B hB
    rcases List.mem_cons.1 hB with rfl | hB
    · exact (hA.constsSat henv (OnCtx.constsSat henv hΓ)).1
    · exact IsTele.constsSat henv (Γ := A :: Γ) t ⟨hΓ, u, hA⟩ B hB

end VEnv

namespace VInductiveType

/-- What an auxiliary type's `AuxWF` gives, at the block's own levels and over its parameters as
variables: the occurrence is typed at the body of the auxiliary type's declared type, and so is
each constructor of the earlier type at the occurrence's parameters. -/
theorem AuxWF.apps {env : VEnv} (henv : env.WF) {d : VInductDecl} {T : VInductiveType}
    {o : VNested} (hP : env.IsTele d.uvars [] d.params) (hA : T.AuxWF env d o) :
    (∀ a ∈ o.args, a.ClosedN d.params.length) ∧
    (∃ ps' X, T.type = .foralls ps' X ∧ env.TeleDefEq d.uvars [] ps' d.params ∧
      env.HasType d.uvars d.params.reverse (.appN (.const o.ind o.lvls) o.args) X) ∧
    ∀ c ∈ T.ctors, VExpr.WF env d.uvars d.params.reverse (.appN (.const c.name o.lvls) o.args) := by
  have hPP : OnCtx d.params.reverse (env.IsType d.uvars) := by simpa using hP.onCtx trivial
  obtain ⟨⟨dI, tI, TI, hind, hTI, hlvlen, hlvwf, hargslen, hargs,
    ⟨psJ, BJ, hTIty, hpsJ, ps', Y, hTD, hTty, hY⟩, hctors⟩⟩ := hA
  obtain ⟨env₀, envTI, h₀, hdI, hTI', hleI, TI', hTI'', hname⟩ := henv.inducts hind
  cases hTI.symm.trans hTI''
  have hTIW := hdI.ctors envTI hTI' TI (List.mem_append_left _ (List.mem_of_getElem? hTI))
  have hdIP0 : envTI.IsTele dI.uvars [] dI.params := hdI.params.mono (VEnv.addConstList_le hTI')
  have hdIP : env.IsTele d.uvars [] (dI.params.map (·.instL o.lvls)) := by
    simpa using (hdIP0.instL hlvwf).mono hleI
  -- the occurrence's parameters, as a substitution for the earlier block's
  have hW : VEnv.Ctx.SubstEq env d.uvars d.params.reverse (Subst.dflt.consList o.args)
      (Subst.dflt.consList o.args) ((dI.params.map (·.instL o.lvls)).reverse ++ []) :=
    VEnv.Ctx.SubstEq.ofGetElem .nil o.args.length rfl hdIP (by simp [hargslen])
      fun r h h' => by
        have h'' : r < dI.params.length := by simpa using h'
        simpa using hargs r _ _ (List.getElem?_eq_getElem h) (List.getElem?_eq_getElem h'')
  -- a constant of the earlier block, applied to the occurrence's parameters
  have happ {name : Name} {psX : List VExpr} {B : VExpr}
      (hc : env.constants name = some ⟨dI.uvars, .foralls psX B⟩)
      (htd : env.TeleDefEq dI.uvars [] psX dI.params)
      (hty : env.IsType dI.uvars [] (.foralls psX B)) :
      env.HasType d.uvars d.params.reverse (.appN (.const name o.lvls) o.args)
        ((B.instL o.lvls).subst (Subst.dflt.consList o.args)) := by
    have hdef := (VEnv.IsType.foralls_teleDefEq henv (Γ := []) trivial hty htd
      (hdIP0.mono hleI)).instL hlvwf
    simp only [List.map_nil, instL_foralls] at hdef
    have hc0 : env.HasType d.uvars [] (.const name o.lvls) ((VExpr.foralls psX B).instL o.lvls) :=
      .const hc hlvwf (by rw [hlvlen])
    rw [instL_foralls] at hc0
    have hc1 := hc0.defeqU_r henv (Γ := []) trivial hdef
    have hc2 := hc1.weak0 henv.ordered (Γ := d.params.reverse)
    rw [← closed_subst henv.ordered hc1 .dflt] at hc2
    exact VEnv.HasType.appN_substT (Δ := []) hc2 (by simp [hargslen]) hW
  have hargsC : ∀ a ∈ o.args, a.ClosedN d.params.length := by
    intro a ha
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ha
    have hi' : i < dI.params.length := hargslen ▸ (List.getElem?_eq_some_iff.1 hi).1
    have := hargs i a _ hi (List.getElem?_eq_getElem hi')
    simpa using this.closedN henv.ordered (VEnv.CtxWF.closed henv.ordered hPP)
  refine ⟨hargsC, ?_, fun c hc => ?_⟩
  · have hcTI : env.constants TI.name = some ⟨dI.uvars, .foralls psJ BJ⟩ := by
      rw [← hTIty]
      exact hleI.constants (VEnv.addConstList_constants_of_mem hTI'
        (List.mem_map.2 ⟨TI, List.mem_of_getElem? hTI, rfl⟩))
    have hG := happ hcTI hpsJ
      (hTIty ▸ ((hdI.types TI (List.mem_of_getElem? hTI)).1.mono
        ((VEnv.addConstList_le hTI').trans hleI)))
    rw [hname] at hG
    have ⟨_, hX⟩ := hG.isType henv.ordered hPP
    exact ⟨ps', _, hTty, hTD, .defeqDF (hX.eqUpToLevels henv.ordered hPP hY.symm) hG⟩
  · obtain ⟨cI, hcI, hcn, psI, BcI, hcIty, hpsIlen, -⟩ :=
      Lean4Lean.List.Forall₂.forall_exists_r hctors c hc
    have hjc : (tI, cI) ∈ dI.ctors := VInductDecl.mem_ctors_iff.2 ⟨TI, hTI, hcI⟩
    have hcIc := henv.ctor_constant hind hjc
    rw [hcIty] at hcIc
    have hcIW := hTIW.2 cI hcI
    obtain ⟨psc, Dsc, hcIty', hpsc, -, -⟩ := hcIW.shape
    rw [hcIty, foralls_append] at hcIty'
    obtain ⟨rfl, -⟩ := VExpr.foralls_inj hcIty' (by rw [hpsIlen, hpsc.length_eq])
    have hH := happ hcIc (hpsc.mono hleI) ((hcIty ▸ hcIW.type).mono hleI)
    rw [← hcn] at hH
    exact ⟨_, hH⟩

end VInductiveType

namespace VInductDecl

/-- Each auxiliary constant of a translated block, replaced by the occurrence it stands for as a
function of the parameters `Ps`. -/
def nestedF (R : Name → Option VAuxHead) (Ps : List VExpr) : Name → Option VExpr :=
  fun c => (R c).map (·.lam Ps)

variable {R : Name → Option VAuxHead} {ren : Name → Option Name} {d : VInductDecl} {n : Nat}
  {ns : List VNested} {cname : Name → Name}

theorem mem_restoreNested_types {T' : VInductiveType} :
    T' ∈ (d.restoreNested R ren n ns cname).types ↔ ∃ j T, j < n ∧ d.types[j]? = some T ∧
      T' = T.restore R ren cname none := by
  simp only [restoreNested, List.mem_map, List.mem_take_iff_getElem, List.getElem_zipIdx]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    refine ⟨j, _, by simp at hj; omega, List.getElem?_eq_getElem (by simp at hj; omega), ?_⟩
    simp [nestedAt, show j < n by simp at hj; omega]
  · rintro ⟨j, T, hj, hT, rfl⟩
    have hjl := (List.getElem?_eq_some_iff.1 hT).1
    refine ⟨_, ⟨j, by simp; omega, rfl⟩, ?_⟩
    simp [nestedAt, hj, (List.getElem?_eq_some_iff.1 hT).2]

theorem mem_restoreNested_aux_of {k : Nat} {T : VInductiveType} {o : VNested}
    (hT : d.types[n + k]? = some T) (ho : ns[k]? = some o) :
    T.restore R ren cname (some o) ∈ (d.restoreNested R ren n ns cname).aux := by
  simp only [restoreNested, List.mem_map]
  have hl := (List.getElem?_eq_some_iff.1 hT).1
  refine ⟨(T, n + k), ?_, by simp [nestedAt, show ¬n + k < n by omega, ho]⟩
  rw [List.mem_iff_getElem?]
  refine ⟨k, ?_⟩
  rw [List.getElem?_drop, List.getElem?_zipIdx, hT]; simp

variable {venv E₁ E₀ : VEnv}

/-- The `RestoreEnv` a translated nested block's check gives, over a parameter context `Qs` of the
restored block: `E₁` has the translation's types, auxiliary ones included, `E₀` the restored
block's own types; each auxiliary constant is replaced by the occurrence it stands for, as a
function of the parameters (`nestedF`), typed in `E₀` from the restored block's `AuxWF`. -/
theorem RestoreSpec.restoreEnv (henv : venv.WF) (H : d.RestoreSpec R ren n ns cname)
    (hRfresh : ∀ c h, R c = some h → venv.constants c = none)
    (hrenfresh : ∀ c c', ren c = some c' → venv.constants c = none)
    (hRdom : ∀ c h, R c = some h → ∃ k T, d.types[n + k]? = some T ∧
      (c = T.name ∨ ∃ c' ∈ T.ctors, c = c'.name))
    (hP : venv.IsTele d.uvars [] d.params)
    (hty : ∀ T ∈ d.types, venv.IsType d.uvars [] T.type)
    (hE₁ : venv.addConstList d.typeConsts = some E₁)
    (hE₀ : venv.addConstList (d.restoreNested R ren n ns cname).typeConsts = some E₀)
    (hAux : ∀ T ∈ (d.restoreNested R ren n ns cname).aux, ∃ o, T.nested = some o ∧
      T.AuxWF E₀ (d.restoreNested R ren n ns cname) o)
    {Qs : List VExpr} (hQ : E₀.IsTele d.uvars [] Qs) (hQP : E₀.TeleDefEq d.uvars [] Qs d.params) :
    RestoreEnv E₁ E₀ d.uvars (nestedF R d.params) R (VLevel.params d.uvars) Qs.reverse := by
  have hO := henv.ordered
  -- what the environment before the block mentions is left alone
  have hfr {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) :
      e.ConstsSat fun c => R c = none ∧ ren c = none :=
    he.mono fun c hc => by
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      refine ⟨?_, ?_⟩
      · cases h : R c with
        | none => rfl
        | some _ => rw [hRfresh c _ h] at hci; cases hci
      · cases h : ren c with
        | none => rfl
        | some _ => rw [hrenfresh c _ h] at hci; cases hci
  have hfrF {e : VExpr} (he : e.ConstsSat (venv.constants · |>.isSome)) :
      e.ConstsSat (nestedF R d.params · = none) :=
    (hfr he).mono fun c hc => by simp [nestedF, hc.1]
  have hPC := VEnv.IsTele.constsSat hO hP trivial
  have hparams : (d.restoreNested R ren n ns cname).params = d.params := by
    simp only [restoreNested]
    exact (List.map_congr_left fun P hP' => restore_of_constsSat (hfr (hPC P hP'))).trans
      (List.map_id' _)
  have huvars : (d.restoreNested R ren n ns cname).uvars = d.uvars := rfl
  have hTC (T) (hT : T ∈ d.types) : T.type.ConstsSat (venv.constants · |>.isSome) := by
    obtain ⟨_, h⟩ := hty T hT; exact (h.constsSat hO trivial).1
  have hTrestore {T : VInductiveType} (hT : T ∈ d.types) : T.type.restore R ren = T.type :=
    restore_of_constsSat (hfr (by
      obtain ⟨_, h⟩ := hty T hT
      exact (h.constsSat hO trivial).1))
  have hle₀ := VEnv.addConstList_le hE₀
  have hE₀wf : E₀.WF := VEnv.WF.addConstList henv (fun p hp => by
    obtain ⟨T', hT', rfl⟩ := List.mem_map.1 hp
    obtain ⟨j, T, hj, hT, rfl⟩ := mem_restoreNested_types.1 hT'
    show venv.IsType d.uvars [] (T.type.restore R ren)
    rw [hTrestore (List.mem_of_getElem? hT)]
    exact hty T (List.mem_of_getElem? hT)) hE₀
  have hP₀ : E₀.IsTele d.uvars [] d.params := hP.mono hle₀
  have hPP₀ : OnCtx d.params.reverse (E₀.IsType d.uvars) := by simpa using hP₀.onCtx trivial
  -- the constants of `E₀` are not auxiliary
  have hE₀R : ∀ c, (E₀.constants c).isSome → R c = none := by
    intro c hc
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
    rcases VEnv.addConstList_constants_cases hE₀ hci with h | h
    · cases hR : R c with
      | none => rfl
      | some _ => rw [hRfresh c _ hR] at h; cases h
    · obtain ⟨T', hT', he⟩ := List.mem_map.1 h
      cases he
      obtain ⟨j, T, hj, hT, rfl⟩ := mem_restoreNested_types.1 hT'
      exact (H.own j T hj hT).1
  -- each auxiliary type's occurrence and constructors, typed over the parameters
  have haux : ∀ k T o, d.types[n + k]? = some T → ns[k]? = some o →
      (∀ a ∈ o.args, a.ClosedN d.params.length) ∧
      (∃ ps' X, T.type = .foralls ps' X ∧ E₀.TeleDefEq d.uvars [] ps' d.params ∧
        E₀.HasType d.uvars d.params.reverse (.appN (.const o.ind o.lvls) o.args) X) ∧
      ∀ c ∈ T.ctors, VExpr.WF E₀ d.uvars d.params.reverse
        (.appN (.const (cname c.name) o.lvls) o.args) := by
    intro k T o hT ho
    obtain ⟨o', ho', hA⟩ := hAux _ (mem_restoreNested_aux_of hT ho)
    cases ho'
    have hP' : E₀.IsTele (d.restoreNested R ren n ns cname).uvars []
        (d.restoreNested R ren n ns cname).params := by rw [hparams]; exact hP₀
    obtain ⟨hargsC, ⟨ps', X, hTty, hTD, hX⟩, hcs⟩ := hA.apps hE₀wf hP'
    rw [hparams] at hargsC hTD hX hcs
    refine ⟨hargsC, ⟨ps', X, ?_, hTD, hX⟩, fun c hc => ?_⟩
    · rw [← hTrestore (List.mem_of_getElem? hT)]; exact hTty
    · have := hcs (c.restore R ren cname) (List.mem_map_of_mem hc)
      exact this
  -- every auxiliary constant's replacement
  have hhead : ∀ c h, R c = some h → h.n = d.params.length ∧
      (∀ a ∈ h.args, a.ClosedN d.params.length) ∧
      VExpr.WF E₀ d.uvars d.params.reverse (.appN (.const h.name h.lvls) h.args) := by
    intro c h hc
    obtain ⟨k, T, hT, hcT⟩ := hRdom c h hc
    have hk : k < ns.length := by
      have := (List.getElem?_eq_some_iff.1 hT).1; rw [H.len] at this; omega
    obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem hk⟩
    obtain ⟨hRT, -, hRc⟩ := H.aux k T o hT ho
    obtain ⟨hargsC, ⟨_, _, -, -, hX⟩, hcs⟩ := haux k T o hT ho
    rcases hcT with rfl | ⟨c', hc', rfl⟩
    · rw [hRT] at hc; cases hc; exact ⟨rfl, hargsC, _, hX⟩
    · rw [(hRc c' hc').1] at hc; cases hc; exact ⟨rfl, hargsC, hcs c' hc'⟩
  -- the replacement, as a closed function of the parameters
  have hlam : ∀ c h, R c = some h → ∃ X,
      E₀.HasType d.uvars [] (h.lam d.params) (.foralls d.params X) ∧
      E₀.HasType d.uvars d.params.reverse (.appN (.const h.name h.lvls) h.args) X := by
    intro c h hc
    obtain ⟨-, -, X, hX⟩ := hhead c h hc
    have hX : E₀.HasType d.uvars d.params.reverse _ X := hX
    exact ⟨X, hP₀.lams (by simpa using hX), hX⟩
  have hclosed : ClosedConsts (nestedF R d.params) := by
    intro c r hr
    simp only [nestedF, Option.map_eq_some_iff] at hr
    obtain ⟨h, hc, rfl⟩ := hr
    obtain ⟨_, hX, -⟩ := hlam c h hc
    exact hX.closedN hE₀wf.ordered trivial
  -- the parameter context and what `E₀`'s judgments mention
  have hQC := VEnv.IsTele.constsSat hE₀wf.ordered hQ trivial
  have hE₀F {e : VExpr} (he : e.ConstsSat (E₀.constants · |>.isSome)) :
      e.ConstsSat (nestedF R d.params · = none) :=
    he.mono fun c hc => by simp [nestedF, hE₀R c hc]
  have hVC := hO.constsSat
  refine {
    wf := hE₀wf
    subst := ?_
    hFR := fun c hc => by simp [nestedF, hc]
    hR := fun c h hc => ?_
    ctx := by simpa using hQ.onCtx trivial
    ctx₀ := ?_ }
  · refine ⟨hclosed, fun c ci hci => ?_, fun df hdf => ?_, fun s b hs => ?_,
      fun s dd t T hs ht => ?_⟩
    · rcases VEnv.addConstList_constants_cases hE₁ hci with h | h
      · obtain ⟨u, hu⟩ := hVC.1 h
        refine .inl ⟨?_, hle₀.constants h, hfrF hu.1⟩
        have : R c = none := by
          cases hR : R c with
          | none => rfl
          | some _ => rw [hRfresh c _ hR] at h; cases h
        simp [nestedF, this]
      · obtain ⟨T, hT, he⟩ := List.mem_map.1 h
        cases he
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hT
        by_cases hjn : j < n
        · have hown := H.own j T hjn hj
          refine .inl ⟨by simp [nestedF, hown.1], ?_, hfrF (hTC T hT)⟩
          refine VEnv.addConstList_constants_of_mem hE₀ (List.mem_map.2
            ⟨_, mem_restoreNested_types.2 ⟨j, T, hjn, hj, rfl⟩, ?_⟩)
          simp [VInductiveType.restore, hTrestore hT]; rfl
        · obtain ⟨k, rfl⟩ : ∃ k, j = n + k := ⟨j - n, by omega⟩
          have hk : k < ns.length := by
            have := (List.getElem?_eq_some_iff.1 hj).1; rw [H.len] at this; omega
          obtain ⟨o, ho⟩ : ∃ o, ns[k]? = some o := ⟨_, List.getElem?_eq_getElem hk⟩
          obtain ⟨hRT, -, -⟩ := H.aux k T o hj ho
          obtain ⟨-, ⟨ps', X, hTty, hTD, hX⟩, -⟩ := haux k T o hj ho
          refine .inr ⟨VAuxHead.lam ⟨d.params.length, o.ind, o.lvls, o.args⟩ d.params,
            by simp [nestedF, hRT], ?_⟩
          show E₀.HasType d.uvars [] _ (T.type.replaceConst _)
          rw [replaceConst_of_constsSat (hfrF (hTC T hT)), hTty]
          have hXT := hX.isType hE₀wf.ordered hPP₀
          have hdef := VEnv.TeleDefEq.foralls hE₀wf (Γ := []) trivial hTD hP₀ (by simpa using hXT)
          exact (hP₀.lams (by simpa using hX)).defeqU_r hE₀wf trivial hdef.symm
    · rw [VEnv.addConstList_defeqs hE₁] at hdf
      refine ⟨by rw [VEnv.addConstList_defeqs hE₀]; exact hdf, ?_⟩
      obtain ⟨⟨h1, h2⟩, ⟨h3, -⟩⟩ := hVC.2 hdf
      exact ⟨hfrF h1, hfrF h3, hfrF h2⟩
    · rw [VEnv.addConstList_inducts hE₁] at hs
      rw [VEnv.addConstList_inducts hE₀]; exact hs
    · rw [VEnv.addConstList_inducts hE₁] at hs
      have hnone {c : Name} (hc : (venv.constants c).isSome) : nestedF R d.params c = none := by
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
        have : R c = none := by
          cases hR : R c with
          | none => rfl
          | some _ => rw [hRfresh c _ hR] at hci; cases hci
        simp [nestedF, this]
      refine ⟨hnone (by obtain ⟨_, h⟩ := henv.constants_of_inducts hs; rw [h]; rfl),
        fun c hc => ?_⟩
      have hjc : (t, c) ∈ dd.ctors := mem_ctors_iff.2 ⟨T, ht, by simp [hc]⟩
      refine ⟨hnone (by rw [henv.ctor_constant (henv.inducts_getElem hs ht) hjc]; rfl), ?_⟩
      obtain ⟨env₀, envT, h₀, hdd, hT, hle, -⟩ := henv.inducts hs
      have henvT : envT.WF := VEnv.WF.addConstList h₀ (fun p hp => by
        obtain ⟨T, hT, rfl⟩ := List.mem_map.1 hp
        exact (hdd.types T hT).1) hT
      have hcW := (hdd.ctors envT hT T (List.mem_append_left _ (List.mem_of_getElem? ht))).2 c
        (by simp [hc])
      obtain ⟨_, _, _, _, hfs, _⟩ := hcW.shape
      have hPd : envT.IsTele dd.uvars [] dd.params := hdd.params.mono (VEnv.addConstList_le hT)
      have hF := VEnv.IsTele.constsSat henvT.ordered (FieldsWF.tele hfs).1
        (by simpa using hPd.onCtx trivial)
      intro f hf
      refine hfrF ((hF _ (List.mem_map_of_mem hf)).mono fun c hc => ?_)
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.1 hc
      rw [hle.constants hci]; rfl
  · obtain ⟨hn, hargsC, -⟩ := hhead c h hc
    obtain ⟨X, hX, -⟩ := hlam c h hc
    have hlw := (hX.levelWF trivial).1
    have hPl := VEnv.IsTele.levelWF hP₀ trivial
    refine ⟨d.params, by simp [nestedF, hc], hn.symm, fun a ha => hn ▸ hargsC a ha, ?_, ?_⟩
    · rw [hlw.instL_id]; exact ⟨_, hX⟩
    · rw [List.map_congr_left fun P hP' => (hPl P hP').instL_id, List.map_id' _]
      exact VEnv.Ctx.SubstEq.id_teleDefEq hE₀wf hQP hP₀
  · rw [List.map_reverse]
    exact congrArg List.reverse <| (List.map_congr_left fun Q hQ' =>
      replaceConst_of_constsSat (hE₀F (hQC Q hQ'))).trans (List.map_id' _)

end VInductDecl

end Lean4Lean
