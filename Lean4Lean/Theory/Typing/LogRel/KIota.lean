import Lean4Lean.Theory.Typing.LogRel.Rules
import Lean4Lean.Theory.Typing.Iota

/-!
# Typed instances of the rules head reduction fires

Each defining equation of an environment is a closed equation `lams Bs L ≡ lams Bs R`. Given that
its bodies are typed under its binders (`VDefEq.BodyWF`), an instance at arguments typed for the
binders is `L ≡ R` at those arguments, by beta and the rule alone. The iota rule, the quotient's
rule and the K-like rule of a propositional type with large elimination are read off from it, with their checks (constructor parameters and levels, indices, the quotient's type and
relation) as explicit hypotheses: the logical relation supplies them by escape.

Nothing here uses uniqueness of typing or injectivity: the conversions are all at a fixed type.
-/

namespace Lean4Lean
open VExpr

/-- A defining equation whose sides are lambdas over common binders `Bs`, with bodies `L` and `R`
typed at `A` under them. -/
structure VDefEq.BodyWF (env : VEnv) (df : VDefEq) (Bs : List VExpr) (L R A : VExpr) : Prop where
  lhs : df.lhs = .lams Bs L
  rhs : df.rhs = .lams Bs R
  type : df.type = .foralls Bs A
  tele : env.IsTele df.uvars [] Bs
  hasL : env.HasType df.uvars Bs.reverse L A
  hasR : env.HasType df.uvars Bs.reverse R A

theorem VExpr.lams_inj : ∀ {As As' : List VExpr} {B B' : VExpr},
    VExpr.lams As B = .lams As' B' → As.length = As'.length → As = As' ∧ B = B'
  | [], [], _, _, h, _ => ⟨rfl, h⟩
  | _ :: _, _ :: _, _, _, h, hl => by
    simp only [lams, lam.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨rfl, rfl⟩ := VExpr.lams_inj h (by simpa using hl)
    exact ⟨rfl, rfl⟩

/-- The variable `as.length - 1 - i` under a substitution consing `as` is `as[i]`. -/
theorem VExpr.bvar_subst_consList (σ : Subst) (as : List VExpr) (i : Nat) (h : i < as.length) :
    (VExpr.bvar (as.length - 1 - i)).subst (σ.consList as) = as[i] := by
  rw [subst_bvar, Subst.consList_apply, dif_pos (by omega), List.getElem_reverse]
  congr 1; omega

namespace VEnv
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- An instance of a rule whose bodies are typed, at arguments typed for its binders: its
left-hand side applied to them is its left body at them, its two bodies agree there, and its
right-hand side applied to them is its right body there. -/
theorem IsDefEq.extra_body (henv : env.Ordered) (hΓ : OnCtx Γ (env.IsType U))
    {df : VDefEq} (hdf : env.defeqs df) {Bs : List VExpr} {L R A : VExpr}
    (hB : df.BodyWF env Bs L R A) {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = df.uvars) {as : List VExpr} (has : as.length = Bs.length)
    (W : Ctx.SubstEq env U Γ (Subst.id.consList as) (Subst.id.consList as)
      (Bs.map (·.instL ls)).reverse) :
    env.IsDefEq U Γ ((df.lhs.instL ls).appN as) ((L.instL ls).subst (Subst.id.consList as))
      ((A.instL ls).subst (Subst.id.consList as)) ∧
    env.IsDefEq U Γ ((L.instL ls).subst (Subst.id.consList as))
      ((R.instL ls).subst (Subst.id.consList as)) ((A.instL ls).subst (Subst.id.consList as)) ∧
    env.IsDefEq U Γ ((df.rhs.instL ls).appN as) ((R.instL ls).subst (Subst.id.consList as))
      ((A.instL ls).subst (Subst.id.consList as)) := by
  have hE := IsDefEq.extra (Γ := Γ) hdf hls hlen
  rw [hB.lhs, hB.rhs, hB.type, VEnv.lams_instL', VEnv.lams_instL',
    VEnv.foralls_instL'] at hE
  rw [hB.lhs, hB.rhs, VEnv.lams_instL', VEnv.lams_instL']
  have hlen' : as.length = (Bs.map (·.instL ls)).length := by simp [has]
  have hT : env.IsTele U [] (Bs.map (·.instL ls)) := by
    simpa using hB.tele.instL hls
  have hLt : env.HasType U ((Bs.map (·.instL ls)).reverse ++ []) (L.instL ls) (A.instL ls) := by
    simpa [List.map_reverse] using hB.hasL.instL hls
  have hRt : env.HasType U ((Bs.map (·.instL ls)).reverse ++ []) (R.instL ls) (A.instL ls) := by
    simpa [List.map_reverse] using hB.hasR.instL hls
  have W' : Ctx.SubstEq env U Γ (Subst.id.consList as) (Subst.id.consList as)
      ((Bs.map (·.instL ls)).reverse ++ []) := by simpa using W
  have hβL := IsDefEq.lams_beta henv hΓ (τ := .id) .nil hT hLt hlen' W'
  have hβR := IsDefEq.lams_beta henv hΓ (τ := .id) .nil hT hRt hlen' W'
  simp only [subst_id] at hβL hβR
  have hE' := IsDefEq.appN_substT (τ := .id) (Δ := []) (by simpa using hE) hlen' W'
  exact ⟨hβL, hβL.symm.trans (hE'.trans hβR), hβR⟩

end VEnv

namespace VInductDecl
variable (d : VInductDecl)

/-- The binders of the iota rule for constructor `c`: the recursor's binders up to its minor
premises, then `c`'s fields. -/
def iotaBinders (ls : List VLevel) (v : VLevel) (c : VConstructor) : List VExpr :=
  d.recBinders ls v ++ VExpr.liftTele (d.allTypes.length + d.allCtors.length)
    (c.fields.map (·.type.instL ls))

/-- The telescope of a recursor of `Ti`: its binders up to its minor premises, the type's indices,
and the major premise. -/
def recTele (ls : List VLevel) (v : VLevel) (Ti : VInductiveType) : List VExpr :=
  let n := d.params.length
  let T := d.allTypes.length
  let C := d.allCtors.length
  let k := Ti.indices.length
  d.recBinders ls v ++ VExpr.liftTele (T + C) (Ti.indices.map (·.instL ls)) ++
    [Ti.typeApp ls (VExpr.bvars n (T + C + k)) (VExpr.bvars k 0)]

theorem recType_eq_recTele (ls : List VLevel) (v : VLevel) (i : Nat) (Ti : VInductiveType) :
    d.recType ls v i Ti = .foralls (d.recTele ls v Ti)
      (.app (.appN (.bvar (1 + Ti.indices.length + d.allCtors.length +
        (d.allTypes.length - 1 - i))) (VExpr.bvars Ti.indices.length 1)) (.bvar 0)) := by
  simp only [recType, recTele, foralls_append]; rfl

/-- The iota rule's bodies are typed under its binders, at the recursor's own levels: what the
declaration's check gives, by inversion of its closed form. -/
def IotaBodyWF (env : VEnv) (q j : Nat) (c : VConstructor) : Prop :=
  ∃ L R A, (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q j c).BodyWF env
    (d.iotaBinders d.recLevels d.motiveLevel c) L R A

end VInductDecl


namespace VEnv
variable {env : VEnv} {U : Nat} {Γ : List VExpr}

/-- Iota reduction, typed, with its checks explicit. The recursor of a recorded block at levels
`lsR`, applied to parameters, motives, minor premises, indices `is` and a major premise `major`,
is the iota rule's right-hand side at the parameters, motives, minor premises and fields `fs`,
given:
- the arguments for the rule's binders are typed (`W`);
- the recursor's arguments are pairwise definitionally equal, along its telescope, to the rule's
  instance: the indices to `c`'s at the fields, the major premise to `c` at the block's levels,
  the parameters and the fields (`Wc`): this is where the constructor's levels and parameters
  and the indices are checked;
- the rule's bodies are typed (`hB`), a fact about the declaration. -/
theorem WF.iotaTyped (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl}
    {t₀ t q : Nat} {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (ht : d.allTypes[t]? = some Tj) (hq : d.allCtors[q]? = some (t, c))
    (hB : d.IotaBodyWF env q t c) {lsR : List VLevel} (hlsR : ∀ l ∈ lsR, l.WF U)
    (hlenR : lsR.length = d.recUVars) {ps Ms ms fs is : List VExpr} {major : VExpr}
    (hps : ps.length = d.params.length) (hMs : Ms.length = d.allTypes.length)
    (hms : ms.length = d.allCtors.length) (hfs : fs.length = c.fields.length)
    (his : is.length = Tj.indices.length)
    (W : Ctx.SubstEq env U Γ (Subst.id.consList (ps ++ Ms ++ ms ++ fs))
      (Subst.id.consList (ps ++ Ms ++ ms ++ fs))
      (d.iotaBinders (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) c).reverse)
    (Wc : Ctx.SubstEq env U Γ
      (Subst.id.consList (ps ++ Ms ++ ms ++
        (c.indices.map (·.instL (d.recLevels.map (·.inst lsR)))).map
          (·.subst ((Subst.id.consList ps).consList fs)) ++
        [Tj.ctorApp c (d.recLevels.map (·.inst lsR)) ps fs]))
      (Subst.id.consList (ps ++ Ms ++ ms ++ is ++ [major]))
      (d.recTele (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) Tj).reverse) :
    env.IsDefEq U Γ (.appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++ is ++ [major]))
      (.appN (d.iotaRule (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) lsR q t c).rhs
        (ps ++ Ms ++ ms ++ fs))
      (.app (.appN (Ms[t]?.getD default)
          ((c.indices.map (·.instL (d.recLevels.map (·.inst lsR)))).map
            (·.subst ((Subst.id.consList ps).consList fs))))
        (Tj.ctorApp c (d.recLevels.map (·.inst lsR)) ps fs)) := by
  have hlenR' := hlenR
  obtain ⟨hrecC, hiotas⟩ := henv.recBlock hs
  have htT : t < d.allTypes.length := (List.getElem?_eq_some_iff.1 ht).1
  have hMt : Ms[t]?.getD default = Ms[t]'(by omega) := by
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  rw [hMt]
  have hdf : env.defeqs (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q t c) :=
    hiotas _ (List.mem_map.2 ⟨((t, c), q), List.mk_mem_zipIdx_iff_getElem?.2 hq, rfl⟩)
  have hlenE : lsR.length =
      (d.iotaRule d.recLevels d.motiveLevel (VLevel.params d.recUVars) q t c).uvars := by
    simp [VInductDecl.iotaRule, hlenR']
  obtain ⟨L, R, A, hBW⟩ := hB
  obtain ⟨hl, hr, hty⟩ :=
    d.iotaRule_instL d.recLevels lsR (VLevel.params d.recUVars) d.motiveLevel q t c
  rw [VLevel.params_inst hlenR'] at hl hr hty
  generalize hlsB : d.recLevels.map (VLevel.inst lsR) = lsB at *
  generalize hv : d.motiveLevel.inst lsR = v at *
  have hlenB : (d.iotaBinders d.recLevels d.motiveLevel c).length =
      (d.iotaBinders lsB v c).length := by
    simp [VInductDecl.iotaBinders, VInductDecl.recBinders, VInductDecl.motiveTypes,
      VInductDecl.minorTypes]
  have hargs : ps ++ Ms ++ ms ++ fs = ps ++ (Ms ++ ms) ++ fs := by simp
  have e1 : (bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
      (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = ps := by
    rw [hargs, show d.allTypes.length + d.allCtors.length + c.fields.length =
      (Ms ++ ms).length + fs.length by simp [hMs, hms, hfs], ← hps, bvars_subst_consList_mid]
  have e2 : (bvars d.allTypes.length (d.allCtors.length + c.fields.length)).map
      (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = Ms := by
    rw [Subst.consList_append, Subst.consList_append, Subst.consList_append, ← hfs, ← hms,
      subst_bvars_consList_ge, ← Nat.zero_add ms.length, subst_bvars_consList_ge, ← hMs,
      subst_bvars_consList]
  have e3 : (bvars d.allCtors.length c.fields.length).map
      (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = ms := by
    rw [Subst.consList_append, Subst.consList_append, ← hfs, ← Nat.zero_add fs.length,
      subst_bvars_consList_ge, ← hms, subst_bvars_consList]
  have e4 : (bvars c.fields.length 0).map
      (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) = fs := by
    rw [Subst.consList_append, ← hfs, subst_bvars_consList]
  have e5 : (c.indices.map fun e => (instL lsB e).reseat (d.allTypes.length + d.allCtors.length)
        c.fields.length c.fields.length 0 0).map
      (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs))) =
      (c.indices.map (·.instL lsB)).map (·.subst ((Subst.id.consList ps).consList fs)) := by
    rw [List.map_map, List.map_map]
    refine List.map_congr_left fun e _ => ?_
    simp only [Function.comp_apply]
    rw [hargs, reseat_subst_consList _ _ (by simp [hMs, hms]) hfs, Subst.consList_append]
  have e6 : (VExpr.bvar (c.fields.length + d.allCtors.length + (d.allTypes.length - 1 - t))).subst
      (Subst.id.consList (ps ++ Ms ++ ms ++ fs)) = Ms[t]'(by omega) := by
    rw [show c.fields.length + d.allCtors.length + (d.allTypes.length - 1 - t) =
      (ps ++ Ms ++ ms ++ fs).length - 1 - (ps.length + t) by simp [hMs, hms, hfs]; omega,
      VExpr.bvar_subst_consList _ _ _ (by simp; omega)]
    simp [List.getElem_append_left, List.getElem_append_right, hMs, htT]
  have e6' : Subst.id.consList (ps ++ Ms ++ ms ++ fs)
      (c.fields.length + d.allCtors.length + (d.allTypes.length - 1 - t)) = Ms[t]'(by omega) := e6
  obtain ⟨Lc, hLc1, hLc2⟩ : ∃ Lc, (d.iotaRule lsB v lsR q t c).lhs =
      .lams (d.iotaBinders lsB v c) Lc ∧
      Lc.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs)) =
        .appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++
          (c.indices.map (·.instL lsB)).map (·.subst ((Subst.id.consList ps).consList fs)) ++
          [Tj.ctorApp c lsB ps fs]) := by
    refine ⟨_, rfl, ?_⟩
    simp only [subst_appN, List.map_append, List.map_cons, List.map_nil, VInductDecl.recConst,
      subst, VInductDecl.ctorAppAt_eq ht, VInductiveType.ctorApp_subst, e1, e2, e3, e4, e5]
  obtain ⟨Ac, hAc1, hAc2⟩ : ∃ Ac, (d.iotaRule lsB v lsR q t c).type =
      .foralls (d.iotaBinders lsB v c) Ac ∧
      Ac.subst (Subst.id.consList (ps ++ Ms ++ ms ++ fs)) =
        .app (.appN (Ms[t]'(by omega))
          ((c.indices.map (·.instL lsB)).map (·.subst ((Subst.id.consList ps).consList fs))))
          (Tj.ctorApp c lsB ps fs) := by
    refine ⟨_, rfl, ?_⟩
    simp only [subst_appN, subst, VInductDecl.ctorAppAt_eq ht, VInductiveType.ctorApp_subst,
      e1, e4, e5, e6']
  -- the rule's binders and bodies at `lsR`
  have hBs : (d.iotaBinders d.recLevels d.motiveLevel c).map (·.instL lsR) =
      d.iotaBinders lsB v c ∧ L.instL lsR = Lc := by
    refine VExpr.lams_inj ?_ (by simpa using hlenB)
    rw [← VEnv.lams_instL', ← hBW.lhs, hl, hLc1]
  have hA : A.instL lsR = Ac := by
    refine (VExpr.foralls_inj
      (As := (d.iotaBinders d.recLevels d.motiveLevel c).map (·.instL lsR)) ?_
      (by simpa using hlenB)).2
    rw [← VEnv.foralls_instL', ← hBW.type, hty, hAc1]
  have hlenF : (ps ++ Ms ++ ms ++ fs).length =
      (d.iotaBinders d.recLevels d.motiveLevel c).length := by
    simp [VInductDecl.iotaBinders, VInductDecl.recBinders, VInductDecl.motiveTypes,
      VInductDecl.minorTypes, hps, hMs, hms, hfs]
  obtain ⟨-, h2, h3⟩ := IsDefEq.extra_body henv.ordered hΓ hdf hBW hlsR hlenE hlenF
    (by rw [hBs.1]; exact W)
  rw [hr] at h3
  rw [hBs.2, hLc2, hA, hAc2] at h2
  rw [hA, hAc2] at h3
  -- the recursor's arguments against the rule's instance
  have hrc := HasType.const (Γ := Γ) (hrecC t Tj ht) hlsR hlenR
  rw [VInductDecl.recType_instL, hlsB, hv, VInductDecl.recType_eq_recTele] at hrc
  have hcil : c.indices.length = Tj.indices.length := by
    obtain ⟨_, envT, -, hd, hT, -⟩ := henv.inducts hs
    have hjc : (t, c) ∈ d.allCtors := List.mem_of_getElem? hq
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_allCtors_iff.1 hjc
    cases ht.symm.trans hT'
    exact ((hd.ctors envT hT Tj (List.mem_of_getElem? ht)).2 c hc).indices.1
  generalize hidx : (c.indices.map (·.instL lsB)).map
    (·.subst ((Subst.id.consList ps).consList fs)) = idx at *
  have hk : idx.length = Tj.indices.length := by rw [← hidx]; simp [hcil]
  have hlenT : (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs]).length =
      (d.recTele lsB v Tj).length := by
    simp [VInductDecl.recTele, VInductDecl.recBinders, VInductDecl.motiveTypes,
      VInductDecl.minorTypes, hps, hMs, hms, hk]
  have hlenT' : (ps ++ Ms ++ ms ++ is ++ [major]).length = (d.recTele lsB v Tj).length := by
    simp [VInductDecl.recTele, VInductDecl.recBinders, VInductDecl.motiveTypes,
      VInductDecl.minorTypes, hps, hMs, hms, his]
  have hcong := IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := [])
    (by rw [subst_id]; exact hrc) hlenT hlenT' (by simpa using Wc)
  have hbody : (((VExpr.bvar (1 + Tj.indices.length + d.allCtors.length +
        (d.allTypes.length - 1 - t))).appN (bvars Tj.indices.length 1)).app (.bvar 0)).subst
      (Subst.id.consList (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs])) =
      .app (.appN (Ms[t]'(by omega)) idx) (Tj.ctorApp c lsB ps fs) := by
    have hb1 := VExpr.bvar_subst_consList Subst.id (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs])
      (ps.length + t) (by simp; omega)
    rw [show (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs]).length - 1 - (ps.length + t) =
      1 + Tj.indices.length + d.allCtors.length + (d.allTypes.length - 1 - t) by
        simp [hMs, hms, hk]; omega] at hb1
    have hb2 : (bvars Tj.indices.length 1).map
        (·.subst (Subst.id.consList (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs]))) = idx := by
      rw [Subst.consList_append, show 1 = 0 + [Tj.ctorApp c lsB ps fs].length from rfl,
        subst_bvars_consList_ge, Subst.consList_append, ← hk, subst_bvars_consList]
    have hb1' : Subst.id.consList (ps ++ Ms ++ ms ++ idx ++ [Tj.ctorApp c lsB ps fs])
        (1 + Tj.indices.length + d.allCtors.length + (d.allTypes.length - 1 - t)) =
        Ms[t]'(by omega) := by
      refine hb1.trans ?_
      simp [List.getElem_append_left, List.getElem_append_right, hMs, htT]
    simp only [subst, subst_appN, hb2, hb1']
    rw [Subst.consList_append]; rfl
  rw [hbody] at hcong
  exact hcong.symm.trans (h2.trans h3.symm)

/-- The last entry of a recursor's telescope, the major premise's type, at its arguments. -/
theorem typeApp_subst_recArgs (Tj : VInductiveType) (lsB : List VLevel) (n nT nC : Nat)
    {ps Ms ms idx : List VExpr} (hps : ps.length = n) (hMs : Ms.length = nT)
    (hms : ms.length = nC) :
    (Tj.typeApp lsB (bvars n (nT + nC + idx.length)) (bvars idx.length 0)).subst
      (Subst.id.consList (ps ++ Ms ++ ms ++ idx)) = Tj.typeApp lsB ps idx := by
  rw [VInductiveType.typeApp_subst]
  congr 1
  · rw [show ps ++ Ms ++ ms ++ idx = ps ++ (Ms ++ ms) ++ idx by simp,
      show nT + nC + idx.length = (Ms ++ ms).length + idx.length by simp [hMs, hms], ← hps,
      bvars_subst_consList_mid]
  · rw [Subst.consList_append, subst_bvars_consList]

/-- K-like reduction, typed. The recursor of a type in `Prop` with large elimination, applied to
parameters, motives, minor premises, indices `is` and any proof `h` of the type at them, is the
iota rule's right-hand side at fields `fs`, given the iota rule's typing (`hB`, `W`) and:
- the recursor's arguments up to the indices are pairwise definitionally equal to the iota rule's
  instance, the indices to the constructor's at `fs` (`Wpre`): the index check;
- the constructor at `fs` is a term of the type at those indices (`hX`), and the type at `is` is a
  proposition of which `h` is a proof (`hP`, `hh`).
Proof irrelevance then makes `h` the constructor application. -/
theorem WF.kIotaTyped (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {d : VInductDecl}
    {t₀ t q : Nat} {Tj : VInductiveType} {c : VConstructor} (hs : env.inducts s = some (d, t₀))
    (ht : d.allTypes[t]? = some Tj) (hq : d.allCtors[q]? = some (t, c))
    (hB : d.IotaBodyWF env q t c) {lsR : List VLevel} (hlsR : ∀ l ∈ lsR, l.WF U)
    (hlenR : lsR.length = d.recUVars) {ps Ms ms fs is : List VExpr} {h : VExpr}
    (hps : ps.length = d.params.length) (hMs : Ms.length = d.allTypes.length)
    (hms : ms.length = d.allCtors.length) (hfs : fs.length = c.fields.length)
    (his : is.length = Tj.indices.length)
    (W : Ctx.SubstEq env U Γ (Subst.id.consList (ps ++ Ms ++ ms ++ fs))
      (Subst.id.consList (ps ++ Ms ++ ms ++ fs))
      (d.iotaBinders (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) c).reverse)
    (Wpre : Ctx.SubstEq env U Γ
      (Subst.id.consList (ps ++ Ms ++ ms ++
        (c.indices.map (·.instL (d.recLevels.map (·.inst lsR)))).map
          (·.subst ((Subst.id.consList ps).consList fs))))
      (Subst.id.consList (ps ++ Ms ++ ms ++ is))
      (d.recBinders (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) ++
        VExpr.liftTele (d.allTypes.length + d.allCtors.length)
          (Tj.indices.map (·.instL (d.recLevels.map (·.inst lsR))))).reverse)
    (hX : env.HasType U Γ (Tj.ctorApp c (d.recLevels.map (·.inst lsR)) ps fs)
      (Tj.typeApp (d.recLevels.map (·.inst lsR)) ps
        ((c.indices.map (·.instL (d.recLevels.map (·.inst lsR)))).map
          (·.subst ((Subst.id.consList ps).consList fs)))))
    (hP : env.HasType U Γ (Tj.typeApp (d.recLevels.map (·.inst lsR)) ps is) (.sort .zero))
    (hh : env.HasType U Γ h (Tj.typeApp (d.recLevels.map (·.inst lsR)) ps is)) :
    env.IsDefEq U Γ (.appN (.const (d.recName t) lsR) (ps ++ Ms ++ ms ++ is ++ [h]))
      (.appN (d.iotaRule (d.recLevels.map (·.inst lsR)) (d.motiveLevel.inst lsR) lsR q t c).rhs
        (ps ++ Ms ++ ms ++ fs))
      (.app (.appN (Ms[t]?.getD default)
          ((c.indices.map (·.instL (d.recLevels.map (·.inst lsR)))).map
            (·.subst ((Subst.id.consList ps).consList fs))))
        (Tj.ctorApp c (d.recLevels.map (·.inst lsR)) ps fs)) := by
  refine henv.iotaTyped hΓ hs ht hq hB hlsR hlenR hps hMs hms hfs his W ?_
  obtain ⟨hrecC, -⟩ := henv.recBlock hs
  have hcil : c.indices.length = Tj.indices.length := by
    obtain ⟨_, envT, -, hd, hT, -⟩ := henv.inducts hs
    obtain ⟨T', hT', hc⟩ := VInductDecl.mem_allCtors_iff.1 (List.mem_of_getElem? hq)
    cases ht.symm.trans hT'
    exact ((hd.ctors envT hT Tj (List.mem_of_getElem? ht)).2 c hc).indices.1
  generalize hlsB : d.recLevels.map (·.inst lsR) = lsB at *
  generalize hv : d.motiveLevel.inst lsR = v at *
  generalize hidx : (c.indices.map (·.instL lsB)).map
    (·.subst ((Subst.id.consList ps).consList fs)) = idx at *
  have hk : idx.length = Tj.indices.length := by rw [← hidx]; simp [hcil]
  -- the major premise's type, as an entry of the recursor's telescope
  have hrc := HasType.const (Γ := []) (hrecC t Tj ht) hlsR hlenR
  rw [VInductDecl.recType_instL, hlsB, hv, VInductDecl.recType_eq_recTele] at hrc
  have hTele := (IsType.foralls_inv henv.ordered (Γ := []) (IsDefEq.isType henv.ordered (Γ := []) trivial hrc)).1
  simp only [VInductDecl.recTele] at hTele
  obtain ⟨hpre, hlast⟩ := IsTele.append_inv hTele
  cases hlast with | cons hA _ =>
  obtain ⟨u, hA⟩ := hA
  rw [List.append_nil] at hA
  have hpreΓ := hpre.onCtx trivial
  rw [List.append_nil] at hpreΓ
  have hTD := hA.substDF henv.ordered hpreΓ hΓ Wpre
  have hlenP : ps.length = d.params.length := hps
  rw [← hk, ← hps, ← hMs, ← hms] at hTD
  have e1 := typeApp_subst_recArgs Tj lsB ps.length Ms.length ms.length (idx := idx) rfl rfl rfl
  have e2 := typeApp_subst_recArgs Tj lsB ps.length Ms.length ms.length (idx := is) rfl rfl rfl
  rw [his, ← hk] at e2
  rw [e1, e2] at hTD
  -- the constructor application is `h`, by proof irrelevance
  have hXh : env.IsDefEq U Γ (Tj.ctorApp c lsB ps fs) h (Tj.typeApp lsB ps idx) :=
    .defeqDF hTD.symm (.proofIrrel hP (.defeqDF hTD hX) hh)
  simp only [VInductDecl.recTele, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append]
  rw [Subst.consList_concat, Subst.consList_concat]
  refine .cons (by rw [← List.reverse_append]; exact Wpre) (by rw [← List.reverse_append]; exact hA) ?_
  show env.IsDefEq U Γ (Tj.ctorApp c lsB ps fs) h (VExpr.subst _ (Subst.id.consList _))
  rw [← hk, ← hps, ← hMs, ← hms, e1]
  exact hXh


/-- The quotient's computation rule, typed, with its checks explicit: `Quot.lift` at levels
`[u, v]` applied to `α r β f h` and `q` is `f a`, given that the rule's bodies are typed (`hB`), the
arguments for its binders are typed (`W`), and `q` is pairwise definitionally equal, along
`Quot.lift`'s telescope, to `Quot.mk` at `u`, `α`, `r` and `a` (`Wc`): this is where `Quot.mk`'s
level, type and relation are checked. -/
theorem WF.quotTyped (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U)) (hdf : env.defeqs quotDefEq)
    (hlift : env.constants ``Quot.lift = some quotLiftConst)
    (hB : ∃ L R A, quotDefEq.BodyWF env (QuotRed.liftBinders ++ [VExpr.bvar 4]) L R A)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U) {α r β f h q a : VExpr}
    (W : Ctx.SubstEq env U Γ (Subst.id.consList [α, r, β, f, h, a])
      (Subst.id.consList [α, r, β, f, h, a])
      ((QuotRed.liftBinders ++ [VExpr.bvar 4]).map (·.instL [u, v])).reverse)
    (Wc : Ctx.SubstEq env U Γ
      (Subst.id.consList [α, r, β, f, h, .appN (.const ``Quot.mk [u]) [α, r, a]])
      (Subst.id.consList [α, r, β, f, h, q])
      ((QuotRed.liftBinders ++
          [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).map
        (·.instL [u, v])).reverse) :
    env.IsDefEq U Γ (.appN (.const ``Quot.lift [u, v]) [α, r, β, f, h, q]) (.app f a) β := by
  have hls : ∀ l ∈ [u, v], l.WF U := by simp [hu, hv]
  obtain ⟨L, R, A, hBW⟩ := hB
  have hL : L = .appN (.const ``Quot.lift [.param 0, .param 1])
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
        .appN (.const ``Quot.mk [.param 0]) [.bvar 5, .bvar 4, .bvar 0]] :=
    (VExpr.lams_inj (hBW.lhs.symm.trans (by rw [QuotRed.quotDefEq_eq])) rfl).2
  have hR : R = .app (.bvar 2) (.bvar 0) :=
    (VExpr.lams_inj (hBW.rhs.symm.trans (by rw [QuotRed.quotDefEq_eq])) rfl).2
  have hA : A = .bvar 3 :=
    (VExpr.foralls_inj (hBW.type.symm.trans (by rw [QuotRed.quotDefEq_eq])) rfl).2
  subst hL hR hA
  obtain ⟨-, h2, -⟩ := IsDefEq.extra_body henv.ordered hΓ hdf hBW hls rfl
    (as := [α, r, β, f, h, a]) rfl W
  simp [instL, VLevel.inst, Subst.consList, Subst.cons] at h2
  have hc := HasType.const (Γ := Γ) hlift hls rfl
  rw [QuotRed.quotLiftConst_eq] at hc
  simp only at hc
  have hcong := IsDefEq.appN_substTDF (τ := .id) (τ' := .id) (Δ := [])
    (As := (QuotRed.liftBinders ++
      [VExpr.app (.app (.const ``Quot [.param 0]) (.bvar 4)) (.bvar 3)]).map (·.instL [u, v]))
    (as := [α, r, β, f, h, .appN (.const ``Quot.mk [u]) [α, r, a]]) (bs := [α, r, β, f, h, q])
    (by rw [subst_id, ← VEnv.foralls_instL']; exact hc) rfl rfl
    (by simpa using Wc)
  simp [instL, Subst.consList, Subst.cons] at hcong
  exact hcong.symm.trans h2

end VEnv
end Lean4Lean
