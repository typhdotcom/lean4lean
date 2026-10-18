import Lean4Lean.Theory.Typing.LogRel.AdeqCtor
import Lean4Lean.Theory.Typing.LogRel.AdeqIndTy

/-!
# Projections of structure values typed along the constructor's telescope

The projections of two definitionally equal terms of a structure type are definitionally equal,
each at its declared domain instantiated by the projections before it: the telescope the relation
reads a structure's fields along.
-/

namespace Lean4Lean
open VExpr

namespace LogRel
open LE_Interp

variable {env : VEnv} {U : Nat} {Γ : List VExpr}

theorem projs_take_succ (s : Name) (e : VExpr) {j k : Nat} (h : j < k) :
    (VExpr.projs s k e).take (j + 1) = VExpr.projs s j e ++ [.proj s j e] := by
  rw [VEnv.projs_take' s e (by omega)]
  simp [VExpr.projs, List.range_succ]

theorem projs_drop (s : Name) (e : VExpr) {j k : Nat} (h : j < k) :
    (VExpr.projs s k e).drop j = .proj s j e :: (VExpr.projs s k e).drop (j + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]
  simp [VExpr.projs]

/-- The projections of definitionally equal values of a structure type, along the constructor's
declared domains `Ds` (at levels `ls`) with the parameters `As` substituted. -/
theorem projsTyped_struct (henvW : env.WF) (hΓ : OnCtx Γ (env.IsType U)) {s : Name}
    {d : VInductDecl} {t : Nat} {T : VInductiveType} {c : VConstructor}
    (hs : env.inducts s = some (d, t)) (hT : d.types[t]? = some T) (hc : T.ctors = [c])
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.uvars) {Ds : List VExpr}
    (hV : ∀ k D (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      env.IsDefEq d.uvars (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse) D f.type
        (.sort f.level))
    (hVT : env.IsTele d.uvars d.params.reverse (c.fields.map (·.type)))
    (hDl : Ds.length = c.fields.length)
    (hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (d.params.length + j))
    {As I : List VExpr} (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (W : VEnv.Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (hP : ∀ k < c.fields.length, d.ProjAllowed c ls k) {M' N' : VExpr}
    (hx : env.IsDefEq U Γ M' N' (.appN (.const s ls) (As ++ I))) (B : VExpr) :
    ProjsTyped env U Γ ((VExpr.foralls (Ds.map (·.instL ls)) B).subst (Subst.id.consList As))
      (VExpr.projs s c.fields.length M') (VExpr.projs s c.fields.length N') := by
  have henv := henvW.ordered
  have hF := henvW.projFacts hs hT hc
  obtain ⟨u, hS⟩ := hx.isType henv hΓ
  have hPC (k : Nat) (f : VField) (hf : c.fields[k]? = some f) :=
    VEnv.projCongr henv hΓ hs hT hc hF hls hlen hA hI hA hI W hS hx k f hf
      (hP k (List.getElem?_eq_some_iff.1 hf).1)
  have hPC' (k : Nat) (f : VField) (hf : c.fields[k]? = some f) :=
    VEnv.projCongr henv hΓ hs hT hc hF hls hlen hA hI hA hI W hS hx.hasType.1 k f hf
      (hP k (List.getElem?_eq_some_iff.1 hf).1)
  have hDP := VEnv.declDom_projs henv hΓ hls hV hVT W (ms := VExpr.projs s c.fields.length M')
    (by simp) fun k h => by
      have hk : k < c.fields.length := by simpa using h
      obtain ⟨f, hf⟩ : ∃ f, c.fields[k]? = some f := ⟨_, List.getElem?_eq_getElem hk⟩
      simpa [VExpr.projs] using (hPC' k f hf).2
  -- the walk along the telescope, after the first `j` fields
  suffices H : ∀ r j, j + r = c.fields.length →
      ProjsTyped env U Γ ((VExpr.foralls ((Ds.map (·.instL ls)).drop j) B).subst
        (Subst.id.consList (As ++ (VExpr.projs s c.fields.length M').take j)))
        ((VExpr.projs s c.fields.length M').drop j) ((VExpr.projs s c.fields.length N').drop j) by
    simpa using H c.fields.length 0 (by omega)
  intro r
  induction r with
  | zero =>
    intro j hj
    have h1 : (VExpr.projs s c.fields.length M').drop j = [] := List.drop_of_length_le (by simp; omega)
    have h2 : (VExpr.projs s c.fields.length N').drop j = [] := List.drop_of_length_le (by simp; omega)
    rw [h1, h2]; trivial
  | succ r ih =>
    intro j hj
    have hjn : j < c.fields.length := by omega
    obtain ⟨f, hf⟩ : ∃ f, c.fields[j]? = some f := ⟨_, List.getElem?_eq_getElem hjn⟩
    obtain ⟨D, hD⟩ : ∃ D, Ds[j]? = some D := ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [projs_drop s M' hjn, projs_drop s N' hjn,
      List.drop_eq_getElem_cons (by simp; omega)]
    simp only [List.getElem_map, VExpr.foralls, VExpr.subst]
    have hDj : Ds[j]'(by omega) = D := Option.some.inj ((List.getElem?_eq_getElem _).symm.trans hD)
    refine ⟨_, _, .rfl, ?_, ?_⟩
    · -- the `j`th projections, at the declared domain
      obtain ⟨-, -, h3⟩ := hDP j (by simpa using hjn) D f hD hf
      have e1 : ((D.instL ls).subst (Subst.id.consList (As ++
          (VExpr.projs s c.fields.length M').take j))) =
          (D.instL ls).subst (Subst.dflt.consList (As ++ VExpr.projs s j M')) := by
        rw [VEnv.projs_take' s M' (Nat.le_of_lt hjn)]
        refine ((hDcl j D hD).instL.subst_congr fun i hi => ?_)
        rw [Subst.consList_lt _ _ _ (by simp; omega), Subst.consList_lt _ _ _ (by simp; omega)]
      rw [hDj, e1]
      exact .defeqDF h3 (hPC j f hf).2
    · -- the rest of the telescope
      rw [subst_lift_inst]
      have e2 : (Subst.id.consList (As ++ (VExpr.projs s c.fields.length M').take j)).cons
          (.proj s j M') =
          Subst.id.consList (As ++ (VExpr.projs s c.fields.length M').take (j + 1)) := by
        rw [projs_take_succ s M' hjn, VEnv.projs_take' s M' (Nat.le_of_lt hjn), ← List.append_assoc,
          Subst.consList_append]
        simp only [Subst.consList_append, Subst.consList]
      rw [e2]
      exact ih (j + 1) (by omega)

/-- What `typeFormer_sat` asks of a recorded type former (`HY`): its applications to arguments typed
along its telescope have stuck values whose projections are typed along the constructor's
telescope. Uniqueness of typing in the environment with the block's types (`hIT`) gives the
fields' declared domains as their views. -/
theorem structTy_spine [ShapeEnv] [AxInterp] (hM : ModelEnv env) (henvW : env.WF)
    {Γ₀ : List VExpr} (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    {E envT : VEnv} {d : VInductDecl} (hd : d.WF E) (h1 : E.addConstList d.typeConsts = some envT)
    (hTle : envT ≤ env) (hTo : envT.Ordered) (hIT : envT.Inj)
    {T : VInductiveType} {t : Nat} (hs : env.inducts T.name = some (d, t))
    (hT : d.types[t]? = some T)
    (hcC : ∀ c' ∈ T.ctors, env.constants c'.name = some ⟨d.uvars, c'.type⟩)
    (hc1 : ∀ cv ∈ T.ctors, IsStruct cv.name = true → T.ctors = [cv])
    {ls ls₃ : List VLevel} (hls₃ : ∀ l ∈ ls₃, l.WF U) (e₃ : List.Forall₂ (· ≈ ·) ls ls₃)
    (hlen : ls.length = d.uvars) (k : Nat) {F : VExpr} {σ : VExpr.Subst}
    (hF : ConstAt U T.name ls F)
    (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ
      (((d.params ++ T.indices).map (·.instL ls₃)).reverse ++ Γ₀)) :
    StructTy env U Γ₀ (typeHeadOf T.name k T) (spineAt F (d.params ++ T.indices).length σ) := by
  have henv := henvW.ordered
  obtain ⟨l, el, hl, rfl⟩ := hF
  show StructTy env U Γ₀ _ ((VExpr.const T.name l).appN
    ((VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ)))
  have hll : l.length = d.uvars := by rw [← List.Forall₂.length_eq el, hlen]
  have hTm : T ∈ d.types := List.mem_of_getElem? hT
  have hn : Inert env T.name := Inert.of_role hM.roles (fun hdf e => henvW.rule_lhs_params hdf e)
    (ConstArity.indTy hs hT) (fun _ h => by cases h) (fun _ _ h => by cases h) (fun h => by cases h)
  -- the arguments, typed along the parameters at the levels `l`
  generalize hargs : (VExpr.bvars (d.params ++ T.indices).length 0).map (·.subst σ) = args
  have hΔ := henvW.blockTele_onCtx hs hT
  have hΔ₃ : OnCtx (((d.params ++ T.indices).map (·.instL ls₃)).reverse) (env.IsType U) := by
    rw [← List.map_reverse]; exact hΔ.instL hls₃
  have W1 := Ctx.SubstEq.vals henv hΔ₃ W
  rw [List.length_reverse, List.length_map, ← List.map_reverse] at W1
  have W2 := Ctx.SubstEq.instL_congr henv hΓ₀ hls₃ hl
    (levels_equiv_trans (levels_equiv_symm e₃) el) hΔ W1
  have hcl : CtxClosed (((d.params ++ T.indices).reverse).map (·.instL l)) :=
    (hΔ.instL hl).ctxClosed henv
  have hlenA : args.length = (d.params ++ T.indices).length := by
    rw [← hargs]; simp [VExpr.bvars]
  have hval : ∀ i < ((d.params ++ T.indices).reverse.map (·.instL l)).length,
      Subst.id.consList args i = Subst.dflt.consList args i := by
    intro i hi
    simp only [List.length_map, List.length_reverse] at hi
    rw [Subst.consList_lt _ _ _ (by rw [hlenA]; exact hi),
      Subst.consList_lt _ _ _ (by rw [hlenA]; exact hi)]
  rw [hargs] at W2
  have W3 := Ctx.SubstEq.congr_closed (τ := Subst.dflt.consList args)
    (τ' := Subst.dflt.consList args) hcl hval hval W2
  have hAl : (args.take d.params.length).length = d.params.length := by
    simp [hlenA]
  have hIl : (args.drop d.params.length).length = T.indices.length := by
    simp [hlenA]
  have Wp : VEnv.Ctx.SubstEq env U Γ₀ (Subst.dflt.consList (args.take d.params.length))
      (Subst.dflt.consList (args.take d.params.length)) (d.params.map (·.instL l)).reverse := by
    rw [← List.take_append_drop d.params.length args, Subst.consList_append] at W3
    simp only [List.map_reverse, List.reverse_append, List.map_append] at W3
    exact VEnv.Ctx.SubstEq.dropList (by simp [hIl]) (by simp [hIl]) W3
  -- the constructor's declared telescope
  intro c i k' hSO hidx har
  obtain ⟨hil, hie, -⟩ := List.idxOf?_eq_some_iff.1 hidx
  have hil' : i < T.ctors.length := by simpa using hil
  have hcv : T.ctors[i] ∈ T.ctors := List.getElem_mem hil'
  have hce : T.ctors[i].name = c := by simpa using hie
  have hk' : k' = T.ctors[i].fields.length := by
    simp only [List.getElem?_map, List.getElem?_eq_getElem hil', Option.map_some] at har
    exact (Option.some.inj har).symm
  subst hce hk'
  refine ⟨_, hcC _ hcv, fun lsA AsA hred hwA M' N' _ _ _ _ hx => ?_⟩
  obtain ⟨-, rfl, rfl⟩ := appN_const_inj (StepS.of_whnf hn.whnf hred)
  generalize T.ctors[i] = cv at hcv hSO hcC
  obtain ⟨hIS, hPA⟩ := hSO
  have hc := hc1 cv hcv hIS
  have hP : ∀ k < cv.fields.length, d.ProjAllowed cv l k :=
    fun k hk => hPA l args .rfl hn.whnf d t T cv hs hT hcv rfl k hk
  -- the constructor's shape, views and closedness in the environment with the block's types
  have hTA : T ∈ d.allTypes := VInductDecl.mem_allTypes_of_types hTm
  have hcW := (hd.ctors envT h1 T hTA).2 cv hcv
  obtain ⟨ps, Ds, hshape, hPD, hFW, -, -⟩ := hcW.shape
  have hpl : ps.length = d.params.length := hPD.length_eq
  have hDl : Ds.length = cv.fields.length := hFW.length
  have hP₀ : envT.IsTele d.uvars [] d.params := hd.params.mono (VEnv.addConstList_le h1)
  have onP : OnCtx d.params.reverse (envT.IsType d.uvars) := by
    simpa using hP₀.onCtx (Γ := []) trivial
  have hV := fun k D f hD hf =>
    ((VInductDecl.FieldsWF.atSort hIT hFW onP k D f hD hf).1.mono hTle)
  have hVT := hFW.viewsTele.mono hTle
  obtain ⟨hTe₀, -⟩ := VEnv.IsType.foralls_inv hTo (hshape ▸ hcW.type)
  have hclT := VEnv.IsTele.closedN hTo hTe₀ trivial
  have hDcl : ∀ j (D : VExpr), Ds[j]? = some D → D.ClosedN (d.params.length + j) := by
    intro j D hD
    have := hclT (ps.length + j) D (by rw [List.getElem?_append_right (by omega)]; simpa using hD)
    simpa [hpl] using this
  have hnone : T.nested = none := (hd.types T hTm).2
  have hx' : env.IsDefEq U Γ₀ M' N'
      (.appN (.const T.name l) (args.take d.params.length ++ args.drop d.params.length)) := by
    rwa [List.take_append_drop]
  have H := projsTyped_struct henvW hΓ₀ hs hT hc hl hll hV hVT hDl hDcl hAl hIl Wp hP hx'
    ((T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length cv.fields.length)
      cv.indices).instL l)
  -- the telescope `ctorTeleAt` reads is the declared one with the parameters substituted
  have hpc : piCount cv.type = d.params.length + cv.fields.length := by
    rw [hshape, piCount_foralls, VInductiveType.typeApp_of_none hnone, piCount_appN_const]
    simp [hpl, hDl]
  have hte : ctorTeleAt ⟨d.uvars, cv.type⟩ cv.fields.length l args =
      (VExpr.foralls (Ds.map (·.instL l))
        ((T.typeApp (VLevel.params d.uvars) (VExpr.bvars d.params.length cv.fields.length)
          cv.indices).instL l)).subst (Subst.id.consList (args.take d.params.length)) := by
    simp only [ctorTeleAt, hpc, Nat.add_sub_cancel]
    rw [hshape, VEnv.foralls_instL', List.map_append, foralls_append]
    exact piInst_foralls _ _ _ (by simp [hAl, hpl])
  rw [hte]; exact H

end LogRel
end Lean4Lean
