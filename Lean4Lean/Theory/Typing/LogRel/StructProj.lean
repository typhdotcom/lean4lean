import Lean4Lean.Theory.Typing.LogRel.Inv
import Lean4Lean.Theory.Typing.Projection

/-!
# Projections of a structure's constructor application

A constructor's fields typed along its declared domains are typed along its views, given
uniqueness of typing in the environment the block was checked in; and the projections of the
constructor application are its fields, at the declared domains instantiated by the projections.
-/

namespace Lean4Lean
open VExpr

namespace VInductDecl
variable {env : VEnv} {d : VInductDecl}

/-- Each field's declared domain is its view, as types of the field's sort, given uniqueness of
typing. -/
theorem FieldsWF.atSort (hI : env.Inj) : ∀ {Γ k Ds fs}, d.FieldsWF env Γ k Ds fs →
    OnCtx Γ (env.IsType d.uvars) → ∀ j (D : VExpr) (f : VField), Ds[j]? = some D →
      fs[j]? = some f →
      env.IsDefEq d.uvars (((fs.take j).map (·.type)).reverse ++ Γ) D f.type (.sort f.level) ∧
      env.HasType d.uvars (((fs.take j).map (·.type)).reverse ++ Γ) f.type (.sort f.level)
  | _, _, _, _, .nil, _, _, _, _, h, _ => by simp at h
  | Γ, _, _ :: _, _ :: _, .cons hD hf _ _ _ _ rest, hΓ, j, D', f', h1, h2 => by
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h1 h2; subst h1; subst h2
      obtain ⟨A, hDA⟩ := hD
      obtain ⟨u, hu⟩ := hI.uniq hΓ hDA hf
      simpa using And.intro (VEnv.IsDefEq.defeqDF hu hDA) hf
    | succ j =>
      simp only [List.getElem?_cons_succ] at h1 h2
      have := FieldsWF.atSort hI rest ⟨hΓ, _, hf⟩ j D' f' h1 h2
      simpa [List.take_succ_cons] using this

/-- The views of a constructor's fields form a telescope over the parameters. -/
theorem FieldsWF.viewsTele : ∀ {Γ k Ds fs}, d.FieldsWF env Γ k Ds fs →
    env.IsTele d.uvars Γ (fs.map (·.type))
  | _, _, _, _, .nil => .nil
  | _, _, _ :: _, _ :: _, .cons _ hf _ _ _ _ rest => .cons ⟨_, hf⟩ (FieldsWF.viewsTele rest)

end VInductDecl

namespace VEnv
open VConstructor

variable {env : VEnv} {U : Nat} {Γ : List VExpr} {d : VInductDecl} {c : VConstructor}
  {ls : List VLevel}

/-- The substitution of parameters and earlier values for a prefix of a constructor's views. -/
theorem views_substEq (hls : ∀ l ∈ ls, l.WF U)
    (hVT : env.IsTele d.uvars d.params.reverse (c.fields.map (·.type))) {As vs : List VExpr}
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (k : Nat) (hk : k ≤ vs.length) (hkf : k ≤ c.fields.length)
    (hv : ∀ j (h : j < vs.length) (f : VField), j < k → c.fields[j]? = some f →
      env.HasType U Γ vs[j] ((f.type.instL ls).subst (Subst.dflt.consList (As ++ vs.take j)))) :
    Ctx.SubstEq env U Γ (Subst.dflt.consList (As ++ vs.take k))
      (Subst.dflt.consList (As ++ vs.take k))
      (((c.fields.take k).map (·.type.instL ls)).reverse ++ (d.params.map (·.instL ls)).reverse) := by
  have hT := (IsTele.append_inv (As := (c.fields.take k).map (·.type))
    (Bs := (c.fields.drop k).map (·.type)) (by rw [← List.map_append, List.take_append_drop]; exact hVT)).1
  have hT' := hT.instL hls
  simp only [List.map_reverse, List.map_map] at hT'
  rw [Subst.consList_append]
  refine Ctx.SubstEq.ofGetElem W k (by simp; omega) (by simpa [Function.comp_def] using hT')
    (by simp; omega) fun r h h' => ?_
  simp only [List.length_take] at h h'
  have hrk : r < k := (Nat.lt_min.1 h).1
  have hr : r < vs.length := by omega
  have hrf : r < c.fields.length := by omega
  have := hv r hr _ hrk (List.getElem?_eq_getElem hrf)
  simp only [List.getElem_take, List.getElem_map, List.take_take, Nat.min_eq_left (Nat.le_of_lt hrk),
    ← Subst.consList_append]
  simpa using this

/-- Values typed along a constructor's declared field domains are typed along its views. -/
theorem fields_views (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U))
    (hls : ∀ l ∈ ls, l.WF U) {Ds : List VExpr}
    (hV : ∀ k D (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      env.IsDefEq d.uvars (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse) D f.type
        (.sort f.level))
    (hVT : env.IsTele d.uvars d.params.reverse (c.fields.map (·.type))) {As vs : List VExpr}
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (hDl : Ds.length = c.fields.length)
    (hvD : ∀ k (h : k < vs.length) D, Ds[k]? = some D →
      env.HasType U Γ vs[k] ((D.instL ls).subst (Subst.dflt.consList (As ++ vs.take k)))) :
    ∀ k (h : k < vs.length) (f : VField), c.fields[k]? = some f →
      env.HasType U Γ vs[k] ((f.type.instL ls).subst (Subst.dflt.consList (As ++ vs.take k))) := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
  intro h f hf
  have hkf : k < c.fields.length := (List.getElem?_eq_some_iff.1 hf).1
  obtain ⟨D, hD⟩ : ∃ D, Ds[k]? = some D := ⟨_, List.getElem?_eq_getElem (by omega)⟩
  have Wk := views_substEq hls hVT W k (Nat.le_of_lt h) (Nat.le_of_lt hkf)
    fun j hj fj hjk hfj => ih j hjk hj fj hfj
  have H := (hV k D f hD hf).instL hls
  simp only [List.map_append, List.map_reverse, List.map_map] at H
  have H2 := H.subst henv Wk hΓ
  exact .defeqDF (by simpa [Function.comp_def, VExpr.instL, VExpr.subst] using H2) (hvD k h D hD)

/-- Telescopes that agree entry by entry give contexts that do, given uniqueness of typing. -/
theorem TeleDefEq.defeqCtx_of_inj (henv : Ordered env) (hI : env.Inj) :
    ∀ {Γ' Γ As Bs}, env.TeleDefEq U Γ As Bs → env.IsDefEqCtx U [] Γ' Γ →
      OnCtx Γ (env.IsType U) → env.IsTele U Γ Bs →
      env.IsDefEqCtx U [] (As.reverse ++ Γ') (Bs.reverse ++ Γ)
  | _, _, [], [], .nil, hΓ, _, _ => hΓ
  | _, _, _ :: _, _ :: _, .cons ⟨_, hAB⟩ t, hΓ, hwf, .cons ⟨_, hB⟩ tB => by
    obtain ⟨_, hv⟩ := hI.uniq hwf hAB hB
    have h1 := (IsDefEq.defeqDF hv hAB).defeqDFC henv (hΓ.symm henv)
    simpa using TeleDefEq.defeqCtx_of_inj henv hI t (.succ hΓ h1) ⟨hwf, _, hB⟩ tB

theorem projs_take' (s : Name) (e : VExpr) {r k : Nat} (h : r ≤ k) :
    (VExpr.projs s k e).take r = VExpr.projs s r e := by
  simp [VExpr.projs, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The projections of a structure's constructor application are its fields, at the declared
domains instantiated by the projections before them, when every field may be projected. -/
theorem ctorApp_projs (henv : Ordered env) (hΓ : OnCtx Γ (env.IsType U)) {s : Name} {t : Nat}
    {T : VInductiveType} (hs : env.inducts s = some (d, t)) (ht : d.types[t]? = some T)
    (hc : T.ctors = [c]) (hF : ProjFacts env d c) (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.uvars) {Ds : List VExpr}
    (hV : ∀ k D (f : VField), Ds[k]? = some D → c.fields[k]? = some f →
      env.IsDefEq d.uvars (((c.fields.take k).map (·.type)).reverse ++ d.params.reverse) D f.type
        (.sort f.level))
    (hVT : env.IsTele d.uvars d.params.reverse (c.fields.map (·.type)))
    (hDl : Ds.length = c.fields.length) {As I fs : List VExpr}
    (hA : As.length = d.params.length) (hI : I.length = T.indices.length)
    (hfs : fs.length = c.fields.length)
    (W : Ctx.SubstEq env U Γ (Subst.dflt.consList As) (Subst.dflt.consList As)
      (d.params.map (·.instL ls)).reverse)
    (hS : env.IsDefEq U Γ (.appN (.const s ls) (As ++ I)) (.appN (.const s ls) (As ++ I)) (.sort u))
    (hX : env.HasType U Γ (.appN (.const c.name ls) (As ++ fs)) (.appN (.const s ls) (As ++ I)))
    (hfD : ∀ k (h : k < fs.length) D, Ds[k]? = some D →
      env.HasType U Γ fs[k] ((D.instL ls).subst (Subst.dflt.consList (As ++ fs.take k))))
    (hP : ∀ k < c.fields.length, d.ProjAllowed c ls k) :
    ∀ k (h : k < fs.length) D, Ds[k]? = some D →
      env.IsDefEq U Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) fs[k]
        ((D.instL ls).subst
          (Subst.dflt.consList (As ++ VExpr.projs s k (.appN (.const c.name ls) (As ++ fs))))) := by
  have hfsT := fields_views henv hΓ hls hV hVT W hDl hfD
  have hPI : ∀ k (h : k < fs.length) (f : VField), c.fields[k]? = some f →
      env.IsDefEq U Γ (.proj s k (.appN (.const c.name ls) (As ++ fs))) fs[k]
        ((f.type.instL ls).subst
          (Subst.dflt.consList (As ++ VExpr.projs s k (.appN (.const c.name ls) (As ++ fs))))) := by
    intro k h f hf
    have := projIota_ctor henv hΓ hs ht hc hF hls hlen hA hI hfs W hS hX hfsT k f fs[k] hf
      (List.getElem?_eq_getElem h) (hP k (by omega))
    simpa [VConstructor.projType, hf] using this
  intro k h D hD
  have hkf : k < c.fields.length := by omega
  obtain ⟨f, hf⟩ : ∃ f, c.fields[k]? = some f := ⟨_, List.getElem?_eq_getElem hkf⟩
  have Wk := views_substEq (vs := VExpr.projs s c.fields.length (.appN (.const c.name ls) (As ++ fs)))
    hls hVT W k (by simp [VExpr.projs]; omega) (Nat.le_of_lt hkf) fun j hj fj hjk hfj => by
      have e1 : (VExpr.projs s c.fields.length (.appN (.const c.name ls) (As ++ fs)))[j] =
          .proj s j (.appN (.const c.name ls) (As ++ fs)) := by simp [VExpr.projs]
      rw [e1, projs_take' _ _ (by simp [VExpr.projs] at hj; omega)]
      exact (hPI j (by simp [VExpr.projs] at hj; omega) fj hfj).hasType.1
  rw [projs_take' _ _ (Nat.le_of_lt hkf)] at Wk
  have H := (hV k D f hD hf).instL hls
  simp only [List.map_append, List.map_reverse, List.map_map] at H
  have H2 := H.subst henv Wk hΓ
  exact .defeqDF (by simpa [Function.comp_def, VExpr.instL, VExpr.subst] using H2.symm)
    (hPI k h f hf)

end VEnv

end Lean4Lean
