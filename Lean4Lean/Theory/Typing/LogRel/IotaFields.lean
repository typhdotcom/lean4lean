import Lean4Lean.Theory.Typing.LogRel.AdeqIotaRepl

/-!
# An iota rule's binders at a substitution

The values a substitution of an iota rule's binders gives its parameters and fields, the fields'
types at them, and, in an environment with injectivity, the typing of the left body's arguments
along the recursor's telescope.
-/

namespace Lean4Lean
open VExpr

namespace LogRel

variable {env : VEnv} {U : Nat}

/-- The iota rule's binder for the `k`th field: its type, past the motives and minor premises. -/
theorem iotaBinders_field (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (c : VConstructor)
    {k : Nat} (hk : k < c.fields.length) :
    (d.iotaBinders lsB v c)[d.params.length + d.allTypes.length + d.allCtors.length + k]'(by
      rw [length_iotaBinders]; omega) =
      (c.fields[k].type.instL lsB).liftN (d.allTypes.length + d.allCtors.length) k := by
  simp only [VInductDecl.iotaBinders]
  rw [List.getElem_append_right (by simp [VInductDecl.recBinders, VInductDecl.minorTypes]; omega)]
  rw [VExpr.getElem_liftTele]
  have key : ∀ a (ha : a < c.fields.length), a = k →
      VExpr.liftN (d.allTypes.length + d.allCtors.length) ((c.fields[a]).type.instL lsB) (0 + a) =
      VExpr.liftN (d.allTypes.length + d.allCtors.length) (c.fields[k].type.instL lsB) k := by
    intro a ha e; subst e; simp
  simp only [List.getElem_map, VInductDecl.recBinders, VInductDecl.minorTypes,
    List.length_append, List.length_map, VInductDecl.length_motiveTypes, List.length_zipIdx]
  exact key _ _ (by omega)

/-- The `i`th of the top binders (the fields, last first) at the substitution's values for the
binders below it: the `k`th field's type at the parameters' and the earlier fields' values. -/
theorem iota_field_subst (d : VInductDecl) (lsB : List VLevel) (v : VLevel) (c : VConstructor)
    {i k : Nat} (hik : i + k + 1 = c.fields.length)
    (hcl : (c.fields[k]'(by omega)).type.ClosedN (d.params.length + k)) (σ : VExpr.Subst)
    (h : i < ((d.iotaBinders lsB v c).drop
      (d.params.length + d.allTypes.length + d.allCtors.length)).reverse.length) :
    (((d.iotaBinders lsB v c).drop
      (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i]).subst (σ.drop (i+1)) =
      ((c.fields[k]'(by omega)).type.instL lsB).subst (Subst.id.consList
        ((VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length)).map
          (·.subst σ) ++ ((VExpr.bvars c.fields.length 0).map (·.subst σ)).take k)) := by
  have hk : k < c.fields.length := by omega
  have hBl := length_iotaBinders d lsB v c
  have e1 : ((d.iotaBinders lsB v c).drop
      (d.params.length + d.allTypes.length + d.allCtors.length)).reverse[i] =
      (d.iotaBinders lsB v c)[d.params.length + d.allTypes.length + d.allCtors.length + k]'(by
        omega) := by
    rw [List.getElem_reverse, List.getElem_drop]
    congr 1; simp only [List.length_drop]; omega
  rw [e1, iotaBinders_field d lsB v c hk]
  have hcl' := (hcl.instL (ls := lsB)).liftN (n := d.allTypes.length + d.allCtors.length) (j := k)
  rw [hcl'.subst_congr (σ' := Subst.id.consList ((VExpr.bvars (d.params.length + k +
      (d.allTypes.length + d.allCtors.length)) (i+1)).map (·.subst σ))) fun j hj => by
    rw [Subst.consList_lt _ _ _ (by simpa using hj)]
    simp only [List.getElem_reverse, List.getElem_map, VExpr.length_bvars, List.length_map]
    rw [getElem_bvars (by simp; omega)]
    simp only [VExpr.subst_bvar, VExpr.Subst.drop]
    congr 1; omega]
  have hb : VExpr.bvars (d.params.length + k + (d.allTypes.length + d.allCtors.length)) (i+1) =
      VExpr.bvars d.params.length (d.allTypes.length + d.allCtors.length + c.fields.length) ++
        VExpr.bvars (d.allTypes.length + d.allCtors.length) c.fields.length ++
        VExpr.bvars k (i+1) := by
    rw [show c.fields.length = k + (i+1) by omega,
      show d.params.length + k + (d.allTypes.length + d.allCtors.length) =
        d.params.length + ((d.allTypes.length + d.allCtors.length) + k) by omega,
      ← bvars_append' d.params.length ((d.allTypes.length + d.allCtors.length) + k) (i+1),
      ← bvars_append' (d.allTypes.length + d.allCtors.length) k (i+1), List.append_assoc]
    congr 2; omega
  have hf : ((VExpr.bvars c.fields.length 0).map (·.subst σ)).take k =
      (VExpr.bvars k (i+1)).map (·.subst σ) := by
    rw [show c.fields.length = k + (i+1) by omega, ← bvars_append' k (i+1) 0, List.map_append,
      List.take_left' (by simp)]
  rw [hb, hf, List.map_append, List.map_append]
  exact VExpr.liftN_subst_consList_mid _ _ (by simp) (by simp)

/-- The parameters' values at a substitution whose fields are replaced. -/
theorem iota_params_consList (np nTC nf : Nat) (σ : VExpr.Subst) {G : List VExpr}
    (hG : G.length = nf) :
    (VExpr.bvars np (nTC + nf)).map (·.subst ((σ.drop nf).consList G)) =
      (VExpr.bvars np (nTC + nf)).map (·.subst σ) := by
  subst hG
  rw [subst_bvars_consList_ge]
  simp [VExpr.bvars, VExpr.Subst.drop, Nat.add_assoc]

/-- The fields' values at a substitution whose fields are replaced. -/
theorem iota_fields_consList (σ : VExpr.Subst) {G : List VExpr} {nf : Nat} (hG : G.length = nf) :
    (VExpr.bvars nf 0).map (·.subst ((σ.drop nf).consList G)) = G := by
  subst hG; exact subst_bvars_consList _ _

/-- The arguments of an iota rule's left body (`iotaL_eq`). -/
def iotaArgs (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor) : List VExpr :=
  VExpr.bvars (d.params.length + d.allTypes.length + d.allCtors.length) c.fields.length ++
    c.indices.map (fun e => (e.instL lsB).reseat (d.allTypes.length + d.allCtors.length)
      c.fields.length c.fields.length 0 0) ++
    [d.ctorAppAt j c lsB (VExpr.bvars d.params.length
      (d.allTypes.length + d.allCtors.length + c.fields.length)) (VExpr.bvars c.fields.length 0)]

theorem iotaL_eq_args (d : VInductDecl) (lsB recLs : List VLevel) (j : Nat) (c : VConstructor) :
    iotaL d lsB recLs j c = (VExpr.const (d.recName j) recLs).appN (iotaArgs d lsB j c) :=
  iotaL_eq ..

theorem length_iotaArgs (d : VInductDecl) (lsB : List VLevel) (j : Nat) (c : VConstructor) :
    (iotaArgs d lsB j c).length =
      d.params.length + d.allTypes.length + d.allCtors.length + c.indices.length + 1 := by
  simp [iotaArgs]; omega

section
variable {E : VEnv}

/-- The arguments of an iota rule's left body, typed in an environment with injectivity where the
recursor is declared, instantiate the recursor's telescope, whose entries are closed. -/
theorem iotaL_args_tele [ShapeEnv] (hI : E.Inj) (hEo : E.Ordered) {d : VInductDecl} {j : Nat}
    {Tj : VInductiveType} {c : VConstructor} {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U)
    (hlen : ls.length = d.recUVars)
    (hrec : E.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    (hcidx : c.indices.length = Tj.indices.length)
    {Δ : List VExpr} (hΔ : OnCtx Δ (E.IsType U)) {A : VExpr}
    (hL : E.HasType U Δ (iotaL d (d.recLevels.map (·.inst ls)) ls j c) A) :
    VEnv.Ctx.SubstEq E U Δ (Subst.id.consList (iotaArgs d (d.recLevels.map (·.inst ls)) j c))
      (Subst.id.consList (iotaArgs d (d.recLevels.map (·.inst ls)) j c))
      (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj).reverse ∧
    ∀ r (B : VExpr), (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj)[r]? =
      some B → B.ClosedN r := by
  have hty (Γ : List VExpr) : (VEnv.HasType E U Γ (.const (d.recName j) ls)
      (.foralls (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj)
        ((.app (.appN (.bvar (1 + Tj.indices.length + d.allCtors.length +
          (d.allTypes.length - 1 - j))) (VExpr.bvars Tj.indices.length 1)) (.bvar 0))))) := by
    have := VEnv.HasType.const (Γ := Γ) hrec hls hlen
    rwa [VInductDecl.recType_instL, VInductDecl.recType_eq_recTele] at this
  have h0 := hty []
  have hcl := (h0.closedN' hEo.closed trivial).2.2
  obtain ⟨hTele, -⟩ := VEnv.IsType.foralls_inv hEo (h0.isType (Γ := []) hEo trivial)
  refine ⟨?_, fun r B hB => by simpa using VExpr.ClosedN.foralls_getElem hcl r B hB⟩
  rw [iotaL_eq_args] at hL
  have := VEnv.Inj.appN_invT hI hEo hΔ (Δ := []) (τ := .id) (by rw [subst_id]; exact hty Δ) .nil
    hTele ⟨_, hL⟩ (by rw [length_iotaArgs, length_recTele, hcidx])
  simpa using this

/-- An argument of an iota rule's left body, typed under its binders in an environment with
injectivity, at a substitution of the binders: typed at its entry of the recursor's telescope,
instantiated by the arguments before it. -/
theorem iotaL_arg_typed [ShapeEnv] (hI : E.Inj) (hEo : E.Ordered) (hle : E ≤ env) (henv : env.Ordered)
    {d : VInductDecl} {j : Nat} {Tj : VInductiveType} {c : VConstructor} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U) (hlen : ls.length = d.recUVars)
    (hrec : E.constants (d.recName j) =
      some ⟨d.recUVars, d.recType d.recLevels d.motiveLevel j Tj⟩)
    (hcidx : c.indices.length = Tj.indices.length)
    {Δ : List VExpr} (hΔ : OnCtx Δ (E.IsType U)) {A : VExpr}
    (hL : E.HasType U Δ (iotaL d (d.recLevels.map (·.inst ls)) ls j c) A)
    {Γ Γ₀ : List VExpr} {σ : VExpr.Subst} (hΓ₀ : OnCtx Γ₀ (env.IsType U))
    (W : VEnv.Ctx.SubstEq env U Γ₀ σ σ (Δ ++ Γ)) (r : Nat)
    (h : r < (iotaArgs d (d.recLevels.map (·.inst ls)) j c).length)
    (h' : r < (d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj).length) :
    env.HasType U Γ₀ ((iotaArgs d (d.recLevels.map (·.inst ls)) j c)[r].subst σ)
      ((d.recTele (d.recLevels.map (·.inst ls)) (d.motiveLevel.inst ls) Tj)[r].subst
        (Subst.id.consList (((iotaArgs d (d.recLevels.map (·.inst ls)) j c).take r).map
          (·.subst σ)))) := by
  obtain ⟨H, hcl⟩ := iotaL_args_tele hI hEo hls hlen hrec hcidx hΔ hL
  have H1 := VEnv.Ctx.SubstEq.getElem (Δ := []) (σ := .id) _ rfl (by rw [List.append_nil]; exact H)
    (by rw [length_iotaArgs, length_recTele, hcidx]) r h h'
  have H2 := ((IsDefEq.weak_closed hEo hΔ H1 Γ).defeq).mono hle
  have H3 := H2.subst henv W hΓ₀
  rwa [VExpr.ClosedN.subst_consList_subst (by
    simpa [Nat.min_eq_left (Nat.le_of_lt h)] using hcl r _ (List.getElem?_eq_getElem h'))] at H3

end

end LogRel
end Lean4Lean
