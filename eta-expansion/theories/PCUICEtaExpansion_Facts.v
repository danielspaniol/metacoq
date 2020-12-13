From Equations Require Import Equations.
From MetaCoq.Template Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICSafeLemmata PCUICReduction PCUICLiftSubst.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.EtaExpansion Require Import PCUICEtaExpansion_Defs.
From Coq Require Import Program ssreflect.

(*******************************************************************************
 * Translation of the context
 ******************************************************************************)

Section TransCtxFacts.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).
  Context (Γ : context) (Hwf : ∥ wf_local Σ Γ∥).

  Lemma trans_ctx_nth n decl :
    nth_error Γ n = Some decl ->
    nth_error (trans_ctx Σ HΣ Γ) n = Some (trans_context_decl Σ HΣ Γ decl).
  Proof.
      by apply: map_nth_error.
  Qed.

End TransCtxFacts.

(*******************************************************************************
 * Translation of the global environment
 ******************************************************************************)

Section TransEnvFacts.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).
  Context (Γ : context) (Hwf : ∥ wf_local Σ Γ∥).

  Lemma trans_env_global_ext_levels :
    global_ext_levels Σ = global_ext_levels (trans_env Σ HΣ Γ).
  Proof.
    elim: Σ HΣ Hwf => /=.
    todo "small bookkeeping".
  Admitted.

End TransEnvFacts.

(*******************************************************************************
 * Translation of terms
 ******************************************************************************)

Section HelperFacts.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).
  Context (Γ : context) (Hwf : ∥ wf_local Σ Γ∥).

  Lemma trans_wt_invariant tm Htm1 Htm2 :
    trans Σ HΣ Γ tm Htm1 = trans Σ HΣ Γ tm Htm2.
  Proof.
  Admitted.

End HelperFacts.

Section EtaExpandFacts.

  Local Existing Instance extraction_checker_flags.

  Lemma eta_expand_preservation Σ Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- eta_expand t T : T.
  Proof.
    elim: T => //= na A IHA B IHB H.
    econstructor.
    - todo "Show A has type tSort ?s1. This should follow from H but needs some bookkeeping".
    - todo "Needs some bookkeeping".
  Admitted.

End EtaExpandFacts.

Section TransFacts.

  (* Small helper to collect all eta-expansions of the same term.
     This uses the fact that the translation is invariant in the welltyped-proof *)
  Ltac collect old_name new_name :=
    let tmp_name := fresh "tmp" in
    set new_name := trans _ _ _ old_name _ ;
    try (set tmp_name := trans _ _ _ old_name _ ;
         (have: new_name = tmp_name by apply: trans_wt_invariant) ;
         move=> <- ;
         clear tmp_name).

  (*
    If t has type T, then the eta-expansion of t has type eta-expansion of T.
    Most cases here are not interesting as the transformation only recurses on the sub-terms.
    However, the proofs for them are more challenging than expected, as they require a lot of
    work to massage all the hypothesis to work correctly...
    The only interesting case is the one for constructors, here we should be able to use the
    preservation of the actual eta-expansion.
   *)
  Lemma trans_preservation `{cf : checker_flags} :
    env_prop
      (fun Σ Γ t T =>
         forall HΣ HηΣ Ht HT,
         let ηΣ := trans_env Σ HΣ Γ in
         let ηΓ := trans_ctx Σ HΣ Γ in
         let ηt := trans     ηΣ HηΣ ηΓ t Ht in
         let ηT := trans     ηΣ HηΣ ηΓ T HT in
          Σ ;;;  Γ |-  t :  T ->
         ηΣ ;;; ηΓ |- ηt : ηT)
      (fun Σ Γ _ =>
         forall HΣ,
         let ηΣ := trans_env Σ HΣ Γ in
         let ηΓ := trans_ctx Σ HΣ Γ in
         wf_local ηΣ ηΓ).
  Proof.
    cbn ; apply: typing_ind_env => Σ wfΣ Γ wfΓ.

    - move=> H HΣ.
      todo "show that the translated context is still wf_local".

    - move=> n [na body ty] /trans_ctx_nth nth_decl IH HΣ Ht HT H Hlift /=.
      simp trans.
      todo "should be an easy lookup in the context now".

    - move=> ℓ IH ℓ_in_ℓs HΣ Ht HT H ?.
      simp trans. constructor.
      + apply: IH.
      + rewrite -trans_env_global_ext_levels.
        * constructor. todo "problems with extraction_flags...".
        * done.

    - move=> na A b ℓ1 ℓ2 IH HA IHA HB IHB HΣ HηΣ Ht HT H.
      simp trans. constructor.
      + apply: IHA ; last done.
        case: Ht => ? /inversion_Prod [].
        * todo "show trans_env Σ is wf. Should be easy".
        * do 5 case => ? ; eexists ; eauto. todo "Show tSort ℓ1 has some type. Should be easy".
      + collect A ηA. collect b ηbA.
        todo "should be an easy lookup now".

    - move=> na A b ℓ B IH HA IHA Hb IHb HB IHB HΣ HT H.
      simp trans.
      collect b ηb ; collect B ηB ; collect A ηA.
      collect A foo ; (have: foo = ηA by todo "this step should work by `collect` alone...") ; move=> -> ; clear foo.
      econstructor.
      + apply: IHA ; last done. todo "show tSort ℓ is welltyped, this should be easy".
      + todo "this needs some massaging, then it should follow from IHb".

    - move=> na b B t ℓ T HΣ Hℓ IH IHb HB IHB Ht IHT HηΣ Hwt HWT H.
      simp trans.
      collect T ηT ; collect t ηt ; collect b ηb ; collect B ηB ; collect b ηb' ; collect B ηB'.
      have: ηb = ηb'.
      { unfold ηb, ηb'. apply trans_wt_invariant. constructor. todo "show translation is wf_local". }
      have: ηB = ηB'.
      { unfold ηB, ηB'. apply trans_wt_invariant. constructor. todo "show translation is wf_local". }
      move=> <- <-.
      econstructor.
      + apply: IH. todo "show tSort ℓ is welltyped". done.
      + by apply: HB.
      + todo "this needs some massaging, then it should follow from IHt".

    - move=> t na A B u IH Ht IHt Hu IHu HΣ HηΣ Hwt HWT H.
      simp trans.
      collect u ηu. collect t ηt. collect (B{0:=u}) ηB.
      todo "not sure how to use substitution here...".

    - move=> cst u decl IH H1 Hdecl Hconsistent HΣ HηΣ Ht HT H.
      simp trans.
      todo "should be an easy lookup".

    - move=> ind u mdecl idecl Hdecl IH Hloc Hconsist HΣ HηΣ Ht HT H.
      simp trans.
      todo "should be an easy lookup".

    - move=> ind i u mdecl idecl cdecl Hdecl Hdecls IH Hconsistent HΣ HηΣ Ht HT H.
      simp trans ; cbn.
      set T := type_of _ _ _ _ _ _.
      set t := tConstruct _ _ _.
      have: trans _ _ _ _ HT = T by todo "this follows from a lookup in the global env".
      move=> ->.
      todo "this should be applicable, but I get an error with extraction_checker_flags...".
      (* apply (eta_expand_preservation ηΣ ηΓ t T). *)

    - move=> ind u npar p c brs args mdecl idecl Idecl IH Hlocal Hnpar Hfirst ps pty Hbuild Hp IHp.
      move=> Hlev Hc Hcofinite IHc btys Hmap_opton HAll2.
      move=> HΣ HηΣ Ht HT Hcase.
      simp trans.
      collect p ηp ; collect c ηc.
      todo "handling the branches seems like some work because we iterate over them".

    - move=> p c u mdecl idecl pdecl Hdecl args Hforall Hlocal Hc IHc Hargs Hpdecl HΣ HηΣ Ht HT H.
      simp trans.
      collect c ηc.
      todo "handling projection seems like some work".

    - move=> mfix n decl ctx Hguard Hlocal IH Hall1 Hall2 Hwffix HΣ HηΣ Ht HT Hmfix.
      simp trans.
      todo "handling fixpoints seems like work because we iterate over them".

    - move=> mfix n decl ctx Hguard Hlocal IH Hall1 Hall2 Hwffix HΣ HηΣ Ht HT Hmfix.
      simp trans.
      todo "handling fixpoints seems like work because we iterate over them".

    - move=> t A B Hlocal HA IHA Harity Hlt HΣ HηΣ Hwt HWT Ht.
      todo "should be an easy lookup".

  Admitted.

End TransFacts.

