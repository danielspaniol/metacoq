From Equations Require Import Equations.
From MetaCoq.Template Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICSafeLemmata PCUICReduction PCUICLiftSubst.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From MetaCoq.EtaExpansion Require Import PCUICEtaExpansion_Defs.
From Coq Require Import Program ssreflect.

(*******************************************************************************
 * Translation of the global environment
 ******************************************************************************)

Section TransEnvFacts.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).
  Context (Γ : context) (Hwf : ∥ wf_local Σ Γ∥).

  Let ηΓ := trans_ctx Σ Γ HΣ Hwf.
  Let ηΣ := trans_env Σ Γ HΣ Hwf.

  Lemma trans_env_global_ext_levels :
    global_ext_levels Σ = global_ext_levels ηΣ.
  Proof.
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
    trans Σ Γ HΣ tm Htm1 = trans Σ Γ HΣ tm Htm2.
  Proof.
  Admitted.

End HelperFacts.

Section EtaExpandFacts.

  Local Existing Instance extraction_checker_flags.

  Lemma eta_expand_preservation Σ Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- eta_expand t T : T.
  Proof.
    elim: T => //=.
    move=> na A HA B HB H.
    econstructor.
    - todo "should be easy".
    - todo "???".
  Admitted.


End EtaExpandFacts.

Section TransFacts.

  Local Existing Instance extraction_checker_flags.

  Ltac collect old_name new_name :=
    let tmp_name := fresh "tmp" in
      set new_name := trans _ _ _ old_name _ ;
      try (set tmp_name := trans _ _ _ old_name _ ;
           (have: new_name = tmp_name by apply: trans_wt_invariant) ;
           move=> <- ;
           clear tmp_name).

  Lemma trans_preservation_prop `{cf : checker_flags} :
    env_prop
      (fun Σ Γ t T =>
         forall HΣ Hwf HηΣ Ht HT,
         let ηΣ := trans_env Σ Γ HΣ Hwf in
         let ηΓ := trans_ctx Σ Γ HΣ Hwf in
         let ηt := trans     ηΣ ηΓ HηΣ t Ht in
         let ηT := trans     ηΣ ηΓ HηΣ T HT in
          Σ ;;;  Γ |-  t :  T ->
         ηΣ ;;; ηΓ |- ηt : ηT)
      (fun Σ Γ _ =>
         forall HΣ Hwf,
         let ηΣ := trans_env Σ Γ HΣ Hwf in
         let ηΓ := trans_ctx Σ Γ HΣ Hwf in
         wf_local ηΣ ηΓ).
  Proof.
    cbn ; apply: typing_ind_env => Σ wfΣ Γ wfΓ.

    - todo "what is this?".

    - move=> n d nth_decl IH Hwf HΣ Ht HT H /inversion_Rel.
      do 3 case => ?.
      simp trans.
      todo "I have no idea...".

    - move=> ℓ IH ℓ_in_ℓs Hwf HΣ Ht HT H ?.
      simp trans. constructor.
      + apply: IH.
      + by rewrite -trans_env_global_ext_levels.

    - move=> na A b ℓ1 ℓ2 IH HA IHA HB IHB Hwf HΣ HηΣ Ht HT H.
      simp trans. constructor.
      + apply: IHA ; last done.
        case: Ht => ? /inversion_Prod [].
        * todo "just some bookkeeping".
        * do 5 case => ? ; eexists ; eauto. todo "just some bookkeeping".
      + collect A ηA. collect b ηbA.
        todo "just some bookkeeping".

    - move=> na A b ℓ B IH HA IHA Hb IHb HB IHB Hwf HΣ HT H.
      simp trans.
      collect b ηb ; collect B ηB ; collect A ηA.
      todo "lambda case".

    - todo "let in case".

    - todo "app case".

    - todo "const case".

    - todo "ind case".

    - move=> ind i u mdecl idecl cdecl Hdecl Hdecls IH Hconsistent HΣ Hwf HηΣ Ht HT H.
      simp trans ; cbn.
      set T := type_of _ _ _ _ _ _.
      set t := tConstruct _ _ _.
      have: Σ ;;; Γ |- eta_expand t T : T. by apply eta_expand_preservation.



  Lemma trans_preservation Σ Γ tm ty HΣ HηΣ Htm Hty :
    let ηΣ  := trans_env Σ Γ HΣ in
    let ηΓ  := trans_ctx ηΣ Γ HηΣ in
    let ηtm := trans ηΣ ηΓ HηΣ tm Htm in
    let ηty := trans ηΣ ηΓ HηΣ tm Hty in

     Σ ;;;  Γ |-  tm :  ty ->
    ηΣ ;;; ηΓ |- ηtm : ηty.

  Proof.

    cbn.
    move: HΣ HηΣ Htm Hty.
    pattern ty, tm, Γ, Σ.

    eapply typing_ind_env.


    cbn ; elim {Γ tm ty} => Γ.
    all: set ηΓ := trans_ctx _ Γ _.
    all: set ηΣ := trans_env Σ _ _.

    - move=> n d Hwf Hnth HηΣ Htm Hty ; simp trans.
      todo "use other induction principle".

    - move=> ℓ Hwf ℓ_in_Σℓs > ; simp trans.
      constructor.
      + by apply trans_env_wf_local.
      + by rewrite -trans_env_global_ext_levels.

    - move=> x A B ℓ1 ℓ2 HA IHA HB IHB > ; simp trans.
      constructor.
      + apply: IHA. todo "Should be easy to show...".
      + collect A ηA ; collect B ηB.

    - move=> n d Hwf_local HΓ >.
      simp trans.
      rewrite trans_lift0.
      + move=> ?.
        todo "???".
      + todo "should be easy".
    - move=> * ; simp trans.
      constructor.
      + by apply: trans_env_wf_local.
      + by rewrite -trans_env_global_ext_levels.
    - move=> x A B ℓ1 ℓ2 _ IHA _ IHB > ; simp trans.
      constructor.
      + apply: IHA. admit. (*TODO: should be easy*)
      + todo "IH has new Γ in trans of Σ".
    - move=> x A b ℓ B ? IHA ? IHb HηΣ Htm Hty ; simp trans.
      rewrite (trans_wt_invariant _ _ _ A
                                  (trans_obligation_4 _ _ _ _ _ _ Htm)
                                  (trans_obligation_2 _ _ _ _ _ _ Hty)).
      econstructor.
      + apply: IHA. admit. (*TODO: should be easy*)
      + todo "IH has new Γ in trans of Σ".
    - move=> x b B t ℓ A ? IHB ? IHb ? IHA ? Htm Hty.
      simp trans.
      prettify b ηb ;
      prettify B ηB ;
      prettify t ηt ;
      prettify A ηA.
      apply type_LetIn with (s1:=ℓ).
      + apply: IHB. admit. (*TODO: should be easy*)
      + apply: IHb.
      + todo "IH has new Γ in trans of Σ".
    - move=> t x A B u ? IHt ? IHu HηΣ Htm Hty.
      simp trans.
      rewrite trans_subst1.
      + move=> ?. prettify u ηu. prettify t ηt.
        apply type_App with (na:=x) (A0:=A).
        * have Hηt: welltyped ηΣ ηΓ t.
          { case: (HηΣ) => -[]*. case: (Htm) => ? /inversion_App [] //= ?. do 4 case => ?. by eexists ; eauto. }
          move: IHt => /(_ HηΣ Hηt).
          admit. (* TODO: should be easy *)
        * todo "ηu should have type ηA".
      + todo "welltyped".
    - move=> *. simp trans. todo "what is going on?".
    - todo "same as above".
    - move=> ind i u Hwf body idecl cdecl Hconstr Hconsistent HηΣ Htm Hty.
      simp trans.
      todo "hard case".
    - move=> *.
      simp trans.
      todo "???".
    - move=> *.
      simp trans.
      todo "handle subst".
    - move=> *. simp trans. todo "this is not true".
    - move=> *. simp trans. todo "this is not true".
  Admitted.


End EtaExpansionFacts.

