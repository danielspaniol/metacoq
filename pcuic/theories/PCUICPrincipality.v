(* Distributed under the terms of the MIT license. *)
From MetaCoq.Template Require Import config utils.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICInduction
     PCUICLiftSubst PCUICTyping PCUICSubstitution PCUICEquality
     PCUICReduction PCUICCumulativity PCUICConfluence PCUICClosed
     PCUICContextConversion PCUICConversion PCUICInversion PCUICUnivSubst
     PCUICArities PCUICValidity PCUICInductives PCUICInductiveInversion 
     PCUICSR PCUICCumulProp. 

Require Import ssreflect.
Require Import Equations.Prop.DepElim.
From Equations Require Import Equations.
Set Equations With UIP.

(** We show that principal types are derivable, without relying on normalization.
  The principal type is burried in the proof here, but [PCUICSafeRetyping.type_of]
  gives an explicit computation, but its definition and correctness proof requires
  completeness of weak-head-reduction. *)

Section Principality.
  Context {cf : checker_flags}.
  Context (Σ : global_env_ext).
  Context (wfΣ : wf_ext Σ).

  Ltac pih :=
    lazymatch goal with
    | ih : forall _ _ _, _ -> _ ;;; _ |- ?u : _ -> _,
    h1 : _ ;;; _ |- ?u : _,
    h2 : _ ;;; _ |- ?u : _
    |- _ =>
  specialize (ih _ _ _ h1 h2)
  end.

  Ltac insum :=
    match goal with
    | |- ∑ x : _, _ =>
      eexists
    end.

  Ltac intimes :=
    match goal with
    | |- _ × _ =>
      split
    end.

  Ltac outsum :=
    match goal with
    | ih : ∑ x : _, _ |- _ =>
      destruct ih as [? ?]
    end.

  Ltac outtimes :=
    match goal with
    | ih : _ × _ |- _ =>
      destruct ih as [? ?]
    end.

  Lemma isWfArity_sort Γ u :
    wf_local Σ Γ ->
    isWfArity typing Σ Γ (tSort u).
  Proof.
    move=> wfΓ. red. exists [], u. intuition auto.
  Qed.
  Hint Extern 10 (isWfArity _ _ _ (tSort _)) => apply isWfArity_sort : pcuic.

  Ltac int inv := intros B hB; eapply inv in hB; auto; split; [|econstructor; eauto].
  Hint Resolve wf_ext_wf : core.

  Theorem principal_type {Γ u A} : Σ ;;; Γ |- u : A ->
    ∑ C, (forall B, Σ ;;; Γ |- u : B -> Σ ;;; Γ |- C <= B × Σ ;;; Γ |- u : C).
  Proof.
    intros hA.
    induction u in Γ, A, hA |- * using term_forall_list_ind.
    - apply inversion_Rel in hA as iA. 2: auto.
      destruct iA as [decl [? [e ?]]].
      eexists; int inversion_Rel.
      destruct hB as [decl' [? [e' ?]]].
      rewrite e' in e. inversion e. subst. clear e.
      repeat insum. repeat intimes.
      all: try eassumption.
    - apply inversion_Var in hA. destruct hA.
    - apply inversion_Evar in hA. destruct hA.
    - apply inversion_Sort in hA as iA. 2: auto.
      repeat outsum. repeat outtimes. subst.
      exists (tSort (Universe.super x)).
      int inversion_Sort.
      repeat outsum. repeat outtimes. subst.
      assert (x0 = x) as ee. {
        clear -e. destruct x, x0; cbnr; invs e; reflexivity. }
      subst. repeat insum. repeat intimes; tea.
    - apply inversion_Prod in hA as [dom1 [codom1 iA]]; auto.
      repeat outtimes.
      specialize (IHu1 _ _ t) as [dom Hdom].
      specialize (IHu2 _ _ t0) as [codom Hcodom].
      destruct (Hdom _ t).
      eapply invert_cumul_sort_r in c0 as [domu [red leq]].
      destruct (Hcodom _ t0).
      eapply invert_cumul_sort_r in c0 as [codomu [cored coleq]].
      exists (tSort (Universe.sort_of_product domu codomu)).
      int inversion_Prod.
      repeat outsum; repeat outtimes.
      + eapply cumul_trans. 1: auto. 2:eapply c0.
        destruct (Hdom _ t3) as [le' u1'].
        eapply invert_cumul_sort_r in le' as [u' [redu' leu']].
        destruct (Hcodom _ t4) as [le'' u2'].
        eapply invert_cumul_sort_r in le'' as [u'' [redu'' leu'']].
        constructor. constructor.
        apply leq_universe_product_mon; auto.
        pose proof (red_confluence wfΣ red redu') as [v' [redl redr]].
        eapply invert_red_sort in redl.
        eapply invert_red_sort in redr. subst. now noconf redr.
        pose proof (red_confluence wfΣ cored redu'') as [v' [redl redr]].
        eapply invert_red_sort in redl.
        eapply invert_red_sort in redr. subst. now noconf redr.
      + eapply type_reduction; eauto.
      + eapply type_reduction; eauto.

    - apply inversion_Lambda in hA => //; eauto.
      repeat outsum. repeat outtimes.
      destruct (IHu1 _ _ t) as [? ?].
      destruct (IHu2 _ _ t0) as [? ?].
      destruct (p _ t).
      destruct (p0 _ t0).
      exists (tProd n u1 x2).
      int inversion_Lambda.
      repeat outsum. repeat outtimes.
      etransitivity; eauto.
      apply invert_cumul_prod_l in c2 as [na' [A' [B' [[redA u1eq] ?]]]] => //; auto.
      destruct (p0 _ t4).
      eapply congr_cumul_prod => //; auto.

    - eapply inversion_LetIn in hA as (s1 & bty & Hu2 & Hu1 & Hu3 & Hcum); auto.
      destruct (IHu1 _ _ Hu1) as [? p].
      destruct (p _ Hu1).
      destruct (IHu2 _ _ Hu2) as [? p'].
      destruct (p' _ Hu2).
      destruct (IHu3 _ _ Hu3) as [? p''].
      destruct (p'' _ Hu3).
      exists (tLetIn n u1 u2 x1).
      int inversion_LetIn.
      destruct hB as (s1' & bty' & Hu2' & Hu1' & Hu3' & Hcum'); eauto.
      etransitivity; eauto.
      eapply cum_LetIn; eauto.
      now specialize (p'' _ Hu3') as [? ?].

    - eapply inversion_App in hA as [na [dom [codom [tydom [tyarg tycodom]]]]] => //; auto.
      destruct (IHu2 _ _ tyarg).
      destruct (IHu1 _ _ tydom).
      destruct (p _ tyarg). destruct (p0 _ tydom).
      apply invert_cumul_prod_r in c0 as [? [A' [B' [[redA u1eq] ?]]]] => //; auto.
      exists (subst [u2] 0 B').
      intros ? hB.
      eapply inversion_App in hB as [na' [dom' [codom' [tydom' [tyarg' tycodom']]]]] => //; auto.
      destruct (p0 _ tydom').
      destruct (p _ tyarg').
      apply invert_cumul_prod_r in c1 as [? [A'' [B'' [[redA' u1eq'] ?]]]] => //; auto.
      destruct (red_confluence wfΣ redA redA') as [nfprod [redl redr]].
      eapply invert_red_prod in redl as [? [? [[? ?] ?]]] => //. subst.
      eapply invert_red_prod in redr as [? [? [[? ?] ?]]] => //. noconf e.
      all:auto.
      assert(Σ ;;; Γ |- A' = A'').
      { apply conv_trans with x3 => //; auto.
        - apply conv_sym; auto. }
      assert(Σ ;;; Γ ,, vass x1 A' |- B' = B'').
      { apply conv_trans with x4 => //. auto.
        - now eapply red_conv.
        - apply conv_sym; auto.
          eapply conv_conv_ctx; eauto.
          constructor; auto. 1: eapply conv_ctx_refl.
          constructor. now eapply conv_sym. }
      split.
      etransitivity; eauto.
      eapply substitution_cumul0 => //. auto.
      transitivity x4; eauto. now eapply red_cumul.
      transitivity B''.
      eapply cumul_conv_ctx; eauto. eapply red_cumul_inv; eauto.
      constructor. apply conv_ctx_refl. constructor. now apply conv_sym.
      eapply cumul_conv_ctx; eauto.
      constructor. apply conv_ctx_refl. constructor. 
      eapply conv_trans; eauto. now apply conv_sym.
      econstructor. eapply type_reduction; eauto.
      eapply type_Cumul; eauto.
      2:transitivity dom; auto; now apply conv_cumul.
      eapply type_reduction in t0. 3:eapply redA. 2:auto.
      eapply validity in t0; auto.
      eapply isWAT_tProd in t0 as [? ?]; eauto.
      eapply typing_wf_local; eauto.

    - eapply inversion_Const in hA as [decl ?] => //; eauto.
      repeat outtimes.
      eexists; int inversion_Const.
      destruct hB as [decl' [wf [declc' [cu cum]]]].
      now rewrite -(PCUICWeakeningEnv.declared_constant_inj _ _ d declc') in cum.
      
    - eapply inversion_Ind in hA as [mdecl [idecl [? [Hdecl ?]]]] => //; auto.
      repeat outtimes.
      exists (subst_instance_constr u (ind_type idecl)).
      int inversion_Ind. destruct hB as [mdecl' [idecl' [? [Hdecl' ?]]]] => //.
      red in Hdecl, Hdecl'. destruct Hdecl as [? ?].
      destruct Hdecl' as [? ?]. red in H, H1.
      rewrite H1 in H; noconf H.
      rewrite H2 in H0; noconf H0.
      repeat intimes; eauto. now destruct p.

    - eapply inversion_Construct in hA as [mdecl [idecl [? [? [Hdecl ?]]]]] => //; auto.
      repeat outtimes.
      exists (type_of_constructor mdecl (i0, t, n0) (i, n) u).
      int inversion_Construct. destruct hB as [mdecl' [idecl' [? [? [Hdecl' [? ?]]]]]] => //.
      red in Hdecl, Hdecl'.
      destruct Hdecl as [[? ?] ?].
      destruct Hdecl' as [[? ?] ?].
      red in H, H2. rewrite H2 in H. noconf H.
      rewrite H3 in H0. noconf H0.
      rewrite H4 in H1. now noconf H1.

    - destruct p as [ind n].
      assert (wf Σ) by auto.
      eapply inversion_Case in hA=>//.
      repeat outsum. repeat outtimes. simpl in *.
      repeat outtimes.
      subst.
      destruct (IHu1 _ _ t) as [? p].
      destruct (IHu2 _ _ t0) as [? p0].
      destruct (p _ t). destruct (p0 _ t0).
      eapply invert_cumul_ind_r in c1 as [u' [x0' [redr [redu ?]]]]; auto.
      exists (mkApps u1 (skipn (ind_npars x1) x0 ++ [u2])); intros b hB; repeat split; auto.
      2:econstructor; eauto.
      eapply inversion_Case in hB=>//; auto.
      repeat outsum. repeat outtimes. simpl in *.
      repeat outtimes.
      destruct (PCUICWeakeningEnv.declared_inductive_inj d d0) as [-> ->].
      destruct (p0 _ t4).
      eapply invert_cumul_ind_r in c2 as [u'' [x9' [redr' [redu' ?]]]]; auto.
      assert (All2 (fun a a' => Σ ;;; Γ |- a = a') x0 x9).
      { destruct (red_confluence wfΣ redr redr').
        destruct p1.
        eapply red_mkApps_tInd in r as [args' [? ?]]; auto.
        eapply red_mkApps_tInd in r0 as [args'' [? ?]]; auto.
        subst. solve_discr.
        clear -wfΣ a0 a1 a2 a3 a4.
        eapply All2_trans with x0'; eauto. eapply conv_trans; eauto.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- x = y)) in a3; auto using red_conv.
        eapply (All2_impl (Q:=fun x y => Σ ;;; Γ |- x = y)) in a4; auto using red_conv.
        eapply All2_trans with args'; eauto. eapply conv_trans; eauto.
        eapply All2_trans with x9'; eauto. eapply conv_trans; eauto.
        eapply All2_symmetry; eauto. eapply conv_sym.
        eapply All2_symmetry; eauto. eapply conv_sym.
      }
      clear redr redr' a1 a2.
      etransitivity. 2:eapply c1.
      eapply conv_cumul, mkApps_conv_args; auto.
      eapply All2_app. 2:constructor; auto.
      now eapply All2_skipn.

    - destruct s as [[ind k] pars]; simpl in *.
      eapply inversion_Proj in hA=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      specialize (IHu _ _ t) as [C HP].
      destruct (HP _ t).
      eapply invert_cumul_ind_r in c0 as [u' [x0' [redr [redu ?]]]]; auto.
      exists (subst0 (u :: List.rev x0') (subst_instance_constr u' t0)).
      intros B hB.
      eapply inversion_Proj in hB=>//; auto.
      repeat outsum. repeat outtimes.
      simpl in *.
      destruct (PCUICWeakeningEnv.declared_projection_inj d d0) as [-> [-> [= -> ->]]].
      destruct (HP _ t2).
      split; cycle 1.
      eapply type_reduction in t0; eauto.
      eapply invert_cumul_ind_r in c1 as [u'' [x0'' [redr' [redu' ?]]]]; auto.
      eapply (type_Proj _ _ _ _ _ _ _ _ d0); simpl; auto.
      now rewrite -(All2_length _ _ a).
      eapply invert_cumul_ind_r in c1 as [u'' [x0'' [redr' [redu' ?]]]]; auto.
      destruct (red_confluence wfΣ redr redr') as [nf [redl redr'']].
      eapply red_mkApps_tInd in redl as [? [-> conv]]; auto.
      eapply red_mkApps_tInd in redr'' as [? [[=] conv']]; auto.
      solve_discr.
      etransitivity; eauto.
      assert (consistent_instance_ext Σ (ind_universes x0) u').
      { eapply type_reduction in t1. 3:eapply redr. all:pcuic. 
        eapply validity in t1; eauto.
        eapply PCUICInductiveInversion.isWAT_mkApps_Ind_isType in t1; auto.
        destruct t1 as [s Hs].
        eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply d. }
      assert (consistent_instance_ext Σ (ind_universes x0) x2).
        { eapply validity in t2; eauto.
          eapply PCUICInductiveInversion.isWAT_mkApps_Ind_isType in t2; auto.
          destruct t2 as [s Hs].
          eapply invert_type_mkApps_ind in Hs. intuition eauto. all:auto. eapply d. }
        transitivity (subst0 (u :: List.rev x0') (subst_instance_constr x2 t3)); cycle 1.
      eapply conv_cumul.
      assert (conv_terms Σ Γ x0' x7).
      { transitivity x4. eapply (All2_impl conv); auto using red_conv.
        transitivity x0''. symmetry. eapply (All2_impl conv'); auto using red_conv.
        now symmetry. }
      eapply (subst_conv _ (projection_context x0 x1 ind u')
      (projection_context x0 x1 ind x2) []); auto.
      eapply (projection_subslet _ _ _ _ _ _ (ind, k, pars)); eauto.
      simpl. eapply type_reduction; eauto. simpl.
      eapply type_reduction in t0. 3:eapply redr. eapply validity; eauto. auto.
      eapply (projection_subslet _ _ _ _ _ _ (ind, k, pars)); eauto.
      simpl. eapply validity; eauto.
      constructor; auto. now apply All2_rev.
      eapply PCUICWeakening.weaken_wf_local; eauto.
      eapply PCUICWeakening.weaken_wf_local; pcuic.
      eapply (wf_projection_context _ (p:= (ind, k, pars))); pcuic.
      eapply (substitution_cumul _ Γ (projection_context x0 x1 ind u') []); auto.
      eapply PCUICWeakening.weaken_wf_local; pcuic.
      eapply PCUICWeakening.weaken_wf_local; pcuic.
      eapply (wf_projection_context _ (p:=(ind, k, pars))); pcuic.
      eapply (projection_subslet _ _ _ _ _ _ (ind, k, pars)); eauto.
      simpl. eapply type_reduction; eauto. simpl.
      eapply type_reduction in t0. 3:eapply redr. all:eauto.
      eapply validity; eauto.
      rewrite e0 in redu'.
      unshelve epose proof (projection_cumulative_indices wfΣ d _ H H0 redu').
      { eapply (PCUICWeakeningEnv.weaken_lookup_on_global_env' _ _ _ wfΣ (proj1 (proj1 d))). }
      eapply PCUICWeakeningEnv.on_declared_projection in d0; eauto.
      eapply weaken_cumul in X; eauto.
      eapply closed_wf_local; eauto.
      eapply (wf_projection_context _ (p:= (ind, k, pars))); pcuic.
      len. simpl. len. simpl.
      rewrite d0.(onNpars).
      rewrite closedn_subst_instance_constr.
      now apply (declared_projection_closed wfΣ d).
      simpl; len. rewrite d0.(onNpars).
      rewrite closedn_subst_instance_constr.
      now apply (declared_projection_closed wfΣ d).
      
    - pose proof (typing_wf_local hA).
      apply inversion_Fix in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_Fix in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      repeat split; eauto.
      eapply type_Fix; eauto.

    - pose proof (typing_wf_local hA).
      apply inversion_CoFix in hA as [decl [hguard [nthe [wfΓ [? [? ?]]]]]]=>//; auto.
      exists (dtype decl).
      intros B hB.
      eapply inversion_CoFix in hB as [decl' [hguard' [nthe' [wfΓ' [? [? ?]]]]]]=>//; auto.
      rewrite nthe' in nthe; noconf nthe.
      repeat split; eauto.
      eapply type_CoFix; eauto.
  Qed.

  (** A weaker version that is often convenient to use. *)
  Lemma common_typing {Γ u A B} : Σ ;;; Γ |- u : A -> Σ ;;; Γ |- u : B ->
    ∑ C, Σ ;;; Γ |- C <= A × Σ ;;; Γ |- C <= B × Σ ;;; Γ |- u : C.
  Proof.
    intros hA hB.
    destruct (principal_type hA) as [P HP]; eauto.
    exists P; split; eauto.
    eapply HP; eauto.
  Qed.

End Principality.

Lemma principal_type_ind {cf:checker_flags} {Σ Γ c ind u u' args args'} {wfΣ: wf_ext Σ} :
  Σ ;;; Γ |- c : mkApps (tInd ind u) args ->
  Σ ;;; Γ |- c : mkApps (tInd ind u') args' ->
  (∑ ui', 
    PCUICEquality.R_global_instance Σ.1 (eq_universe (global_ext_constraints Σ))
     (leq_universe (global_ext_constraints Σ)) (IndRef ind) #|args| ui' u * 
    PCUICEquality.R_global_instance Σ.1 (eq_universe (global_ext_constraints Σ))
     (leq_universe (global_ext_constraints Σ)) (IndRef ind) #|args'| ui' u') * 
  All2 (conv Σ Γ) args args'.
Proof.
  intros h h'.
  destruct (common_typing _ wfΣ h h') as [C [l [r ty]]].
  eapply invert_cumul_ind_r in l as [ui' [l' [red [Ru eqargs]]]]; auto.
  eapply invert_cumul_ind_r in r as [ui'' [l'' [red' [Ru' eqargs']]]]; auto.
  destruct (red_confluence wfΣ red red') as [nf [redl redr]].
  eapply red_mkApps_tInd in redl as [args'' [-> eq0]]; auto.
  eapply red_mkApps_tInd in redr as [args''' [eqnf eq1]]; auto.
  solve_discr.
  split.
  assert (#|args| = #|args'|).
  now rewrite (All2_length _ _ eqargs) (All2_length _ _ eqargs') (All2_length _ _ eq0) (All2_length _ _ eq1).
  exists ui'. split; auto.

  eapply All2_trans; [|eapply eqargs|]. intro; intros. eapply conv_trans; eauto.
  eapply All2_trans. intro; intros. eapply conv_trans; eauto.
  2:{ eapply All2_sym. eapply (All2_impl eqargs'). intros. now apply conv_sym. }
  eapply All2_trans. intro; intros. eapply conv_trans; eauto.
  eapply (All2_impl eq0). intros. now apply red_conv.
  eapply All2_sym; eapply (All2_impl eq1). intros. symmetry. now apply red_conv.
Qed.
 
Lemma eq_term_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term Σ Σ x y ->
  leq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma eq_term_empty_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term [] Σ x y ->
  leq_term [] Σ x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma eq_term_empty_eq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  eq_term [] Σ x y ->
  eq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_empty_impl; auto; typeclasses eauto.
Qed.

Lemma leq_term_empty_leq_term {cf:checker_flags} {Σ : global_env_ext} {x y} :
  leq_term [] Σ x y ->
  leq_term Σ Σ x y.
Proof.
  eapply eq_term_upto_univ_empty_impl; auto; typeclasses eauto.
Qed.

Notation eq_term_napp Σ n x y :=
  (eq_term_upto_univ_napp Σ (eq_universe Σ) (eq_universe Σ) n x y).

Notation leq_term_napp Σ n x y :=
    (eq_term_upto_univ_napp Σ (eq_universe Σ) (leq_universe Σ) n x y).
    
Lemma eq_term_upto_univ_napp_leq {cf:checker_flags} {Σ : global_env_ext} {n x y} :
  eq_term_napp Σ n x y -> 
  leq_term_napp Σ n x y.
Proof.
  eapply eq_term_upto_univ_impl; auto; typeclasses eauto.
Qed.

Lemma R_global_instance_empty_universe_instance Re Rle ref napp u u' :
  R_global_instance [] Re Rle ref napp u u' ->
  R_universe_instance Re u u'.
Proof.
  rewrite /R_global_instance.
  now rewrite global_variance_empty.
Qed.

Lemma typing_leq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' : 
  wf Σ.1 ->
  on_udecl Σ.1 Σ.2 ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  leq_term [] Σ t' t -> 
  (* No cumulativity of inductive types, as they can relate 
    inductives in different sorts. *)
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ onu Ht.
  revert Σ wfΣ Γ t T Ht onu t' T'.
  eapply (typing_ind_env 
  (fun Σ Γ t T =>
    forall (onu : on_udecl Σ.1 Σ.2),
    forall t' T' : term, Σ ;;; Γ |- t' : T' -> leq_term [] Σ t' t -> Σ;;; Γ |- t' : T)
  (fun Σ Γ wfΓ => wf_local Σ Γ)); auto;intros Σ wfΣ Γ wfΓ; intros.
    1-13:match goal with
    [ H : leq_term _ _ _ _ |- _ ] => depelim H
    end.
  all:try solve [econstructor; eauto].
  13:{ eapply type_Cumul.
       eapply X1. eauto. eauto. auto.
       destruct X2; [left|right].
       red in i. apply i.
       exists s.π1. apply s.π2. auto.
    }
  - eapply inversion_Sort in X0 as [l' [_ [Inl' [-> ?]]]].
    eapply type_Cumul with (tSort (Universe.super l')).
    constructor; auto. left; eexists _, _; simpl; intuition eauto.
    constructor. constructor. apply leq_universe_super.
    apply x. auto.

  - eapply inversion_Prod in X4 as [s1' [s2' [Ha [Hb Hs]]]]; auto.
    specialize (X1 onu _ _ Ha). 
    specialize (X1 (eq_term_empty_leq_term X5_1)).
    apply eq_term_empty_eq_term in X5_1.
    eapply context_conversion in Hb. 3:{ constructor. apply conv_ctx_refl. constructor.
      constructor. eauto. }
    all:eauto.
    2:{ constructor; eauto. now exists s1. }
    specialize (X3 onu _ _ Hb X5_2).
    econstructor; eauto.
    apply leq_term_empty_leq_term in X5_2.
    eapply context_conversion; eauto.
    constructor; pcuic. constructor. symmetry;  now constructor.
    constructor; pcuic.

  - eapply inversion_Lambda in X4 as (s & B & dom & codom & cum); auto.
    specialize (X1 onu _ _ dom (eq_term_empty_leq_term X5_1)).
    apply eq_term_empty_eq_term in X5_1.
    assert(conv_context Σ (Γ ,, vass na ty) (Γ ,, vass n t)).
    { repeat constructor; pcuic. }
    specialize (X3 onu t0 B).
    forward X3 by eapply context_conversion; eauto; pcuic.
    econstructor.
    econstructor. eauto. instantiate (1 := bty).
    eapply context_conversion; eauto; pcuic.
    constructor; pcuic. constructor; pcuic. symmetry; constructor; auto.
    have tyl := type_Lambda _ _ _ _ _ _ _ X0 X2.
    now eapply PCUICValidity.validity in tyl.
    eapply congr_cumul_prod; eauto.
    constructor; auto. reflexivity.
    
  - eapply inversion_LetIn in X6 as (s1' & A & dom & bod & codom & cum); auto.
    specialize (X1 onu _ _ dom (eq_term_empty_leq_term X7_2)).
    specialize (X3 onu _ _ bod (eq_term_empty_leq_term X7_1)).
    apply eq_term_empty_eq_term in X7_1.
    apply eq_term_empty_eq_term in X7_2.
    assert(conv_context Σ (Γ ,, vdef na t ty) (Γ ,, vdef n b b_ty)).
    { repeat constructor; pcuic. }
    specialize (X5 onu u A).
    forward X5 by eapply context_conversion; eauto; pcuic.
    specialize (X5 X7_3).
    eapply leq_term_empty_leq_term in X7_3.
    econstructor.
    econstructor. eauto. eauto.
    instantiate (1 := b'_ty).
    eapply context_conversion; eauto.
    apply conv_context_sym; auto.
    pcuic. eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply cum_LetIn; pcuic.
    
  - eapply inversion_App in X4 as (na' & A' & B' & hf & ha & cum); auto.
    unfold leq_term in X1.
    eapply eq_term_upto_univ_empty_impl in X5_1.
    specialize (X1 onu _ _ hf X5_1). all:try typeclasses eauto.
    specialize (X3 onu _ _ ha (eq_term_empty_leq_term X5_2)).
    eapply leq_term_empty_leq_term in X5_1.
    eapply eq_term_empty_eq_term in X5_2.
    econstructor.
    econstructor; [eapply X1|eapply X3].
    eapply PCUICValidity.validity; pcuic.
    eapply type_App; eauto.
    eapply conv_cumul. eapply (subst_conv Γ [vass na A] [vass na A] []); pcuic.
    repeat constructor. now rewrite subst_empty.
    repeat constructor. now rewrite subst_empty.
    eapply PCUICValidity.validity in X0; auto.
    apply PCUICArities.isWAT_tProd in X0 as [tyA]; auto.
    constructor; auto.

  - eapply inversion_Const in X1 as [decl' [wf [declc [cu cum]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    eapply conv_cumul. constructor.
    pose proof (PCUICWeakeningEnv.declared_constant_inj _ _ H declc); subst decl'.
    eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Ind in X1 as [decl' [idecl' [wf [declc [cu cum]]]]]; auto.
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.

    eapply conv_cumul.
    constructor.
    pose proof (PCUICWeakeningEnv.declared_inductive_inj isdecl declc) as [-> ->].
    eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.
  
  - eapply inversion_Construct in X1 as [decl' [idecl' [cdecl' [wf [declc [cu cum]]]]]]; auto.
    
    econstructor; eauto.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor; eauto.
    pose proof (PCUICWeakeningEnv.declared_constructor_inj isdecl declc) as [-> [-> ->]].
    unfold type_of_constructor.
    transitivity (subst0 (inds (inductive_mind (ind, i).1) u (ind_bodies mdecl))
    (subst_instance_constr u0 cdecl'.1.2)).
    * eapply conv_cumul.
      eapply (conv_subst_conv _ Γ _ _ []); eauto.
      { eapply conv_inds. now eapply R_global_instance_empty_universe_instance. }
      eapply subslet_untyped_subslet.
      eapply (PCUICSpine.weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
      eapply subslet_untyped_subslet.
      eapply (PCUICSpine.weaken_subslet _ _ _ Γ []); eauto.
      eapply PCUICArities.subslet_inds; eauto.
      destruct declc; eauto.
    * constructor. eapply PCUICEquality.subst_leq_term.
      eapply PCUICEquality.eq_term_leq_term.
      eapply PCUICUnivSubstitution.eq_term_upto_univ_subst_instance_constr; eauto; typeclasses eauto.

  - eapply inversion_Case in X6 as (u' & args' & mdecl' & idecl' & ps' & pty' & btys' & inv); auto.
    intuition auto.
    intuition auto.
    pose proof (X2 _ _ a6 (eq_term_empty_leq_term X7_2)).
    eapply eq_term_empty_eq_term in X7_1.
    eapply eq_term_empty_eq_term in X7_2.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply (type_Case _ _ (ind, npar)). eapply isdecl.
    all:eauto.
    eapply (All2_impl X5); firstorder.
    eapply conv_cumul.
    eapply mkApps_conv_args; pcuic.
    eapply All2_app. simpl in *.
    2:constructor; pcuic.
    eapply All2_skipn.
    clear -onu wfΣ a6 X4 X6.
    unshelve eapply (principal_type_ind a6 X4).
    split; auto.
    
  - eapply inversion_Proj in X3 as (u' & mdecl' & idecl' & pdecl' & args' & inv); auto.
    intuition auto.
    specialize (X3 _ _ a0 (eq_term_empty_leq_term X4)).
    eapply eq_term_empty_eq_term in X4.
    assert (wf_ext Σ) by (split; assumption).
    pose proof (principal_type_ind X3 a0) as [Ruu' X3'].
    eapply type_Cumul. clear a0.
    econstructor; eauto.
    now rewrite (All2_length _ _ X3').
    eapply PCUICValidity.validity; eauto.
    eapply type_Proj; eauto.
    transitivity (subst0 (c :: List.rev args) (subst_instance_constr u pdecl'.2)).
    eapply conv_cumul.
    set (ctx := PCUICInductives.projection_context mdecl' idecl' p.1.1 u).
    set (ctx' := PCUICInductives.projection_context mdecl' idecl' p.1.1 u).
    eapply (conv_subst_conv _ Γ ctx ctx' []); eauto.
    constructor. now constructor. 
    eapply All2_rev. eapply All2_refl. intros; apply conv_refl'.
    eapply subslet_untyped_subslet; eauto.
    eapply PCUICInductives.projection_subslet; eauto.
    eapply validity in X3; auto.
    eapply subslet_untyped_subslet; eauto.
    eapply PCUICInductives.projection_subslet; eauto.
    eapply validity in X3; auto.
    constructor. eapply PCUICEquality.subst_leq_term.
    destruct (PCUICWeakeningEnv.declared_projection_inj a isdecl) as [<- [<- <-]].
    subst ty. reflexivity.

  - eapply inversion_Fix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wffix & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    econstructor. 2:eapply H0. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. eapply eq_term_empty_leq_term in eqty.
    now eapply leq_term_empty_leq_term.
  
  - eapply inversion_CoFix in X2 as (decl' & fixguard' & Hnth & types' & bodies & wfcofix & cum); auto.
    eapply type_Cumul.
    econstructor; eauto.
    eapply PCUICValidity.validity; eauto.
    eapply type_CoFix. 2:eapply H0. all:eauto.
    eapply (All_impl X0); firstorder.
    eapply (All_impl X1); firstorder.
    eapply All2_nth_error in a; eauto.
    destruct a as [[eqty _] _].
    constructor. apply eq_term_empty_leq_term in eqty.
    now eapply leq_term_empty_leq_term.
Qed.

Lemma typing_eq_term {cf:checker_flags} (Σ : global_env_ext) Γ t t' T T' : 
  wf_ext Σ ->
  Σ ;;; Γ |- t : T ->
  Σ ;;; Γ |- t' : T' ->
  eq_term [] Σ t t' ->
  Σ ;;; Γ |- t' : T.
Proof.
  intros wfΣ ht ht' eq.
  eapply typing_leq_term; eauto. apply wfΣ.
  now eapply eq_term_empty_leq_term.
Qed.

Print Assumptions principal_type.
