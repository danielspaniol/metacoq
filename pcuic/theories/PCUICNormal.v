(* Distributed under the terms of the MIT license.   *)

From Coq Require Import Bool String List Program BinPos Compare_dec Arith Lia.
From MetaCoq.Template
Require Import config Universes monad_utils utils BasicAst AstUtils UnivSubst.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInduction.
Require Import ssreflect.
Set Asymmetric Patterns.

(* Require Import Equations.Type.DepElim. *)

Module RedFlags.

  Record t := mk {
    beta   : bool ;
    iota   : bool ;
    zeta   : bool ;
    delta  : bool ;
    fix_   : bool ;
    cofix_ : bool
  }.

  Definition default := mk true true true true true true.

End RedFlags.

Lemma mkApps_snoc a l b :
  PCUICAst.mkApps a (l ++ [b]) = PCUICAst.tApp (PCUICAst.mkApps a l) b.
Proof.
  revert a; induction l; cbn; congruence.
Qed.

Section Normal.

  Context (flags : RedFlags.t).
  Context (Σ : global_env).

  (* Relative to reduction flags *)
  Inductive whnf (Γ : context) : term -> Prop :=
  | whnf_ne t : whne Γ t -> whnf Γ t
  | whnf_sort s : whnf Γ (tSort s)
  | whnf_prod na A B : whnf Γ (tProd na A B)
  | whnf_lam na A B : whnf Γ (tLambda na A B)
  | whnf_cstrapp i n u v : whnf Γ (mkApps (tConstruct i n u) v)
  | whnf_indapp i u v : whnf Γ (mkApps (tInd i u) v)
  | whnf_fixapp mfix idx v :
    match unfold_fix mfix idx with
    | Some (rarg, body) => nth_error v rarg = None
    | None => True
    end ->
    whnf Γ (mkApps (tFix mfix idx) v)
  | whnf_cofixapp mfix idx v : whnf Γ (mkApps (tCoFix mfix idx) v)

  with whne (Γ : context) : term -> Prop :=
  | whne_rel i :
      option_map decl_body (nth_error Γ i) = Some None ->
      whne Γ (tRel i)

  | whne_rel_nozeta i :
      RedFlags.zeta flags = false ->
      whne Γ (tRel i)
           
  | whne_lam_nobeta na A b :
      RedFlags.beta flags = false ->
      whne Γ (tLambda na A b)

  | whne_var v :
      whne Γ (tVar v)

  | whne_evar n l :
      whne Γ (tEvar n l)

  | whne_letin_nozeta na B b t :
      RedFlags.zeta flags = false ->
      whne Γ (tLetIn na B b t)

  | whne_const c u decl :
      lookup_env Σ c = Some (ConstantDecl decl) ->
      decl.(cst_body) = None ->
      whne Γ (tConst c u)

  | whne_const_nodelta c u :
      RedFlags.delta flags = false ->
      whne Γ (tConst c u)

  | whne_app f v :
      whne Γ f ->
      whne Γ (tApp f v)

  (* Stuck fixpoints are neutrals *)
  | whne_fixapp mfix idx args rarg arg body :
     unfold_fix mfix idx = Some (rarg, body) ->
     nth_error args rarg = Some arg -> 
     whne Γ arg ->
     whne Γ (mkApps (tFix mfix idx) args)
          
  | whne_fix_nofix defs i :
      RedFlags.fix_ flags = false ->
      whne Γ (tFix defs i)
  
  | whne_case i p c brs :
      whne Γ c ->
      whne Γ (tCase i p c brs)

  | whne_case_noiota i p c brs :
      RedFlags.iota flags = false ->
      whne Γ (tCase i p c brs)

  | whne_proj p c :
      whne Γ c ->
      whne Γ (tProj p c)

  | whne_proj_noiota p c :
      RedFlags.iota flags = false ->
      whne Γ (tProj p c).

  Lemma whne_mkApps :
    forall Γ t args,
      whne Γ t ->
      whne Γ (mkApps t args).
  Proof.
    intros Γ t args h.
    induction args in t, h |- *.
    - assumption.
    - simpl. eapply IHargs. econstructor. assumption.
  Qed.

  Lemma whnf_mkApps :
    forall Γ t args,
      whne Γ t ->
      whnf Γ (mkApps t args).
  Proof.
    intros. econstructor. now eapply whne_mkApps.
  Qed.
  
  Lemma whne_mkApps_inv :
    forall Γ t l,
      negb (isApp t) ->
      whne Γ (mkApps t l) ->
      whne Γ t \/ exists mfix idx narg body a, t = tFix mfix idx /\ unfold_fix mfix idx = Some (narg, body) /\ nth_error l narg = Some a /\ whne Γ a.
  Proof.
    intros Γ t l Ha h. revert t Ha h.
    induction l using rev_ind; intros.
    - eauto.
    - rewrite mkApps_snoc in h.
      depelim h.
      + edestruct IHl as [ | (? & ? & ? & ? & ? & ? & ? & ? & ?)]; eauto. subst.
        right. exists x0, x1, x2, x3, x4. repeat split; eauto. now eapply nth_error_app_left.
      + rewrite <- mkApps_snoc in x.
        eapply (f_equal decompose_app) in x;
          rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
        inversion x. subst. 
        right. exists mfix, idx, rarg, body, arg. repeat split; eauto.
  Qed.
  
End Normal.

Derive Signature for whnf.
Derive Signature for whne.
Derive Signature for All.
Hint Constructors whnf whne : core.

Local Ltac inv H := inversion H; subst; clear H.

Ltac help' := try repeat match goal with
| [ H0 : _ = mkApps _ _ |- _ ] => 
  eapply (f_equal decompose_app) in H0;
    rewrite !decompose_app_mkApps in H0; cbn in *; firstorder congruence
| [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
  destruct args using rev_ind; cbn in *; [ inv H1 |
                                           rewrite <- mkApps_nested in H1; cbn in *; inv H1
                                  ]
        end.
Ltac help := help'; try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; help'.

Hint Resolve All_Forall : core.

Notation decision P := ({P} + {~P}).

Lemma dec_All X (L : list X) P : All (fun x => decision (P x)) L ->
                                 All P L + (All P L -> False).
Proof.
  intros. induction X0.
  - left. econstructor.
  - destruct p.
    + destruct IHX0. left; econstructor; eauto. right. inversion 1. subst. eauto.
    + right. inversion 1; subst; eauto.
Defined.

Lemma negb_is_true b :
 ~ is_true b -> is_true (negb b).
Proof.
  destruct b; firstorder.
Qed.
Hint Resolve negb_is_true : core.

Lemma whnf_mkApps_inv flags :
  forall Σ Γ t l,
    ~ isApp t ->
    whnf flags Σ Γ (mkApps t l) ->
    whnf flags Σ Γ t.
Proof.
  intros Σ Γ t l Hr h.
  induction l using rev_ind.
  - assumption.
  - rewrite <- mkApps_nested in h. cbn in h. depelim h. depelim H. eauto.
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. eauto. inv x.
      eapply whnf_fixapp with (v := []); eauto. rewrite H. now destruct rarg.    
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_cstrapp with (v := []).
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
        rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_indapp with (v := []).
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eapply whnf_fixapp with (v := []).
      destruct unfold_fix as [[rarg arg] | ]; eauto. now destruct rarg.
    + change (tApp (mkApps t l) x0) with (mkApps (mkApps t l) [x0]) in *.
      rewrite mkApps_nested in x.
      eapply (f_equal decompose_app) in x.
      rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x.
      eauto.
Qed.

Lemma whnf_fixapp' {flags} Σ Γ mfix idx narg body v :
unfold_fix mfix idx = Some (narg, body) ->
nth_error v narg = None ->
whnf flags Σ Γ (mkApps (tFix mfix idx) v).
Proof.
 intros E1 H. eapply whnf_fixapp. rewrite E1. eauto.
Qed. 
Hint Resolve whnf_fixapp' : core.

Definition whnf_whne_dec flags Σ Γ t : ({whnf flags Σ Γ t} + {~ (whnf flags Σ  Γ t)}) * ({whne flags Σ Γ t} + {~ (whne flags Σ Γ t)}).
Proof.
  induction t using term_forall_mkApps_ind in Γ |- *; split; eauto.
  all: try now (right; intros H; depelim H;help).
  - destruct (RedFlags.zeta flags) eqn:Er.
    + destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help. 
      * eauto.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help. 
    + eauto.
  - destruct (RedFlags.zeta flags) eqn:Er.
    + destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
      * right. intros H. depelim H. congruence. congruence. help.
      * eauto.
      * right. intros H. depelim H. congruence. congruence. help.
    + eauto.
  - destruct (RedFlags.beta flags) eqn:Er; eauto.
    right. intros ?. depelim H. congruence. help.
  - destruct (RedFlags.zeta flags) eqn:Er; eauto.
    right. intros ?. depelim H. depelim H. all:help. congruence.
  - destruct (RedFlags.zeta flags) eqn:Er; eauto.
    right. intros ?. depelim H. congruence. help.
  - destruct (IHt Γ) as [[] _].
    + destruct t. all:try now (left; eauto using whnf_mkApps, All_Forall).
      all: try now left; eapply whnf_mkApps; depelim w; eauto; help.
      * destruct v as [ | ? v].
        -- eauto.
        -- right. intros ?. depelim H0. depelim H0. all:help. clear IHl.
           eapply whne_mkApps_inv in H0 as []; eauto.
           ++ depelim H0. help.
           ++ firstorder congruence.
      * destruct v as [ | ? v].
        -- eauto.
        -- right. intros ?. depelim H0. depelim H0. all:help. clear IHl.
            eapply whne_mkApps_inv in H0 as []; eauto.
            ++ depelim H0. help.
            ++ firstorder congruence.
      * destruct v as [ | ? v].
        -- eauto.
        -- destruct (RedFlags.beta flags) eqn:?.
           ++ right. intros ?. depelim H0. depelim H0. all:help. clear IHl.
              eapply whne_mkApps_inv in H0 as []; eauto.
              ** depelim H0. congruence. help.
              ** firstorder congruence.
           ++ left.
              apply whnf_mkApps.
              constructor.
              assumption.
      * destruct (unfold_fix mfix idx) as [(narg, body) |] eqn:E1.
        -- destruct (nth_error v narg) as [a  | ] eqn:E2.
           ++ destruct (nth_error_all E2 X Γ) as [_ []].
              ** left. eauto.
              ** destruct (RedFlags.fix_ flags) eqn:?.
                 --- right. intros ?. depelim H0. depelim H0. all:help. clear IHv. 
                     eapply whne_mkApps_inv in H0 as []; eauto.
                     +++ depelim H0; [|congruence]. help. 
                         eapply (f_equal decompose_app) in x; 
                           rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. 
                         inv x. destruct rarg; inv H1. 
                     +++ destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ?). inv H0.
                         rewrite E1 in H1. inv H1.
                         eapply (nth_error_app_left v [x0]) in H2.
                         rewrite E2 in H2. inv H2. eauto.
                     +++ help.
                         eapply (f_equal decompose_app) in x; 
                           rewrite !decompose_app_mkApps in x;
                           cbn in *; try firstorder congruence.
                         inv x. rewrite E1 in H0. congruence. 
                 --- left.
                     apply whnf_mkApps.
                     constructor.
                     assumption.
           ++ left. eauto.
        -- left. eapply whnf_fixapp. rewrite E1. eauto.
    + right. intros ?. eapply n. now eapply whnf_mkApps_inv. 
  - destruct (IHt Γ) as [_ []].
    + left. now eapply whne_mkApps.
    + destruct t.
      all: try now (right; intros [ | (mfix & idx & narg & body & a & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto).
      * destruct (unfold_fix mfix idx) as [(narg, body) |] eqn:E1.
      -- destruct (nth_error v narg) as [a  | ] eqn:E2.
         ++ destruct (nth_error_all E2 X Γ) as [_ []].
            ** left. eauto.
            ** destruct (RedFlags.fix_ flags) eqn:?.
               --- right. intros ?. depelim H0. depelim H0. all:help. clear IHv. 
                   eapply whne_mkApps_inv in H0 as []; eauto.
                   destruct H0 as (? & ? & ? & ? & ? & ? & ? & ? & ?). inv H0.
                   rewrite E1 in H1. inv H1.
                   eapply (nth_error_app_left v [x0]) in H2.
                   rewrite E2 in H2. inv H2. eauto.
               --- left. apply whne_mkApps. constructor. assumption.
         ++ right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
            congruence.
      -- right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
         congruence.
      * right. intros [ | (mfix' & idx' & narg' & body' & a' & [=] & ? & ? & ?) ] % whne_mkApps_inv; subst; cbn; eauto.
  - destruct (RedFlags.delta flags) eqn:Er; eauto.
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. depelim H. congruence. congruence. all:help.
      * eauto. 
    +   right. intros H. depelim H. depelim H. congruence. congruence. all:help.
    +   right. intros H. depelim H. depelim H. congruence. congruence. all:help.
  - destruct (RedFlags.delta flags) eqn:Er; eauto.
    destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. congruence. congruence. help.
      * eauto.
    +   right. intros H. depelim H. congruence. congruence. help.
    +   right. intros H. depelim H. congruence. congruence. help.
  - left. eapply whnf_indapp with (v := []). 
  - left. eapply whnf_cstrapp with (v := []). 
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt2 Γ) as [_ []].
    + eauto. 
    + right. intros ?. depelim H. depelim H. all:help. eauto. congruence.
  -  destruct (RedFlags.iota flags) eqn:Eq; eauto.
     destruct (IHt2 Γ) as [_ []].
    + eauto. 
    + right. intros ?. depelim H. all:help. eauto. congruence.
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. depelim H. all:eauto. all:help.
  - destruct (RedFlags.iota flags) eqn:Eq; eauto.
    destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. all:help. eauto. congruence.
  - destruct (unfold_fix m n) as [(narg, body) |] eqn:E1.
    + left. eapply whnf_fixapp with (v := []). rewrite E1. now destruct narg.
    + left. eapply whnf_fixapp with (v := []). now rewrite E1.
  - destruct (RedFlags.fix_ flags) eqn:?; eauto.
    right. intros ?. depelim H; [|congruence].
    destruct args using rev_ind; try rewrite mkApps_snoc in H3; inv x.
    destruct rarg; inv H0. rewrite mkApps_snoc in H3. inv H3.
  - left. eapply whnf_cofixapp with (v := []).
Defined.

Definition whnf_dec flags Σ Γ t := fst (whnf_whne_dec flags Σ Γ t).
Definition whne_dec flags Σ Γ t := snd (whnf_whne_dec flags Σ Γ t).

Lemma red1_mkApps_tConstruct_inv Σ Γ i n u v t' :
  red1 Σ Γ (mkApps (tConstruct i n u) v) t' -> ∑ v', (t' = mkApps (tConstruct i n u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto. 
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tInd_inv Σ Γ i u v t' :
  red1 Σ Γ (mkApps (tInd i u) v) t' -> ∑ v', (t' = mkApps (tInd i u) v') * (OnOne2 (red1 Σ Γ) v v').
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X. help.
  - rewrite mkApps_snoc in X. depelim X.
    + help.
    + help.
    + eapply IHv in X as (? & ? & ?). subst.
      exists (x0 ++ [x]). rewrite mkApps_snoc. split; eauto.
      apply OnOne2_app_r. assumption.
    + exists (v ++ [N2]). rewrite mkApps_snoc. split; eauto. 
      eapply OnOne2_app. econstructor. eauto.
Qed.

Ltac hhelp' :=
  try
    repeat match goal with
           | [ H0 : _ = mkApps _ _ |- _ ] => 
             eapply (f_equal decompose_app) in H0;
             rewrite !decompose_app_mkApps in H0; cbn in *; firstorder congruence
           | [ H1 : tApp _ _ = mkApps _ ?args |- _ ] =>
             destruct args eqn:E using rev_ind ; cbn in *;
             [ inv H1 | rewrite <- mkApps_nested in H1; cbn in *; inv H1]
           end.

Ltac hhelp := hhelp';
              try match goal with | [ H0 : mkApps _ _ = _ |- _ ] => symmetry in H0 end; hhelp'.

Lemma is_constructor_app_false i x y :
  is_constructor i (x ++ y) = false ->
  is_constructor i x = false.
Proof.
  unfold is_constructor.
  destruct (nth_error (x ++ y) i) eqn:nth.
  - destruct nth_error eqn:nth' in |- *; [|easy].
    erewrite nth_error_app_left in nth by easy.
    intros; congruence.
  - apply nth_error_None in nth.
    rewrite (proj2 (nth_error_None _ _)); [|easy].
    rewrite app_length in nth.
    lia.
Qed.
  
Lemma red1_mkApps_tFix_inv Σ Γ mfix id v t' :
  match unfold_fix mfix id with
  | Some (rarg, body) => is_constructor rarg v = false
  | None => True
  end ->
  red1 Σ Γ (mkApps (tFix mfix id) v) t' ->
  (∑ v', (t' = mkApps (tFix mfix id) v') * (OnOne2 (red1 Σ Γ) v v'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ Γ) dtype (fun x0 : def term => (dname x0, dbody x0, rarg x0))) mfix mfix'))
  + (∑ mfix', (t' = mkApps (tFix mfix' id) v) * (OnOne2 (on_Trel_eq (red1 Σ (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody (fun x0 : def term => (dname x0, dtype x0, rarg x0))) mfix mfix')).
Proof.
  intros not_ctor. revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
    solve_discr.
    unfold is_constructor in e0.
    rewrite nth_error_nil in e0.
    congruence.
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + solve_discr.
      rewrite e in not_ctor, IHv.
      congruence.
    + eapply IHv in X as [ [(? & ? & ?)|(?&?&?)] | (?&?&?)].
      * subst. left. left. exists (x0 ++ [x]). split. now rewrite mkApps_snoc.
        now apply OnOne2_app_r.
      * subst. left. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * subst. right. exists x0. split. now rewrite mkApps_snoc. eauto.
      * destruct unfold_fix as [(?&?)|]; [|easy].
        now eapply is_constructor_app_false.
    + left. left. exists (v ++ [N2]). split.
      now rewrite mkApps_snoc. 
      eapply OnOne2_app. econstructor. eauto.
Qed.

Lemma red1_mkApps_tCoFix_inv Σ Γ mfix id v t' :
  red1 Σ Γ (mkApps (tCoFix mfix id) v) t' ->
  ∑ mfix' v', t' = mkApps (tCoFix mfix' id) v'.
Proof.
  revert t'. induction v using rev_ind; intros.
  - cbn in *. depelim X; help; eauto.
    + now eexists _, [].
    + now eexists _, [].
  - rewrite mkApps_snoc in X.
    depelim X; help; eauto.
    + eapply IHv in X as (?&?&->).
      exists x0, (x1 ++ [x]).
      now rewrite <- mkApps_nested.
    + exists mfix, (v ++ [N2]).
      now rewrite <- mkApps_nested.
Qed.

Lemma whne_isConstruct_app flags Σ Γ t :
  isConstruct_app t ->
  whne flags Σ Γ t ->
  False.
Proof.
  intros ctor wh.
  unfold isConstruct_app in *.
  destruct decompose_app eqn:decomp.
  destruct t0; try easy.
  apply decompose_app_notApp in decomp as notapp.
  apply decompose_app_inv in decomp as ->.
  cbn in *.
  apply whne_mkApps_inv in wh; [|easy].
  destruct wh as [wh|(?&?&?&?&?&?&?)]; [|easy].
  depelim wh.
  solve_discr.
Qed.

Lemma whne_pres1 Σ Γ t t' :
  red1 Σ Γ t t' ->
  whne RedFlags.default Σ Γ t ->
  whne RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  induction wh in wh, t, r, t' |- *; cbn in *; try easy.
  - depelim r; [congruence|now solve_discr].
  - depelim r; cbn in *.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - depelim r; try easy.
    + depelim wh.
      solve_discr.
    + destruct args using List.rev_ind; [now solve_discr|].
      rewrite <- mkApps_nested in x.
      cbn in *.
      inv x.
      apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|].
      * depelim H.
        solve_discr.
        rewrite H in e.
        inv e.
        rewrite nth_error_nil in H0; congruence.
      * destruct H as (?&?&?&?&?&?&?&?&?).
        inv H.
        rewrite H0 in e.
        inv e.
        unfold is_constructor in e0.
        erewrite nth_error_app_left in e0 by eassumption.
        now apply whne_isConstruct_app in H2; auto.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { rewrite H.
         unfold is_constructor.
         rewrite H0.
         destruct isConstruct_app eqn:ctor; [|easy].
         now eapply whne_isConstruct_app in ctor. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + eapply OnOne2_nth_error in H0; eauto.
      destruct H0 as (?&?&[->|]).
      * eapply whne_fixapp; eauto.
      * apply IHwh in r.
        eapply whne_fixapp; eauto.
    + unfold unfold_fix in *.
      destruct (nth_error mfix idx) eqn:nth; [|easy].
      eapply OnOne2_nth_error in nth; eauto.
      inv H.
      destruct nth as (?&?&[->|(?&?)]).
      * eapply whne_fixapp; eauto.
        unfold unfold_fix.
        rewrite e.
        reflexivity.
      * eapply whne_fixapp; eauto.
        unfold unfold_fix.
        rewrite e.
        inv e0.
        rewrite H3.
        reflexivity.
    + unfold unfold_fix in *.
      destruct (nth_error mfix idx) eqn:nth; [|easy].
      eapply OnOne2_nth_error in nth; eauto.
      inv H.
      destruct nth as (?&?&[->|(?&?)]).
      * eapply whne_fixapp; eauto.
        unfold unfold_fix.
        rewrite e.
        reflexivity.
      * eapply whne_fixapp; eauto.
        unfold unfold_fix.
        rewrite e.
        inv e0.
        rewrite H3.
        reflexivity.
  - depelim r; try easy.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim H.
      solve_discr.
    + solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim H.
      solve_discr.
  - depelim r; try easy.
    + solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim H.
      solve_discr.
    + apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?)]; [|discriminate].
      depelim H.
      solve_discr.
Qed.

Lemma whne_pres Σ Γ t t' :
  red Σ Γ t t' ->
  whne RedFlags.default Σ Γ t -> whne RedFlags.default Σ Γ t'.
Proof.
  induction 1; intros.
  - eapply whne_pres1; eauto.
  - eauto.
  - eauto.
Qed.
  
Lemma whnf_pres1 Σ Γ t t' :
  red1 Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t ->
  whnf RedFlags.default Σ Γ t'.
Proof.
  intros r wh.
  induction wh in wh, t, t', r |- *; cbn in *.
  - constructor.
    now eapply whne_pres1.
  - depelim r.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - depelim r; try easy.
    solve_discr.
  - apply red1_mkApps_tConstruct_inv in r as (?&->&?).
    apply whnf_cstrapp.
  - apply red1_mkApps_tInd_inv in r as (?&->&?).
    apply whnf_indapp.
  - eapply red1_mkApps_tFix_inv in r; eauto.
    2: { destruct unfold_fix as [(?&?)|]; [|easy].
         unfold is_constructor.
         now rewrite H. }
    destruct r as [[(?&->&?)|(?&->&?)]|(?&->&?)].
    + apply whnf_fixapp.
      apply OnOne2_length in o.
      destruct unfold_fix as [(?&?)|]; [|easy].
      apply nth_error_None.
      apply nth_error_None in H.
      lia.
    + apply whnf_fixapp.
      unfold unfold_fix in *.
      destruct (nth_error x idx) eqn:nth; [|easy].
      eapply OnOne2_nth_error_r in nth; eauto.
      destruct nth as (?&nth&?).
      rewrite nth in H.
      destruct s as [->|(?&?)]; [easy|].
      now inv e.
    + apply whnf_fixapp.
      unfold unfold_fix in *.
      destruct (nth_error x idx) eqn:nth; [|easy].
      eapply OnOne2_nth_error_r in nth; eauto.
      destruct nth as (?&nth&?).
      rewrite nth in H.
      destruct s as [->|(?&?)]; [easy|].
      now inv e.
  - eapply red1_mkApps_tCoFix_inv in r; eauto.
    destruct r as (?&?&->).
    apply whnf_cofixapp.
Qed.

Lemma whnf_pres Σ Γ t t' :
  red Σ Γ t t' ->
  whnf RedFlags.default Σ Γ t -> whnf RedFlags.default Σ Γ t'.
Proof.
  induction 1; intros.
  - eapply whnf_pres1; eauto.
  - eauto.
  - eauto.
Qed.

Lemma whnf_red1_sort Σ Γ t u :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t (tSort u) -> t = tSort u.
Proof.
  intros. remember (tSort u) as t'. 
  induction X using red1_ind_all.
  all: repeat match goal with
         | [ H : whnf _ _ _ (?f ?a) |- _ ] => depelim H
         | [ H : whne _ _ _ (?f ?a)|- _ ] => depelim H
         end.
  all:try (cbn in *; congruence).
  all:do 2 help.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. rewrite H2 in H. inv H.
    destruct args0 using rev_ind; cbn in *.
    destruct rarg; inv H0.
    rewrite mkApps_snoc in  Heqt'. congruence.
  - destruct args using rev_ind.
    + inv Heqt'. destruct narg; inv H1.
    + rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply whne_mkApps_inv in H as [ | (? & ? & ? & ? & ? & ? & ? & ? & ?)]; cbn; eauto.
    depelim H. help. congruence.  
Qed.

Lemma whnf_red_sort Σ Γ t u :
  whnf RedFlags.default Σ Γ t ->
  red Σ Γ t (tSort u) -> t = tSort u.
Proof.
  intros. remember (tSort u) as t'. induction X using red_rect'.
  - eauto.
  - subst. eapply whnf_red1_sort in X0. subst. eauto.
    eapply whnf_pres; eauto.
Qed.

Lemma whnf_red1_prod Σ Γ t na t1 t2 :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t (tProd na t1 t2) -> exists t1 t2, t = tProd na t1 t2.
Proof.
  intros. remember (tProd na t1 t2) as t'. 
  induction X using red1_ind_all.
  all: repeat match goal with
         | [ H : whnf _ _ _ (?f ?a) |- _ ] => depelim H
         | [ H : whne _ _ _ (?f ?a)|- _ ] => depelim H
         end.
  all:try (cbn in *; congruence).
  all:do 2 help.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. rewrite H2 in H. inv H.
    destruct args0 using rev_ind; cbn in *.
    destruct rarg; inv H0.
    rewrite mkApps_snoc in  Heqt'. congruence.
  - destruct args using rev_ind.
    + inv Heqt'. destruct narg; inv H1.
    + rewrite <- mkApps_nested in Heqt'. inv Heqt'.
  - eapply whne_mkApps_inv in H. destruct H; try firstorder congruence. depelim H. help. firstorder.
  - inv Heqt'. eauto.
  - inv Heqt'. eauto.
Qed.

Lemma whnf_red_prod Σ Γ t na t1 t2 :
  whnf RedFlags.default Σ Γ t ->
  red Σ Γ t (tProd na t1 t2) -> exists t1 t2, t = tProd na t1 t2.
Proof.
  intros. remember (tProd na t1 t2) as t'. revert t1 t2 Heqt'. induction X using red_rect'; intros.
  - eauto.
  - subst. eapply whnf_red1_prod in X0 as (? & ? & ?). subst. eauto.
    eapply whnf_pres; eauto.
Qed.

Lemma whne_mkApps_tInd Σ Γ ind u args :
  whne RedFlags.default Σ Γ (mkApps (tInd ind u) args) ->
  False.
Proof.
  intros wh.
  apply whne_mkApps_inv in wh; [|easy].
  destruct wh as [|(?&?&?&?&?&?&?&?&?)].
  - depelim H; solve_discr.
  - inv H.
Qed.

Lemma whne_red1_mkApps_tInd Σ Γ ind u args t :
  whne RedFlags.default Σ Γ t ->
  red1 Σ Γ t (mkApps (tInd ind u) args) ->
  False.
Proof.
  intros wh r.
  remember (mkApps (tInd ind u) args) as t' eqn:t'eq.
  revert t' r args t'eq.
  induction wh; intros t' r args' ->; cbn in *; try easy.
  - depelim r; [congruence|now solve_discr].
  - depelim r; cbn in *.
    solve_discr.
  - depelim r; solve_discr.
  - depelim r; solve_discr.
    unfold PCUICAst.declared_constant in isdecl.
    rewrite H in isdecl.
    inv isdecl.
    congruence.
  - depelim r.
    + depelim wh; solve_discr.
    + destruct args using rev_ind; [cbn in *; congruence|].
      rewrite <- mkApps_nested in x0.
      cbn in *.
      inv x0.
      apply whne_mkApps_inv in wh; [|easy].
      destruct wh as [|(?&?&?&?&?&?&?&?&?)].
      * depelim H; solve_discr.
        now rewrite nth_error_nil in H0.
      * inv H.
        rewrite e in H0.
        inv H0.
        unfold is_constructor in e0.
        erewrite nth_error_app_left in e0; [|eassumption].
        now eapply whne_isConstruct_app.
    + destruct args' as [|? ? _] using rev_ind; [cbn in *; congruence|].
      rewrite <- mkApps_nested in x.
      cbn in *.
      inv x.
      eauto.
    + destruct args' as [|? ? _] using rev_ind; [cbn in *; congruence|].
      rewrite <- mkApps_nested in x.
      cbn in *.
      inv x.
      eapply whne_mkApps_tInd; eauto.
  - apply red1_mkApps_tFix_inv in r.
    2: { rewrite H.
         unfold is_constructor.
         rewrite H0.
         destruct isConstruct_app eqn:ctor; [|easy].
         now eapply whne_isConstruct_app in ctor. }
    destruct r as [[(?&?&?)|(?&?&?)]|(?&?&?)]; solve_discr.
  - depelim r; solve_discr.
    apply whne_mkApps_inv in wh; [|easy].
    destruct wh as [|(?&?&?&?&?&?&?&?&?)]; [|congruence].
    depelim H; solve_discr.
  - depelim r; solve_discr.
    apply whne_mkApps_inv in wh; [|easy].
    destruct wh as [|(?&?&?&?&?&?&?&?&?)]; [|congruence].
    depelim H; solve_discr.
Qed.

Lemma whnf_red1_mkApps_tInd Σ Γ ind u args t :
  whnf RedFlags.default Σ Γ t ->
  red1 Σ Γ t (mkApps (tInd ind u) args) ->
  exists args', t = mkApps (tInd ind u) args'.
Proof.
  intros wh r.
  remember (mkApps (tInd ind u) args) as t' eqn:t'eq.
  revert t' r args t'eq.
  induction wh; intros t' r args' ->; cbn in *; try easy.
  - exfalso; eauto using whne_red1_mkApps_tInd.
  - depelim r; solve_discr.
  - depelim r; solve_discr.
  - depelim r; solve_discr.
  - apply red1_mkApps_tConstruct_inv in r as (?&?&?); solve_discr.
  - apply red1_mkApps_tInd_inv in r as (?&?&?).
    apply (f_equal decompose_app) in e.
    rewrite !decompose_app_mkApps in e; try easy.
    now inv e.
  - apply red1_mkApps_tFix_inv in r.
    2: { destruct unfold_fix as [(?&?)|]; [|easy].
         unfold is_constructor.
         now rewrite H. }
    destruct r as [[(?&?&?)|(?&?&?)]|(?&?&?)]; solve_discr.
  - apply red1_mkApps_tCoFix_inv in r as (?&?&?); solve_discr.
Qed.

Lemma whnf_red_mkApps_tInd Σ Γ ind u args t :
  whnf RedFlags.default Σ Γ t ->
  red Σ Γ t (mkApps (tInd ind u) args) ->
  exists args', t = mkApps (tInd ind u) args'.
Proof.
  remember (mkApps (tInd ind u) args) as hd eqn:hdeq.
  intros wh r.
  revert args hdeq.
  induction r using red_rect'; intros args ->.
  - easy.
  - apply whnf_red1_mkApps_tInd in X as (?&->); eauto.
    eapply whnf_pres; eauto.
Qed.
(* 

  Definition head_arg_is_constructor mfix idx args :=
    match unfold_fix mfix idx with Some (narg, body) => is_constructor narg args | None => false end.
  

  Inductive normal (Γ : context) : term -> Prop :=
  | nf_ne t : neutral Γ t -> normal Γ t
  | nf_lam na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                    normal Γ (tLambda na A B)
  | nf_cstrapp i n u v : All (normal Γ) v -> normal Γ (mkApps (tConstruct i n u) v)
  | nf_indapp i u v : All (normal Γ) v -> normal Γ (mkApps (tInd i u) v)
  | nf_fix mfix idx args : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                           All (normal Γ) args ->
                           head_arg_is_constructor mfix idx args = false ->
                           All (compose (normal Γ) dtype) mfix ->
                      normal Γ (mkApps (tFix mfix idx) args)
  | nf_cofix mfix idx : All (compose (normal (Γ ,,, PCUICLiftSubst.fix_context mfix)) dbody) mfix ->
                      All (compose (normal Γ) dtype) mfix ->
                        normal Γ (tCoFix mfix idx)

  with neutral (Γ : context) : term -> Prop :=
  | ne_rel i :
      (forall b, option_map decl_body (nth_error Γ i) <> Some (Some b)) ->
      neutral Γ (tRel i)
  | ne_var v : neutral Γ (tVar v)
  | ne_evar n l : neutral Γ (tEvar n l)
  | ne_const c u :
      (forall decl b, lookup_env Σ c = Some (ConstantDecl decl) -> decl.(cst_body) = Some b -> False) ->
      neutral Γ (tConst c u)
  | ne_sort s : neutral Γ (tSort s)
  | ne_prod na A B : normal Γ A -> normal (Γ ,, vass na A) B ->
                     neutral Γ (tProd na A B)
  | ne_app f v : neutral Γ f -> normal Γ v -> neutral Γ (tApp f v)
  | ne_case i p c brs : neutral Γ c -> normal Γ p -> All (compose (normal Γ) snd) brs ->
                        neutral Γ (tCase i p c brs)
  | ne_proj p c : neutral Γ c -> neutral Γ (tProj p c).

Definition normal_neutral_dec Σ Γ t : ({normal Σ Γ t} + {~ (normal Σ  Γ t)}) * ({neutral Σ Γ t} + {~ (neutral Σ Γ t)}).
Proof.
  induction t using term_forall_mkApps_ind in Γ |- *; split; eauto.
  all: try now (right; intros H; depelim H).
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. depelim H. congruence. help. help. help.
    + eauto.
    + right. intros H. depelim H. depelim H. congruence. help. help. help.
  - destruct (option_map decl_body (nth_error Γ n)) as [ [ | ] | ] eqn:E.
    + right. intros H. depelim H. congruence.
    + eauto.
    + right. intros H. depelim H. congruence.
  - todo "evar".
  - todo "evar".
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. eauto. 
    + right. intros H. depelim H. eauto.
  - destruct (IHt1 Γ) as [[] _];
      [destruct (IHt2 (Γ,, vass n t1)) as [[] _]|]; eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - right. intros H. depelim H. depelim H. help. help. help.
  - destruct (IHt Γ) as [[] _].
    + destruct dec_All with (P := (normal Σ Γ)) (L := v).
      -- eapply All_impl. eassumption. intros ? ?. apply X0.
      -- destruct t. all:eauto using normal_mkApps, All_Forall.
         all: try now (left; depelim n; help; eauto).
         ++ destruct v as [ | ? v].
            ** eauto.
            ** right. todo "admit". (*  intros ?. depelim X. depelim X. all:help. clear IHt. *)
               (* eapply neutral_mk_Apps_inv in H0. as []; eauto. *)
               (* depelim H1. *)
         ++ destruct (head_arg_is_constructor mfix idx v) eqn:E.
            ** right. intros ?. todo "admit". (* depelim H1. depelim H1. all:help. clear IHv. *)
               (* eapply neutral_mk_Apps_inv in H1 as []; eauto. depelim H1. *)
            ** left. todo "admit". (* depelim n. all:help. depelim H1. *)
               (* eapply (f_equal decompose_app) in x; *)
               (*   rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x. *)
               (* eauto. *)
         ++ todo "cofix".
      -- right. intros ?. eapply f. eapply Forall_All.
         now eapply normal_mk_Apps_inv.
    + right. intros ?. eapply n. now eapply normal_mk_Apps_inv.
  - destruct v using rev_ind.
    + cbn. eapply IHt.
    + rewrite <- mkApps_nested. cbn.
      eapply All_app in X as []. eapply IHv in a. inv a0. clear X0.
      rename X into IHt2.
      revert a.
      generalize (mkApps t v) as t1. intros t1 IHt1.
      destruct (IHt1) as [];
      [destruct (IHt2 Γ) as [[] _]|]; eauto.
      * right. intros HH. depelim HH. eauto.
      * right. intros HH. depelim HH. eauto.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. depelim H. congruence. help. help. help.
      * eauto. 
    +   right. intros H. depelim H. depelim H. congruence. help. help. help.
    +   right. intros H. depelim H. depelim H. congruence. help. help. help.
  - destruct (lookup_env Σ s) as [[] | ] eqn:E.
    + destruct (cst_body c) eqn:E2.
      * right. intros H. depelim H. congruence.
      * eauto. 
    +   right. intros H. depelim H. congruence.
    +   right. intros H. depelim H. congruence.
  - left. eapply nf_indapp with (v := []). econstructor.
  - left. eapply nf_cstrapp with (v := []). econstructor.
  - destruct (IHt2 Γ) as [_ []].
    + destruct (IHt1 Γ) as [[] _].
      * destruct dec_All with(L := l) (P := (normal Σ Γ ∘ @snd nat term)).
        -- eapply All_impl. eassumption. intros ? ?. eapply X0.
        -- eauto.
        -- right. intros ?. depelim H. depelim H. all:help. eauto.
      * right. intros ?. depelim H. depelim H. all:help. eauto.
    + right. intros ?. depelim H. depelim H. all:help. eauto.
  -  destruct (IHt2 Γ) as [_ []].
    + destruct (IHt1 Γ) as [[] _].
      * destruct dec_All with(L := l) (P := (normal Σ Γ ∘ @snd nat term)).
        -- eapply All_impl. eassumption. intros ? ?. eapply X0.
        -- eauto.
        -- right. intros ?. depelim H. all:help. eauto.
      * right. intros ?. depelim H. all:help. eauto.
    + right. intros ?. depelim H. all:help. eauto.
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. depelim H. eauto. help. help. help.
  - destruct (IHt Γ) as [_ []].
    + eauto.
    + right. intros H. depelim H. eauto.
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply X0.

    destruct dec_All with (P := normal Σ  (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply X0.

    + left. eapply nf_fix with (args := []). eauto. eauto. unfold head_arg_is_constructor.
      destruct unfold_fix; eauto. destruct p.
      unfold is_constructor. destruct n0; eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. eapply f.
      eapply (f_equal decompose_app) in x;
        rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x.
      eauto.
    + right. intros H. depelim H. depelim H. help. help. 
      eapply (f_equal decompose_app) in x;
        rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.  inv x.
      eauto.      
  - hnf in X.

    destruct dec_All with (P := (normal Σ Γ ∘ dtype)) (L := m).
    eapply All_impl. eassumption. cbn. intros. eapply X0.

    destruct dec_All with (P := normal Σ (Γ ,,, PCUICLiftSubst.fix_context m) ∘ dbody) (L := m).
    eapply All_impl. exact X. cbn. intros. eapply X0.

    + left. eapply nf_cofix. eauto. eauto.
    + right. intros H. depelim H. depelim H. help. help. help. eauto.
    + right. intros H. depelim H. depelim H. help. help. help. eauto.
Defined.

Definition normal_dec Σ Γ t := fst (normal_neutral_dec Σ Γ t).
Definition neutral_dec Σ Γ t := snd (normal_neutral_dec Σ Γ t).
 *)


(* 


Lemma OnOn2_contra A  (P : A -> A -> Type) l1 l2 : (forall x y, P x y -> False) -> OnOne2 P l1 l2 -> False.
Proof.
  intros. induction X; eauto.
Qed.

Lemma normal_nf Σ Γ t t' : normal Σ Γ t \/ neutral Σ Γ t -> red1 Σ Γ t t' -> False.
Proof.
  intros. induction X using red1_ind_all; destruct H.
  all: repeat match goal with
         | [ H : normal _ _ (?f ?a) |- _ ] => depelim H
         | [ H : neutral _ _ (?f ?a)|- _ ] => depelim H
         end.
  all: try congruence.
  all: help.
  all: try tauto.
  all: try now (clear - H; depind H; help; eauto).
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence.
    inv x. unfold head_arg_is_constructor in H.
    rewrite H0 in H. congruence.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply IHX. left.
    eapply nf_cstrapp. now eapply All_app in X as [X _].
  - eapply IHX. left.
    eapply nf_indapp. now eapply All_app in X as [X _].
  - clear IHargs.
    eapply IHX. left.
    eapply nf_fix.
    + eauto.
    + eapply All_app in X0. eapply X0.
    + unfold head_arg_is_constructor in *.
      destruct unfold_fix; eauto. destruct p.
      unfold is_constructor in *.
      destruct (nth_error args n) eqn:E; eauto.
      erewrite nth_error_app_left in H; eauto.
    + eauto.
  - eapply IHX. left.
    eapply All_app in X as [_ X]. now inv X.
  - eapply IHX. left.
    eapply All_app in X as [_ X]. now inv X.
  - eapply IHX. left.
    eapply All_app in X0 as [_ X0]. now inv X0.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
    firstorder.
  - eapply (f_equal decompose_app) in x;
      rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. inv x.
    eapply OnOne2_All_mix_left in X; try eassumption.
    eapply OnOn2_contra; try eassumption.
(*     firstorder. *)
(*   - eapply (f_equal decompose_app) in x; *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try firstorder congruence. inv x. *)
(*     eapply OnOne2_All_mix_left in X. 2:exact H. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(*   - eapply OnOne2_All_mix_left in X. 2:exact H0. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(*   - eapply OnOne2_All_mix_left in X. 2:exact H. *)
(*     eapply OnOn2_contra; try eassumption. *)
(*     firstorder. *)
(* Qed. *)
Admitted.

Hint Constructors normal neutral : core.

Lemma normal_mk_Apps_inv:
  forall (Σ : global_env) (Γ : context) (t : term) (v : list term), ~ isApp t -> normal Σ Γ (mkApps t v) -> normal Σ Γ t /\ Forall (normal Σ Γ) v.
Proof.
(*   intros Σ Γ t v H H1. *)
(*   induction v using rev_ind. *)
(*   - split. eapply H1. econstructor.  *)
(*   - rewrite <- mkApps_nested in H1. cbn in H1. depelim H1. depelim H0. *)
(*     + split. *)
(*       * firstorder. *)
(*       * eapply app_Forall. firstorder. firstorder. *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_cstrapp with (v := []). econstructor. *)
(*       now eapply All_Forall.  *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_indapp with (v := []). econstructor. *)
(*       now eapply All_Forall. *)
(*     + change (tApp (mkApps t v) x0) with (mkApps (mkApps t v) [x0]) in *. *)
(*       rewrite mkApps_nested in x. *)
(*       eapply (f_equal decompose_app) in x. *)
(*       rewrite !decompose_app_mkApps in x; cbn in *; try congruence. firstorder. inv x. *)
(*       split. eapply nf_fix with (args := []). *)
(*       * eauto. *)
(*       * econstructor. *)
(*       * unfold head_arg_is_constructor in *. *)
(*         destruct unfold_fix; eauto. destruct p. *)
(*         unfold is_constructor in *. destruct n; reflexivity. *)
(*       * eauto. *)
(*       * now eapply All_Forall. *)
(* Qed. *)
Admitted.

Lemma neutral_mk_Apps_inv:
  forall (Σ : global_env) (Γ : context) (t : term) (v : list term), ~ isApp t -> neutral Σ Γ (mkApps t v) -> neutral Σ Γ t /\ Forall (normal Σ Γ) v.
Proof.
  intros Σ Γ t v H H1.
  induction v using rev_ind.
  - split. eapply H1. econstructor. 
  - rewrite <- mkApps_nested in H1. cbn in H1. depelim H1. 
    split.
    + firstorder.
    + eapply app_Forall. firstorder. firstorder.
Qed.

Lemma normal_mkApps Σ Γ t v :
  neutral Σ Γ t -> Forall (normal Σ Γ) v -> normal Σ Γ (mkApps t v).
Proof.
  intros. induction H0 in t, H |- *; cbn in *.
  - eauto.
  - eapply IHForall. eauto.
Qed.  
 *)
