(*******************************************************************************
 *                   PCUIC ETA EXPANSION ON CONSTRUCTORS
 *                   ===================================
 *
 * This file contains the definitions for eta-expansion of constructors.
 * The basic idea is quite simple:
 * > Iterate over the PCUIC AST until you find an constructor,
 * > then call the actual eta-expansion on that constructor.
 *
 * The eta-expansion itself works by recursively adding lambda abstractions
 * for each of the argument types. For example:
 *
 *   current term                 | remaining type
 *  ------------------------------+--------------------------------------------
 *  η cons                        | Π(X : U). Π(x : X). Π(xs : List X). List X
 *  λ (η (cons 0))                | Π(x : X). Π(xs : List X). List X
 *  λ λ (η ((cons 1) 0))          | Π(xs : List X). List X
 *  λ λ λ (η (((cons 2) 1) 0))    | List X
 *  λ λ λ ((cons 2) 1) 0)         |
 ******************************************************************************)

From Equations Require Import Equations.

From MetaCoq.Template Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICSafeLemmata PCUICLiftSubst.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.

From Coq Require Import Program ssreflect.

(** ** The actual η-expansion *)
Section EtaExpansion.

  Fixpoint eta_expand (t T : term) : term :=
    match T with
    | tProd na A B => tLambda na A (eta_expand (tApp (lift0 1 t) (tRel 0)) B)
    | _            => t
    end.

End EtaExpansion.

(** ** Recursive transformation of PCUIC terms *)
Section Transformation.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).

  Section TransBrs.
    Context (trans : forall (Γ : context)(t : term) (Ht : welltyped Σ Γ t), term).

    Definition trans_brs Γ (brs : list (nat * term))
               (H : forall d, In d brs -> welltyped Σ Γ d.2) : list (nat * term) :=
      map_InP (fun br wt => let br' := trans Γ br.2 wt in (br.1, br')) brs H.
  End TransBrs.

  Section TransMfix.
    Context (trans : forall (Γ : context) (t : term) (Ht : welltyped Σ Γ t), term).

    Definition trans_mfix Γ (defs : mfixpoint term)
               (H : forall d, In d defs -> welltyped Σ (Γ ,,, PCUICLiftSubst.fix_context defs) d.(dbody)) : mfixpoint term :=
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
      map_InP (fun d wt =>
                 let dbody' := trans Γ' d.(dbody) wt in
                 ({| dname := d.(dname); rarg := d.(rarg); dbody := dbody'; dtype := d.(dtype) |})) defs H.
  End TransMfix.

  Equations? trans Γ (tm : term) (Ht : welltyped Σ Γ tm) : term :=
    {
      trans Γ (tRel n)              Ht => tRel n ;
      trans Γ (tVar i)              Ht => tVar i ;
      trans Γ (tEvar n l)           Ht => tEvar n (map_InP (trans Γ) l _) ;
      trans Γ (tSort u)             Ht => tSort u ;
      trans Γ (tProd na A B)        Ht => tProd na (trans Γ A _) (trans (vass na A :: Γ) B _) ;
      trans Γ (tLambda na A t)      Ht => tLambda na (trans Γ A _) (trans (vass na A :: Γ) t _) ;
      trans Γ (tLetIn na b B t)     Ht => tLetIn na (trans Γ b _) (trans Γ B _) (trans (vdef na b B :: Γ) t _) ;
      trans Γ (tApp u v)            Ht => tApp (trans Γ u _) (trans Γ v _) ;
      trans Γ (tConst k ui)         Ht => tConst k ui ;
      trans Γ (tInd ind ui)         Ht => tInd ind ui ;
      trans Γ (tConstruct ind n ui) Ht => let tm := tConstruct ind n ui in
                                              let ty := type_of Σ _ _ Γ tm Ht in
                                              eta_expand tm ty ;
      trans Γ (tCase indn p c brs)  Ht => tCase indn (trans Γ p _) (trans Γ c _) (trans_brs trans Γ brs _) ;
      trans Γ (tProj p c)           Ht => tProj p (trans Γ c _) ;
      trans Γ (tFix mfix idx)       Ht => tFix (trans_mfix trans Γ mfix _) idx ;
      trans Γ (tCoFix mfix idx)     Ht => tCoFix (trans_mfix trans Γ mfix _) idx
    }.
  Proof.
    all: case: HΣ => -[]* ; case: Ht => ?.
    11,12: by constructor.
    - move=> /inversion_Evar. done.
    - move=> /inversion_Prod   [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_Prod   [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_Lambda [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_Lambda [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 13 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 15 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 14 case => ?. move=> [H__brs ?].
      eapply All2_In in H__brs as [(? & (? & ?) & ?)]; eauto.
      eexists; eauto.
    - move=> /inversion_Proj   [] //= ?. do  6 case => ?. by eexists ; eauto.
    - move=> /inversion_Fix    [] //= ?. do  3 case => ?. move=> [H__fix ?].
      eapply All_In in H__fix as [[]] ; eauto.
      eexists; eauto.
    - move=> /inversion_CoFix  [] //= ?. do  3 case => ?. move=> [H__cofix ?].
      eapply All_In in H__cofix as [] ; eauto.
      eexists; eauto.
  Qed.

End Transformation.

(** ** Transformation of contexts and environments *)
Section EnvTrans.

  Local Existing Instance extraction_checker_flags.

  Context (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).
  Context (Γ : context) (Hwf : ∥ wf_local Σ Γ ∥).

  Program Definition trans_constant_body body : constant_body :=
    if body.(cst_body) is Some tm
    then
      {|
        cst_type := body.(cst_type) ;
        cst_body := Some (trans Σ HΣ Γ tm _) ;
        cst_universes := body.(cst_universes) ;
      |}
    else body.
  Admit Obligations. (* TODO: Use wf_local to show `body.(cst_body)` is welltyped *)

  Program Definition trans_context_decl decl : context_decl :=
    if decl.(decl_body) is Some tm
    then
      {|
        decl_name := decl.(decl_name) ;
        decl_body := Some (trans Σ HΣ Γ tm _) ;
        decl_type := decl.(decl_type) ;
      |}
    else decl.
  Admit Obligations. (* TODO: Use wf_local to show `decl.(decl_body)` is welltyped *)

  Definition trans_env :=
    let go decl := if decl is ConstantDecl b
                   then ConstantDecl (trans_constant_body b)
                   else decl in
    (map (on_snd go) Σ.1, Σ.2).

  Definition trans_ctx := map trans_context_decl Γ.

End EnvTrans.
