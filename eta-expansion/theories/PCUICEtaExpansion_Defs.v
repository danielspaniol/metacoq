(*******************************************************************************
 *                   PCUIC ETA EXPANSION ON CONSTRUCTORS
 *                   ===================================
 *
 * This file contains the definitions for eta-expansion of constructors.
 * The basic idea is quite simple:
 *    Iterate over the PCUIC AST until you find an constructor,
 *    then call the actual eta-expansion on that constructor.
 *
 * The eta-expansion itself works by recursively adding lambda abstractions
 * for each of the arguments. For example:
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

(** Haskell's $ notation can come in handy *)
Notation "f $ a" := (f a) (at level 50).

(** ** The actual η-expansion *)
Section EtaExpansion.

  Fixpoint eta_expand (t T : term) : term :=
    match T with
    | tProd na A B => tLambda na A $ eta_expand (tApp (lift0 1 t) (tRel 0)) B
    | _            => t
    end.

End EtaExpansion.

(** ** Recursive transformation of PCUIC terms *)
Section Transformation.

  Local Existing Instance extraction_checker_flags.

  Section TransBrs.
    Context (trans : forall (Σ : global_env_ext) (Γ : context) (HΣ : ∥ wf_ext Σ ∥) (t : term) (Ht : welltyped Σ Γ t), term).

    Definition trans_brs Σ Γ HΣ (brs : list (nat * term))
               (H : forall d, In d brs -> welltyped Σ Γ d.2) : list (nat * term) :=
      map_InP (fun br wt => let br' := trans Σ Γ HΣ br.2 wt in (br.1, br')) brs H.
  End TransBrs.

  Section TransMfix.
    Context (trans : forall (Σ : global_env_ext) (Γ : context) (HΣ : ∥ wf_ext Σ ∥) (t : term) (Ht : welltyped Σ Γ t), term).


    Definition trans_mfix Σ Γ HΣ (defs : mfixpoint term)
               (H : forall d, In d defs -> welltyped Σ (Γ ,,, PCUICLiftSubst.fix_context defs) d.(dbody)) : mfixpoint term :=
      let Γ' := (PCUICLiftSubst.fix_context defs ++ Γ)%list in
      map_InP (fun d wt =>
                 let dbody' := trans Σ Γ' HΣ d.(dbody) wt in
                 ({| dname := d.(dname); rarg := d.(rarg); dbody := dbody'; dtype := d.(dtype) |})) defs H.
  End TransMfix.

  Equations? trans Σ Γ (HΣ : ∥ wf_ext Σ ∥) (tm : term) (Ht : welltyped Σ Γ tm) : term :=
    {
      trans Σ Γ HΣ (tRel n)              Ht => tRel n ;
      trans Σ Γ HΣ (tVar i)              Ht => tVar i ;
      trans Σ Γ HΣ (tEvar n l)           Ht => tEvar n $ map_InP (trans Σ Γ HΣ) l _ ;
      trans Σ Γ HΣ (tSort u)             Ht => tSort u ;
      trans Σ Γ HΣ (tProd na A B)        Ht => tProd na $ trans Σ Γ HΣ A _ $ trans Σ (vass na A :: Γ) HΣ B _ ;
      trans Σ Γ HΣ (tLambda na A t)      Ht => tLambda na $ trans Σ Γ HΣ A _ $ trans Σ (vass na A :: Γ) HΣ t _ ;
      trans Σ Γ HΣ (tLetIn na b B t)     Ht => tLetIn na $ trans Σ Γ HΣ b _ $ trans Σ Γ HΣ B _ $ trans Σ (vdef na b B :: Γ) HΣ t _ ;
      trans Σ Γ HΣ (tApp u v)            Ht => tApp $ trans Σ Γ HΣ u _ $ trans Σ Γ HΣ v _ ;
      trans Σ Γ HΣ (tConst k ui)         Ht => tConst k ui ;
      trans Σ Γ HΣ (tInd ind ui)         Ht => tInd ind ui ;
      trans Σ Γ HΣ (tConstruct ind n ui) Ht => let tm := tConstruct ind n ui in
                                              let ty := type_of Σ _ _ Γ tm Ht in
                                              eta_expand tm ty ;
      trans Σ Γ HΣ (tCase indn p c brs)  Ht => tCase indn $ trans Σ Γ HΣ p _ $ trans Σ Γ HΣ c _ $ trans_brs trans Σ Γ HΣ brs _ ;
      trans Σ Γ HΣ (tProj p c)           Ht => tProj p $ trans Σ Γ HΣ c _ ;
      trans Σ Γ HΣ (tFix mfix idx)       Ht => tFix $ trans_mfix trans Σ Γ HΣ mfix _ $ idx ;
      trans Σ Γ HΣ (tCoFix mfix idx)     Ht => tCoFix $ trans_mfix trans Σ Γ HΣ mfix _ $ idx
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
      eapply All2_In in H__brs as [(x' & (? & ?) & ?)]; eauto.
      cbn in *. eexists; eauto.
    - move=> /inversion_Proj   [] //= ?. do  6 case => ?. by eexists ; eauto.
    - move=> /inversion_Fix    [] //= ?. do  3 case => ?. move=> [H__fix ?].
      eapply All_In in H__fix as [[? _]] ; eauto.
      eexists; eauto.
    - move=> /inversion_CoFix    [] //= ?. do  3 case => ?. move=> [H__cofix ?].
      eapply All_In in H__cofix as [?] ; eauto.
      eexists; eauto.
  Qed.

  Program Definition trans_constant_body Σ Γ HΣ (Hwf : ∥ wf_local Σ Γ ∥) body : constant_body :=
    if body.(cst_body) is Some tm
    then
      {|
        cst_type := body.(cst_type) ;
        cst_body := Some $ trans Σ Γ HΣ tm _ ;
        cst_universes := body.(cst_universes) ;
      |}
    else body.
  Admit Obligations. (* TODO: How to use wf_local here? *)

  Program Definition trans_context_decl Σ Γ HΣ (Hwf : ∥ wf_local Σ Γ∥) decl : context_decl :=
    if decl.(decl_body) is Some tm
    then
      {|
        decl_name := decl.(decl_name) ;
        decl_body := Some $ trans Σ Γ HΣ tm _ ;
        decl_type := decl.(decl_type) ;
      |}
    else decl.
  Admit Obligations. (* TODO: How to use wf_local here? *)

  Definition trans_env Σ Γ HΣ Hwf :=
    let go decl := if decl is ConstantDecl b
                   then ConstantDecl $ trans_constant_body Σ Γ HΣ Hwf b
                   else decl in
    (map (on_snd go) Σ.1, Σ.2).

  Definition trans_ctx Σ Γ HΣ Hwf := map (trans_context_decl Σ Γ HΣ Hwf) Γ.

End Transformation.
