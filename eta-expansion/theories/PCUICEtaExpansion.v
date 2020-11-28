(*******************************************************************************
 * PCUIC η Expansion
 * =================
 *
 * This file implements η-expansion on constructors for PCUIC terms.
 * This works by recursively looking at the term and wrapping it in a lambda
 * if it is a constructor.
 *
 * For example:
 *    η-expand cons
 *  ⇒ λ. (η-expand (cons 0))
 *  ⇒ λ. λ. (η-expand (cons 0 1))
 *  ⇒ λ. λ. λ. (η-expand (cons 0 1 2))
 *  ⇒ λ. λ. λ. cons 0 1 2
 ******************************************************************************)

From Equations Require Import Equations.
From MetaCoq.Template Require Import config.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICSafeLemmata.
From MetaCoq.SafeChecker Require Import PCUICSafeRetyping.
From Coq Require Import Program ssreflect.

Section EtaExpansion.

  Local Existing Instance extraction_checker_flags.
  Variables (Σ : global_env_ext) (HΣ : ∥ wf_ext Σ ∥).

  Notation "f $ args" := (f args) (at level 60, only parsing).


  Local Fixpoint expand_term (t T : term) (lvl : nat) : term :=
    match T with
    | tProd na A (tProd _ _ _ as B) => tLambda na A $ expand_term t B (S lvl)
    | tProd na A _                  => tLambda na A t
    | _                             => t
    end.

  Equations? eta_expand Γ (t : term) (Ht : welltyped Σ Γ t) : term :=
    {
      eta_expand Γ (tRel n)              _  := tRel n ;
      eta_expand Γ (tVar i)              _  := tVar i ;
      eta_expand Γ (tEvar n l)           Ht := tEvar n $ map_InP (eta_expand Γ) l _ ;
      eta_expand Γ (tSort u)             _  := tSort u ;
      eta_expand Γ (tProd na A B)        Ht :=
        (* TODO: I think I need to place `A'` in Γ, but I don't know how to prove it and `Admitted` does not work... *)
        let A' := eta_expand Γ A _ in
        let B' := eta_expand (vass na A :: Γ) B _ in
        tProd na A' B' ;
        (* tProd   na $ eta_expand Γ A _ $ eta_expand (vass na A :: Γ) B _ ; *)
      eta_expand Γ (tLambda na A t)      Ht := tLambda na $ eta_expand Γ A _ $ eta_expand (vass na A :: Γ) t _ ;
      eta_expand Γ (tLetIn na b B t)     Ht := tLetIn  na $ eta_expand Γ b _ $ eta_expand Γ B _ $ eta_expand (vdef na b B :: Γ) t _ ;
      eta_expand Γ (tApp u v)            Ht := tApp $ eta_expand Γ u _ $ eta_expand Γ v _ ;
      eta_expand Γ (tConst k ui)         Ht := tConst k ui ;
      eta_expand Γ (tInd ind ui)         Ht := tInd ind ui ;
      eta_expand Γ (tConstruct ind n ui) Ht := let t := tConstruct ind n ui in expand_term t (type_of Σ _ _ Γ t Ht) 0 ;
      eta_expand Γ (tCase indn p c brs)  Ht := tCase indn $ eta_expand Γ p _ $ eta_expand Γ c _ $ brs (*TODO*) ;
      eta_expand Γ (tProj p c)           Ht := tProj p $ eta_expand Γ c _ ;
      eta_expand Γ (tFix mfix idx)       Ht := tFix mfix idx (*TODO*) ;
      eta_expand Γ (tCoFix mfix idx)     Ht := tCoFix mfix idx (*TODO*)
    }.
  Proof.
    clear eta_expand.
    all: case: HΣ => -[]* ; try case: Ht => ?.
    11,12: by constructor.
    - move=> /inversion_Evar. done.
    - move=> /inversion_Prod   [] //= ?. do  2 case => ?. by eexists ; eauto.
    - todo "Handle A'".
      (* move=> /inversion_Prod   [] //= ?. do  3 case => ?. by eexists ; eauto. *)
    - move=> /inversion_Lambda [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_Lambda [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 13 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 15 case => ?. by eexists ; eauto.
    (* - move=> /inversion_Case   [] //= ?. do 14 case => ?. *)
    (*   case=> H__all2 ?. eapply All2_In in H__all2 as [(x' & (? & ?) & ?)]; eauto. *)
    (*   by eexists; eauto. *)
    - move=> /inversion_Proj   [] //= ?. do  6 case => ?. by eexists ; eauto.
  Qed.


  Lemma expand_term_preserves_typing Γ t T :
    Σ ;;; Γ |- t : T ->
    Σ ;;; Γ |- (expand_term t T 0) : T.
  Proof.
    elim {Γ} => Γ.
    - admit. (* Does the expansion handle this correctly? *)
    - by constructor.
    - by constructor.
    - admit. (* Case needs more general IH *)
    - by econstructor ; eauto.
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
    - admit. (* Substitution makes this hard *)
  Admitted.



  Lemma η_preserves_typing Γ t T :
    Σ ;;; Γ |- t : T ->
    forall Ht, Σ ;;; Γ |- (eta_expand Γ t Ht) : T.
  Proof.
    elim {Γ} => Γ.
    - move=> n d H__wf H__d H__t. simp eta_expand. by constructor.
    - move=> ℓ H__wf ℓ_in_ℓs H__t. simp eta_expand. by constructor.
    - move=> x A B ℓ1 ℓ2 H1 IH1 H2 IH2 Ht. simp eta_expand. constructor.
      + apply: IH1.
      + todo "Need to use A', but can't `admit` the goal...".
    - move=> x A b ℓ B H1 IH1 H2 IH2 Ht. simp eta_expand.
      todo "Need to use A', but can't `admit` the goal...".
    - todo "Need to use A', but can't `admit` the goal...".
    - move=> u x A B v H1 IH1 H2 IH2 Ht. simp eta_expand.
      todo "Need to use v', but can't `admit` the goal...".
    - move=> *. simp eta_expand. by constructor.
    - todo "Need to use v', but can't `admit` the goal...".
    - move=> *. simp eta_expand. cbn. todo "Use expand_term_preserves_typing".
    - todo "Need to use v', but can't `admit` the goal...".
    - move=> *. simp eta_expand. 
      todo "Need to use A', but can't `admit` the goal...".
    - move=> *. simp eta_expand. by constructor.
    - move=> *. simp eta_expand. by constructor.
    - todo "don't know yet what to do".
  Qed.
