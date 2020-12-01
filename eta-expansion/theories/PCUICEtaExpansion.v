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

  Equations? eta_expand Γ (t : term) (Ht : welltyped Σ Γ t) : term :=
    {
      eta_expand Γ (tRel n)              _  := tRel n ;
      eta_expand Γ (tVar i)              _  := tVar i ;
      eta_expand Γ (tEvar n l)           Ht := tEvar n $ map_InP (eta_expand Γ) l _ ;
      eta_expand Γ (tSort u)             _  := tSort u ;
      eta_expand Γ (tProd na A B)        Ht :=
        let A' := eta_expand Γ A _ in
        let B' := eta_expand (vass na A' :: Γ) B _ in
        tProd na A' B' ;
      eta_expand Γ (tLambda na A t)      Ht := tLambda na $ eta_expand Γ A _ $ eta_expand (vass na A :: Γ) t _ ;
      eta_expand Γ (tLetIn na b B t)     Ht := tLetIn  na $ eta_expand Γ b _ $ eta_expand Γ B _ $ eta_expand (vdef na b B :: Γ) t _ ;
      eta_expand Γ (tApp u v)            Ht := tApp $ eta_expand Γ u _ $ eta_expand Γ v _ ;
      eta_expand Γ (tConst k ui)         Ht := tConst k ui ;
      eta_expand Γ (tInd ind ui)         Ht := tInd ind ui ;
      eta_expand Γ (tConstruct ind n ui) Ht := tConstruct ind n ui ;
      eta_expand Γ (tCase indn p c brs)  Ht := tCase indn $ eta_expand Γ p _ $ eta_expand Γ c _ $ brs  ;
      eta_expand Γ (tProj p c)           Ht := tProj p $ eta_expand Γ c _ ;
      eta_expand Γ (tFix mfix idx)       Ht := tFix mfix idx (*TODO*) ;
      eta_expand Γ (tCoFix mfix idx)     Ht := tCoFix mfix idx (*TODO*)
    }.
  Proof.
    all: case: HΣ => -[]* ; try case: Ht => ?.
    - move=> /inversion_Evar. done.
    - move=> /inversion_Prod   [] //= ?. do  2 case => ?. by eexists ; eauto.
    - todo "Handle A'".
    - move=> /inversion_Lambda [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_Lambda [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  3 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  2 case => ?. by eexists ; eauto.
    - move=> /inversion_LetIn  [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_App    [] //= ?. do  4 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 13 case => ?. by eexists ; eauto.
    - move=> /inversion_Case   [] //= ?. do 15 case => ?. by eexists ; eauto.
    - move=> /inversion_Proj   [] //= ?. do  6 case => ?. by eexists ; eauto.
  Qed.
(*
    Produces
    > Error: Anomaly "Uncaught exception Not_found." Please report at http://coq.inria.fr/bugs/.
    Change the `Qed` to `Admitted` for a
    > Error: Anomaly "more than one statement." Please report at http://coq.inria.fr/bugs/.
*)



End EtaExpansion.
