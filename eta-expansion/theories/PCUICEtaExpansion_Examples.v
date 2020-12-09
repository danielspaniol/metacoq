(*******************************************************************************
 *                 ETA EXPANSION EXAMPLES
 *                 ======================
 *
 * This files contains some examples to show that the eta expansion can't
 * be completely wrong.
 ******************************************************************************)

From MetaCoq.Template Require Import utils config All.
From MetaCoq.PCUIC Require PCUICToTemplate TemplateToPCUIC.
From MetaCoq.PCUIC Require Import PCUICAst PCUICAstUtils PCUICTyping PCUICInversion PCUICSafeLemmata PCUICLiftSubst.
From MetaCoq.EtaExpansion Require PCUICEtaExpansion_Defs.

From Coq Require Vector.
From Coq Require Import ssreflect.

Module ToTemplate := PCUICToTemplate.
Module FromTemplate := TemplateToPCUIC.
Module Eta := PCUICEtaExpansion_Defs.

Local Existing Instance extraction_checker_flags.

(* Some assumptions to make handling of the context a bit easier *)

Axiom HΣ : forall Σ, ∥ wf_ext Σ ∥.
Axiom HΓ : forall Σ, ∥ wf_local Σ [] ∥.
Axiom Hwt : forall Σ tm, welltyped Σ [] tm.

Notation "f $ a" := (f a) (at level 50, only parsing).

(* Translate the quoted coq-term to PCUIC, perform eta-expansion on the global environment
   and the term itself, then translate back.

   Note how the term is still typed by it's old type.
   Unless you have some exotic types, this should always be the case.
   In the exotic cases the type would also have been eta-expanded. *)
Definition testη {A} (a : A) :=
  p <- tmQuoteRec a ;;
  let Σ  := FromTemplate.trans_global $ Ast.empty_ext p.1 in
  let ηΣ := Eta.trans_env Σ [] (HΣ Σ) (HΓ Σ) in
  let t  := FromTemplate.trans p.2 in
  let ηt := Eta.trans Σ [] (HΣ Σ) t (Hwt Σ t) in
  let t' := ToTemplate.trans ηt in
  tmUnquoteTyped A t'.

Unset Printing Notations.
Set Printing Implicit.

(* Eta expansion works on both constructors of nat (so non-function constructors are no problem) *)
MetaCoq Run (tm <- testη 0 ;; tmPrint tm).
MetaCoq Run (tm <- testη S ;; tmPrint tm).

(* Eta expansion works on both constructors of list (so multiple arguments are no problem) *)
MetaCoq Run (tm <- testη (@cons) ;; tmPrint tm).
MetaCoq Run (tm <- testη (@nil) ;; tmPrint tm).

(* Eta expansion works on both constructors of vectors (so more involved dependent types are no problem) *)
MetaCoq Run (tm <- testη (@Vector.cons) ;; tmPrint tm).
MetaCoq Run (tm <- testη (@Vector.nil) ;; tmPrint tm).

(* Eta expansion looks recursively in the term *)
MetaCoq Run (tm <- testη (fun X x xs => @cons X x xs) ;; tmPrint tm).

(* Some more complex expressions work too *)
MetaCoq Run (tm <- testη (if 1 is 0 then bool else Vector.t (list (Vector.t bool 1)) 2) ;; tmPrint tm).

