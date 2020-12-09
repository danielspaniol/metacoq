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
  a' <- tmUnquoteTyped A t' ;;
  tmPrint a'.

Unset Printing Notations.
Set Printing Implicit.

MetaCoq Run (testη 0).
(*=> O *)
MetaCoq Run (testη S).
(*=> (fun H : nat => S H) *)

MetaCoq Run (testη (@cons)).
(*=> (fun (A : Type) (H : A) (H0 : list A) => @cons A H H0) *)
MetaCoq Run (testη (@nil)).
(*=> (fun A : Type => @nil A) *)

MetaCoq Run (testη (@Vector.cons)).
(*=> (fun (A : Type) (h : A) (n : nat) (H : VectorDef.t A n) => VectorDef.cons A h n H)*)
MetaCoq Run (testη (@Vector.nil)).
(*=> (fun A : Type => VectorDef.nil A)*)

MetaCoq Run (testη (fun X x xs => @cons X x xs)).
(*=> (fun (X : Type) (x : X) (xs : list X) => (fun (A : Type) (H : A) (H0 : list A) => @cons A H H0) X x xs) *)

MetaCoq Run (testη (if 1 is 0 then bool else Vector.t (list (Vector.t bool 1)) 2)).
(*=> match (fun H : nat => S H) O with
     | O => bool
     | S _ => VectorDef.t (list (VectorDef.t bool ((fun H : nat => S H) O))) ((fun H : nat => S H) ((fun H : nat => S H) O))
     end *)

Inductive rosetree T := mkTree of T & list $ rosetree T.
MetaCoq Run (testη mkTree).
(*=> (fun (T : Type) (H : T) (H0 : list (rosetree T)) => mkTree T H H0) *)

Inductive SN {X} (R : X -> X -> Prop) x := sn of forall y, R x y -> SN R y.
MetaCoq Run (testη (@sn)).
(*=> (fun (X : Type) (R : forall (_ : X) (_ : X), Prop) (x : X) (H : forall (y : X) (_ : R x y), @SN X R y) => @sn X R x H) *)
