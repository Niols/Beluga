(**
   @author Brigitte Pientka
   modified: Joshua Dunfield
*)

module LF : sig 

  open Syntax.Int.LF

  type error =
    | CtxVarMismatch   of mctx * ctx_var * schema
    | CtxVarDiffer     of mctx * ctx_var * ctx_var
    | IllTyped         of mctx * dctx * nclo * tclo
    | SigmaIllTyped    of mctx * dctx * trec_clo * trec_clo
    | TupleArity       of mctx * dctx * nclo * trec_clo
    | KindMismatch     of mctx * dctx * sclo * (kind * sub)
    | TypMismatch      of mctx * dctx * nclo * tclo * tclo
    | SpineIllTyped
    | SubIllTyped
    | LeftoverFV
    | CtxVarMisCheck	of mctx * dctx * tclo * schema
  exception Error of Syntax.Loc.t * error

  val check       : mctx -> dctx -> nclo -> tclo -> unit
  val syn         : mctx -> dctx -> nclo -> tclo
  val checkTyp    : mctx -> dctx -> tclo         -> unit
  val checkKind   : mctx -> dctx -> kind         -> unit
  val checkDCtx   : mctx -> dctx                 -> unit

  val checkSchemaWf : schema -> unit
  val checkSchema : Syntax.Loc.t -> mctx -> dctx -> schema -> unit
  val subsumes    : mctx -> ctx_var -> ctx_var -> bool

  val checkTypeAgainstSchema: Syntax.Loc.t ->  mctx -> dctx -> typ -> sch_elem list -> (typ_rec * sub)
  val instanceOfSchElem     : mctx -> dctx -> tclo -> sch_elem ->  (typ_rec * sub)
  val instanceOfSchElemProj : mctx -> dctx -> tclo -> (head * int) -> sch_elem -> (typ_rec * sub)

  val checkMSub   : Syntax.Loc.t -> mctx -> msub -> mctx -> unit

end


module Comp : sig 
  open Syntax.Int.Comp
  open Syntax.Int

  type typeVariant = VariantCross | VariantArrow | VariantCtxPi | VariantPiBox | VariantBox

  type error =
      MismatchChk     of LF.mctx * gctx * exp_chk * tclo * tclo
    | MismatchSyn     of LF.mctx * gctx * exp_syn * typeVariant * tclo
    | PatIllTyped     of LF.mctx * gctx * pattern * tclo * tclo
    | CtxFunMismatch  of LF.mctx * gctx  * tclo 
    | FunMismatch     of LF.mctx * gctx  * tclo 
    | MLamMismatch    of LF.mctx * gctx  * tclo 
    | PairMismatch    of LF.mctx * gctx  * tclo 
    | BoxMismatch     of LF.mctx * gctx  * tclo 
    | SBoxMismatch    of LF.mctx * gctx  * LF.dctx  * LF.dctx
    | SynMismatch     of LF.mctx * tclo (* expected *) * tclo (* inferred *)
    | SubPattMismatch of (LF.mctx * LF.dctx * LF.sub * LF.dctx) * 
                         (LF.mctx * LF.dctx * LF.dctx)  
    | BoxCtxMismatch  of LF.mctx * LF.dctx * (LF.psi_hat * LF.normal)
    | PattMismatch    of (LF.mctx * LF.dctx * LF.normal option * LF.tclo) * 
                         (LF.mctx * LF.dctx * LF.tclo)  
    | IfMismatch      of LF.mctx * gctx  * tclo 
    | EqMismatch      of LF.mctx * tclo (* arg1 *) * tclo (* arg2 *)
    | EqTyp           of LF.mctx * tclo 
    | MAppMismatch    of LF.mctx * (meta_typ * LF.msub)
    | AppMismatch     of LF.mctx * (meta_typ * LF.msub)

  exception Error of Syntax.Loc.t * error

  val check       : LF.mctx -> gctx -> exp_chk -> tclo -> unit
  val syn         : LF.mctx -> gctx -> exp_syn -> tclo
  val checkTyp    : LF.mctx -> typ                  -> unit

end


module Sgn : sig
  open Syntax.Int.Sgn

  val check_sgn_decls :  decl list -> unit
end
