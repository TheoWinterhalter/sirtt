(* SIRTT, all in one file *)

(* I do not export Level to not export really short names like R,S,I *)
Require SAst SSubst SReduction SScoping STyping SSR.
Include SAst.
Include SSubst.
Include SReduction.
Include SScoping.
Include STyping.
Include SSR.