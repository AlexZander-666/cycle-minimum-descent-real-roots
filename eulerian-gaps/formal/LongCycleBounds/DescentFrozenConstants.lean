import Lean.Elab.Term

/-! Name resolution for the fixed private declarations of earlier audited certificate modules. -/

open Lean Elab Term in
/-- Access a fixed declaration by its compiled module and original qualified name.
This only constructs a reference to an existing declaration, which the kernel checks. -/
elab "descentFrozenConst " source:ident decl:ident : term => do
  let compiled := mkPrivateNameCore source.getId decl.getId
  let _ ← getConstInfo compiled
  pure (mkConst compiled)
