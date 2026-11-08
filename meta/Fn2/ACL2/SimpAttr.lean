module

public import Lean.Meta.Tactic.Simp.RegisterCommand
public meta import Lean.Meta.Tactic.Simp.Attr

public meta section

/-!
# Fn2.ACL2.SimpAttr: the dispatch simp set

`fn2_dispatch` collects the generated dispatch equations (`fns "F" [a0 ...] = some («F» a0 ...)`,
`guardOf "F" [...] = some («F».guard ...)`), so PW3's symbolic evaluation rewrites a call of a
translated function to the function itself without unfolding the dispatch.
-/

register_simp_attr fn2_dispatch

end
