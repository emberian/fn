# The hand half of the carrier move: the carrier book and the helper books
# rewritten over it.  Run after xf over a pristine tree.
import os,re,shutil,sys
H=os.path.join(os.path.dirname(os.path.abspath(__file__)),'hand')
for f in ('owner-carrier.lisp','owner-state-accessors.lisp','owner-retain-state.lisp'):
    shutil.copy(os.path.join(H,f),'books/'+f)
p='books/owner-obligation-state.lisp'
s=open(p).read()
i=s.index('; This is the exact host-called function, moved from owner-host.')
s=s[:i]+open(os.path.join(H,'obligation-tail.lisp')).read()
s=s.replace('(include-book "owner-config")','(include-book "owner-config")\n(include-book "owner-carrier")',1)
open(p,'w').write(s)
p='books/owner-retain-transitions.lisp'
s=open(p).read()
i=s.index('(defthm fn-owner-retain-carry-of-install-ocfg')
j=s.index('(defthm fn-owner-retain-statep-implies-entry-guard')
s=s[:i]+open(os.path.join(H,'retain-statep.lisp')).read()+s[j:]
open(p,'w').write(s)

# Prose that names the old globals, fixed where the transformer cannot.
FIX=[('books/owner-retain-carried.lisp',
 "(create-fn-arena$a) (create-fn-cat$a) (create-fn-hist$a)\n                           (fn-owner-retain-witness-state))",
 "(create-fn-arena$a) (create-fn-cat$a) (create-fn-hist$a)\n                           (create-fn-owner-st) (fn-owner-retain-witness-state))"),
('books/owner-recovery-retain.lisp',"""; only the report globals: the owner, its binding and the retain carry
; pass through it.""","""; only report globals of STATE; the owner's carrier passes through it by the
; stobj discipline (it takes no FN-OWNER-ST).""")]
for f,a,b in FIX:
    s=open(f).read()
    if a not in s: sys.exit('hand.py: fixup not found in %s: %r'%(f,a[:60]))
    open(f,'w').write(s.replace(a,b))
