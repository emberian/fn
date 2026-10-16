#!/bin/sh
# tools/cut_measure.sh [REF] -- the G4 line for the breaking cut (cut/breaking).
#
# Prints one line per measure and a final one-line summary that every commit
# on cut/breaking carries in its message (git commit -F with this output
# appended).  The four G4 commands are GOALS.md's, byte for byte; the fifth
# (executable-definition lines) and the sixth (books in the execution
# closure) are the proxies ANATOMY-20261009 used, computed here so they are
# in the repo.  REF defaults to HEAD; a working-tree measure uses `.`.
#
#   G4 <ref>: books F files L lines D def-forms | host H lines | exec E books X lines | tests/acl2 T books
set -eu
REF=${1:-HEAD}
cd "$(dirname "$0")/.."
if [ "$REF" = . ]; then
    files=$(find books -name '*.lisp' | wc -l | tr -d ' ')
    lines=$(find books -name '*.lisp' -print0 | xargs -0 cat | wc -l | tr -d ' ')
    defs=$(find books -name '*.lisp' -print0 | xargs -0 grep -h -E '^[[:space:]]*\((defun|defund|define|defun-inline|defun-sk|defexec|defmacro)[[:space:]]' | wc -l | tr -d ' ')
    host=$(find host -name '*.lisp' -print0 | xargs -0 cat | wc -l | tr -d ' ')
    tests=$(find tests/acl2 -name '*.lisp' | wc -l | tr -d ' ')
    label=worktree
else
    files=$(git ls-tree -r --name-only "$REF" books | grep -c '\.lisp$')
    lines=$(git grep -c '' "$REF" -- 'books/*.lisp' 'books/**.lisp' | awk -F: '{s+=$NF} END{print s}')
    defs=$(git grep -h -E '^[[:space:]]*\((defun|defund|define|defun-inline|defun-sk|defexec|defmacro)[[:space:]]' "$REF" -- 'books/*.lisp' 'books/**.lisp' | wc -l | tr -d ' ')
    host=$(git grep -c '' "$REF" -- 'host/*.lisp' 'host/**.lisp' | awk -F: '{s+=$NF} END{print s}')
    tests=$(git ls-tree -r --name-only "$REF" tests/acl2 | grep -c '\.lisp$')
    label=$(git rev-parse --short "$REF")
fi
# Execution closure: books reached, transitively through include-book, from
# the host files the image builds ld/load (the working tree; a REF other than
# the checked-out one is measured on its checkout, not on git history).
exec_line=$(python3 - <<'PY'
import re,os,glob
INC=re.compile(r'\(include-book\s+"([^"]+)"([^)]*)'); LD=re.compile(r'\((?:ld|load)\s+"([^"]+\.lisp)"')
SYS=('arithmetic','std/','ihs/','proto/','centaur/','tools/','misc/','coi/','kestrel/','projects/','rtl/','data-structures/','ordinals/','sorting/','clause-processors/','system/','xdoc/','acl2s/')
def includes(path):
    out=[]
    try: txt=open(path,errors='replace').read()
    except OSError: return out
    d=os.path.dirname(path)
    for name,rest in INC.findall(txt):
        if ':dir' in rest or (name.startswith(SYS) and not name.startswith('../')): continue
        p=os.path.normpath(os.path.join(d,name))+'.lisp'
        if p.startswith(('books/','host/')): out.append(p)
    return out
seeds=set()
for b in ['host/native/build.lisp','host/native/build-dtn.lisp','tools/extract/world-host.lisp']:
    if os.path.exists(b): seeds.update(p for p in LD.findall(open(b,errors='replace').read()) if p.startswith('host/'))
seen=set(); st=list(seeds)
while st:
    p=st.pop()
    if p in seen or not os.path.exists(p): continue
    seen.add(p); st.extend(includes(p))
books=[p for p in seen if p.startswith('books/')]
print(len(books), sum(sum(1 for _ in open(p,'rb')) for p in books))
PY
)
set -- $exec_line
printf 'books files %s\nbook lines %s\nbook def-forms %s\nhost lines %s\nexec-closure books %s\nexec-closure lines %s\ntests/acl2 books %s\n' "$files" "$lines" "$defs" "$host" "$1" "$2" "$tests"
printf 'G4 %s: books %s files %s lines %s def-forms | host %s lines | exec %s books %s lines | tests/acl2 %s books\n' "$label" "$files" "$lines" "$defs" "$host" "$1" "$2" "$tests"
