#!/usr/bin/env python3
"""Generate the selective available reader from the actual owner read source.

This is source specialization, not a second implementation of parsing or policy.
The legacy logical reader remains the raw reference.  The consumed route is
LOGIC mode with its guards owed (every form carries :verify-guards nil; the
host reaches it through raw Lisp, so no *1* evaluation changes): the chain's
measures are the source's, and the ledger keystones of books/owner-credits
over the read the host calls -- fn-mca-read-span-keeps-funded and its three
siblings -- are carried over the generated read under their fn-av- names
(lane proofs, PRF-1287: the read the host calls regains a proved subject).
The selective reference (fn-scr-command-available against fn-scr-command)
and the guards remain owed.
"""
from pathlib import Path
import argparse
import re
from proof_repl import forms, head_and_name
from available_command_emit import TOKEN
ROOT = Path(__file__).resolve().parents[1]
SOURCES = ('served-catalog-chain', 'owner-reader-read', 'owner-time-admission',
           'owner-article-slots', 'owner-credits')


def symbols(form):
    return {m.group().lower() for m in TOKEN.finditer(form)
            if m.group().lower().startswith('fn-')}


def renamed(form, mapping):
    return ''.join(mapping.get(m.group().lower(), m.group())
                   if not m.group().startswith('"') else m.group()
                   for m in TOKEN.finditer(form))


AUTH = '''(defun fn-av-scr-auth-delegate
    (as live trie lver arts cache archive index verdicts config observation injection wire-event
        v fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((restricted (fn-auth-access-read as config))
         (view (and restricted (fn-scr-cached-view as config archive index cache)))
         (a (if restricted (if view (fn-ag-car view)
                             (fn-auth-view-archive as config archive)) archive))
         (ix (if restricted (if view (fn-ag-cdr view)
                              (fn-auth-view-index as config archive index)) index))
         (r (fn-av-scr-peer-step
             (fn-auth-view-session as config) live trie lver arts a ix verdicts
             (fn-auth-view-config as (fn-auth-moderation-config as config) archive)
             observation injection wire-event v fn-arena fn-cat)))
    (fn-post-make-result (fn-auth-with-base as (fn-post-result-session r))
                         (fn-post-result-effects r) (fn-post-result-submission r))))'''


def logic_mode(form):
    """The form in :logic mode with its guard owed, never a :program twin."""
    if ':verify-guards' in form:
        return form
    return form.replace('(xargs ', '(xargs :verify-guards nil ', 1)


def render():
    inventory = []
    theorems = []
    for book in SOURCES:
        for form in forms((ROOT / f'books/{book}.lisp').read_text()):
            head, name = head_and_name(form)
            if head == 'defun':
                inventory.append((name, form))
            elif head == 'defthm' and book == 'owner-credits':
                theorems.append((name, form))
    affected = {'fn-scr-command', 'fn-scr-peer-arm'}
    while True:
        new = {name for name, form in inventory if symbols(form) & affected}
        if new <= affected:
            break
        affected |= new
    by_name = dict(inventory)
    needed = {'fn-mca-read-span'}
    while True:
        new = set().union(*(symbols(by_name[name]) & affected for name in needed))
        # Auth's restricted fallback is now the same peer route as the unrestricted one.
        if 'fn-scr-auth-delegate' in needed:
            new.add('fn-scr-peer-step')
        if new <= needed:
            break
        needed |= new
    mapping = {name: 'fn-av-' + name[3:] for name in needed}
    mapping['fn-scr-command'] = 'fn-scr-command-available'
    # The ledger keystones over the read: owner-credits' theorems whose
    # statement names a carried function, restated over the fn-av- chain.
    carried = [(name, form) for name, form in theorems if symbols(form) & needed]
    for name, _ in carried:
        mapping[name] = 'fn-av-' + name[3:]
    result = []
    for name, form in inventory:
        if name not in needed or name == 'fn-scr-command':
            continue
        if name == 'fn-scr-auth-delegate':
            result.append(AUTH)
            continue
        if name == 'fn-scr-peer-arm':
            form = form.replace('wire-event fn-arena fn-cat)', 'wire-event v fn-arena fn-cat)', 1)
            # Delegate reader commands through the same captured available route;
            # peer transfer and explicit transit arms preserve their original priority.
            form = form.replace('fn-pix-peer-delegate-pinned', 'fn-scr-peer-delegate')
            form = form.replace('wire-event fn-arena)', 'wire-event v fn-arena fn-cat)')
        if name == 'fn-scr-peer-step':
            form = form.replace('observation injection wire-event fn-arena fn-cat)',
                                'observation injection wire-event v fn-arena fn-cat)')
        form = renamed(form, mapping)
        result.append(logic_mode(form))
    result.append('; The ledger keystones over the read the host calls (books/owner-credits.lisp\n'
                  '; fn-mca-read-span-keeps-funded and its siblings), restated over this read.\n'
                  '(local (include-book "arithmetic-5/top" :dir :system))')
    for name, form in carried:
        result.append(renamed(form, mapping))
    return '''; Generated by tools/available_read_emit.py from the actual read chain.
; LOGIC source route with its guards owed (:verify-guards nil on every form):
; the selective reference and the carried frames are owed, not borrowed from
; the legacy raw-pinned route. All request decisions remain ACL2's.
(in-package "ACL2")
(include-book "owner-credits")
(include-book "served-available-commands")

''' + '\n\n'.join(result) + '\n'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--check', action='store_true')
    args = p.parse_args()
    target = ROOT / 'books/served-available-read.lisp'
    text = render()
    if args.check:
        return 0 if target.exists() and target.read_text() == text else 1
    target.write_text(text)
    return 0

if __name__ == '__main__':
    raise SystemExit(main())
