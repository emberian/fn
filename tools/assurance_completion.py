#!/usr/bin/env python3
"""Refuse product completion without qualified live claims and semantic coverage.

The scope selects rows from fn2-squares; it is not another obligation ledger.
No JSON status, witness, candidate count or existing .cert is admission evidence.
This command never launches a prover or changes the certificate cache.
"""
from pathlib import Path
import argparse
import hashlib
import json
import sys

BASE = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(BASE / 'tools'))
sys.path.insert(0, str(BASE / 'meta/emit'))
import ledger

BOOK = 'meta/emit/assurance-completion'
RESOURCE_BOOK = 'meta/emit/assurance-resource-join'
RESOURCE_SUBJECTS = ('FN2-MACHINE-RUN', 'FN2-TURN', 'FN2-EXEC-ATURN')
CATEGORIES = {'durable-acceptance', 'uncertainty', 'recovery', 'authorization',
              'identity', 'framing-parsing', 'ownership', 'persistent-reclamation',
              'resource-bounds', 'progress', 'consumer', 'peer-delivery'}


def sha(data):
    return hashlib.sha256(data).hexdigest()


def symbol(text):
    """Only inert, unqualified ACL2 symbols from a source-owned declaration."""
    if not isinstance(text, str) or not text or any(c not in 'ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-$' for c in text):
        raise ValueError('invalid scope symbol ' + repr(text))
    if text in ('NIL', 'T'):
        raise ValueError('invalid scope symbol ' + text)
    return text


def scope(root=BASE):
    value = json.loads((root / 'tools/assurance_scope.json').read_text())
    if value.get('schema') != 1 or value.get('name') != 'served-product':
        raise ValueError('unsupported completion scope')
    if not value.get('profile') or not value.get('assumptions'):
        raise ValueError('scope must name profile and assumptions')
    rows = value['requirements']
    categories = [row[0] for row in rows]
    if len(categories) != len(set(categories)) or set(categories) != CATEGORIES:
        raise ValueError('missing or duplicate required product category')
    for category, name, entries in rows:
        symbol(name)
        if not isinstance(entries, list) or not entries or len(entries) != len(set(entries)):
            raise ValueError('missing or duplicate required served entrypoint: ' + category)
        for entry in entries:
            symbol(entry)
    return value


def world_books(root, declaration):
    # Reuse the actual OWED assembly, not the stale rendered Markdown census.
    forms = ledger.read_forms((root / 'tools/owed-export.lsp').read_text())
    books = [str(f[1]) for f in forms if isinstance(f, list) and f and str(f[0]).lower() == 'include-book']
    books += declaration.get('world_books', [])
    for book in books:
        if Path(book).is_absolute() or '..' in Path(book).parts or not (root / (book + '.lisp')).is_file():
            raise ValueError('missing or escaping world book: ' + book)
    return list(dict.fromkeys(books))


def canonical(package):
    from emit_served_certificate import header, function_records, decode, as_list
    with package.open(newline='') as stream:
        h = header(stream)
        records = list(function_records(stream, int(str(h[':FUNCTION-COUNT']))))
    inventory = decode(h[':ARM-INVENTORY'])
    roots = []
    for row in inventory:
        if len(row) != 8:
            raise ValueError('malformed canonical served arm')
        roots.append(str(row[4] if str(row[5]) == 'NIL' else row[5]))
    if not roots or len(roots) != len(set(roots)):
        raise ValueError('empty or duplicate canonical served root')
    natives = [str(decode(n)) for n in as_list(h[':NATIVES'])]
    return h, records, roots, natives


def canonical_world_forms(root, package, declaration):
    from emit_served_certificate import canonical_text, decode, show, metadata_checks, packed_text, as_list
    h, records, roots, natives = canonical(package)
    lines = ['(in-package "ACL2")']
    for book in ['books/assurance-completion', 'books/assurance-resource-join',
                 'books/translation-validation', *world_books(root, declaration)]:
        lines.append('(include-book "../../' + book + '")')
    lines.extend(['(fn2-resolve :coverage)', '(fn2-seal :evidence :coverage :square)'])
    # Literal identities are forms in this book, hence part of its closure key.
    lines.append('(defconst *fn2-assurance-scope-identity* ' + json.dumps(sha(json.dumps(declaration, sort_keys=True).encode())) + ')')
    lines.append('(defconst *fn2-assurance-package-identity* ' + json.dumps(sha(package.read_bytes())) + ')')
    lines.append("(fn2-tv-check-manifest '" + canonical_text(h[':MANIFEST']) + ')')
    lines.append("(fn2-tv-check-arm-inventory '" + show(decode(h[':ARM-INVENTORY'])) + ')')
    lines.append(metadata_checks(h))
    lines.append("(fn2-tv-check-packed-functions '(")
    lines.extend('(' + name + ' . ' + packed_text(row) + ')' for name, row, fields in records)
    lines.append('))')
    refused = [str(decode(n)) for n in as_list(h[':REFUSED'])]
    lines.append("(fn2-tv-check-served-closure '(" + ' '.join(sorted(name for name, _, _ in records)) + ") '(" + ' '.join(refused) + '))')
    return lines


def resource_subject_requirements(package):
    """Bind actual caller ABI/domain records; these requirements are not proofs."""
    from emit_served_certificate import canonical_text, decode, show
    h, records, roots, natives = canonical(package)
    by_name = {name: (row, fields) for name, row, fields in records}
    result = []
    signatures = {
        'FN2-MACHINE-RUN': ('(ID BUDGET FN2-CORE)', '(NIL NIL FN2-CORE)', '(NIL NIL NIL NIL FN2-CORE)'),
        'FN2-TURN': ('(FN2-CORE)', '(FN2-CORE)', '(NIL NIL NIL NIL FN2-CORE)'),
        'FN2-EXEC-ATURN': ('(FN2-CORE)', '(FN2-CORE)', '(NIL)'),
    }
    for name in RESOURCE_SUBJECTS:
        if name not in by_name:
            raise ValueError('missing actual typed resource join subject: ' + name)
        row, fields = by_name[name]
        expected = dict(zip((':FORMALS', ':STOBJS-IN', ':STOBJS-OUT'), signatures[name]))
        expected[':GUARD'] = '(FN2-CORE-WFP FN2-CORE)'
        for key, shape in expected.items():
            if key not in fields or show(decode(fields[key])) != shape:
                raise ValueError(name + ': required caller ABI/domain mismatch in ' + key)
        if ':LOGICAL-BODY' not in fields or str(decode(fields[':LOGICAL-BODY'])) in ('NIL', ':MISSING'):
            raise ValueError(name + ': actual logical body missing')
        # Preserve exact canonical formals, guard, body and all remaining fields.
        result.append({'name': name, 'record_sha256': sha(canonical_text(row).encode()),
                       'fields': {key: sha(canonical_text(value).encode()) for key, value in fields.items()}})
    return result


def generated_resource_book(root, package, declaration):
    subjects = resource_subject_requirements(package)
    lines = canonical_world_forms(root, package, declaration)
    lines.append('(defconst *fn2-assurance-resource-subjects-identity* ' +
                 json.dumps(sha(json.dumps(subjects, sort_keys=True).encode())) + ')')
    lines.append('(fn2-join-served-resource-contracts)')
    return '\n'.join(lines) + '\n'


def generated_book(root, package, declaration):
    # A separate evidence book can qualify this actual-served facet while the
    # remaining required product guarantees are still incomplete.
    lines = ['(in-package "ACL2")', '(include-book "assurance-resource-join")']
    rows = ['(:' + category + ' ' + name + ' (' + ' '.join(entries) + '))'
            for category, name, entries in declaration['requirements']]
    lines.append("(fn2-assert-assurance-complete '(" + '\n'.join(rows) + '))')
    return '\n'.join(lines) + '\n'


def qualified_claims(root, launcher, book=BOOK):
    import acl2_toolchain, certs
    found = acl2_toolchain.fingerprint(launcher)
    if not found.qualified:
        raise ValueError('unqualified record ACL2 toolchain')
    entries = certs.book_entries(root, certs.cache_directory(), book,
                                metadata_filter=lambda m: m.get('toolchain_identity') == found.identity)
    entry = certs.choose_entry(entries, str(root.resolve()))
    if entry is None:
        raise ValueError('no qualified live-claim certificate at current completion closure: ' + book)
    directory, metadata = entry
    return {'cache_entry': str(directory), 'toolchain': found.identity,
            'certificate_sha256': metadata['cert_sha256']}


def semantic_problems(package, report):
    """Regenerate the ONE bridge requirement inventory, never trust its flags."""
    from served_semantic_inventory import function_semantics, semantic_inventory
    h, records, roots, natives = canonical(package)
    if sorted(r['name'] for r in report['roots']) != sorted(roots):
        raise ValueError('missing or extra required canonical served root in bridge report')
    functions = [{'name': name, 'record_sha256': sha(__import__('emit_served_certificate').canonical_text(row).encode()),
                  'semantic': function_semantics(name, row, fields)} for name, row, fields in records]
    inventory = semantic_inventory(functions, [{'name': n} for n in roots], natives)
    if report.get('semantic_inventory') != inventory:
        raise ValueError('bridge requirement inventory differs from canonical packet')
    # There is currently no typed evidence join discharging these obligations.
    # An authored 'complete' bit or whole-arm candidate pass cannot supply it.
    return ['semantic proof discharge join unavailable; ' + str(sum(len(r['obligations']) for r in inventory['roots'])) +
            ' required obligations remain pending across ' + str(len(roots)) + ' served roots']


def inspect(root, package, bridge_report, launcher):
    declaration = scope(root)
    expected = generated_book(root, package, declaration)
    target = root / (BOOK + '.lisp')
    problems = []
    resource_expected = None
    try:
        resource_expected = generated_resource_book(root, package, declaration)
        resource_target = root / (RESOURCE_BOOK + '.lisp')
        if not resource_target.is_file() or resource_target.read_text() != resource_expected:
            raise ValueError('typed resource join checker missing or stale; run --emit')
        qualified_claims(root, launcher, RESOURCE_BOOK)
    except (OSError, ValueError, KeyError) as error:
        problems.append('actual served resource join unavailable: ' + str(error))
    # Registry :depends edges do not establish the actual proof assumptions.
    # No extracted, qualified theorem/constraint dependency evidence exists yet.
    problems.append('actual theorem/constraint dependency closure unresolved; authored :depends is insufficient')
    if not target.is_file() or target.read_text() != expected:
        problems.append('completion checker missing or differs from current scope/canonical package; run --emit')
    else:
        try:
            qualified_claims(root, launcher)
        except (OSError, ValueError) as error:
            problems.append(str(error))
    try:
        from check_served_certificate import current
        current(bridge_report, root=root)
        if bridge_report['package_sha256'] != sha(package.read_bytes()):
            raise ValueError('bridge report names a different canonical package')
        problems.extend(semantic_problems(package, bridge_report))
    except (ImportError, OSError, ValueError, KeyError) as error:
        problems.append('semantic completion unavailable: ' + str(error))
    # Recheck generated identity after cache/report reads to refuse source drift.
    if declaration != scope(root) or expected != generated_book(root, package, declaration):
        problems.append('completion inputs changed during check')
    elif not target.is_file() or target.read_text() != expected:
        problems.append('completion checker bytes changed or are missing')
    else:
        try:
            qualified_claims(root, launcher)
        except (OSError, ValueError) as error:
            if str(error) not in problems:
                problems.append(str(error))
    if resource_expected is not None:
        if resource_expected != generated_resource_book(root, package, declaration):
            problems.append('typed resource join inputs changed during check')
        elif not resource_target.is_file() or resource_target.read_text() != resource_expected:
            problems.append('typed resource join checker bytes changed or are missing')
        else:
            try:
                qualified_claims(root, launcher, RESOURCE_BOOK)
            except (OSError, ValueError) as error:
                if str(error) not in problems:
                    problems.append(str(error))
    return problems


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', type=Path, required=True)
    parser.add_argument('--report', type=Path, default=BASE / 'build/served-certificate-coverage.json')
    parser.add_argument('--acl2', type=Path, default=BASE / 'tools/acl2')
    parser.add_argument('--emit', action='store_true', help='write proposed live-world checker; supplies no evidence')
    args = parser.parse_args()
    if args.emit:
        target = BASE / (BOOK + '.lisp')
        resource_target = BASE / (RESOURCE_BOOK + '.lisp')
        resource_target.write_text(generated_resource_book(BASE, args.package, scope()))
        target.write_text(generated_book(BASE, args.package, scope()))
        print('PROPOSAL ONLY: ' + str(resource_target) + '\nPROPOSAL ONLY: ' + str(target))
        return 0
    problems = inspect(BASE, args.package, json.loads(args.report.read_text()), args.acl2)
    print('ASSURANCE COMPLETION: ' + ('INCOMPLETE' if problems else 'COMPLETE'))
    for problem in problems:
        print('  ' + problem)
    return 1 if problems else 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (OSError, ValueError, KeyError, ImportError) as error:
        print('ASSURANCE COMPLETION: INCOMPLETE\n  ' + str(error))
        sys.exit(1)
