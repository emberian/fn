"""Required semantic proof subjects, never evidence or a completion certificate.

Keep logical bodies distinct from selected executable attachments. Missing or
unsupported metadata stays a named frontier; a smaller graph is not success.
"""
import hashlib
from emit_certificate import (
    Atom,
    List,
    canonical_text,
    decode,
    fields as canonical_fields,
    is_lambda,
    object_list,
    show,
    validate_syntax_symbols,
)
from emit_embed import NATIVE, SPECIAL, calls_of

FUNCTION_LAYERS = ('acl2_body', 'lean_body', 'closed_calls', 'guard_domain',
                   'literal_representation', 'result_representation')
ROOT_LAYERS = ('admission_domain', 'domain_preservation', 'whole_arm', 'strict_join')


def canonical_digest(value):
    return hashlib.sha256(canonical_text(value).encode()).hexdigest()


def _symbols(value):
    if isinstance(value, List):
        return set().union(*(_symbols(x) for x in value)) if value else set()
    return {str(value)} if isinstance(value, Atom) else set()


def _call_sites(term, path=()):
    if not isinstance(term, List) or not term or term[0] == 'QUOTE':
        return
    if is_lambda(term[0]):
        yield from _call_sites(term[0][2], path+(0,2))
    else:
        yield str(term[0]), path, term
    for index, arg in enumerate(term[1:], 1):
        yield from _call_sites(arg, path+(index,))


def _is_canonical_symbol(atom, package=None, name=None):
    return (isinstance(atom, Atom)
            and hasattr(atom, 'symbol_package')
            and (package is None or atom.symbol_package == package)
            and (name is None or atom.symbol_name == name))


def _is_variable_symbol(atom):
    if not (isinstance(atom, Atom) and hasattr(atom, 'symbol_package')):
        return False
    if atom.symbol_package not in ('ACL2', 'COMMON-LISP'):
        return False
    if atom.symbol_name in ('NIL', 'T'):
        return False
    if len(atom.symbol_name) >= 2 and atom.symbol_name.startswith('*') and atom.symbol_name.endswith('*'):
        return False
    return True


def _is_function_symbol(atom):
    if not (isinstance(atom, Atom) and hasattr(atom, 'symbol_package')):
        return False
    if atom.symbol_package not in ('ACL2', 'COMMON-LISP'):
        return False
    if atom.symbol_name in ('NIL', 'T') or str(atom) in SPECIAL:
        return False
    return True


def _validate_canonical_term(raw_term, bound_vars=None):
    """Validate a canonical translated ACL2 term and return its free variable names."""
    if not isinstance(raw_term, List) or not raw_term:
        raise ValueError('malformed canonical term node')
    tag = str(raw_term[0])
    if tag == ':SYMBOL':
        sym = decode(raw_term)
        if not _is_variable_symbol(sym):
            raise ValueError('non-variable symbol in term position: ' + str(sym))
        if bound_vars is not None and str(sym) not in bound_vars:
            raise ValueError('variable outside measured subset: ' + str(sym))
        return {str(sym)}
    if tag != ':CONS':
        raise ValueError('unquoted literal in translated term: ' + tag)
    elems = object_list(raw_term)
    if not elems:
        raise ValueError('empty application in translated term')
    head_raw = elems[0]
    if not isinstance(head_raw, List) or not head_raw:
        raise ValueError('malformed application head')
    if str(head_raw[0]) == ':SYMBOL':
        head = decode(head_raw)
        if str(head) == 'QUOTE':
            if not _is_canonical_symbol(head, 'COMMON-LISP', 'QUOTE') or len(elems) != 2:
                raise ValueError('malformed QUOTE term')
            decode(elems[1])
            return set()
        if str(head) == 'IF':
            if not _is_canonical_symbol(head, 'COMMON-LISP', 'IF') or len(elems) != 4:
                raise ValueError('malformed IF term')
        elif str(head) == 'RETURN-LAST':
            if not _is_canonical_symbol(head, 'ACL2', 'RETURN-LAST') or len(elems) != 4:
                raise ValueError('malformed RETURN-LAST term')
        elif str(head) == 'LAMBDA' or not _is_function_symbol(head):
            raise ValueError('invalid function head in translated term: ' + str(head))
        used = set()
        for arg in elems[1:]:
            used |= _validate_canonical_term(arg, bound_vars)
        return used
    if str(head_raw[0]) == ':CONS':
        lam = object_list(head_raw)
        if len(lam) != 3:
            raise ValueError('malformed LAMBDA head')
        lam_sym = decode(lam[0])
        if not _is_canonical_symbol(lam_sym, 'COMMON-LISP', 'LAMBDA'):
            raise ValueError('compound head is not COMMON-LISP::LAMBDA')
        lam_formals_raw = object_list(lam[1])
        lam_formals = [decode(v) for v in lam_formals_raw]
        if any(not _is_variable_symbol(v) for v in lam_formals):
            raise ValueError('invalid LAMBDA formal parameter')
        lam_names = [str(v) for v in lam_formals]
        if len(set(lam_names)) != len(lam_names):
            raise ValueError('duplicate LAMBDA formal parameter')
        if len(lam_names) != len(elems) - 1:
            raise ValueError('LAMBDA arity mismatch')
        _validate_canonical_term(lam[2], set(lam_names))
        used = set()
        for arg in elems[1:]:
            used |= _validate_canonical_term(arg, bound_vars)
        return used
    raise ValueError('unsupported application head in translated term')


def decode_justification(raw_obj, formals=None):
    """Strictly decode an ACL2 canonical `(defrec justification ...)` export.

    ACL2 defines `(defrec justification (subset . ((subversive-p . (mp . rel))
    (measure . ruler-extenders))) nil)`, exported as the 4-element proper list:
      `(ACL2::JUSTIFICATION subset (subversive-p mp . rel) (measure . ruler-extenders))`
    """
    decoded = decode(raw_obj)
    if isinstance(decoded, Atom) and str(decoded) == ':MISSING':
        if not _is_canonical_symbol(decoded, 'KEYWORD', 'MISSING'):
            raise ValueError('malformed :MISSING justification marker')
        return {'state': 'missing'}
    if isinstance(decoded, Atom) and str(decoded) == 'NIL':
        return {'state': 'nil'}
    if not isinstance(raw_obj, List) or not raw_obj or str(raw_obj[0]) != ':CONS':
        raise ValueError('justification record must be a canonical cons list')
    items = object_list(raw_obj)
    if len(items) != 4:
        raise ValueError('justification record must have 4 elements')
    tag_obj, subset_obj, wfr_obj, measure_pair_obj = items
    tag = decode(tag_obj)
    if not _is_canonical_symbol(tag, 'ACL2', 'JUSTIFICATION'):
        raise ValueError('justification record lacks ACL2::JUSTIFICATION tag')
    subset_raw = object_list(subset_obj)
    subset_atoms = [decode(v) for v in subset_raw]
    if any(not _is_variable_symbol(v) for v in subset_atoms):
        raise ValueError('measured subset must contain variable symbols')
    subset = [str(v) for v in subset_atoms]
    if len(set(subset)) != len(subset):
        raise ValueError('duplicate variable in measured subset')
    if formals is not None and not (set(subset) <= set(formals)):
        raise ValueError('measured subset variable outside function formals')
    if not (isinstance(wfr_obj, List) and len(wfr_obj) == 3 and str(wfr_obj[0]) == ':CONS'):
        raise ValueError('malformed justification wfr cons')
    subv_obj, mp_rel_obj = wfr_obj[1], wfr_obj[2]
    if not (isinstance(mp_rel_obj, List) and len(mp_rel_obj) == 3 and str(mp_rel_obj[0]) == ':CONS'):
        raise ValueError('malformed justification domain/relation cons')
    mp_obj, rel_obj = mp_rel_obj[1], mp_rel_obj[2]
    subv = decode(subv_obj)
    if _is_canonical_symbol(subv, 'COMMON-LISP', 'NIL'):
        subversive = False
    elif _is_canonical_symbol(subv, 'COMMON-LISP', 'T'):
        subversive = True
    else:
        raise ValueError('malformed justification subversive flag')
    mp = decode(mp_obj)
    if not (_is_canonical_symbol(mp, 'COMMON-LISP', 'T') or _is_function_symbol(mp)):
        raise ValueError('malformed justification domain predicate')
    rel = decode(rel_obj)
    if not _is_function_symbol(rel):
        raise ValueError('malformed justification well-founded relation')
    if not (isinstance(measure_pair_obj, List) and len(measure_pair_obj) == 3
            and str(measure_pair_obj[0]) == ':CONS'):
        raise ValueError('malformed justification measure/ruler-extenders cons')
    measure_obj, rulers_obj = measure_pair_obj[1], measure_pair_obj[2]
    measure_term = decode(measure_obj)
    validate_syntax_symbols(List(subset_atoms), List([mp, rel]), measure_term)
    free_vars = sorted(_validate_canonical_term(measure_obj, set(subset)))
    rulers_dec = decode(rulers_obj)
    if (isinstance(rulers_dec, Atom) and _is_canonical_symbol(rulers_dec, 'KEYWORD')
            and rulers_dec.symbol_name in ('ALL', 'BASIC', 'LAMBDAS')):
        ruler_extenders = str(rulers_dec)
    else:
        ruler_items = [decode(r) for r in object_list(rulers_obj)]
        for r in ruler_items:
            if _is_canonical_symbol(r, 'KEYWORD', 'LAMBDAS'):
                continue
            if _is_canonical_symbol(r, 'COMMON-LISP', 'IF') or _is_canonical_symbol(r, 'ACL2', 'RETURN-LAST'):
                continue
            if _is_function_symbol(r):
                continue
            raise ValueError('malformed ruler-extender entry: ' + str(r))
        ruler_extenders = [str(r) for r in ruler_items]
    wfr_deps = []
    if not (_is_canonical_symbol(mp, 'COMMON-LISP', 'T') or _is_canonical_symbol(mp, 'ACL2', 'O-P')):
        wfr_deps.append(str(mp))
    if not _is_canonical_symbol(rel, 'ACL2', 'O<'):
        wfr_deps.append(str(rel))
    return {
        'state': 'present',
        'subset': subset,
        'free_vars': free_vars,
        'wfr': {
            'domain': str(mp),
            'domain_package': mp.symbol_package,
            'relation': str(rel),
            'relation_package': rel.symbol_package,
            'subversive': subversive,
        },
        'wfr_calls': sorted(set(wfr_deps)),
        'wfr_sha256': canonical_digest(wfr_obj),
        'measure': show(measure_term),
        'measure_term': measure_term,
        'measure_calls': sorted(calls_of(measure_term, set())),
        'measure_sha256': canonical_digest(measure_obj),
        'ruler_extenders': ruler_extenders,
        'ruler_extenders_sha256': canonical_digest(rulers_obj),
        'justification_sha256': canonical_digest(raw_obj),
    }


def _extract_canonical_formals(raw_formals):
    elems = object_list(raw_formals)
    atoms = [decode(v) for v in elems]
    if any(not _is_variable_symbol(v) for v in atoms):
        raise ValueError('formals must be variable symbols')
    names = [str(v) for v in atoms]
    if len(set(names)) != len(names):
        raise ValueError('duplicate formal parameter')
    return names, atoms


def function_semantics(name, row, fields):
    """Bind each obligation to exact canonical fields before proposal rewriting."""
    bound_fields = canonical_fields(row)
    if ':FUNCTION' not in bound_fields or str(decode(bound_fields[':FUNCTION'])) != name:
        raise ValueError('canonical function subject mismatch '+name)
    if fields != bound_fields:
        raise ValueError('canonical function fields mismatch '+name)
    hashes = {}
    decoded = {}
    states = {}
    frontiers = []
    for key in (':FORMALS', ':LOGICAL-BODY', ':GUARD', ':JUSTIFICATION', ':ATTACHMENT',
                ':STOBJS-IN', ':STOBJS-OUT'):
        if key not in fields:
            frontiers.append('missing field '+key)
            states[key] = 'absent'
            continue
        hashes[key] = canonical_digest(fields[key])
        try:
            decoded[key] = decode(fields[key])
            states[key] = ('missing' if str(decoded[key]) == ':MISSING' else
                           'nil' if str(decoded[key]) == 'NIL' else 'present')
        except (ValueError, TypeError) as error:
            frontiers.append('unsupported '+key+': '+str(error))
            states[key] = 'unsupported'
    for key in (':FORMALS', ':LOGICAL-BODY', ':GUARD', ':STOBJS-IN', ':STOBJS-OUT'):
        if str(decoded.get(key, ':MISSING')) == ':MISSING':
            frontiers.append('unresolved '+key)
    calls = {'body': [], 'guard': [], 'measure': [], 'wfr': []}
    sites = []
    for area, key in [('body', ':LOGICAL-BODY'), ('guard', ':GUARD')]:
        value = decoded.get(key)
        calls[area] = sorted(calls_of(value, set())) if value is not None else []
        for callee, path, term in _call_sites(value):
            if callee in NATIVE:
                sites.append({'site': area+':'+('.'.join(map(str,path)) or 'root'),
                              'callee': callee, 'field_sha256': hashes[key],
                              'term_sha256': hashlib.sha256(show(term).encode()).hexdigest()})
    selected = None
    attachment = decoded.get(':ATTACHMENT', Atom(':MISSING'))
    if str(attachment) not in ('NIL', ':MISSING'):
        if (isinstance(attachment, List) and len(attachment) == 3
                and str(attachment[0]) == name and str(attachment[1]) == '.'
                and isinstance(attachment[2], Atom) and str(attachment[2]) not in ('NIL', ':MISSING')):
            selected = str(attachment[2])
        else:
            frontiers.append('malformed attachment subject/selection')
    elif str(attachment) == ':MISSING':
        frontiers.append('unresolved :ATTACHMENT')
    justification_meta = None
    justification_symbols = []
    if states.get(':JUSTIFICATION') not in ('absent', 'unsupported'):
        raw_just = fields[':JUSTIFICATION']
        just_dec = decoded[':JUSTIFICATION']
        try:
            parsed = decode_justification(raw_just)
            states[':JUSTIFICATION'] = parsed['state']
            if parsed['state'] == 'present':
                if ':FORMALS' in fields and states.get(':FORMALS') not in ('missing', 'unsupported'):
                    formals_list, formal_atoms = _extract_canonical_formals(fields[':FORMALS'])
                    if not (set(parsed['subset']) <= set(formals_list)):
                        raise ValueError('measured subset variable outside function formals')
                    validate_syntax_symbols(List(formal_atoms), parsed['measure_term'])
                measure_term = parsed['measure_term']
                calls['measure'] = parsed['measure_calls']
                calls['wfr'] = parsed['wfr_calls']
                for callee, path, term in _call_sites(measure_term):
                    if callee in NATIVE:
                        sites.append({
                            'site': 'measure:' + ('.'.join(map(str, path)) or 'root'),
                            'callee': callee,
                            'field_sha256': parsed['measure_sha256'],
                            'term_sha256': hashlib.sha256(show(term).encode()).hexdigest(),
                        })
                if parsed['wfr']['subversive']:
                    frontiers.append('subversive justification')
                justification_meta = {
                    k: v for k, v in parsed.items()
                    if k not in ('state', 'measure_term', 'measure_calls', 'wfr_calls')
                }
        except (ValueError, TypeError) as error:
            states[':JUSTIFICATION'] = 'malformed'
            frontiers.append('malformed :JUSTIFICATION: ' + str(error))
            justification_symbols = sorted(_symbols(just_dec))
    return {'record_sha256': canonical_digest(row), 'fields': hashes, 'metadata_states': states, 'calls': calls,
            'primitive_sites': sites, 'selected_attachment': selected,
            'justification': justification_meta,
            'justification_symbols': justification_symbols,
            'frontiers': sorted(set(frontiers))}


def _recursive_components(graph):
    """Tarjan components include cross edges to already completed DFS siblings."""
    indices, low = {}, {}
    stack, stacked = [], set()
    components = []
    def visit(name):
        indices[name] = low[name] = len(indices)
        stack.append(name)
        stacked.add(name)
        for callee in graph[name]:
            if callee not in graph:
                continue
            if callee not in indices:
                visit(callee)
                low[name] = min(low[name], low[callee])
            elif callee in stacked:
                low[name] = min(low[name], indices[callee])
        if low[name] == indices[name]:
            component = []
            while True:
                member = stack.pop()
                stacked.remove(member)
                component.append(member)
                if member == name:
                    break
            if len(component) > 1 or name in graph[name]:
                components.append(component)
    for name in graph:
        if name not in indices:
            visit(name)
    return components


def semantic_inventory(functions, roots, native_boundary):
    """Produce a closed requirement inventory; no input status can mark it proved."""
    by_name = {row['name']:row for row in functions}
    if len(by_name) != len(functions):
        raise ValueError('duplicate semantic function subject')
    boundary = set(native_boundary)
    unknown_native = boundary - set(NATIVE) - SPECIAL
    inventory = []
    for root in roots:
        visited = set()
        graph = {}
        missing = set()
        frontiers = []
        obligations = {}
        def require(layer, subject, digest):
            key = layer+':'+subject
            value = {'id':key, 'layer':layer, 'subject':subject, 'source_sha256':digest}
            old = obligations.setdefault(key,value)
            if old != value:
                raise ValueError('conflicting semantic obligation '+key)
        def visit(name):
            if name in SPECIAL or name in NATIVE:
                return
            if name in visited:
                return
            visited.add(name)
            row = by_name.get(name)
            if row is None:
                missing.add(name)
                return
            semantic = row.get('semantic')
            if semantic is None:
                frontiers.append(name+': semantic record missing')
                return
            record_sha = row['record_sha256']
            if semantic['record_sha256'] != record_sha:
                raise ValueError('semantic record digest mismatch '+name)
            graph[name] = set()
            require('canonical_record',name,record_sha)
            for layer in FUNCTION_LAYERS:
                require(layer,name,record_sha)
            for item in semantic['frontiers']:
                frontiers.append(name+': '+item)
            for site in semantic['primitive_sites']:
                subject=name+'/'+site['site']+'/'+site['callee']
                require('primitive_domain',subject,site['field_sha256'])
                require('primitive_correspondence',subject,site['field_sha256'])
                if site['callee'] not in boundary:
                    frontiers.append(name+': primitive absent from canonical boundary '+site['callee'])
            for area in ('body', 'guard', 'measure', 'wfr'):
                for callee in semantic['calls'].get(area, ()):
                    graph[name].add(callee)
                    visit(callee)
            just_meta = semantic.get('justification')
            if just_meta is not None:
                for builtin_sym in (just_meta['wfr']['domain'], just_meta['wfr']['relation']):
                    if builtin_sym != 'T' and builtin_sym in by_name:
                        graph[name].add(builtin_sym)
                        visit(builtin_sym)
            selected = semantic['selected_attachment']
            if selected is not None:
                require('attachment_refinement',name,semantic['fields'][':ATTACHMENT'])
                graph[name].add(selected)
                visit(selected)
            for symbol in semantic.get('justification_symbols', ()):
                if symbol in by_name:
                    graph[name].add(symbol)
                    visit(symbol)
        visit(root['name'])
        for component in _recursive_components(graph):
            for member in component:
                entry = by_name[member]
                require('termination', member, entry['record_sha256'])
                just_meta = entry['semantic'].get('justification')
                if just_meta is not None:
                    require('measure_domain', member, just_meta['measure_sha256'])
                if entry['semantic']['metadata_states'].get(':JUSTIFICATION') in (
                        'missing', 'nil', 'absent', 'unsupported', 'malformed'):
                    frontiers.append(member+': recursive component has unresolved justification')
        root_record = by_name.get(root['name'],{}).get('record_sha256')
        for layer in ROOT_LAYERS:
            require(layer,root['name'],root_record)
        frontiers.extend('missing function '+name for name in sorted(missing))
        frontiers.extend('unsupported canonical native '+name for name in sorted(unknown_native))
        inventory.append({'name':root['name'], 'status':'pending',
                          'function_records':[{ 'name':name, 'record_sha256':by_name[name]['record_sha256']}
                                              for name in sorted(visited) if name in by_name],
                          'obligations':[obligations[k] for k in sorted(obligations)],
                          'frontiers':sorted(set(frontiers))})
    if len({row['name'] for row in inventory}) != len(inventory):
        raise ValueError('duplicate semantic root subject')
    return {'schema':1, 'kind':'required-obligations-only', 'roots':inventory}
