"""Required semantic proof subjects, never evidence or a completion certificate.

Keep logical bodies distinct from selected executable attachments. Missing or
unsupported metadata stays a named frontier; a smaller graph is not success.
"""
import hashlib
from emit_certificate import Atom, List, canonical_text, decode, fields as canonical_fields, is_lambda, show
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
    calls = {}
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
    justification = decoded.get(':JUSTIFICATION', Atom(':MISSING'))
    has_justification = str(justification) not in ('NIL', ':MISSING')
    if has_justification:
        # The canonical ACL2 justification record is not a term. Do not pretend
        # calls_of(record) is an exact measure decoder. Known symbols are a
        # conservative dependency hint; this frontier must still be discharged.
        frontiers.append('justification/measure binding requires a checked decoder')
    return {'record_sha256': canonical_digest(row), 'fields': hashes, 'metadata_states': states, 'calls': calls,
            'primitive_sites': sites, 'selected_attachment': selected,
            'justification_symbols': sorted(_symbols(justification)) if has_justification else [],
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
            for area in ('body','guard'):
                for callee in semantic['calls'][area]:
                    graph[name].add(callee)
                    visit(callee)
            selected = semantic['selected_attachment']
            if selected is not None:
                require('attachment_refinement',name,semantic['fields'][':ATTACHMENT'])
                graph[name].add(selected)
                visit(selected)
            for symbol in semantic['justification_symbols']:
                if symbol in by_name:
                    graph[name].add(symbol)
                    visit(symbol)
        visit(root['name'])
        for component in _recursive_components(graph):
            for member in component:
                entry = by_name[member]
                require('termination', member, entry['record_sha256'])
                if entry['semantic']['metadata_states'].get(':JUSTIFICATION') in ('missing', 'absent', 'unsupported'):
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
