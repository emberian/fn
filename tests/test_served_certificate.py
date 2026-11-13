"""Controls for the generated coverage boundary; proof gates run separately."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

ROOT=Path(__file__).parents[1]
def module(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'meta/emit'/(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
c=module('check_served_certificate')
e=module('emit_served_certificate')

class CoverageControls(unittest.TestCase):
    def test_attachment_proposal_preserves_logical_body_and_argument_order(self):
        missing=e.Atom(':MISSING'); attached=e.Atom('FN2-HOOK-IMPL')
        call=e.proposal_body(missing, ['ID', 'BUDGET', 'FN2-CORE'], attached)
        self.assertEqual(call, e.List([attached, e.Atom('ID'), e.Atom('BUDGET'), e.Atom('FN2-CORE')]))
        # An attachment must not replace a real logical body, including NIL.
        for body in [e.Atom('NIL'), e.List([e.Atom('QUOTE'), e.Atom('NIL')])]:
            self.assertEqual(e.proposal_body(body, ['ID'], attached), body)
        self.assertEqual(e.proposal_body(missing, ['ID'], e.Atom('NIL')), missing)
        with self.assertRaisesRegex(ValueError, 'attachment must name'):
            e.proposal_body(missing, ['ID'], e.List([attached]))

    def test_elan_proxy_does_not_hide_selected_compiler_changes(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); (root/'meta').mkdir(); (root/'tool/bin').mkdir(parents=True)
            (root/'tool/lib/lean').mkdir(parents=True)
            for p in ['meta/lean-toolchain', 'meta/lake-manifest.json', 'proxy', 'tool/bin/lean', 'tool/lib/lean/libleanshared.so']:
                (root/p).write_text(p)
            def query(args, **kwargs):
                self.assertEqual(kwargs['cwd'], root/'meta')
                return str(root/'tool') if args[-1]=='--print-prefix' else 'Lean 4.30.0'
            with mock.patch.object(c.shutil,'which',return_value=str(root/'proxy')), \
                 mock.patch.object(c.subprocess,'check_output',side_effect=query):
                a=c.toolchain_fingerprint(root)
                (root/'tool/bin/lean').write_text('different selected compiler')
                b=c.toolchain_fingerprint(root)
                self.assertNotEqual(a,b)
                (root/'tool/lib/lean/libleanshared.so').write_text('different runtime')
                self.assertNotEqual(b,c.toolchain_fingerprint(root))

    def test_dependency_rebuild_artifact_invalidates_downstream(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td); (root/'meta/Fn2').mkdir(parents=True)
            (root/'meta/Fn2/A.lean').write_text('def a := 1')
            (root/'meta/Fn2/B.lean').write_text('import Fn2.A\ndef b := 2')
            lib=root/'lib'; cache={}; calls=[]; revision=[0]
            def compile_fake(source, lib, seconds, logname, **kwargs):
                calls.append(source)
                artifact=lib/Path(source).relative_to('meta').with_suffix('.olean')
                artifact.parent.mkdir(parents=True,exist_ok=True)
                artifact.write_text(source+str(revision[0]))
                log=root/'log'; log.write_text('checked')
                return 0,'checked','log'
            with mock.patch.object(c,'compile_one',side_effect=compile_fake):
                c.compile_closure(['Fn2.B'],lib,5,1,root=root,cache=cache,tool='tool')
                calls.clear(); revision[0]=1
                (lib/'Fn2/A.olean').write_text('damaged artifact')
                c.compile_closure(['Fn2.B'],lib,5,1,root=root,cache=cache,tool='tool')
                self.assertEqual(calls,['meta/Fn2/A.lean','meta/Fn2/B.lean'])

    def test_proposals_never_count(self):
        report={'functions':[{'name':'F','canonical_export':'proposed'}],
          'roots':[{'name':'ARM','status':'unvalidated','reason':'not checked'}], 'unresolved':['MISSING']}
        text=c.summary(report)
        self.assertIn('0/1 validated',text)
        for name in ['F:','ARM:','MISSING:']: self.assertIn(name,text)

    def test_census_is_named_and_rejects_extra_axioms(self):
        self.assertTrue(c.census("'N.validated' depends on axioms: [propext, Quot.sound]",'N.validated'))
        self.assertFalse(c.census("'Other.validated' does not depend on any axioms",'N.validated'))
        for extra in ['sorryAx','UnprovedContract']:
            self.assertFalse(c.census("'N.validated' depends on axioms: ["+extra+"]",'N.validated'))
        self.assertFalse(c.census("warning: declaration uses 'sorry'\n'N.validated' does not depend on any axioms",'N.validated'))

    def test_stale_body_and_package_invalidate_coverage(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'package';p.write_text('package')
            b=root/'proof';b.write_text('checked body')
            report={'package':'package','package_sha256':e.digest(p),'inputs':{'proof':e.digest(b)},
              'roots':[],'functions':[]}
            c.current(report,root)
            b.write_text('altered body')
            with self.assertRaisesRegex(ValueError,'input changed'):c.current(report,root)
            b.write_text('checked body');p.write_text('different attachment')
            with self.assertRaisesRegex(ValueError,'package changed'):c.current(report,root)

    def test_duplicate_root_cannot_inflate_denominator(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);p=root/'package';p.write_text('package')
            report={'package':'package','package_sha256':e.digest(p),'inputs':{},
              'roots':[{'name':'F'},{'name':'F'}],'functions':[]}
            with self.assertRaisesRegex(ValueError,'duplicate roots'):c.current(report,root)

    def test_missing_function_record_is_not_ignored(self):
        with self.assertRaisesRegex(ValueError,'function count'):
            list(e.function_records([],1))

    def test_commit_phase_is_not_a_durable_statement(self):
        decl=e.List([e.List([e.Atom(':CASE'),e.Atom('PHASE'),
          e.List([e.Atom(':COMMIT'),e.List([e.Atom(':IDLE')])])])])
        self.assertEqual(e.statement_words(decl),{':CASE',':IDLE'})
        self.assertNotIn('durable-word',e.proof_obligations(decl))

    def test_packed_symbol_keeps_package_and_name(self):
        obj=e.read_canonical('(:SYMBOL (65 67 76 50) (70 79 79))')
        self.assertEqual(e.packed_text(obj),'(:PACKED-SYMBOL "ACL2" "FOO")')
        obj=e.read_canonical('(:SYMBOL (65) (34 92))')
        self.assertEqual(e.packed_text(obj),'(:PACKED-SYMBOL "A" "\\"\\\\")')

    def test_list_constant_keeps_every_element(self):
        value=e.alist_value(e.List([e.Atom('K'),e.Atom('1'),e.Atom('2'),e.Atom('3')]))
        self.assertEqual(value,e.List([e.Atom('1'),e.Atom('2'),e.Atom('3')]))

    def test_parse_and_batch_module_slices_scope_and_reject_axioms(self):
        m0=e.as_module('import Fn2.Arms.Core\nnamespace Fn2.Arms.Served.Root0Proof\ntheorem t : True := trivial\nend Fn2.Arms.Served.Root0Proof\n',
          expose=True, import_all=('Init.Data.String.Basic',))
        m1=e.as_module('import Fn2.Arms.Core\nimport Fn2.Arms.Wrapper\nnamespace Fn2.Arms.Served.Root1Proof\ntheorem t : True := trivial\nend Fn2.Arms.Served.Root1Proof\n',
          expose=True, import_all=('Init.Data.String.Basic',))
        s0=c.parse_module_slice(m0); s1=c.parse_module_slice(m1)
        self.assertIsNotNone(s0); self.assertIsNotNone(s1)
        batched,ranges=c.build_batch_source([(0,*s0),(1,*s1)])
        self.assertEqual(batched.count('public import Fn2.Arms.Core'),1)
        self.assertEqual(batched.count('import all Init.Data.String.Basic'),1)
        self.assertIn('section Batch_Root0Proof',batched)
        self.assertIn('section Batch_Root1Proof',batched)
        self.assertLess(ranges[0][1],ranges[1][0])
        with_axiom=m0.replace('theorem t','axiom bad : False\ntheorem t')
        self.assertIsNone(c.parse_module_slice(with_axiom))

    def test_batched_lean_gates_cache_invalidation_and_error_isolation(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            (root/'meta/Fn2/Arms').mkdir(parents=True)
            (root/'meta/Fn2/Instances/ServedCertificates').mkdir(parents=True)
            (root/'meta/lean-toolchain').write_text('v4.30.0\n')
            (root/'meta/lake-manifest.json').write_text('{}\n')
            (root/'meta/Fn2/Arms/Wrapper.lean').write_text('module\n@[expose] public section\nend\n')
            for k in range(1,5):
                (root/f'meta/Fn2/Instances/LayerAEqns{k}.lean').write_text('module\n@[expose] public section\nend\n')
            cpath='meta/Fn2/Instances/ServedCertificates/Kind0Contracts.lean'
            (root/cpath).write_text(e.as_module(
              'import Fn2.Arms.Wrapper\nnamespace Fn2.Arms.Served.Root0\ndef contract := True\nend Fn2.Arms.Served.Root0\n'
              'namespace Fn2.Arms.Served.Root1\ndef contract := True\nend Fn2.Arms.Served.Root1\n'
              'namespace Fn2.Arms.Served.Root2\ndef contract := True\nend Fn2.Arms.Served.Root2\n', expose=True))
            for ri in range(3):
                pp=root/f'meta/Fn2/Instances/ServedCertificates/Root{ri}Proof.lean'
                pp.write_text(e.as_module(
                  f'import Fn2.Instances.ServedCertificates.Kind0Contracts\nnamespace Fn2.Arms.Served.Root{ri}Proof\n'
                  f'theorem validated : True := trivial\n'
                  f'theorem accepted_entry_positive : True := trivial\n'
                  f'theorem omitted_child_rejected : True := trivial\n'
                  f'end Fn2.Arms.Served.Root{ri}Proof\n', expose=True))

            calls=[]
            fail_root=set()
            def fake_compile_one(source, lib, seconds, logname, root=root, write_olean=True):
                src_p=Path(source) if Path(source).is_absolute() else (root/source)
                calls.append((src_p.name, write_olean))
                txt=src_p.read_text()
                if write_olean:
                    out=lib/src_p.relative_to(root/'meta').with_suffix('.olean')
                    out.parent.mkdir(parents=True,exist_ok=True)
                    out.write_text('olean:'+src_p.name)
                lines=[]
                rc=0
                for ri in range(3):
                    ns=f'Fn2.Arms.Served.Root{ri}Proof'
                    if f'namespace {ns}' in txt:
                        if ri in fail_root:
                            rc=1
                            ln=next(idx+1 for idx,l in enumerate(txt.splitlines()) if f'namespace {ns}' in l)
                            lines.append(f'{src_p.name}:{ln}:0: error: tactic failed')
                        else:
                            for t in c.ROOT_THEOREMS:
                                lines.append(f"'{ns}.{t}' depends on axioms: [propext, Quot.sound]")
                out_str='\n'.join(lines)+('\n' if lines else '')
                log=root/'build/served-certificate-gates'/logname
                log.parent.mkdir(parents=True,exist_ok=True)
                log.write_text(out_str)
                return rc, out_str, str(log.relative_to(root))

            def make_report():
                return {'gates':{}, 'commit_words':0, 'roots':[
                  {'name':f'R{ri}','kind':'K0','contract':cpath,
                   'proof':f'meta/Fn2/Instances/ServedCertificates/Root{ri}Proof.lean',
                   'status':'unvalidated','reason':'pending'} for ri in range(3)]}

            fake_bin=root/'fake-lean'; fake_bin.write_text('lean-bin')
            lib=root/'build/lean-lib'
            with mock.patch.object(c,'compile_one',side_effect=fake_compile_one), \
                 mock.patch.object(c.shutil,'which',return_value=str(fake_bin)), \
                 mock.patch.object(c,'toolchain_fingerprint',return_value='test-toolchain'), \
                 mock.patch.object(c.subprocess,'check_output',return_value='Lean test'):
                # Run 1: All 3 proofs batch into a single Lean invocation; shared contract compiled once.
                rep1=make_report()
                c.lean_gates(rep1,lib,30,2,root=root,batch_size=4)
                self.assertEqual([r['status'] for r in rep1['roots']],['validated']*3)
                proof_invocations=[n for n,wo in calls if not wo]
                self.assertEqual(len(proof_invocations),1)
                contract_invocations=[n for n,wo in calls if n=='Kind0Contracts.lean']
                self.assertEqual(len(contract_invocations),1)

                # Run 2: Unchanged inputs hit bound cache with 0 compiler calls.
                calls.clear()
                rep2=make_report()
                c.lean_gates(rep2,lib,30,2,root=root,batch_size=4)
                self.assertEqual([r['status'] for r in rep2['roots']],['validated']*3)
                self.assertEqual(calls,[])

                # Run 3: Editing Root1Proof invalidates ONLY Root1Proof; if Root1Proof fails in a batch,
                # error isolation validates healthy siblings and rejects Root1Proof.
                (root/'meta/Fn2/Instances/ServedCertificates/Root1Proof.lean').write_text(
                  (root/'meta/Fn2/Instances/ServedCertificates/Root1Proof.lean').read_text()+'\n-- edit 1\n')
                (root/'meta/Fn2/Instances/ServedCertificates/Root2Proof.lean').write_text(
                  (root/'meta/Fn2/Instances/ServedCertificates/Root2Proof.lean').read_text()+'\n-- edit 2\n')
                fail_root.add(1)
                calls.clear()
                rep3=make_report()
                c.lean_gates(rep3,lib,30,2,root=root,batch_size=4)
                self.assertEqual([r['status'] for r in rep3['roots']],['validated','unvalidated','validated'])
                self.assertIn('Lean rejected proof/census',rep3['roots'][1]['reason'])

if __name__=='__main__':unittest.main()
