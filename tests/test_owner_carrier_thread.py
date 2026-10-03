import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'tools'))
from owner_carrier.thread import Refused, prepare

class ThreadTests(unittest.TestCase):
    def signature(self, formals, ins, outs, writer=False, touch=True):
        return dict(formals=formals, ins=ins, outs=outs, writer=writer, touch=touch)

    def render(self, source, signatures):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)/'input'; root.mkdir()
            path = root/'writer.lisp'; path.write_text(source)
            snapshot = dict(schema='fn-owner-carrier-world-v1', world_coordinate='fixture-world',
                            source_files={'writer.lisp':hashlib.sha256(path.read_bytes()).hexdigest()},
                            functions=signatures)
            original = path.read_bytes()
            dest = Path(temp)/'output'
            prepare(root, snapshot, dest)
            self.assertEqual(path.read_bytes(), original)
            return (dest/'writer.lisp').read_text()

    def test_single_state_output_keeps_auxiliary_effect_and_both_objects(self):
        text = self.render('''(defun writer (oc state)
 (declare (xargs :stobjs state :guard t))
 (let* ((state (fn-owner-install-ocfg oc state))
        (state (f-put-global 'aux :held state))) state))''',
        {'writer':self.signature(['oc','state'],[None,'state'],['state'],True),
         'fn-owner-install-ocfg':self.signature(['oc','state'],[None,'state'],['state'],True)})
        self.assertIn('(mv fn-owner-st state)', text)
        self.assertIn("(f-put-global 'aux :held state)", text)
        self.assertIn('(fn-owner-install-ocfg oc fn-owner-st)',text)

    def test_mv_scalar_word_and_state_positions_are_preserved(self):
        text=self.render('''(defun child (state)
 (declare (xargs :stobjs state :guard t)) (value :child))
(defun entry (state)
 (declare (xargs :stobjs state :guard t))
 (mv-let (erp word state) (child state) (mv erp word state)))''',
        {'entry':self.signature(['state'],['state'],[None,None,'state'],True),
         'child':self.signature(['state'],['state'],[None,None,'state'],True)})
        self.assertIn('(mv-let (erp word fn-owner-st state)',text)
        self.assertIn('(mv erp word fn-owner-st state)',text)

    def test_value_macro_preserves_error_and_word(self):
        text=self.render('''(defun answer (state)
 (declare (xargs :stobjs state :guard t)) (value :refused))''',
        {'answer':self.signature(['state'],['state'],[None,None,'state'],True)})
        self.assertIn('(mv nil :refused fn-owner-st state)',text)

    def test_read_only_owner_does_not_acquire_a_write_return(self):
        text=self.render('''(defun reader (state)
 (declare (xargs :stobjs state :guard (boundp-global 'fn-owner state)))
 (fn-owner-ocfg state))''',
        {'reader':self.signature(['state'],['state'],[None]),
         'fn-owner-ocfg':self.signature(['state'],['state'],[None])})
        self.assertIn('(fn-owner-boundp fn-owner-st)',text)
        self.assertIn('(fn-owner-ocfg fn-owner-st)',text)
        self.assertNotIn('(mv ',text)

    def test_proof_instance_substitutions_are_preserved_not_guessed(self):
        source="""(defthm old-claim (p state)
 :hints ((\"Goal\" :use ((:instance proof (state (f-put-global 'aux nil state)))))))"""
        self.assertEqual(self.render(source,{}),source)

    def test_refuses_unknown_binding_signature_and_direct_write(self):
        sig={'writer':self.signature(['state'],['state'],['state'],True)}
        for body in ["(f-put-global 'fn-owner nil state)",
                     '(unknown-tail state)',
                     '(case op (:ok state) (otherwise state))',
                     '#.(owner-read-time state)', '`(state)']:
            with self.subTest(body=body), self.assertRaises(Refused):
                self.render('(defun writer (state) (declare (xargs :stobjs state :guard t)) '+body+')',sig)
        with self.assertRaises(Refused):
            self.render('(defun writer (other) (declare (xargs :stobjs state :guard t)) state)',sig)

    def test_changed_input_and_existing_output_refuse_without_writing(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'input';root.mkdir();path=root/'writer.lisp';path.write_text('(value-triple :original)')
            snapshot=dict(schema='fn-owner-carrier-world-v1',world_coordinate='fixture-world',
                          source_files={'writer.lisp':hashlib.sha256(path.read_bytes()).hexdigest()},functions={})
            original=path.read_bytes(); path.write_text('(value-triple :dirty)')
            dest=Path(temp)/'output'
            with self.assertRaisesRegex(Refused,'digest mismatch'):
                prepare(root,snapshot,dest)
            self.assertFalse(dest.exists());self.assertEqual(path.read_text(),'(value-triple :dirty)')
            path.write_bytes(original);dest.mkdir();(dest/'owned').write_text('leave it')
            with self.assertRaisesRegex(Refused,'must not exist'):
                prepare(root,snapshot,dest)
            self.assertEqual((dest/'owned').read_text(),'leave it')

    def test_catalog_authority_cannot_be_left_in_globals_by_threading(self):
        for key in ('fn-owner-catalog-root-counter','fn-owner-catalog-root-incarnation'):
            for body,writer in [(f"(f-get-global '{key} state)",False),
                                (f"(boundp-global '{key} state)",False),
                                (f"(f-put-global '{key} nil state)",True)]:
                signatures={'writer':self.signature(['state'],['state'],
                            ['state'] if writer else [None],writer)}
                with self.subTest(body=body), self.assertRaises(Refused):
                    self.render('(defun writer (state) (declare (xargs :stobjs state :guard t)) '+body+')',signatures)

    def test_absolute_and_parent_paths_cannot_escape_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'input';root.mkdir();path=root/'writer.lisp';path.write_text('(value-triple :keep)')
            digest=hashlib.sha256(path.read_bytes()).hexdigest()
            for relative in (str(path), '../input/writer.lisp'):
                snapshot=dict(schema='fn-owner-carrier-world-v1',world_coordinate='fixture-world',
                              source_files={relative:digest},functions={})
                dest=Path(temp)/'output'
                with self.assertRaisesRegex(Refused,'relative input paths'):prepare(root,snapshot,dest)
                self.assertFalse(dest.exists())
                self.assertEqual(path.read_text(),'(value-triple :keep)')

    def test_all_files_are_validated_before_any_output(self):
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp)/'input';root.mkdir(); path=root/'first.lisp';path.write_text('(value-triple :first)')
            snapshot=dict(schema='fn-owner-carrier-world-v1',world_coordinate='fixture-world',
                          source_files={'first.lisp':hashlib.sha256(path.read_bytes()).hexdigest(),
                                        'missing.lisp':'not-a-hash'},functions={})
            dest=Path(temp)/'output'
            with self.assertRaises(OSError): prepare(root,snapshot,dest)
            self.assertFalse(dest.exists())

if __name__=='__main__':unittest.main()
