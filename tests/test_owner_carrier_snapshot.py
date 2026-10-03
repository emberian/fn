from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'tools'))
from owner_carrier.snapshot import bind
from owner_carrier.thread import Refused

class SnapshotTests(unittest.TestCase):
    binding=dict(world_coordinate='fixture admitted world',source_files={'fixture.lisp':'a'*64})
    def test_actual_slots_and_writer_effects(self):
        snapshot=bind('''(:DIRECT (OCWT-DIRECT OCWT-WRITE)
 :FUNCTIONS ((OCWT-DIRECT (STATE) (STATE) (NIL) :PROGRAM NIL)
             (OCWT-WRITE (OC STATE) (NIL STATE) (STATE) :PROGRAM T)
             (OCWT-CALLER (OC STATE) (NIL STATE) (NIL NIL STATE) :PROGRAM T)))''',self.binding)
        self.assertFalse(snapshot['functions']['ocwt-direct']['writer'])
        self.assertEqual(snapshot['functions']['ocwt-caller']['outs'],[None,None,'state'])
        self.assertEqual(snapshot['source_files'],self.binding['source_files'])
    def test_missing_binding_malformed_slots_duplicate_or_incomplete_closure_refuse(self):
        dumps=['(:DIRECT (MISSING) :FUNCTIONS ((READER (STATE) (STATE) (NIL) :PROGRAM NIL)))',
               '(:DIRECT NIL :FUNCTIONS ((R (STATE) (STATE) (NIL) :PROGRAM T)))',
               '(:DIRECT NIL :FUNCTIONS ((R (STATE) NIL (NIL) :PROGRAM NIL)))',
               '(:DIRECT NIL :FUNCTIONS ((R (STATE) (STATE) (NIL) :PROGRAM NIL) (R (STATE) (STATE) (NIL) :PROGRAM NIL)))']
        for dump in dumps:
            with self.subTest(dump=dump),self.assertRaises(Refused):bind(dump,self.binding)
        with self.assertRaises(Refused):bind('(:DIRECT NIL :FUNCTIONS NIL)',{})
if __name__=='__main__':unittest.main()
