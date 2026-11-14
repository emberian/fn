import sys
import unittest
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from checkpoint_frame_rewrite import rewrite


class CheckpointFrameRewrite(unittest.TestCase):
    def test_actual_readonly_guard_and_all_type_premises(self):
        source = '''(defun fn2-checkpoint-frozen-map-entry (e p f)
        (declare (xargs :stobjs (p f) :guard (and (p-wfp p) (f-wfp f)))) (mv :entry f))
        (f-preserves fn2-checkpoint-frozen-map-entry (e p f) :position 1)'''
        result, count = rewrite(source)
        self.assertEqual(count, 1)
        self.assertIn(':hyps ((pp p) (fp f) (p-wfp p) (f-wfp f))', result)
        self.assertIn('("-GUARD-DOMAIN-TYPE" fp 1)', result)
        self.assertIn('("-PRESERVES-WFP" f-wfp 1 :hyps ((fp f) (f-wfp f)))', result)
        self.assertIn('("-PRESERVES-ROWS" f-rows 1 :frame f)', result)
        self.assertEqual(rewrite(result)[0], result)
        self.assertEqual(result[:source.index('(f-preserves')], source[:source.index('(f-preserves')])

    def test_explicit_multi_output_observations_survive(self):
        source = '''(defun fn2-checkpoint-map-pack-entry (p f pool)
        (declare (xargs :stobjs (p f pool) :guard (and (p-wfp p) (f-wfp f) (pool-wfp pool)))) (mv :ok f pool))
        (f-preserves fn2-checkpoint-map-pack-entry (p f pool)
        :specs (("-FIELDS-TYPE" fp 1) ("-FIELDS-WFP" f-wfp 1)
                ("-FIELDS-ROWS" f-rows 1 :frame f) ("-POOL-TYPE" poolp 2)
                ("-POOL-WFP" pool-wfp 2) ("-POOL-ROWS" pool-rows 2 :frame pool)))'''
        result, _ = rewrite(source)
        for suffix in ('-GUARD-DOMAIN-FIELDS-TYPE', '-GUARD-DOMAIN-FIELDS-WFP',
                       '-FIELDS-ROWS', '-GUARD-DOMAIN-POOL-TYPE', '-GUARD-DOMAIN-POOL-WFP', '-POOL-ROWS'):
            self.assertIn(suffix, result)
        self.assertIn('(poolp pool)', result)

    def test_different_call_or_missing_guard_is_refused(self):
        for source in (
            '(defun fn2-checkpoint-restore-entry (p f) (declare (xargs :stobjs (p f) :guard t)) f) (f-preserves fn2-checkpoint-restore-entry (f p) :position 1)',
            '(defun fn2-checkpoint-restore-entry (p f) (declare (xargs :stobjs (p f))) f) (f-preserves fn2-checkpoint-restore-entry (p f) :position 1)',
        ):
            with self.assertRaises(ValueError):
                rewrite(source)

    def test_single_input_zero_helper_is_outside_the_class(self):
        source = '(p-preserves fn2-checkpoint-map-zero (n at p) :position 1)'
        self.assertEqual(rewrite(source), (source, 0))


if __name__ == "__main__":
    unittest.main()
