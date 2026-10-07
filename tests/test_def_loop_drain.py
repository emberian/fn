"""tools/def_loop_drain.py: three conversions reproduced byte for byte and three
named refusals.  The fixtures are excerpts of real books at the pre-conversion
revision (feed-pause, peer-config, extent-retire; nntp-responses, bp-route,
arena-forget); the expected outputs are the tool's own, each REPL-checked in
its book on persvati when the lane converted it (REGEN=1 rewrites them)."""
import os
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / "tools"))
import def_loop_drain as d  # noqa: E402

FIX = ROOT / "tests" / "fixtures" / "def_loop_drain"


def run(name):
    text = (FIX / f"{name}.in.lisp").read_text()
    return d.analyse(text, name, {}), text


class Conversions(unittest.TestCase):
    def check(self, name, count):
        (conv, resid), text = run(name)
        self.assertEqual(resid, [])
        self.assertEqual(len(conv), count)
        out = d.apply_text(text, conv)
        expected = FIX / f"{name}.out.lisp"
        if os.environ.get("REGEN"):
            expected.write_text(out)
        self.assertEqual(out, expected.read_text())
        # the twin, its bridge and its verify-guards are gone
        self.assertEqual(d.loop_count(out), 0)
        self.assertNotIn("-loop-is-", out)
        self.assertNotIn("verify-guards", out)
        # and the result is still readable, with one def-loop per conversion
        forms, _ = d.book_forms(out)
        self.assertEqual(sum(1 for f in forms if f.kind == "def-loop"), count)

    def test_feed_pause_two_maps(self):
        self.check("feed-pause", 2)

    def test_peer_config_filter_map(self):
        self.check("peer-config", 1)

    def test_extent_retire_take_and_stobj_map(self):
        self.check("extent-retire", 2)


HAND = FIX / "hand"


class HandConversions(unittest.TestCase):
    """The tool's output against what the drain-loop lane hand-converted and landed:
    byte for byte, from the pre-conversion text (the commit's parent; see each
    .src: commit book twin).  The .in.lisp is the book's first include-book plus
    the twin's four forms plus the next form; the .out.lisp is the landed
    def-loop form with that same context.  Twins whose wrapper carries a comment
    are not here: the tool hoists the comment above the def-loop where the hand
    conversion dropped it (a difference inside the replaced span, by design)."""

    def check(self, tag):
        text = (HAND / f"{tag}.in.lisp").read_text()
        conv, resid = d.analyse(text, tag, {})
        self.assertEqual(resid, [])
        self.assertEqual(len(conv), 1)
        self.assertEqual(d.apply_text(text, conv), (HAND / f"{tag}.out.lisp").read_text())

    def test_config_stop_value_and_tail_share_a_line(self):          # 742658cc3
        self.check("config-fn-cfg-row-replace-key")

    def test_config_keep_order_option_on_the_keep_line(self):        # 167ff78da
        self.check("config-fn-cfg-rows-without-key")

    def test_owner_feed_keep_with_a_wrapped_free_call(self):         # a8df6a676
        self.check("owner-feed-fn-own-feed-targets")

    def test_a_wrapped_keep_leaves_keep_order_on_its_own_line(self):
        # the config.lisp hand layout for a :keep too long for one line
        text = (HAND / "config-fn-cfg-rows-without-key.in.lisp").read_text()
        pred = ("(and (fn-cfg-binding-rowp %s) (equal (fn-record-string-octets (fn-cfg-row-a %s)) "
                "(fn-record-string-octets login)))")
        text = text.replace("(equal (fn-cfg-row-a (car rows)) a)", pred % ("(car rows)", "(car rows)"))
        text = text.replace("(rows a", "(rows login").replace("rows a)", "rows login)")
        text = text.replace(" a acc", " login acc").replace(" a nil", " login nil")
        text = text.replace("(cdr rows) a", "(cdr rows) login")
        conv, resid = d.analyse(text, "synthetic", {})
        self.assertEqual(resid, [])
        out = d.apply_text(text, conv)
        self.assertIn("\n             (equal (fn-record-string-octets (fn-cfg-row-a r))"
                      " (fn-record-string-octets login)))\n  :keep-order :skip-first\n  :body r)", out)


class LateGuard(unittest.TestCase):
    """A callee verified after the wrapper: the def-loop moves down past its
    verify-guards when nothing between mentions the function, else that
    verify-guards moves up above the wrapper."""

    def conv(self, name):
        (conv, resid), text = run(name)
        self.assertEqual(resid, [])
        return d.apply_text(text, conv)

    def test_def_loop_moves_down_after_the_callee_guard(self):
        out = self.conv("late-guard-down")
        self.assertLess(out.index("(verify-guards fn-nntp-active-line)"), out.index("(def-loop"))
        self.assertEqual(out.count("verify-guards"), 1)

    def test_guard_moves_up_when_a_form_between_uses_the_function(self):
        out = self.conv("late-guard-up")
        self.assertLess(out.index("(verify-guards fn-nntp-active-line)"), out.index("(def-loop"))
        self.assertLess(out.index("(def-loop"), out.index("fn-nntp-active-lines-true-listp"))
        self.assertEqual(out.count("verify-guards"), 1)

    def test_a_guard_callee_verified_later_moves_up(self):
        # wire's fn-wire-lines-size: its :guard calls fn-wire-octet-linesp, whose
        # verify-guards sat at the book's end; def-loop verifies guards where it stands
        out = self.conv("late-guard-in-guard")
        self.assertLess(out.index("(verify-guards fn-wire-octet-linesp)"), out.index("(def-loop"))
        self.assertLess(out.index("(verify-guards fn-wire-octet-listp)"),
                        out.index("(verify-guards fn-wire-octet-linesp)"))
        self.assertEqual(out.count("(verify-guards fn-wire-octet-linesp)"), 1)


class ExecDiffers(unittest.TestCase):
    """The exec-differs drain (lane drain-gv3): a hand loop that is the logic's terms in
    another form converts (step helper, book helper, renamed accumulator, let inlined, a
    rev-onto per branch); a loop that really computes other terms is refused by name."""

    def conv(self, name, count=1):
        (conv, resid), text = run(name)
        self.assertEqual(resid, [])
        self.assertEqual(len(conv), count)
        out = d.apply_text(text, conv)
        expected = FIX / f"{name}.out.lisp"
        if os.environ.get("REGEN"):
            expected.write_text(out)
        self.assertEqual(out, expected.read_text())
        return out

    def refused(self, name, why, detail):
        (conv, resid), _ = run(name)
        self.assertEqual(conv, [])
        self.assertEqual([r[1] for r in resid], ["exec-differs"])
        self.assertIn(detail, resid[0][2])

    def test_step_helper_goes_with_the_twin(self):
        out = self.conv("gv3-step-helper")
        self.assertNotIn("key-values-step", out)

    def test_step_helper_guard_verification_goes_with_it(self):
        out = self.conv("gv3-step-helper-vg")
        self.assertNotIn("ready-peers-step", out)
        self.assertNotIn("verify-guards", out)

    def test_step_helper_named_elsewhere_stays(self):
        out = self.conv("gv3-step-helper-kept")
        self.assertIn("(defun fn-cll-key-values-step", out)
        self.assertIn(":shape :foldr", out)

    def test_step_helper_with_a_let_and_a_cond(self):
        self.conv("gv3-step-helper-let")

    def test_multi_binding_let_names_the_recursion_result(self):
        self.conv("gv3-multi-let")

    def test_rev_onto_repeated_in_each_branch(self):
        self.conv("gv3-rev-if")

    def test_accumulator_renamed_by_a_let(self):
        self.conv("gv3-atom-let")

    def test_logic_let_variable_inlined_in_the_loop(self):
        self.conv("gv3-let-var-body")

    def test_book_helper_is_the_logic_term(self):
        self.conv("gv3-book-helper")

    def test_foldr_over_a_stobj_refuses_by_name(self):
        (conv, resid), _ = run("gv3-refuse-foldr-stobj")
        self.assertEqual(conv, [])
        self.assertEqual([r[1] for r in resid], ["foldr-stobjs"])

    def test_guard_total_accessors_refuse_by_name(self):
        self.refused("gv3-refuse-ag-accessor", "exec-differs", "fn-ag-car")

    def test_early_exit_refuses_by_name(self):
        self.refused("gv3-refuse-early-exit", "exec-differs", "control flow differs")

    def test_true_listp_seed_refuses_by_name(self):
        self.refused("gv3-refuse-seed", "exec-differs", "true-listp seed")


class PairResult(unittest.TestCase):
    """The pair-result drain: a let* that names the recursion result next to other bindings
    is a plain :step (newnews-scan); the rest is refused with the kind of result named."""

    def test_recursion_result_bound_in_a_multi_binding_let_is_a_step(self):
        (conv, resid), text = run("gv3-pair-newnews")
        self.assertEqual(resid, [])
        spec = conv[0]["spec"]
        self.assertEqual((spec.shape, spec.svars), ("step", ["articles", "horizon"]))
        out = d.apply_text(text, conv)
        expected = FIX / "gv3-pair-newnews.out.lisp"
        if os.environ.get("REGEN"):
            expected.write_text(out)
        self.assertEqual(out, expected.read_text())

    def refused(self, name, kind):
        (conv, resid), _ = run(name)
        self.assertEqual(conv, [])
        self.assertEqual([r[1] for r in resid], ["pair-result"])
        self.assertTrue(resid[0][2].startswith(kind), resid[0][2])

    def test_prefix_split_refuses_by_name(self):
        self.refused("gv3-pair-split", "split:")

    def test_position_search_refuses_by_name(self):
        self.refused("gv3-pair-position", "position:")

    def test_error_record_parser_refuses_by_name(self):
        self.refused("gv3-pair-failure", "failure:")


class Refusals(unittest.TestCase):
    def refused(self, name, why):
        (conv, resid), _ = run(name)
        self.assertEqual(conv, [])
        self.assertEqual([r[1] for r in resid], [why])

    def test_late_guard_hints_naming_a_later_event_refuse(self):
        self.refused("late-guard-refuse", "late-guard")

    def test_step_by_other_than_cdr(self):
        self.refused("refuse-step", "step")

    def test_two_lists_are_a_step_over_both(self):
        (conv, resid), _ = run("refuse-two-list")
        self.assertEqual(resid, [])
        self.assertEqual(conv[0]["spec"].shape, "step")
        self.assertEqual(conv[0]["spec"].svars, ["old", "new"])
        self.assertIn(":over (old new)", conv[0]["text"])


class Reader(unittest.TestCase):
    def test_char_literals_and_strings_do_not_unbalance(self):
        forms, comments = d.book_forms('(defun f (x) ; c\n  (if (equal x #\\() "a)b" (quote (1))))\n')
        self.assertEqual(len(forms), 1)
        self.assertEqual(forms[0].name, "f")
        self.assertEqual(len(comments), 1)


class GenVocabFixtures(unittest.TestCase):
    """The gen-vocab hand conversions are the byte fixtures: each .in is the book's
    pre-conversion text (git 1e190ff19), each .expect the def-loop form gen-vocab
    wrote (git 4d2d53390).  The tool regenerates the form from the pre-image."""

    def form_of(self, book, name):
        text = (FIX / f"gv-{book}.in.lisp").read_text()
        conv, resid = d.analyse(text, book, {})
        self.assertEqual(resid, [])
        c = [c for c in conv if c["name"] == name][0]
        out = c["text"]
        return out[out.index("(def-loop"):]

    def expect(self, name):
        return (FIX / f"gv-{name}.expect").read_text().rstrip("\n")

    def test_foldr_forms_are_byte_identical(self):
        self.assertEqual(self.form_of("stx-index", "fn-stx-index-of-store"), self.expect("fn-stx-index-of-store"))
        self.assertEqual(self.form_of("replay-identity-index", "fn-rii-kbuild-releases"),
                         self.expect("fn-rii-kbuild-releases"))
        self.assertEqual(self.form_of("replay-identity-index", "fn-rii-kbuild-pins"),
                         self.expect("fn-rii-kbuild-pins"))

    def test_fold_form_with_lets_and_guard_hints_is_byte_identical(self):
        self.assertEqual(self.form_of("payload-lz-replay", "fn-lzr-intern-events"),
                         self.expect("fn-lzr-intern-events"))

    def test_fold_form_differs_only_by_carried_guard_hints(self):
        mine = self.form_of("store-intern", "fn-intern-events")
        theirs = self.expect("fn-intern-events")
        self.assertEqual(mine.replace('\n  :guard-hints (("Goal" :in-theory (disable fn-intern-event))))', ")"), theirs)


class Ledger(unittest.TestCase):
    def test_library_bridge_by_shape(self):
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :map :over x)"),
                         "fn-dl-map-loop-is-revappend")
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :sum :over x)"),
                         "fn-dl-sum-loop-is-plus")
        self.assertEqual(d.library_bridge("(def-loop f (x) :shape :concat :over x)"),
                         "fn-dl-concat-loop-is-revappend")

    def test_loopish_names_only(self):
        self.assertTrue(d.LOOPISH.search("fn-x-loop-is-rev-onto"))
        self.assertFalse(d.LOOPISH.search("fn-x-is-sorted"))


if __name__ == "__main__":
    unittest.main()
