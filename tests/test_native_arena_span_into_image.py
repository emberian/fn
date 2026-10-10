"""A-ARENA-SPAN-INTO on the real image (books/assumptions-durable-spans.lisp,
host/native/extent.lisp fn-arena-get-span-into).

For a handle H, an offset AT and a count N inside H's payload,

    fn-arena-get-span-into H AT N ARENA OUT

leaves OUT byte-equal to the buffer

    (fn-octets-append-list (fn-arena-get-span H AT N ARENA) OUT)

would, whatever OUT held before, for every kind of arena entry
host/native/extent.lisp distinguishes (fn-arena$x-exti, books/payload-arena-
extent.lisp):

* :extent    a durable extent (FILE EOFF ELEN POFF PLEN TRAILER).  The host's
             run loop (fnn-extent-window-realize-run) in the window mode and
             one REPLACE from the trailer-verified entry in the synchronous
             mode; the window route's runs end at the window, the request or
             fnn-extent-span-capacity octets.
* :lz        a compressed extent (fn-arn-lz-extentp): not an extent to
             fn-arn-extentp, so the arena's own span answers it.
* :resident  a payload in the paged child (entry 0).
* :staged    a payload in the handle's stage page (a POST not yet durable).
* :forgotten a reclaimed handle (the empty payload).

The live arena of a restarted developer owner holds :extent and :lz handles
(the open's replay); a scratch arena built in the owner's world holds all five
(the extent and lz descriptors are the live arena's own, copied).  The routes
of the window mode that need an issued window job (a worker's returned window,
the verified-window cache) are reached through the served path: an ARTICLE of
an extent handle read cold and again warm.  A span that no route holds throws
fnn-extent-cold and leaves the buffer as it was; a window outside the payload
is refused by name (fnn-extent-fault) and leaves the buffer as it was.

The Lisp is evaluated by the developer REPL (host/native/dev-repl.lisp,
FN_NATIVE_DEV_REPL) in the running owner; each helper's name starts fn-spi-.

Runs on the developer image only: FN_NATIVE_DEVELOPER_HOST.  Without the
image every test skips.
"""
import re
import unittest

from tools import fn_dev
from tests import test_native_operator_verbs as verbs
from tests.native_harness import EXIT_OK, Node, native_image

IMAGE = native_image("FN_NATIVE_DEVELOPER_HOST")
# Plain and compressible bodies.  Three runs of fnn-extent-span-capacity (16384)
# and a remainder: a span from 0 crosses two run boundaries.
BIG = 3 * 16384 + 4321
ARTICLE_OCTETS = 2 * BIG
KINDS = ("extent", "lz", "resident", "staged", "forgotten")

# The helpers, one form (the REPL evaluates one form per connection).
HELPERS = r"""
(progn
 (defun fn-spi-kind (arena h)
   (let ((e (fn-arena$x-exti h arena)))
     (cond ((fn-arn-extentp e) :extent) ((fn-arn-lz-extentp e) :lz)
           ((eq e :staged) :staged) ((eq e :forgotten) :forgotten) (t :resident))))
 (defun fn-spi-buffer (prefix)
   (let ((out (create-fn-octets$c))) (fn-octets-append-list prefix out) out))
 ;; (AT . N) inside [0, PLEN]: the ends, the middle, a run's boundary crossed.
 (defun fn-spi-cases (plen)
   (let* ((cap +fnn-extent-span-capacity+) (mid (floor plen 2)))
     (remove-duplicates
      (remove-if-not
       (lambda (c) (and (<= 0 (car c)) (<= 0 (cdr c)) (<= (+ (car c) (cdr c)) plen)))
       (list (cons 0 plen) (cons 0 0) (cons 0 1) (cons plen 0) (cons mid 0)
             (cons mid (- plen mid)) (cons mid 1) (cons mid 100) (cons 1 (- plen 1))
             (cons (- plen 1) 1) (cons (- plen 17) 17) (cons 5 100) (cons 100 (- plen 100))
             (cons 1 cap) (cons 0 (+ cap 1)) (cons (- cap 1) 2) (cons (- cap 5) 10)
             (cons (- cap 1) (+ cap 1)) (cons cap cap) (cons (- (* 2 cap) 5) 10)
             (cons (- (* 2 cap) 1) (- plen (- (* 2 cap) 1))) (cons 0 (+ (* 2 cap) 1))
             (cons (+ cap 3) (- plen cap 3))))
      :test #'equal)))
 ;; The twin is fn-arena-get-span's octets: an extent's one host span, any
 ;; other kind octet by octet (fn-arx-get-loop's definition, which conses one
 ;; frame per octet and exhausts the owner's stack on a 53 KB payload).
 (defun fn-spi-span (arena h at n)
   (if (fn-arn-extentp (fn-arena$x-exti h arena))
       (fn-arena-get-span h at n arena)
     (loop for k from at below (+ at n) collect (fn-arena$x-get h k arena))))
 (defun fn-spi-check (arena h at n prefix)
   (let ((into (fn-spi-buffer prefix)) (twin (fn-spi-buffer prefix)))
     (fn-arena-get-span-into h at n arena into)
     (fn-octets-append-list (fn-spi-span arena h at n) twin)
     (if (and (equal (fn-octets-list into) (fn-octets-list twin))
              (= (fn-octets-len into) (+ (length prefix) n)))
         nil
       (list :fail h at n (length prefix) (fn-octets-len into) (fn-octets-len twin)))))
 ;; Every case of every handle of ARENA (or of handle ONLY), with and without a
 ;; prefix already in OUT.
 (defun fn-spi-sweep (arena &optional only)
   (let ((counts nil) (fails nil))
     (dotimes (h (fn-arena$x-count arena))
       (when (or (null only) (eql h only))
       (let ((kind (fn-spi-kind arena h)) (plen (fn-arena$x-payload-len h arena)))
         (dolist (c (fn-spi-cases plen))
           (dolist (prefix (list nil (list 9 8 7)))
             (let ((f (fn-spi-check arena h (car c) (cdr c) prefix)))
               (if f (push f fails)
                 (let ((cell (assoc kind counts)))
                   (if cell (incf (cdr cell)) (push (cons kind 1) counts))))))))))
     (list :counts counts :fails (reverse fails))))
 ;; The kinds and payload lengths of ARENA's handles.
 (defun fn-spi-survey (arena)
   (loop for h below (fn-arena$x-count arena)
         collect (list :h h (fn-spi-kind arena h) (fn-arena$x-payload-len h arena))))
 ;; An arena with every kind: the live arena's first extent and lz descriptors
 ;; copied beside resident, staged and forgotten entries.
 (defun fn-spi-scratch (live)
   (let ((s (create-fn-arena$x)) (buf (create-fn-octets$c)) (ext nil) (lz nil))
     (dotimes (h (fn-arena$x-count live))
       (let ((e (fn-arena$x-exti h live)))
         (when (and (null ext) (fn-arn-extentp e) (> (nth 4 e) 16384)) (setq ext e))
         (when (and (null lz) (fn-arn-lz-extentp e) (> (nth 6 e) 0)) (setq lz e))))
     (when (or (null ext) (null lz)) (error "live arena lacks an extent or an lz handle"))
     (fn-arena$x-seal-list (loop for i below 300 collect (mod (* 7 i) 256)) s)
     (fn-arena$x-seal-list nil s)
     (fn-octets-append-list (loop for i below 700 collect (mod (* 11 i) 256)) buf)
     (fn-arena$x-seal-buffer buf s)
     (fn-arena$x-seal-list (list 1 2 3) s)
     (fn-arena$x-forget 3 s)
     (destructuring-bind (file eoff elen poff plen trailer) ext
       (fn-arena$x-seal-extent file eoff elen poff plen trailer s))
     (destructuring-bind (file eoff elen poff plen trailer n dict) lz
       (fn-arena$x-seal-lz-extent file eoff elen poff plen trailer n dict s))
     s))
 ;; A window outside the payload is refused by name and the buffer is as it was.
 (defun fn-spi-refusal (arena h at n)
   (let ((out (fn-spi-buffer (list 1 2 3))))
     (let ((word (handler-case (progn (fn-arena-get-span-into h at n arena out) :accepted)
                   (fnn-extent-fault () :refused))))
       (list word (fn-octets-list out)))))
 ;; The window mode with no worker and no cache: a stretch no route holds
 ;; throws fnn-extent-cold; either way the buffer holds the prefix, then the
 ;; whole span or nothing.
 (defun fn-spi-cold (arena h n)
   (let* ((out (fn-spi-buffer (list 1 2 3)))
          (word (let ((*fnn-extent-window-mode* t) (*fnn-extent-window-worker* nil)
                      (*fnn-extent-window-cache* nil) (*fnn-extent-window-token* nil))
                  (catch 'fnn-extent-cold (fn-arena-get-span-into h 0 n arena out) :returned))))
     (list (if (eq word :returned) :returned :cold)
           (equal (fn-octets-list out)
                  (if (eq word :returned)
                      (append (list 1 2 3) (fn-spi-span arena h 0 n))
                    (list 1 2 3)))))))
"""


def counts(text):
    """The sweep's per-kind case counts from the REPL's printed list."""
    block = text.split(":FAILS")[0]
    return {kind.lower(): int(n) for kind, n in re.findall(r"\(:(\w+) \. (\d+)\)", block)}


def failures(text):
    return re.findall(r"\(:FAIL [^)]*\)", text)


def survey(text):
    return [(int(h), kind.lower(), int(n))
            for h, kind, n in re.findall(r":H (\d+) :(\w+) (\d+)", text)]


class ArenaSpanIntoImageTests(verbs.NativeOperatorVerbFixture):
    image = IMAGE
    listener = True

    def setUp(self):
        if not self.image.is_file():
            self.skipTest("the developer image {} is not built; set FN_NATIVE_DEVELOPER_HOST "
                          "(these tests run fn-arena-get-span-into in a live owner)".format(self.image))
        super().setUp()
        self.node.image = self.image
        self.sock = self.root / "dev.sock"
        self.ids = []

    # -- the store: plain extents, then compressed ones, replayed by a restart --

    @staticmethod
    def body(n, size, compressible):
        """SIZE octets of CRLF lines (no bare CR or LF, no leading dot): repeated
        text when COMPRESSIBLE, hex digits of a congruential stream otherwise."""
        state, lines, total = 0x9E3779B1 + n, [], 0
        while total < size:
            if compressible:
                line = b"article %d: the quick brown fox jumps over the lazy dog\r\n" % n
            else:
                digits = bytearray()
                for _ in range(9):
                    state = (state * 1103515245 + 12345) & 0x7FFFFFFF
                    digits.extend(b"%08x" % state)
                line = bytes(digits) + b"\r\n"
            lines.append(line)
            total += len(line)
        cut = b"".join(lines)[:size - 2].rstrip(b"\r\n")
        return cut + b"x" * (size - 2 - len(cut)) + b"\r\n"

    def post(self, compressible, size, count):
        ids = []
        with self.node.session(timeout=180) as client:
            for _ in range(count):
                message_id = "<span-into-{}@example.invalid>".format(len(self.ids) + len(ids))
                first, final = client.post(verbs.article(
                    message_id, subject="span into",
                    body=self.body(len(self.ids) + len(ids), size, compressible)))
                self.assertTrue(first.startswith(b"340"), first)
                self.assertEqual(final.rstrip(b"\r\n"), b"240 article received OK")
                ids.append(message_id)
        self.ids += ids
        return ids

    def build_store(self):
        # The development profile refuses an article of 32 KiB and up; BIG needs
        # its own bound (a whole article: BIG's body plus the header), and the
        # record of one such article must fit, so the groups per article are
        # bounded as in test_native_article_slots.
        created = self.node.operator("init", "--profile", "development",
                                     "--max-article-octets", str(ARTICLE_OCTETS),
                                     "--max-groups-per-article", "16", "fn.test")
        self.assertEqual(created.returncode, EXIT_OK, created.stderr.decode())
        self.node.start()
        self.big = self.post(False, BIG, 2)
        self.post(False, 900, 3)
        self.node.stop()
        row = self.node.operator("policy", "set", "compress-min-octets", "64")
        self.assertEqual(row.returncode, EXIT_OK, row.stderr.decode())
        self.node.start()
        self.big_lz = self.post(True, BIG, 2)
        self.post(True, 900, 3)
        self.node.stop()

    def open_owner(self):
        """Build the store, restart it so every payload is the open's replay, and
        install the helpers in the owner's world."""
        self.build_store()
        self.node.start(env={"FN_NATIVE_DEV_REPL": str(self.sock)})
        ok, text = fn_dev.evaluate(self.sock, HELPERS, 60)
        self.assertTrue(ok, text)

    def repl(self, form, timeout=180):
        with self.node.log_on_failure():
            try:
                ok, text = fn_dev.evaluate(self.sock, form, timeout)
            except ValueError as error:   # the owner went away mid-reply
                self.fail("{}: {}".format(error, form[:200]))
            self.assertTrue(ok, text[-1500:])
        return text

    LIVE = "(fnn-live-arena)"

    # -- the equality, per kind --

    def test_the_live_arena_holds_extent_and_lz_handles_and_each_equals_the_append_of_its_span(self):
        self.open_owner()
        held = survey(self.repl("(fn-spi-survey {})".format(self.LIVE)))
        kinds = {kind for _h, kind, _n in held}
        self.assertTrue({"extent", "lz"} <= kinds, held)
        self.assertTrue(any(n >= BIG for _h, kind, n in held if kind == "extent"), held)
        self.assertTrue(any(n >= BIG for _h, kind, n in held if kind == "lz"), held)
        # One handle per REPL call: an lz handle reads about 68 us an octet
        # (fn-durable-realize-lz-octet, on hbox), so a 53 KB handle's cases
        # take about 90 s, past one call's bound for the whole arena.
        got, fails = {}, []
        for h, _kind, _n in held:
            text = self.repl("(fn-spi-sweep {} {})".format(self.LIVE, h), timeout=900)
            fails += failures(text)
            for kind, n in counts(text).items():
                got[kind] = got.get(kind, 0) + n
        self.assertEqual(fails, [], fails[:20])
        for kind in ("extent", "lz"):
            self.assertGreater(got.get(kind, 0), 0, got)

    def test_every_entry_kind_equals_the_append_of_its_span_in_a_scratch_arena(self):
        self.open_owner()
        text = self.repl("(let ((arena (fn-spi-scratch {}))) (fn-spi-sweep arena))".format(self.LIVE))
        self.assertEqual(failures(text), [], text[-1500:])
        got = counts(text)
        for kind in KINDS:
            # a forgotten handle has the empty payload: its one case is (0 . 0)
            self.assertGreater(got.get(kind, 0), 0, "{} not covered: {}".format(kind, text[-800:]))

    def test_a_span_crossing_run_boundaries_is_covered_for_the_big_extent_and_lz_handles(self):
        self.open_owner()
        held = survey(self.repl("(fn-spi-survey {})".format(self.LIVE)))
        for kind in ("extent", "lz"):
            big = [h for h, k, n in held if k == kind and n >= BIG]
            self.assertTrue(big, (kind, held))
            for h in big:
                # from 0 across the first two boundaries, from just before the
                # first to just after the second, and the last octets
                for at, n in ((0, BIG), (16384 - 5, 2 * 16384 + 10), (BIG - 1, 1)):
                    for prefix in ("nil", "(list 9 8 7)"):
                        form = "(fn-spi-check {} {} {} {} {})".format(self.LIVE, h, at, n, prefix)
                        self.assertEqual(self.repl(form).strip(), "NIL", (kind, h, at, n))

    # -- the refusals --

    def test_a_window_outside_the_payload_is_refused_by_name_and_leaves_the_buffer(self):
        self.open_owner()
        text = self.repl("(let ((arena (fn-spi-scratch {}))) (fn-spi-survey arena))".format(self.LIVE))
        held = survey(text)
        self.assertEqual({kind for _h, kind, _n in held}, set(KINDS), held)
        for h, _kind, plen in held:
            for at, n in ((0, plen + 1), (plen, 1), (plen + 1, 0), (-1, 1), (0, -1),
                          (plen + 1, plen + 1)):
                form = ("(let ((arena (fn-spi-scratch {}))) (fn-spi-refusal arena {} {} {}))"
                        .format(self.LIVE, h, at, n))
                self.assertEqual(self.repl(form).strip(), "(:REFUSED (1 2 3))", (h, at, n))
        count = len(held)
        for h in (count, count + 5, -1):
            form = ("(let ((arena (fn-spi-scratch {}))) (fn-spi-refusal arena {} 0 0))"
                    .format(self.LIVE, h))
            self.assertEqual(self.repl(form).strip(), "(:REFUSED (1 2 3))", h)

    def test_a_stretch_no_window_route_holds_throws_cold_and_leaves_the_buffer(self):
        self.open_owner()
        held = survey(self.repl("(fn-spi-survey {})".format(self.LIVE)))
        for h, kind, n in held:
            if n == 0:
                continue
            text = self.repl("(fn-spi-cold {} {} {})".format(self.LIVE, h, n)).strip()
            word = re.fullmatch(r"\(:(\w+) T\)", text)
            self.assertIsNotNone(word, (h, kind, text))
            if kind == "extent":
                self.assertEqual(word.group(1), "COLD", (h, kind, text))

    # -- the window and cache routes, through the served path --

    def test_a_served_article_is_the_same_cold_and_warm(self):
        """The ARTICLE render reads its extent payload a window at a time
        (fn-arena-get-span-into in the window mode: a worker's returned
        window, then the verified-window cache); the octets served the first
        time, the second and the third are the same, and carry the posted body."""
        self.open_owner()
        for message_id in (self.big[0], self.big_lz[0]):
            reads = []
            with self.node.log_on_failure(), self.node.session(timeout=180) as client:
                for _ in range(3):
                    try:
                        reads.append(client.article(message_id))
                    except EOFError as error:   # the node closed the connection
                        self.fail("{}: ARTICLE {} read {}".format(error, message_id, len(reads)))
            self.assertIsNotNone(reads[0], message_id)
            self.assertEqual(reads[1], reads[0], message_id)
            self.assertEqual(reads[2], reads[0], message_id)
            self.assertGreaterEqual(len(reads[0]), BIG, message_id)


if __name__ == "__main__":
    unittest.main()
