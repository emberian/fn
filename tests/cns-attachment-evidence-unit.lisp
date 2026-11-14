; Actual selected CNS tuple; these checks cannot pass without its current
; selected implementations, full constraint group and kernel proof record.
(in-package "ACL2")
(include-book "../books/cns-attachment-evidence")
(include-book "std/testing/must-fail" :dir :system)
(make-event
 (let ((packet (fn2-av-packet *fn2-av-cns-pairs* (w state))))
  (if (not packet) (er soft 'cns-attachment-evidence-unit "Missing actual CNS evidence.")
   (value `(fn2-av-check-packet ',packet *fn2-av-cns-pairs*)))))
(make-event
 (let* ((packet (fn2-av-packet *fn2-av-cns-pairs* (w state)))
        (at (position-eq :constraints packet))
        (mutant (update-nth (+ 1 at) (fn2-tv-object nil) packet)))
  (value `(must-fail (fn2-av-check-packet ',mutant *fn2-av-cns-pairs*)))))
(make-event
 (let* ((packet (fn2-av-packet *fn2-av-cns-pairs* (w state)))
        (at (position-eq :proved-instances packet))
        (mutant (update-nth (+ 1 at) (fn2-tv-object nil) packet)))
  (value `(must-fail (fn2-av-check-packet ',mutant *fn2-av-cns-pairs*)))))
(make-event
 (let ((packet (fn2-av-packet *fn2-av-cns-pairs* (w state))))
  (value `(must-fail
   (fn2-av-check-packet ',packet
    '((fn2-cns-run-stub . fn2-cns-run-default)
      (fn2-machine-observe-fn2-cns-stub . fn2-machine-observe-fn2-cns)
      (fn2-cns-arm-charge-ok-p-stub . fn2-cns-arm-charge-ok-p)
      (fn2-cns-arm-bound-stub . fn2-cns-arm-bound)))))))
