; Actual cold runtime status boundary, including malformed input states.
; Host write effects are produced by the outer writer, never by codec status.
(in-package "ACL2")
(include-book "history-cold-record-runtime")

(local (defthm fn-hrcur-status-mv-zero-is-car-unfolds
  (equal (mv-nth 0 x) (car x))
  :hints (("Goal" :in-theory (enable mv-nth)))))

(local (defthm fn-hrcur-nil-tick-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-nil-tick c)) :write)) (not (equal (car (fn-hrcur-nil-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-nil-tick  fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrcur-nil-supply-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-nil-supply c position byte)) :write)) (not (equal (car (fn-hrcur-nil-supply c position byte)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-nil-supply fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrcur-dos-tick-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-dos-tick c)) :write)) (not (equal (car (fn-hrcur-dos-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-dos-tick fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrcur-dos-supply-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-dos-supply c position byte)) :write)) (not (equal (car (fn-hrcur-dos-supply c position byte)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-dos-supply fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrsc-tick-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrsc-tick c)) :write)) (not (equal (car (fn-hrsc-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrsc-tick fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrcur-span-tick-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-span-tick c)) :write)) (not (equal (car (fn-hrcur-span-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-span-tick fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hrcur-span-supply-has-no-write-status-unfolds
  (and (not (equal (car (fn-hrcur-span-supply c position byte)) :write)) (not (equal (car (fn-hrcur-span-supply c position byte)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-span-supply fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-span-tick-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hdsn-tick-has-no-write-status-unfolds
  (and (not (equal (car (fn-hdsn-tick c)) :write)) (not (equal (car (fn-hdsn-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hdsn-tick fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-span-tick-has-no-write-status-unfolds fn-hrcur-span-supply-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(local (defthm fn-hdsn-supply-has-no-write-status-unfolds
  (and (not (equal (car (fn-hdsn-supply position serial byte c)) :write)) (not (equal (car (fn-hdsn-supply position serial byte c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hdsn-supply fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-span-tick-has-no-write-status-unfolds fn-hrcur-span-supply-has-no-write-status-unfolds fn-hdsn-tick-has-no-write-status-unfolds fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not))))))

(defthm fn-hrcur-cold-tick-has-no-write-status
  (and (not (equal (car (fn-hrcur-cold-tick c)) :write)) (not (equal (car (fn-hrcur-cold-tick c)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-cold-tick fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-span-tick-has-no-write-status-unfolds fn-hrcur-span-supply-has-no-write-status-unfolds fn-hdsn-tick-has-no-write-status-unfolds fn-hdsn-supply-has-no-write-status-unfolds
        fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not)))))

(defthm fn-hrcur-cold-supply-has-no-write-status
  (and (not (equal (car (fn-hrcur-cold-supply c position byte)) :write)) (not (equal (car (fn-hrcur-cold-supply c position byte)) :io)))
  :hints (("Goal" :do-not-induct t
    :in-theory (union-theories
      (union-theories (theory 'minimal-theory) (executable-counterpart-theory :here))
      '(fn-hrcur-cold-supply fn-hrcur-nil-tick-has-no-write-status-unfolds fn-hrcur-nil-supply-has-no-write-status-unfolds fn-hrcur-dos-tick-has-no-write-status-unfolds fn-hrcur-dos-supply-has-no-write-status-unfolds fn-hrsc-tick-has-no-write-status-unfolds fn-hrcur-span-tick-has-no-write-status-unfolds fn-hrcur-span-supply-has-no-write-status-unfolds fn-hdsn-tick-has-no-write-status-unfolds fn-hdsn-supply-has-no-write-status-unfolds
        fn-hrcur-status-mv-zero-is-car-unfolds car-cons cdr-cons member-equal eq not)))))
