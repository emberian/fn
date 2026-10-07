; Teeth for books/send-progress (CONVERGE-2 row 20): the verdict at the
; profile's rows on each side of each limit, the measured 38 KB/s reader and a
; reader that stops, and one must-fail per premise of each keystone.
(in-package "ACL2")
(include-book "../../books/send-progress")
(include-book "must-fail-checked")
(include-book "std/testing/assert-bang" :dir :system)

(assert! (equal *fn-send-stall-seconds* 10))
(assert! (equal *fn-send-min-octets-per-second* 4096))
; The floor admits the slowest reader the native tests name with margin.
(assert! (<= (* 8 *fn-send-min-octets-per-second*) 38000))

; A state: since 0, start 0, queue 0 at the start, last queue 1000, last handed 50000.
(defconst *sp-st* '(0 0 0 1000 50000))

; Stalled: no progress, 10 s elapsed refuses, 9.999 s continues.
(assert! (equal (fn-send-progress-decide *sp-st* '(10000 1000 50000)) '(:refuse :send-stalled)))
(assert! (equal (fn-send-progress-decide *sp-st* '(9999 1000 50000)) :continue))
; A queue that grew with nothing accepted is not progress.
(assert! (equal (fn-send-progress-decide *sp-st* '(10000 2000 50000)) '(:refuse :send-stalled)))
; The queue shrinking by one octet, or one more octet accepted, is progress.
(assert! (equal (fn-send-progress-decide '(0 0 0 1000 50000) '(10000 999 50000)) :continue))
(assert! (equal (fn-send-progress-decide '(0 0 0 1000 50000) '(10000 1000 50001)) :continue))
; Unknown queue: only the accepted octets show progress.
(assert! (equal (fn-send-progress-decide '(0 0 nil nil 50000) '(10000 nil 50000)) '(:refuse :send-stalled)))
(assert! (equal (fn-send-progress-decide '(0 0 nil nil 50000) '(10000 nil 50001)) :continue))

; Too slow: progress, a backlog, a window run.  The floor is 4096/s: over
; 10 s that is 40,960 octets; 40,959 drained is refused, 40,960 is not.
(assert! (equal (fn-send-progress-decide '(9000 0 0 100000 100000) '(10000 59041 100000))
                '(:refuse :reader-too-slow)))
(assert! (equal (fn-send-progress-decide '(9000 0 0 100000 100000) '(10000 59040 100000))
                :continue))
; Not judged before the window: the same pace at 9.999 s.
(assert! (equal (fn-send-progress-decide '(9000 0 0 100000 100000) '(9999 99999 100000)) :continue))
; No backlog: an empty queue is a reader that keeps up, however slow the server.
(assert! (equal (fn-send-progress-decide '(9000 0 0 100 0) '(20000 0 100)) :continue))
; Unknown queue: judged on the octets accepted alone.
(assert! (equal (fn-send-progress-decide '(9000 0 nil nil 0) '(10000 nil 40959))
                '(:refuse :reader-too-slow)))
(assert! (equal (fn-send-progress-decide '(9000 0 nil nil 0) '(10000 nil 40960)) :continue))
; A reader that is not reading is stalled, not slow.
(assert! (equal (fn-send-progress-decide '(0 0 0 100000 0) '(10000 100000 0))
                '(:refuse :send-stalled)))

; Malformed arguments refuse.
(assert! (equal (fn-send-progress-decide nil '(1 0 0)) '(:refuse :send-stalled)))
(assert! (equal (fn-send-progress-decide *sp-st* '(1 0)) '(:refuse :send-stalled)))
(assert! (equal (fn-send-progress-decide *sp-st* '(-1 0 0)) '(:refuse :send-stalled)))
(assert! (equal (fn-send-progress-decide *sp-st* '(5 1000 nil)) '(:refuse :send-stalled)))
; An observation before the last progress is malformed.
(assert! (equal (fn-send-progress-decide '(500 0 0 0 0) '(100 0 0)) '(:refuse :send-stalled)))

; The state: begin, and next moves SINCE only on progress.
(assert! (equal (fn-send-progress-begin 7 100) '(7 7 100 100 0)))
(assert! (equal (fn-send-progress-begin 7 nil) '(7 7 nil nil 0)))
(assert! (equal (fn-send-progress-next '(0 0 0 1000 50000) '(300 900 50000)) '(300 0 0 900 50000)))
(assert! (equal (fn-send-progress-next '(0 0 0 1000 50000) '(300 1000 50000)) '(0 0 0 1000 50000)))
(assert! (equal (fn-send-progress-next nil '(300 1000 50000)) nil))

; The measured reader and the stopped reader, by the book's runs (the kernel
; queue at 3,383,427 octets, observations 250 ms apart).
(assert! (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                                      (fn-send-reader-trace 350 0 3383427 3383427 250 9500)
                                      10 4096)
                :continue))
(assert! (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                                      (fn-send-reader-trace 400 0 3383427 3383427 250 0)
                                      10 4096)
                '(:refuse :send-stalled)))
; 3 KB/s (below the 4,096 floor) reading with new octets accepted each tick:
; refused too slow once a window has run.
(assert! (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                                      (fn-send-reader-trace 400 0 3383427 3383427 250 750)
                                      10 4096)
                '(:refuse :reader-too-slow)))
; The first refusal of a stopped reader lands at the first observation 10 s
; after progress last showed: observations 250 ms apart, so within one tick of
; the window.
(assert! (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                                      (fn-send-reader-trace 40 0 3383427 3383427 250 0) 10 4096)
                :continue))
(assert! (equal (fn-send-progress-run (fn-send-progress-begin 0 0)
                                      (fn-send-reader-trace 41 0 3383427 3383427 250 0) 10 4096)
                '(:refuse :send-stalled)))

; Premise removal: each premise of each keystone, dropped, is refused.
(must-fail-checked
 (defthm sp-draining-without-the-pace-premise
   (implies (and (fn-send-pair-p st obs) (posp stall-seconds) (natp min-octets-per-second)
                 (or (fn-send-progress-p st obs)
                     (< (- (nth 0 obs) (nth 0 st)) (* 1000 stall-seconds))))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   :continue))))

(must-fail-checked
 (defthm sp-draining-without-the-freshness-premise
   (implies (and (fn-send-pair-p st obs) (posp stall-seconds) (natp min-octets-per-second)
                 (or (equal (nth 1 obs) 0)
                     (< (- (nth 0 obs) (nth 1 st)) (* 1000 stall-seconds))
                     (<= (* min-octets-per-second (- (nth 0 obs) (nth 1 st)))
                         (* 1000 (fn-send-drained st obs)))))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   :continue))))

(must-fail-checked
 (defthm sp-stalled-without-the-window-premise
   (implies (and (fn-send-pair-p st obs) (natp stall-seconds) (natp min-octets-per-second)
                 (not (fn-send-progress-p st obs)))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   '(:refuse :send-stalled)))))

(must-fail-checked
 (defthm sp-stalled-without-the-no-progress-premise
   (implies (and (fn-send-pair-p st obs) (natp stall-seconds) (natp min-octets-per-second)
                 (<= (* 1000 stall-seconds) (- (nth 0 obs) (nth 0 st))))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   '(:refuse :send-stalled)))))

(must-fail-checked
 (defthm sp-too-slow-without-the-floor-premise
   (implies (and (fn-send-pair-p st obs) (posp stall-seconds) (natp min-octets-per-second)
                 (fn-send-progress-p st obs)
                 (not (equal (nth 1 obs) 0))
                 (<= (* 1000 stall-seconds) (- (nth 0 obs) (nth 1 st))))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   '(:refuse :reader-too-slow)))))

(must-fail-checked
 (defthm sp-too-slow-without-the-backlog-premise
   (implies (and (fn-send-pair-p st obs) (posp stall-seconds) (natp min-octets-per-second)
                 (fn-send-progress-p st obs)
                 (<= (* 1000 stall-seconds) (- (nth 0 obs) (nth 1 st)))
                 (< (* 1000 (fn-send-drained st obs))
                    (* min-octets-per-second (- (nth 0 obs) (nth 1 st)))))
            (equal (fn-send-progress-verdict st obs stall-seconds min-octets-per-second)
                   '(:refuse :reader-too-slow)))))
