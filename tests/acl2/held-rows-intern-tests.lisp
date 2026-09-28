; tests/acl2/held-rows-tests builds the test corpus's fixtures below
; books/store-intern; this book proves each builder IS the entry, so a
; fixture built there is the row, the wire view and the verdict the host's
; entries produce.
(in-package "ACL2")
(include-book "held-rows-tests")
(include-book "../../books/store-intern")

;; Rules withdrawn at their source that this book's proofs use
;; (lane rule-hygiene, tools/rule_cost.py).
(local (in-theory (enable (:rewrite fn-intern-event-arena)
                          (:rewrite fn-stxa-is-no-other-wire-event))))

(defthm fn-hrt-event-is-intern-event-by-definition
  (equal (fn-hrt-event w keyring generation fn-arena)
         (fn-intern-event w keyring generation fn-arena))
  :hints (("Goal" :in-theory (enable fn-hrt-event fn-intern-event))))

(defthm fn-hrt-events-is-intern-events-by-definition
  (equal (fn-hrt-events ws keyring generation fn-arena)
         (fn-intern-events ws keyring generation fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-hrt-events fn-intern-events)
                                  (fn-hrt-event fn-intern-event)))))

(defthm fn-hrt-rows-wire-of-is-rows-wire-of-by-definition
  (equal (fn-hrt-rows-wire-of rows fn-arena) (fn-rows-wire-of rows fn-arena))
  :hints (("Goal" :in-theory (enable fn-hrt-rows-wire-of fn-rows-wire-of fn-row-wire-of
                                     fn-row-bytes fn-hrt-handle-bytes))))

(defthm fn-hrt-articles-alpha-is-articles-wire-of-by-definition
  (equal (fn-hrt-articles-alpha articles fn-arena) (fn-articles-wire-of articles fn-arena))
  :hints (("Goal" :in-theory (enable fn-hrt-articles-alpha fn-articles-wire-of
                                     fn-handle-bytes fn-hrt-handle-bytes))))

(defthm fn-hrt-row-at-is-intern-row-at-by-definition
  (equal (fn-hrt-row-at w h) (fn-intern-row-at w nil 0 h))
  :hints (("Goal" :in-theory (enable fn-hrt-row-at fn-intern-row-at))))

; The verdict helper is store-intern's entry (its keystone, instantiated).
; For a Message-ID string, the keystone's hypothesis.
(defthm fn-hrt-existing-action-in-is-the-entry
  (implies (stringp msgid)
           (equal (mv-nth 0 (fn-hrt-existing-action-in prior msgid payload groups s fn-arena))
                  (fn-store-existing-action msgid payload groups s
                                            (mv-nth 1 (fn-intern-events prior nil 0 fn-arena)))))
  :hints (("Goal" :use ((:instance fn-store-existing-action-is-the-verdict-over-alpha
                                    (fn-arena (mv-nth 1 (fn-intern-events prior nil 0 fn-arena)))))
                  :in-theory (e/d (fn-hrt-existing-action-in)
                                  (fn-store-existing-action-is-the-verdict-over-alpha
                                   fn-store-existing-action fn-rcl-action-over
                                   fn-hrt-articles-alpha fn-articles-wire-of
                                   fn-intern-events)))))
