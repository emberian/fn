(in-package "ACL2")
(include-book "../../books/cold-guard-bootstrap")
(include-book "std/testing/assert-bang" :dir :system)
(assert! (and (equal (len (fn-cgb-roster)) 21)
              (no-duplicatesp-eq (fn-cgb-roster))
              (equal (fn-cgb-capacity) 21)))
(assert! (and (fn-cgb-namep 'fn-ews-begin)
              (fn-cgb-namep 'fn-owner-page-window-executor-acquire-funded)
              (not (fn-cgb-namep 'fn-owner-step))
              (not (fn-cgb-namep nil))))
; Independent source and selected layout pins, no runtime allocation claim.
(assert! (equal (fn-cgb-retained-conses) 96))
(assert! (equal (fn-cgb-prewarm-conses) 82))
(assert! (equal (fn-crl-table-octets 21 nil) 848))
(assert! (equal (fn-cgb-baseline-octets) 7392))

(assert! (fn-cgb-planp '(:admitted nil (7392 0 0 0 0) 8 8 9 1 21)))
; Mutation witnesses: oldseven-field shape, wrong capacity, missing credit.
(assert! (and (not (fn-cgb-planp '(:admitted nil (7392 0 0 0 0) 8 8 9 1)))
              (not (fn-cgb-planp '(:admitted nil (7392 0 0 0 0) 8 8 9 1 12)))
              (not (fn-cgb-planp '(:admitted nil (7391 0 0 0 0) 8 8 9 1 21)))))

(assert! (and (fn-cgb-specp 'fn-crw-supportedp '(2))
              (fn-cgb-specp 'fn-ews-read '(6 (2 s true-listp list)))
              (fn-cgb-specp 'fn-pwx-boundp '(4))
              (fn-cgb-specp 'fn-owner-page-window-byte-at '(12 (2 plan true-listp list)))
              (fn-cgb-specp 'fn-ews-begin
                            '(11 (0 file natp natural) (1 eoff natp natural)
                                 (2 elen natp natural) (3 poff natp natural)
                                 (4 plen natp natural) (5 offset natp natural)
                                 (9 expected natp natural)))))
; Unsupported/missing metadata is distinct from a prepared guarded entry.
(assert! (and (not (fn-cgb-specp 'fn-ews-begin :unknown))
              (not (fn-cgb-specp 'fn-ews-read '(6)))
              (not (fn-cgb-specp 'fn-ews-read '(6 (2 s natp natural))))
              (not (fn-cgb-specp 'fn-pwx-boundp '(3)))
              (not (fn-cgb-specp 'fn-owner-page-window-byte-at '(13 (2 plan true-listp list))))
              (not (fn-cgb-specp 'fn-owner-step '(2)))))

(assert! (and (fn-cgb-specp 'fn-owner-page-window-current-octet
                          '(3 (0 h natp natural) (1 i natp natural)))
              (fn-cgb-specp 'fn-owner-page-window-executor-cancel '(3))
              (fn-cgb-specp 'fn-owner-page-window-decoded-refusal '(0))))
(assert! (and (not (fn-cgb-specp 'fn-owner-page-window-current-octet
                               '(3 (0 h natp natural))))
              (not (fn-cgb-specp 'fn-owner-page-window-current-octet
                               '(3 (0 h natp natural) (1 i true-listp list))))
              (not (fn-cgb-specp 'fn-owner-page-window-decoded-refusal '(1)))))
