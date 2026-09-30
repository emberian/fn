(in-package "ACL2")
(include-book "../../books/outgoing-operation-cost")
; MODEL descriptor only. No immutable runtime installer or storage factory.
(defun-nx outgoingmt-installation ()
 '(:outgoing-operation-installation 9 (1 2 3 4 5 6) 17 10000
   (100 100 1 0 1) 100 4 8 32 64 :window))
(defthm outgoingmt-derived-window-model
 (let ((answer (mv-list 5 (fn-outgoing-operation-evaluate
  (outgoingmt-installation) :window 16 64 2 9 '(1 2 3 4 5 6) 17))))
  (equal answer '(:derived (100 100 1 0 1) 24 188 32)))
 :rule-classes nil)
(defthm outgoingmt-missing-and-mismatched-source-model
 (and (equal (mv-nth 0 (fn-outgoing-operation-evaluate nil :window 16 64 2 9 '(1 2 3 4 5 6) 17)) :outgoing-source-unavailable)
      (equal (mv-nth 0 (fn-outgoing-operation-evaluate (outgoingmt-installation) :window 16 64 2 9 '(1 2 3 4 5 6) 18)) :outgoing-source-unavailable)
      (equal (mv-nth 0 (fn-outgoing-operation-evaluate (outgoingmt-installation) :observe 16 64 2 9 '(1 2 3 4 5 6) 17)) :outgoing-source-unavailable))
 :rule-classes nil)
(defthm outgoingmt-window-refused-without-truncation-model
 (and (equal (mv-list 5 (fn-outgoing-operation-evaluate (outgoingmt-installation) :window 33 64 2 9 '(1 2 3 4 5 6) 17)) '(:refused nil 0 0 32))
      (equal (mv-nth 0 (fn-outgoing-operation-evaluate (outgoingmt-installation) :window 16 63 2 9 '(1 2 3 4 5 6) 17)) :outgoing-source-unavailable))
 :rule-classes nil)
(defthm outgoingmt-current-fixed-scalar-fence-model
 (and
  (equal (mv-list 5 (fn-outgoing-current-evaluate
   (outgoingmt-installation) :window 16 64 2 9 '(1 2 3 4 5 6) 17))
    '(:derived (100 100 1 0 1) 24 188 32))
  (equal (mv-list 5 (fn-outgoing-current-evaluate
   (outgoingmt-installation) :window 16 64 2 9 '(1 2 (3) 4 5 6) 17))
    '(:outgoing-source-unavailable nil 0 0 0)))
 :rule-classes nil)
