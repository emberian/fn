(in-package "ACL2")
(include-book "../../books/output-command-admission")
; Fixed parser fixtures use the exact existing command tokenizer.
(assert-event (equal (fn-ocap-command-family '(110 101 119 110 101 119 115 32 102 110 46 116 101 115 116 32 50 48 48 48 48 49 48 49 32 48 48 48 48 48 48)) :newnews))
(assert-event (equal (fn-ocap-command-family '(65 82 84 73 67 76 69 32 49)) :article))
(assert-event (equal (fn-ocap-command-family '(88 72 68 82 32 83 117 98 106 101 99 116 32 49 45)) :header-range))
(assert-event (equal (fn-ocap-command-family '(76 73 83 84 32 65 67 84 73 86 69)) :list))
(assert-event (equal (fn-ocap-command-family '(88 67 85 83 84 79 77)) :extension))
(assert-event (equal (fn-ocap-command-family '(32 78 69 87 78 69 87 83)) :protocol-error))
; Literal held-boundary positive, removal by refusing the actual word, and
; wrong-family/unpriced/insufficient-capacity cases all preserve exact prefix.
(assert-event
 (let* ((preview '(:preview 17 :newnews nil))
        (tariff '(:tariff :newnews 8192)) (capacity 8192)
        (word (fn-ocap-admit-preview preview tariff capacity)))
   (and (equal (fn-ocap-at 0 word) :hold)
        (fn-ocap-previewp preview) (fn-ocap-tariffp tariff)
        (equal (fn-ocap-at 2 preview) (fn-ocap-at 1 tariff))
        (natp capacity) (<= (fn-ocap-at 2 tariff) capacity)
        (equal (fn-ocap-at 1 word) (fn-ocap-at 1 preview)))))
(assert-event
 (let* ((preview '(:preview 17 :article nil))
        (tariff '(:tariff :newnews 8192)) (capacity 8192)
        (word (fn-ocap-admit-preview preview tariff capacity)))
   (and (not (equal (fn-ocap-at 0 word) :hold))
        (fn-ocap-previewp preview) (fn-ocap-tariffp tariff)
        (not (equal (fn-ocap-at 2 preview) (fn-ocap-at 1 tariff)))
        (natp capacity) (<= (fn-ocap-at 2 tariff) capacity)
        (not (equal (fn-ocap-at 1 word) (fn-ocap-at 1 preview))))))
(assert-event (equal (fn-ocap-admit-preview '(:preview 17 :newnews nil) nil 8192)
                     '(:refused :unpriced-output-family :newnews)))
(assert-event (equal (fn-ocap-admit-preview '(:preview 17 :newnews nil) '(:tariff :newnews 8192) 8191)
                     '(:refused :output-tariff-unaffordable :newnews)))
; Actual first-event scanner into the private test octet stobj. It must stop
; before the second pipelined ARTICLE, rather than execute both under a
; single NEWNEWS tariff. The suffix remains in the input buffer unchanged.
(assert-event
 (let* ((xs '(78 69 87 78 69 87 83 13 10 65 82 84 73 67 76 69 32 49 13 10))
        (fn-octets (fn-octets-from-list xs fn-octets))
        (wire (fn-wire-make-state :command nil 0 nil nil 0 510 8192))
        (p (fn-ocap-preview wire 0 20 fn-octets)))
   (mv (and (fn-wire-fast-statep wire)
        (natp 0) (natp 20) (<= 0 20) (<= 20 (fn-octets-len fn-octets))
        (<= 0 (fn-ocap-at 1 p)) (<= (fn-ocap-at 1 p) 20)
        (equal (fn-ocap-at 1 p) 9) (equal (fn-ocap-at 2 p) :newnews)
        (equal (fn-oct-slice-list 9 20 fn-octets) '(65 82 84 73 67 76 69 32 49 13 10)))
       fn-octets))
 :stobjs-out '(nil fn-octets))

; Literal hypothesis-removal teeth of the strengthened range boundary.
; The guards are deliberately disabled only for these corrupted model inputs.
(assert-event
 (with-guard-checking :none
   (let* ((start (/ 1 2)) (end 1)
          (wire (fn-wire-make-state :command nil 0 nil nil 0 510 8192))
          (next (fn-ocap-at 1 (fn-ocap-preview wire start end fn-octets))))
     (and (not (natp start)) (<= start end)
          (not (and (<= start next) (<= next end)))))))
(assert-event
 (with-guard-checking :none
   (let* ((start 1) (end 0)
          (wire (fn-wire-make-state :command nil 0 nil nil 0 510 8192))
          (next (fn-ocap-at 1 (fn-ocap-preview wire start end fn-octets))))
     (and (natp start) (not (<= start end))
          (not (and (<= start next) (<= next end)))))))
