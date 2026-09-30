; GENERATED proof-only composition by tools/decoded_window_buffer_exec.py.

; books/deflate-inflate.lisp SHA256 11c45d893c92fd4bf256312faeaea795654ef472c414480b8d1483b0058e62e6

; books/octets-stobj.lisp SHA256 3fbd390317fe7c3527add9c3d831ec967e8dccd3247142f2fa37fa29423697c4

; books/payload-window.lisp SHA256 87b57c941ba4a4e046845a5f330c55b2d791959f6af7bc05262896b6e67808ab

(in-package "ACL2")

(include-book "decoded-window-initial-buffer-capacity")

(defun-nx fn-piwc-payload-ready (dict cwin ctab)
 (let* ((n (len dict)) (tail (if (< *fn-zin-window* n) (nthcdr (- n *fn-zin-window*) dict) dict)) (h (min n *fn-zin-window*)) (cwin (fn-octets$c-clear cwin)) (cwin (fn-octets$c-reserve *fn-zin-win-octets* cwin)) (cwin (fn-octets$c-append-octet 0 cwin)) (cwin (fn-octets$c-append-back 1 (1- *fn-zin-window*) cwin)) (cwin (fn-oct-write-list tail cwin)) (cwin (if (< h *fn-zin-window*) (let ((cwin (fn-octets$c-append-octet 0 cwin))) (fn-octets$c-append-back 1 (- *fn-zin-window* (+ 1 h)) cwin)) cwin)) (ctab (fn-octets$c-clear ctab)) (ctab (fn-octets$c-reserve *fn-zin-tab-octets* ctab)) (ctab (fn-octets$c-append-octet 0 ctab)) (ctab (fn-octets$c-append-back 1 (1- *fn-zin-tab-octets*) ctab))) (mv h cwin ctab)))

(defun-nx fn-piwc-initialize (dict fn-zin-st cwin ctab cout)
 (let* ((fn-zin-st (fn-zin-reset fn-zin-st)) (cout (fn-octets$c-clear cout)) (cout (fn-octets$c-reserve 64 cout))) (mv-let (h cwin ctab) (fn-piwc-payload-ready dict cwin ctab) (let ((fn-zin-st (fn-zin-set 18 h fn-zin-st))) (mv fn-zin-st cwin ctab cout)))))

; books/extent-window-compressed.lisp SHA256 7df8e635553ea55f514888dd3f19fa377014b02a837dadf53c3d11b448990ff2

(defun-nx fn-piwc-ewz-begin (file eoff elen poff compressed decoded offset ticket incarnation lease expected dict pgs-digest-state fn-zin-st cwin ctab cout)
 (mv-let (plan pgs-digest-state) (fn-ews-begin file eoff elen poff compressed compressed ticket incarnation lease expected pgs-digest-state) (mv-let (fn-zin-st cwin ctab cout) (fn-piwc-initialize dict fn-zin-st cwin ctab cout) (mv (fn-ewz-state (cond ((or (eq (nth 0 plan) :bounds) (< decoded offset)) :bounds) ((not (fn-pzw-stored-admissiblep compressed decoded)) :codec-error) ((zp compressed) :drain) (t :scan)) plan decoded offset (min 16384 (nfix (- decoded offset))) (fn-pzd-budget compressed decoded) 0 0 :more) pgs-digest-state fn-zin-st cwin ctab cout))))

; books/decoded-window-begin.lisp SHA256 0daa1e9abcd5aacb90e83dc00b22e0962cf4a0280ced4d526a0d0adfa5eaccf7

(defun-nx fn-piwc-begin (token incarnation pgs-digest-state fn-zin-st cwin ctab cout)
 (fn-piwc-ewz-begin (nfix (fn-pwz-nth 2 token)) (nfix (fn-pwz-nth 3 token)) (nfix (fn-pwz-nth 4 token)) (nfix (fn-pwz-nth 5 token)) (nfix (fn-pwz-nth 6 token)) (nfix (fn-pwz-nth 9 token)) (nfix (fn-pwz-nth 7 token)) (fn-pwz-nth 1 token) incarnation token (nfix (fn-pwz-nth 8 token)) (fn-pwz-dictionary token) pgs-digest-state fn-zin-st cwin ctab cout))
