# cost-ratchet continuation
Head 7d37f13e9 on lane/cost-ratchet. All 9 rows are in host/cost-host.lisp (the image-world cost seam, ld'd after host/interfaces.lisp; not a certified book).
Proved: fn-asto-quantum, fn-heap-reclaim-chunk-rows (0 visits, 0 conses), fn-native-config-reclaim-livep (32, over new fn-ncfg-nth row 1+n).
Derived (no bound): fn-mca-figure-octets, fn-rrv-extend-reservation, 4 owner-page span borrows. To bound them, give their callees rows first (fn-heap-with-nursery, fn-mca-base-octets, fn-pwr-span-at ...); adding callee rows changes derived unaccounted sets of any caller already declared.
Checked locally in a scratch world (books + ld of host page-read/window/decoded host files + 11 matching definterfaces): all def-costs accepted. The full image-world check (host_translate_check) is NOT RUN: 43 books uncertified on the laptop. hbox must run it (or a build) to confirm the unaccounted sets.
--baseline refuses (hundreds of undeclared names not in baseline), so the 2 stale rows were removed by exact-name edit.
