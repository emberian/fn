# BP production producer driver

The dtn7 application receipt lab explicitly selects a DEFAULT producer image
with `--producer-image` and requires `--signed-receipts`. The producer starts an
operator owner, posts every fixture through `operator CONFIG post`, and retrieves
the resulting injected article through the core's NNTP ARTICLE path. It writes
those served bytes and records their length and SHA-256. The owner is stopped by
tracked PID before FNWF/BP accesses its Store; every failure after spawn stops it.
Refused and uncertain posting failures retain their exit code and abort setup.
The bridge request branch also receives served bytes instead of pre-injection
input. Production DTN developer cut selectors remain a separate open concern.

`python3 tests/bp-dtn7/test_producer_lifecycle.py`: two tests pass, covering the
positive served-byte path, rc1 refusal, rc3 uncertainty and an unready owner.
`python3 -m py_compile tests/bp-dtn7/run_fn_dtn7_app_receipt.py` and driver `--help`
pass. These are mocked driver lifecycle checks, not a native image or transport
claim. Matching DEFAULT/DTN images, signed native receipt and full Q4 execution
remain pending with the runner. No live node, image build or farm was used.
