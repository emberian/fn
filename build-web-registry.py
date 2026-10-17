from pathlib import Path
import json
p=Path('specs/human-client.md');s=p.read_text();a=s.index('This scheduling contract does not yet establish')
s=s[:a]+'''The native page path requests a validated immutable segment plan from
`fn-wss-page`, then counts and emits it through `fn-web-host-page-step`
(`books/web-page-cursor.lisp`) outside the owner section. Each step has fixed
cursor fuel and a window of at most 4096 octets. A short encoded header may
add the existing bounded RFC 2047 decode; long headers remain span reads.
Count mode allocates no output list. GET emits the counted page from the same
retained reply and plan; HEAD counts the page and sends its head alone. It
never constructs a complete HTML output buffer. SCN-1105 compares all segment
kinds and native partial writes to the existing segment reference.

The cursor is presently a program boundary. Its guard verification and
refinement to `fn-wr-seq` are planned in PRF-1277; raw equality witnesses do not
extend the existing web proofs to it. Owner admission, session decisions and
segment construction still run to completion under the owner lock. A long
owner operation or page-plan construction can therefore delay event handling;
this is not a full semantic-event fairness guarantee. The fixed semantic
worker also serializes operations that need that worker.

This scheduling contract does not yet establish full allocation funding.
The NNTP reply backing buffer, page segment spine and text, bounded decoder,
head/window/cursor and job capture remain the actual tariff frontier. Eliminating
the complete HTML output buffer does not fund the retained input or plan.
''';p.write_text(s)
p=Path('planning/requirements.json');obj=json.loads(p.read_text())
for r in obj['requirements']:
 if r['id']=='WEB-006':
  r['proof_targets']=['PRF-1277']
  r['evidence'] += ['books/web-page-cursor.lisp','tests/native_web_page_cursor_raw.lisp']
  r['implementation_note']='Source implementation: fixed I/O actor plus one semantic worker, profile-bounded HTTP slots/mailbox and exact per-CID lifetime leases. Native page count/emit now consumes immutable ACL2 segments outside O in bounded windows, with no complete HTML OUT; actual raw mixed-segment/reference and partial-write consumer witness passes. Cursor remains program mode, planned guard/refinement target PRF-1277. Session/plan construction and owner admission still run to completion under O, and one worker can wait on owner admission. Matching image checks and full retained NNTP/plan/job funding remain open; this is not full semantic-event fairness or universal allocation warranty.'
p.write_text(json.dumps(obj,indent=2)+'\n')
p=Path('planning/proofs.json');obj=json.loads(p.read_text());obj['proofs'].append({'id':'PRF-1277','title':'Native incremental web page count/emit refines the segment renderer with retained input spans','statement':'Planned: the actual host-called fn-web-host-page-step (fn-wpc-step/fn-wpc-drive) maintains a cursor over a validated fn-wr segment plan and immutable retained NNTP input. Arbitrary quantum partitions concatenate exactly fn-wr-seq; count mode reports its exact length while allocating no output list. Every emitted window is bounded by fuel and every span read lies in the captured input. Establish guards and carry the cursor/input invariant through actual native count, write, cancel and terminal cleanup. Existing fn-wr-emit-is-seq does not establish this new boundary.','milestone':'M6','requirements':['WEB-006'],'depends_on':['PRF-338'],'assumptions':[],'status':'planned','evidence':['books/web-page-cursor.lisp','host/web-host.lisp','host/native/web-host.lisp','tests/native_web_page_cursor_raw.lisp'],'progress_note':'Source program boundary and actual raw native consumer present; no logical refinement, guard verification or matching image claim yet.'});p.write_text(json.dumps(obj,indent=2)+'\n')
p=Path('tests/scenarios/catalog.json');obj=json.loads(p.read_text());obj['scenarios'].append({'id':'SCN-1105','title':'Count and stream an escaped web page from retained segments without a complete HTML output buffer','milestone':'M6','status':'specified','requirements':['WEB-006'],'steps':['Construct mixed markup/text/URL/span/dot-stuffed/encoded-header segments over a retained input, including a header beyond the decoder quantum.','Count and emit the same plan using fuel 1, 2, 7 and 4096; compare all emitted octets and count with fn-wr-seq.','Run actual fnn-web-page-step and write-ready through 137-byte partial writes; retain zero-length HTML OUT throughout.'],'expected':['Every partition gives exactly the reference page and counted Content-Length; count mode returns no output list.','Each emitted window is at most its fuel; the long decoded-header fallback is exact.','Native output is exactly the response head followed by reference bytes while no complete HTML output is materialized.'],'evidence':['tests/native_web_page_cursor_raw.lisp','tests/test_native_web_page_cursor_raw.sh'],'note':'Actual source/raw witness only; program-mode cursor guard/refinement and matching image remain open (PRF-1277).'});p.write_text(json.dumps(obj,indent=2)+'\n')
p=Path('host/native/web-host.lisp');s=p.read_text().replace('  (let* ((out (fnn-web-conn-out conn))\n         (head','  (let* ((head');p.write_text(s)
p=Path('tests/native_web_page_cursor_raw.lisp');s=p.read_text().replace('(fn-wrq-oct "..first<&\\r\\n..second\'\\r\\n")', '(append (fn-wrq-oct "..first<&") \'(13 10) (fn-wrq-oct "..second\'") \'(13 10))');p.write_text(s)
