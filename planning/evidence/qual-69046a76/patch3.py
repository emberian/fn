p="/tank/fn/scratch/qual-69046a76/mixed.py"
s=open(p).read()
old='    b = signer("agent-b", 0xB2, 2)\n'
assert old in s
new=old+('    # qual-69046a76 harness repair: fn_consumer now requires its own keyring (the authors it trusts);\n'
         '    # both agents trust A and B, built with tools/fn_verify.py keyring_entry from the enrolled keys.\n'
         '    sys.path.insert(0, str(T / "tools")); import fn_verify as _FV\n'
         '    _ents = []\n'
         '    for _c, _g in ((a, 1), (b, 2)):\n'
         '        _k = json.loads(Path(_c).read_text())["keys"]\n'
         '        _ents.append(_FV.keyring_entry(_k["principal"], _k["ed_public"], _k["ml_public"], _g))\n'
         '    _ring = W / "keyring.json"; _ring.write_text(json.dumps({"format": "fn-verify-keyring-v1", "principals": _ents}))\n'
         '    for _c in (a, b):\n'
         '        _d = json.loads(Path(_c).read_text()); _d["keyring"] = str(_ring); Path(_c).write_text(json.dumps(_d))\n')
s=s.replace(old,new)
open(p,"w").write(s); print("patched")
