"""SHA-256 of the Filecoin setup files both key derivations read, against their pins.

Usage: setup-digests.py ASSETS_DIR. Prints {FILE: {"sha256", "pinned"}} as JSON. bls_filecoin_2p19 is
the published setup (srs-literal/generate.py's SRS_SHA256); bls_filecoin_2p13 is what midnight-zk's
sha_preimage example derives from it at 1e39c120."""
import hashlib, json, sys
from pathlib import Path

PINS = {"bls_filecoin_2p13": "b9af43892c3cb90321fa00a36e5e59051f356df145d7f58368531f28d212937b",
        "bls_filecoin_2p19": "0574a536c128142e89c0f28198d048145e2bb2bf645c8b81c8697cba445a1fb1"}

def digest(path):
    if not path.is_file(): return None
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(1 << 20): h.update(chunk)
    return h.hexdigest()

assets = Path(sys.argv[1])
print(json.dumps({name: {"sha256": (d := digest(assets / name)), "pinned": d == pin} for name, pin in PINS.items()}))
