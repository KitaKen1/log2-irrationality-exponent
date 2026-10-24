"""Adapt only the module wrapper; preserve the PR mathematical body verbatim."""
import argparse
import hashlib
from common import HERE, source_check


def generate(check=False):
    source_check()
    raw = (HERE / "reference/LogTwo.pr.lean").read_text()
    marker = "namespace LogTwo\n"
    if raw.count(marker) != 1 or raw.count("  sorry\n") != 1:
        raise ValueError("Unexpected PR source layout")
    body = raw[raw.index(marker):]
    prefix = ("-- Generated from the pinned PR; mathematical namespace body is verbatim.\n"
              "import Mathlib\n"
              "import FormalConjecturesUtil.Answer\n"
              "import FormalConjecturesUtil.Attributes.Basic\n\n")
    for name in ["RawPRFC.lean", "ChallengeFC.lean"]:
        path = HERE / name
        output = prefix + body
        if check:
            if path.read_text() != output:
                raise ValueError("Reference differs from the actual PR: " + name)
        else:
            path.write_text(output)
    return {"namespace_body_verbatim": True,
            "namespace_body_sha256": hashlib.sha256(body.encode()).hexdigest(),
            "changes": ["replace FC module/public import/public section wrapper with 4.34.1 imports"],
            "raw_pr_variant": "RawPRFC.lean; identical to ChallengeFC.lean",
            "answer": "answer(2), unchanged", "placeholder": "one intentional Challenge sorry"}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    print(generate(parser.parse_args().check))
