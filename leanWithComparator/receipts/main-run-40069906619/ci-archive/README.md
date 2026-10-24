# Original public main CI archive

[Main run 40069906619, attempt 1](https://github.com/KitaKen1/log2-irrationality-exponent/actions/runs/40069906619) succeeded on 2026-10-24. These copies are stored in Git, independently of the Actions artifact retention period.

| Record | Value |
| --- | --- |
| Branch | `main` |
| Tested verification commit | `5d606b4adbc451061271f89636f9fc0187b64bd4` |
| Original proof commit | `93a66a6c6b69e5e2f7775d791fd4943f4b1cf671` |
| FC statement commit | `78d227fba77b02455c326e4e4d93d9881b3db025` |
| Target | `LogTwo.irrationalityExponent_log_two` |
| Artifact ID | `12551343637` |
| Artifact SHA-256 | `7abed9d244cd8d01f02d5f09a132eadec1eabe83bbea3c8b41cbfacff64b1725` |

## Preserved files

- [Original artifact ZIP](fc6923-evidence-40069906619-1.zip), byte-for-byte as downloaded. Its SHA-256 matches GitHub's artifact metadata. It contains verification receipts, stage logs, tool-build logs and dependency-bootstrap logs.
- [Full job log](job-120800899084.log), downloaded from the completed job's GitHub API log endpoint without text conversion.
- [Run metadata](run.json), [job and step metadata](jobs.json), and [artifact metadata](artifacts.json), saved from the GitHub API.
- [Archive manifest](archive.json) and [SHA-256 checksums](SHA256SUMS).
- [Readable receipt, original result JSON and extracted stage logs](../).

The original ZIP's `evidence/result.json` matches the separately committed [result.json](../result.json) byte for byte. That receipt records successful comparison, independent nanoda replay of 117,647 declarations, exactly the three permitted axioms, and seven passing controls. The archive manifest identifies the tested source commit separately from the later commits which preserve receipts and documentation.

Successful-run NDJSON exports are represented by their hashes in the receipt. The workflow uploads the full exports only for failure diagnostics. The original pinned proof was rebuilt from source with the fixed Mathlib cache; no proof-project build cache was restored. The eight recorded pre-existing style/deprecation warnings were allowed, and unexpected warnings failed the build.

## Verify this archive

From this directory, run:

```bash
sha256sum -c SHA256SUMS
# macOS:
shasum -a 256 -c SHA256SUMS
```

To repeat the mathematical checks, use the [workflow at the tested commit](https://github.com/KitaKen1/log2-irrationality-exponent/blob/5d606b4adbc451061271f89636f9fc0187b64bd4/.github/workflows/fc-log2-verification.yml) and its [reproduction instructions](https://github.com/KitaKen1/log2-irrationality-exponent/tree/5d606b4adbc451061271f89636f9fc0187b64bd4/leanWithComparator). This run used the pinned Comparator-core driver, lean4export and independent nanoda checker. The separate landrun CLI pipeline, a full dependency cold build and human mathematical review are outside this receipt's scope.
