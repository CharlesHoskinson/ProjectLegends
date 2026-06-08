## Design

Extend the capability truth model without breaking the existing Markdown matrix checker.

Recommended fields:

- `direct_status`: current direct capability status.
- `proxy_status`: public proxy capability status.
- `proxy_route_status`: whether transport/dispatcher routing exists.
- `evidence_files`: implementation and test evidence.
- `notes`: concise human-readable rationale.

Rules:

- `proxy-supported` requires functional support evidence, not only a message route.
- `proxy-routed` may be used when request/dispatcher plumbing exists but public behavior remains partial or unsupported.
- A `direct_status` of `partial` should normally prevent `proxy-supported` unless a note and test evidence prove the proxy path resolves the direct limitation.
- `proxy-missing` should mean no proxy body or dispatcher route exists.
- `proxy-unsupported` should mean the proxy explicitly returns unsupported.

Update the validator to enforce these rules and emit actionable errors.

## Migration

Apply the new fields to all 50 public APIs. Preserve the current Markdown table while adding enough evidence to make semantic drift detectable.
