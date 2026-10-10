// Sharing (docs/design/website.md 4.10): the program, deflated with the browser's CompressionStream and
// base64url-encoded, in the URL fragment (`#code=…`), or a reference example by name (`#example=…`).
// The fragment never reaches the server; nothing is stored.

async function pipe(bytes, stream) {
  const out = new Blob([bytes]).stream().pipeThrough(stream);
  return new Uint8Array(await new Response(out).arrayBuffer());
}

function toBase64url(bytes) {
  let s = "";
  for (let i = 0; i < bytes.length; i += 0x8000) s += String.fromCharCode(...bytes.subarray(i, i + 0x8000));
  return btoa(s).replace(/\+/g, "-").replace(/\//g, "_").replace(/=+$/, "");
}

function fromBase64url(text) {
  const s = atob(text.replace(/-/g, "+").replace(/_/g, "/"));
  return Uint8Array.from(s, (c) => c.charCodeAt(0));
}

export async function encodeProgram(text) {
  const bytes = await pipe(new TextEncoder().encode(text), new CompressionStream("deflate-raw"));
  return "code=" + toBase64url(bytes);
}

// the fragment's request: { code } or { example }, or {} for an unknown or broken fragment
export async function readFragment(hash) {
  const params = new URLSearchParams(hash.replace(/^#/, ""));
  try {
    if (params.has("code")) {
      const bytes = await pipe(fromBase64url(params.get("code")), new DecompressionStream("deflate-raw"));
      return { code: new TextDecoder().decode(bytes) };
    }
  } catch (_) {
    return {};
  }
  return params.has("example") ? { example: params.get("example") } : {};
}
