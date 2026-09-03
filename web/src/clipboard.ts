// The clipboard boundary. Every pane's text is produced by a pure serializer;
// this is the one place a produced string leaves the app, isolated so those
// serializers stay testable without a DOM.
//
// There is no `document.execCommand` fallback. `navigator.clipboard` requires a
// secure context, and the inspector is served at `http://localhost:<port>` — a
// potentially-trustworthy origin, so the API is present in the deployment this
// ships for. A port-forwarded `http://<lan-ip>:<port>` has no clipboard; that
// reports failure rather than appearing to copy nothing.

/**
 * Write `text` to the system clipboard, resolving whether it landed.
 *
 * False covers both an absent API and a refused write (a denied permission, an
 * unfocused document). The caller surfaces that on the button — a rejected
 * `writeText` swallowed here would look identical to a successful copy.
 */
export async function copyToClipboard(text: string): Promise<boolean> {
  const clipboard: Clipboard | undefined = navigator.clipboard;
  if (!clipboard?.writeText) return false;
  try {
    await clipboard.writeText(text);
    return true;
  } catch {
    return false;
  }
}
