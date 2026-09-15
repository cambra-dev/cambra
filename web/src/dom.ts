// Element construction shared by the pane views.

/**
 * A new element with an optional class and text.
 *
 * Text goes in through `textContent`, never `innerHTML`: a pane renders payload
 * content — node labels, rendered types, a rejected value in a wire error — and
 * that content is a compiler's output, not markup.
 */
export function el(tag: string, className?: string, text?: string): HTMLElement {
  const node = document.createElement(tag);
  if (className) node.className = className;
  if (text !== undefined) node.textContent = text;
  return node;
}
