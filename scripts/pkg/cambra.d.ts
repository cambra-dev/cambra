/* tslint:disable */
/* eslint-disable */

/**
 * A compiled program the page drives.
 */
export class Program {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Say that no further rows will arrive on `source`.
     */
    close(source: string): void;
    /**
     * Compile `source` against `channels`, a JSON array of
     * `{name, kind, type}` declarations.
     *
     * Throws with the rendered diagnostics rather than returning a status, so
     * a caller that forgets to check gets an exception instead of a program
     * that silently does nothing.
     */
    static compile(name: string, source: string, channels: any): Program;
    /**
     * The live frame for what the program has produced.
     *
     * The same bytes the native inspector's websocket sends, so the frontend
     * consumes one format whichever host it is attached to. Worth rendering on
     * a tick that reported `produced`; on any other it repeats what the last
     * one said.
     */
    frame(final_frame: boolean): string;
    /**
     * Append `rows` to the source named `source`.
     *
     * `rows` is a JSON array of objects matching the source's declared row
     * type. A missing, extra or mistyped field throws.
     */
    push(source: string, rows: any): void;
    /**
     * The `/api/snapshot` payload, computed once at compile.
     *
     * What the inspector renders its source and IR panes from.
     */
    snapshot(): string;
    /**
     * Advance the program once, and return what its sinks produced as
     * `{outputs: [{sink, rows}], produced, done}`.
     */
    tick(): any;
}

/**
 * Route a Rust panic to the browser console rather than an opaque trap.
 *
 * A panic in a WebAssembly module unwinds into an `unreachable`, which reaches
 * the page as "RuntimeError: unreachable executed" and names nothing. Call once
 * before anything else.
 */
export function init_panic_hook(): void;
