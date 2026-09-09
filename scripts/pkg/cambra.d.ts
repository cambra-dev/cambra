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

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_program_free: (a: number, b: number) => void;
    readonly init_panic_hook: () => void;
    readonly program_close: (a: number, b: number, c: number, d: number) => void;
    readonly program_compile: (a: number, b: number, c: number, d: number, e: number, f: number) => void;
    readonly program_frame: (a: number, b: number, c: number) => void;
    readonly program_push: (a: number, b: number, c: number, d: number, e: number) => void;
    readonly program_snapshot: (a: number, b: number) => void;
    readonly program_tick: (a: number, b: number) => void;
    readonly __wbindgen_export: (a: number, b: number) => number;
    readonly __wbindgen_export2: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_export3: (a: number) => void;
    readonly __wbindgen_export4: (a: number, b: number, c: number) => void;
    readonly __wbindgen_add_to_stack_pointer: (a: number) => number;
}

export type SyncInitInput = BufferSource | WebAssembly.Module;

/**
 * Instantiates the given `module`, which can either be bytes or
 * a precompiled `WebAssembly.Module`.
 *
 * @param {{ module: SyncInitInput }} module - Passing `SyncInitInput` directly is deprecated.
 *
 * @returns {InitOutput}
 */
export function initSync(module: { module: SyncInitInput } | SyncInitInput): InitOutput;

/**
 * If `module_or_path` is {RequestInfo} or {URL}, makes a request and
 * for everything else, calls `WebAssembly.instantiate` directly.
 *
 * @param {{ module_or_path: InitInput | Promise<InitInput> }} module_or_path - Passing `InitInput` directly is deprecated.
 *
 * @returns {Promise<InitOutput>}
 */
export default function __wbg_init (module_or_path?: { module_or_path: InitInput | Promise<InitInput> } | InitInput | Promise<InitInput>): Promise<InitOutput>;
