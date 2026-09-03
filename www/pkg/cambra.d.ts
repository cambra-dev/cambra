/* tslint:disable */
/* eslint-disable */

/**
 * Result of [`compile_and_run`]. Every field defaults to empty; `error`
 * non-empty means the others carry whatever partial information was
 * available before the failure (e.g. `ast`/`operators` are still populated
 * on a driver-level error, since those are captured before the run loop
 * starts, but not on a compile error, since there is no compiled tree yet).
 */
export class RunResult {
    private constructor();
    free(): void;
    [Symbol.dispose](): void;
    /**
     * Symbolic-form join-planned AST (see [`symbolic`]).
     */
    ast: string;
    /**
     * Non-empty on failure: a compile error, an unsupported program shape
     * (sink-driven), or the `MAX_TICKS` hang guard firing.
     */
    error: string;
    /**
     * Pretty-printed operator tree, one per program output.
     */
    operators: string;
    /**
     * Newline-joined trace of each tick's emitted tile.
     */
    output: string;
    /**
     * The last tick's producer snapshot, as the JSON object
     * `{"tick":N,"producers":[...]}` that `www/index.html`'s inspector
     * panel expects (the same shape the native `--inspect` dashboard
     * polls from `/api/snapshot`).
     */
    snapshot: string;
}

/**
 * Compiles and runs a Cambra program to completion.
 */
export function compile_and_run(code: string): RunResult;

/**
 * Registers a panic hook that forwards Rust panics to the browser console
 * (`console.error`) instead of the opaque "unreachable executed" trap
 * message. Call this once before `compile_and_run`.
 */
export function init_panic_hook(): void;

export type InitInput = RequestInfo | URL | Response | BufferSource | WebAssembly.Module;

export interface InitOutput {
    readonly memory: WebAssembly.Memory;
    readonly __wbg_get_runresult_ast: (a: number) => [number, number];
    readonly __wbg_get_runresult_error: (a: number) => [number, number];
    readonly __wbg_get_runresult_operators: (a: number) => [number, number];
    readonly __wbg_get_runresult_output: (a: number) => [number, number];
    readonly __wbg_get_runresult_snapshot: (a: number) => [number, number];
    readonly __wbg_runresult_free: (a: number, b: number) => void;
    readonly __wbg_set_runresult_ast: (a: number, b: number, c: number) => void;
    readonly __wbg_set_runresult_error: (a: number, b: number, c: number) => void;
    readonly __wbg_set_runresult_operators: (a: number, b: number, c: number) => void;
    readonly __wbg_set_runresult_output: (a: number, b: number, c: number) => void;
    readonly __wbg_set_runresult_snapshot: (a: number, b: number, c: number) => void;
    readonly compile_and_run: (a: number, b: number) => number;
    readonly init_panic_hook: () => void;
    readonly __wbindgen_free: (a: number, b: number, c: number) => void;
    readonly __wbindgen_malloc: (a: number, b: number) => number;
    readonly __wbindgen_realloc: (a: number, b: number, c: number, d: number) => number;
    readonly __wbindgen_externrefs: WebAssembly.Table;
    readonly __wbindgen_start: () => void;
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
