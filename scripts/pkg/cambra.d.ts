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
     * Replace the running program with the version `source` describes, and
     * report what it kept as `{"generation": n, "kept": k, "bound": b}`.
     *
     * The page swaps its edited source in without losing what the program is
     * holding: every operator whose computation is unchanged keeps running, and
     * every mutable variable resumes from the value it held. `kept` of `bound`
     * counts the operators taken from the replaced version rather than built,
     * which is the evidence for the rest. Re-deriving the state instead, by
     * pushing a journal of rows into a second program, would keep none of them.
     *
     * `generation` is the version now running, counting from `0`. The same
     * number rides `snapshot()`'s `meta.generation` and every `frame()`, which
     * is how a reader holding panes from one version recognizes a frame naming
     * nodes it has never seen: a rebuilt operator is minted a fresh `NodeId`,
     * and re-reading the payload is what resolves it.
     *
     * A JSON string, as `snapshot()`, `frame()` and `subscriptions()` return,
     * because a page hands all four to the one consumer that parses them. An
     * object would buy destructuring at the price of the `json_compatible` care
     * [`tick`](Self::tick) documents, for a payload read once per edit rather
     * than once per pass. The rendered diff and the loops a version adds above
     * the start of what they read stay off it: those two are the control port's
     * reply to an author at a terminal, and a page re-reads `snapshot()` after
     * an accepted reload, whose source and IR panes are the new version.
     *
     * Throws the rendered diagnostics for a version that does not compile, or
     * that cannot take over the state the running program is holding. Such a
     * throw leaves the running program answering, at the generation this last
     * reported: the version is compiled and checked before anything is torn
     * down. A typo is a caught exception and a stale page, not a program that
     * stops.
     */
    reload(source: string): string;
    /**
     * Make one call against the route `method path`, as `rows`.
     *
     * The page is the listener a `wasm_serve` in the program binds, so this is
     * what a `fetch` in the page turns into: the request crosses as rows of the
     * route's declared record type rather than as a body, and the reply comes
     * back in the next `tick`'s `outputs` under the route's own name
     * (`"PATCH /cart"`). Nothing in the program parses or renders a body.
     */
    request(method: string, path: string, rows: any): void;
    /**
     * The `/api/snapshot` payload for the running version.
     *
     * What the inspector renders its source and IR panes from. Computed at
     * compile and re-rendered by an accepted [`reload`](Self::reload), which is
     * when a page re-reads it: the version it describes is the one
     * `meta.generation` names.
     */
    snapshot(): string;
    /**
     * What the program subscribes to, as
     * `[{source, endpoint, feed, products}]`.
     *
     * The page owns the WebSocket. A `wasm_socket_subscribe` in the program
     * binds a declared source and says what fills it; this is how the page
     * learns what to connect to, so the endpoint and the products live in the
     * program rather than in two places that have to agree. What comes back
     * off the socket is decoded by the page and pushed into `source` through
     * [`push`](Self::push), like any other source — there is no socket in the
     * module, and on `wasm32` there could not be one.
     *
     * Read after `compile` and after an accepted [`reload`](Self::reload),
     * which replaces the list rather than adding to it: a feed that leaves it
     * is a socket the page should close, and one that arrives or changes its
     * products is one it should open.
     */
    subscriptions(): string;
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
    readonly program_reload: (a: number, b: number, c: number, d: number) => void;
    readonly program_request: (a: number, b: number, c: number, d: number, e: number, f: number, g: number) => void;
    readonly program_snapshot: (a: number, b: number) => void;
    readonly program_subscriptions: (a: number, b: number) => void;
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
