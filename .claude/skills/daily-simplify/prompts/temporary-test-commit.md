# Trying a test in a temporary commit

A reviewer reads a commit it must not change, but may try a new test against it. The test goes in a
temporary commit on top of `@`, which the reviewer removes before it reports. `WS` is the review's
workspace, `SCRATCH` its scratch directory and `SKILL` the daily-simplify skill directory, as the
reviewer's prompt gives them.

1. Record where `@` is: `jj -R WS log -r @ --no-graph -T commit_id`, the id `ORIG`.
2. `jj -R WS new ORIG -m "temporary: review test"`, then write the test. Edit nothing but the test.
3. Run it with `SKILL/scripts/in-workspace.sh WS 1800 cargo test …`, scoped to the one binary that
   holds it: `-p <crate> --lib <name>` for a unit test, `--test it <name>` for one under
   `tests/it/`. Save its output under `SCRATCH`.
4. Copy the test into the report, with the file it belongs in and the result it produced.
5. `jj -R WS edit ORIG`, then `jj -R WS abandon <the temporary commit>`. Confirm that
   `jj -R WS log -r @ --no-graph -T commit_id` prints `ORIG` again and `jj -R WS status` shows no
   changes.

The orchestrator compares the workspace's commit ids before and after the review. A temporary
commit left behind, or any other edit, voids the review.
