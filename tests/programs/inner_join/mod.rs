//! SQL-style INNER JOIN over two record lists — pair each user with their
//! orders by user-id, projecting customer name and order total.

use super::common::expect_scalar;

#[test]
fn inner_join() {
    expect_scalar(
        include_str!("program.cambra"),
        r#"Function [ {customer: "alice", total: 50}, {customer: "alice", total: 100}, {customer: "bob", total: 75} ]"#,
    );
}
